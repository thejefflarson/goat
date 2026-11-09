#if os(macOS)
import Combine
import WebKit
import XCTest

@testable import GoatKit

/// Drives the real `Engine` through a real, off-screen `WKWebView`: the bundled
/// page loads, the compiler wasm boots, a program compiles and draws. Everything
/// the page says is captured, so a failure names its cause instead of leaving a
/// blank canvas. Needs `scripts/stage-web.sh` to have filled `Resources/web`.
@MainActor
final class EngineWebViewTests: XCTestCase {
    private let spiral = """
        color("purple");
        for side from 1 to 60 do
          forward(side * 3);
          right(89)
        done
        """

    func testTheEngineBootsCompilesAndDrawsASpiral() async throws {
        let probe = try EngineProbe()

        try await probe.wait(for: .ready)
        probe.engine.run(source: spiral)
        try await probe.wait(for: .finished)

        let inked = try await probe.inkedPixels()
        XCTAssertGreaterThan(inked, 100, "the canvas is blank after the program finished\n\(probe.report)")
    }

    func testAProgramWithAProblemReportsDiagnosticsInsteadOfDrawing() async throws {
        let probe = try EngineProbe()

        try await probe.wait(for: .ready)
        probe.engine.run(source: "forward(\"far\")")
        try await probe.wait(for: .failed("your program has problems"))

        XCTAssertFalse(probe.engine.diagnostics.isEmpty, probe.report)
        let inked = try await probe.inkedPixels()
        XCTAssertEqual(inked, 0)
    }
}

/// An `Engine` plus a record of everything its page does: console output,
/// uncaught errors, CSP violations, navigation failures and web content process exits.
@MainActor
private final class EngineProbe: NSObject, WKScriptMessageHandler {
    static let timeout: TimeInterval = 30

    let engine: Engine
    private var log: [String] = []
    private var phases: [Engine.Phase] = []
    private var subscription: AnyCancellable?
    private var navigation: NavigationLog?

    var report: String {
        "engine phases: \(phases)\npage log:\n"
            + (log.isEmpty ? "  (nothing)" : log.map { "  " + $0 }.joined(separator: "\n"))
    }

    init(file: StaticString = #filePath) throws {
        let assets = try Self.stagedWeb(near: file)
        engine = Engine(assets: assets)
        super.init()
        subscription = engine.$phase.sink { [weak self] in self?.phases.append($0) }
        watchPage(of: engine.webView)
    }

    func wait(for phase: Engine.Phase) async throws {
        let deadline = Date().addingTimeInterval(Self.timeout)
        while engine.phase != phase {
            if case .failed(let message) = engine.phase {
                XCTFail("the engine failed while waiting for \(phase): \(message)\n\(report)")
                throw CancellationError()
            }
            if Date() > deadline {
                XCTFail("the engine never reached \(phase) in \(Self.timeout)s, stuck at \(engine.phase)\n\(report)")
                throw CancellationError()
            }
            try await Task.sleep(nanoseconds: 20_000_000)
        }
    }

    /// Counts canvas pixels with any ink; a blank canvas is all transparent.
    func inkedPixels() async throws -> Int {
        let script = """
            const canvas = document.getElementById("canvas");
            const data = canvas.getContext("2d").getImageData(0, 0, canvas.width, canvas.height).data;
            let inked = 0;
            for (let i = 3; i < data.length; i += 4) if (data[i] !== 0) inked++;
            return inked;
            """
        let result = try await engine.webView.callAsyncJavaScript(script, contentWorld: .page)
        return result as? Int ?? -1
    }

    func userContentController(_ controller: WKUserContentController, didReceive message: WKScriptMessage) {
        log.append("\(message.body)")
    }

    private func watchPage(of webView: WKWebView) {
        // A web view outside a visible window never delivers animation frames, so
        // the drawing would wait forever; a timer stands in for the display link.
        let hook = """
            const send = (line) => window.webkit.messageHandlers.goatlog.postMessage(line);
            for (const level of ["log", "info", "warn", "error"]) {
              const original = console[level].bind(console);
              console[level] = (...args) => { send("console." + level + ": " + args.join(" ")); original(...args); };
            }
            window.addEventListener("error", (e) => send("uncaught: " + e.message + " @ " + e.filename + ":" + e.lineno));
            window.addEventListener("unhandledrejection", (e) => send("unhandled rejection: " + e.reason));
            window.requestAnimationFrame = (frame) => setTimeout(() => frame(performance.now()), 1);
            document.addEventListener("securitypolicyviolation", (e) =>
              send("CSP violation: " + e.violatedDirective + " blocked " + e.blockedURI));
            """
        let controller = webView.configuration.userContentController
        controller.add(self, name: "goatlog")
        controller.addUserScript(WKUserScript(source: hook, injectionTime: .atDocumentStart, forMainFrameOnly: true))
        navigation = NavigationLog(engine: engine) { [weak self] in self?.log.append($0) }
        webView.navigationDelegate = navigation
    }

    /// The host app's bundled copy when sandboxed tests run inside it, which cannot
    /// read the source tree; otherwise the staged folder beside this package.
    private static func stagedWeb(near file: StaticString) throws -> URL {
        let hostsApple = URL(fileURLWithPath: "\(file)")
            .deletingLastPathComponent().deletingLastPathComponent().deletingLastPathComponent()
            .deletingLastPathComponent()
        let root = Bundle.main.url(forResource: "web", withExtension: nil)
            ?? hostsApple.appendingPathComponent("Resources/web")
        guard FileManager.default.fileExists(atPath: root.appendingPathComponent("embed.html").path) else {
            throw XCTSkip("\(root.path) is not staged; run hosts/apple/scripts/stage-web.sh")
        }
        return root
    }
}

/// Records how navigation went and leaves every policy decision to the engine,
/// whose delegate role this stands in for.
@MainActor
private final class NavigationLog: NSObject, WKNavigationDelegate {
    private let engine: Engine
    private let record: (String) -> Void

    init(engine: Engine, record: @escaping (String) -> Void) {
        self.engine = engine
        self.record = record
    }

    func webView(
        _ webView: WKWebView, decidePolicyFor action: WKNavigationAction,
        decisionHandler: @escaping (WKNavigationActionPolicy) -> Void
    ) {
        record("navigation to \(action.request.url?.absoluteString ?? "?")")
        engine.webView(webView, decidePolicyFor: action, decisionHandler: decisionHandler)
    }

    func webView(_ webView: WKWebView, didFinish navigation: WKNavigation!) {
        record("navigation finished")
    }

    func webView(_ webView: WKWebView, didFail navigation: WKNavigation!, withError error: Error) {
        record("navigation failed: \(error)")
    }

    func webView(_ webView: WKWebView, didFailProvisionalNavigation navigation: WKNavigation!, withError error: Error) {
        record("navigation failed before committing: \(error)")
    }

    func webViewWebContentProcessDidTerminate(_ webView: WKWebView) {
        record("web content process terminated (in a sandboxed app, check for com.apple.security.network.client)")
    }
}
#endif
