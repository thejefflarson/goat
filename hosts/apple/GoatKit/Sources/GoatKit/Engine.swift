import Foundation
import WebKit

/// Owns the web view that compiles and draws, and speaks to it: source goes in
/// through `callAsyncJavaScript`, and `EngineMessage`s come back through a
/// script message handler. The web view loads only the bundled page.
@MainActor
public final class Engine: NSObject, ObservableObject {
    public enum Phase: Equatable {
        case loading, ready, running, finished
        case failed(String)
    }

    public static let maxOutputLines = 2000

    @Published public private(set) var phase = Phase.loading
    @Published public private(set) var diagnostics: [Diagnostic] = []
    @Published public private(set) var output: [String] = []

    /// Replaced when the watchdog stops a program, so a view must follow this property.
    @Published public private(set) var webView: WKWebView

    private let assets: URL?
    private var bridge: ScriptBridge
    private var stoppedNotice: String?
    private var watchdog: WatchdogTimer!

    /// `assets` is the folder holding embed.html, dist/ and goat_web.wasm.
    public init(assets: URL?) {
        self.assets = assets
        (webView, bridge) = Self.makeWebView(assets: assets)
        super.init()
        watchdog = WatchdogTimer { [weak self] call in self?.replaceWebView(stopped: call.overrunMessage) }
        attach()
        if assets == nil {
            phase = .failed("This copy of goat is missing its drawing engine.")
        } else {
            webView.load(URLRequest(url: AssetScheme.url("embed.html")))
        }
    }

    public func run(source: String) {
        guard phase != .loading else { return }
        diagnostics = []
        output = []
        evaluate("return await window.goat.run(source)", source: source)
    }

    public func stop() {
        evaluate("window.goat?.stop()")
        if phase == .running { phase = .ready }
    }

    public func clearDiagnostics() {
        if !diagnostics.isEmpty { diagnostics = [] }
    }

    func receive(_ body: Any) {
        guard let message = EngineMessage.decode(body) else { return }
        switch message {
        case .ready:
            guard phase == .loading else { break }
            phase = stoppedNotice.map(Phase.failed) ?? .ready
            stoppedNotice = nil
        case .diagnostics(let found):
            diagnostics = found
        case .output(let lines):
            output = Array((output + lines).suffix(Self.maxOutputLines))
        case .state(.running, _):
            phase = .running
        case .state(.finished, _):
            phase = .finished
        case .state(.failed, let message):
            phase = .failed(message ?? "your program stopped")
        case .beat(let count, let call):
            watchdog.beat(count: count, call: call)
        }
    }

    /// A non-persistent data store gives every web view its own web content
    /// process, so a replacement never shares one with the runaway it replaces.
    private static func makeWebView(assets: URL?) -> (WKWebView, ScriptBridge) {
        let configuration = WKWebViewConfiguration()
        configuration.websiteDataStore = .nonPersistent()
        let bridge = ScriptBridge()
        configuration.userContentController.add(bridge, name: "goat")
        if let assets {
            configuration.setURLSchemeHandler(AssetSchemeHandler(root: assets), forURLScheme: AssetScheme.name)
        }
        return (WKWebView(frame: .zero, configuration: configuration), bridge)
    }

    private func attach() {
        bridge.receive = { [weak self] body in self?.receive(body) }
        webView.navigationDelegate = self
    }

    /// Drops the stuck page and loads a fresh one; Run stays disabled (`.loading`)
    /// until the new page is ready, and then the stop is what the user sees.
    private func replaceWebView(stopped message: String) {
        bridge.receive = nil
        webView.navigationDelegate = nil
        webView.configuration.userContentController.removeScriptMessageHandler(forName: "goat")
        webView.removeFromSuperview()
        watchdog.reset()
        (webView, bridge) = Self.makeWebView(assets: assets)
        attach()
        diagnostics = []
        stoppedNotice = message
        phase = .loading
        webView.load(URLRequest(url: AssetScheme.url("embed.html")))
    }

    /// Uses the completion-handler form and holds the web view weakly: an awaiting
    /// task would keep a stuck web view alive, and its web content process with it.
    /// A failure from a web view the watchdog has since replaced is not the new
    /// page's failure.
    private func evaluate(_ script: String, source: String? = nil) {
        webView.callAsyncJavaScript(
            script, arguments: source.map { ["source": $0] } ?? [:], in: nil, in: .page
        ) { [weak self, weak target = webView] result in
            guard case .failure(let error) = result, let self, let target, target === self.webView else { return }
            self.phase = .failed("The drawing engine did not respond: \(error.localizedDescription)")
        }
    }
}

extension Engine: WKNavigationDelegate {
    public func webView(
        _ webView: WKWebView, decidePolicyFor action: WKNavigationAction,
        decisionHandler: @escaping (WKNavigationActionPolicy) -> Void
    ) {
        decisionHandler(action.request.url?.scheme == AssetScheme.name ? .allow : .cancel)
    }
}

/// Keeps the web view's strong reference to its message handler from forming a
/// cycle with the engine, and drops messages that did not come from the bundled page.
private final class ScriptBridge: NSObject, WKScriptMessageHandler {
    var receive: ((Any) -> Void)?

    func userContentController(_ controller: WKUserContentController, didReceive message: WKScriptMessage) {
        guard message.frameInfo.isMainFrame, message.frameInfo.request.url?.scheme == AssetScheme.name else {
            return
        }
        receive?(message.body)
    }
}
