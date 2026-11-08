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

    public let webView: WKWebView

    /// `assets` is the folder holding embed.html, dist/ and goat_web.wasm.
    public init(assets: URL?) {
        let configuration = WKWebViewConfiguration()
        let bridge = ScriptBridge()
        configuration.userContentController.add(bridge, name: "goat")
        if let assets {
            configuration.setURLSchemeHandler(AssetSchemeHandler(root: assets), forURLScheme: AssetScheme.name)
        }
        webView = WKWebView(frame: .zero, configuration: configuration)
        super.init()
        bridge.receive = { [weak self] body in self?.receive(body) }
        webView.navigationDelegate = self
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
            if phase == .loading { phase = .ready }
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
        }
    }

    private func evaluate(_ script: String, source: String? = nil) {
        Task {
            do {
                _ = try await webView.callAsyncJavaScript(
                    script, arguments: source.map { ["source": $0] } ?? [:], in: nil, contentWorld: .page)
            } catch {
                phase = .failed("The drawing engine did not respond: \(error.localizedDescription)")
            }
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
