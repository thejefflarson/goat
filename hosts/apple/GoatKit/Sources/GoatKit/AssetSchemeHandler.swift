import Foundation
import WebKit

final class AssetSchemeHandler: NSObject, WKURLSchemeHandler {
    private let root: URL

    init(root: URL) {
        self.root = root
    }

    func webView(_ webView: WKWebView, start task: WKURLSchemeTask) {
        guard let url = task.request.url else {
            return task.didFailWithError(URLError(.badURL))
        }
        let file = AssetPath.resolve(url, under: root)
        let body = file.flatMap { try? Data(contentsOf: $0) }
        let response = HTTPURLResponse(
            url: url,
            statusCode: body == nil ? 404 : 200,
            httpVersion: "HTTP/1.1",
            headerFields: [
                "Content-Type": file.map(AssetPath.mimeType(for:)) ?? "text/plain",
                "Content-Length": String(body?.count ?? 0),
                "Cache-Control": "no-store",
                "X-Content-Type-Options": "nosniff",
            ])!
        task.didReceive(response)
        task.didReceive(body ?? Data())
        task.didFinish()
    }

    func webView(_ webView: WKWebView, stop task: WKURLSchemeTask) {}
}
