import Foundation

/// The custom URL scheme the web view loads its bundled pages through. File
/// URLs would block the page's module scripts and its `fetch` of the compiler,
/// and a private scheme keeps the page from reaching the network.
public enum AssetScheme {
    public static let name = "goat-app"
    public static let host = "app"

    public static func url(_ path: String) -> URL {
        URL(string: "\(name)://\(host)/\(path)")!
    }
}

public enum AssetPath {
    /// The file under `root` that `url` names, or nil when it names anything
    /// else: another host, a `..` segment, a directory, or a symlink that leaves `root`.
    public static func resolve(_ url: URL, under root: URL) -> URL? {
        guard url.scheme == AssetScheme.name, url.host == AssetScheme.host else { return nil }
        let segments = url.path.split(separator: "/").map(String.init)
        guard !segments.isEmpty, !segments.contains(where: { $0 == ".." || $0 == "." || $0.contains("\0") })
        else { return nil }
        let base = root.resolvingSymlinksInPath()
        let file = segments.reduce(base) { $0.appendingPathComponent($1) }.resolvingSymlinksInPath()
        guard file.path.hasPrefix(base.path + "/") else { return nil }
        var isDirectory: ObjCBool = false
        guard FileManager.default.fileExists(atPath: file.path, isDirectory: &isDirectory), !isDirectory.boolValue
        else { return nil }
        return file
    }

    public static func mimeType(for file: URL) -> String {
        switch file.pathExtension {
        case "html": return "text/html; charset=utf-8"
        case "js": return "text/javascript; charset=utf-8"
        case "wasm": return "application/wasm"
        case "css": return "text/css; charset=utf-8"
        case "json": return "application/json"
        default: return "application/octet-stream"
        }
    }
}
