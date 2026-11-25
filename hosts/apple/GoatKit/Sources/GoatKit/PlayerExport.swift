#if os(macOS)
import Foundation

/// Export App…: the signed GoatPlayer.app that ships in Goat's Resources, copied
/// with the program and the app's name written in.
public enum PlayerExport {
    public static let programPath = "Contents/Resources/program.goat"

    /// The player template inside `bundle` (the running app), if it has one.
    public static func templateURL(in bundle: Bundle = .main) -> URL? {
        bundle.url(forResource: "GoatPlayer", withExtension: "app")
    }

    /// `local.goat.` and `name` in lowercase ASCII letters, digits and hyphens;
    /// the same rule `goat build --native` uses.
    public static func bundleIdentifier(name: String) -> String {
        let slug = name.lowercased()
            .split { !($0.isASCII && ($0.isLetter || $0.isNumber)) }
            .joined(separator: "-")
        return goatBundlePrefix + (slug.isEmpty ? "app" : slug)
    }

    /// Writes the app `destination`, named after its file, that runs `program`.
    public static func export(program: String, template: URL, to destination: URL) throws {
        guard FileManager.default.fileExists(atPath: template.path) else {
            throw ExportError.missingPlayer
        }
        let name = destination.deletingPathExtension().lastPathComponent
        try exportBundle(template: template, to: destination) { bundle in
            let resources = bundle.appendingPathComponent("Contents/Resources")
            try FileManager.default.createDirectory(
                at: resources, withIntermediateDirectories: true)
            try Data(program.utf8).write(to: bundle.appendingPathComponent(programPath))
            try patchInfo(of: bundle, name: name)
        }
    }

    private static func patchInfo(of bundle: URL, name: String) throws {
        let path = bundle.appendingPathComponent("Contents/Info.plist")
        let data = try Data(contentsOf: path)
        var info =
            try PropertyListSerialization.propertyList(from: data, format: nil) as? [String: Any]
            ?? [:]
        info["CFBundleName"] = name
        info["CFBundleDisplayName"] = name
        info["CFBundleIdentifier"] = bundleIdentifier(name: name)
        try PropertyListSerialization.data(fromPropertyList: info, format: .xml, options: 0)
            .write(to: path)
    }
}

/// Whether this Mac has the Command Line Tools, which a native export needs.
public enum NativeExport {
    public static let clangPath = "/Library/Developer/CommandLineTools/usr/bin/clang"

    public static func toolsInstalled(clang: String = clangPath) -> Bool {
        FileManager.default.isExecutableFile(atPath: clang)
    }

    /// Why the app cannot run a native build itself, and what to do instead.
    public static func explanation(name: String) -> String {
        """
        A native app is compiled with the Command Line Tools and the goat command, and \
        Goat's sandbox does not let it run either. Save the program, then in Terminal run:

        goat build --native \(name).goat -o \(name).app
        """
    }
}
#endif
