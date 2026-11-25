#if os(macOS)
import Foundation

public enum ExportError: Error, Equatable {
    /// Something that goat did not make is already at the destination.
    case destinationExists(URL)
    case codesign(status: Int32, output: String)
    case missingPlayer
}

extension ExportError: LocalizedError {
    public var errorDescription: String? {
        switch self {
        case .destinationExists(let url):
            "\(url.lastPathComponent) already exists and wasn't made by goat. Choose another name."
        case .codesign(let status, let output):
            "Signing the app failed (codesign exit \(status)): \(output)"
        case .missingPlayer:
            "This copy of goat has no player to export."
        }
    }
}

/// The bundle identifier prefix every app goat writes carries (`goat build --native`
/// and Export App… alike); it is how a later export knows an existing app is its own.
let goatBundlePrefix = "local.goat."

/// Copies the `.app` at `template` to `destination`, lets `prepare` change the
/// copy, and signs it ad hoc. A goat-made app already at `destination` is
/// replaced; anything else there is refused and left alone.
/// `destination` must sit in a folder the sandbox lets the app write: one the
/// user picked (`com.apple.security.files.user-selected.read-write`) with its
/// security scope open until this returns, or the app's container.
/// `prepare` runs before signing because the signature seals every file in the bundle.
public func exportBundle(
    template: URL, to destination: URL, prepare: (URL) throws -> Void = { _ in }
) throws {
    let files = FileManager.default
    try clearPreviousBundle(destination)
    try files.copyItem(at: template, to: destination)
    do {
        try prepare(destination)
        try adHocSign(destination)
    } catch {
        try? files.removeItem(at: destination)
        throw error
    }
}

/// Removes the app at `destination` if goat made it; throws for anything else
/// there (another app, a file, a symlink, which is never followed).
private func clearPreviousBundle(_ destination: URL) throws {
    let files = FileManager.default
    guard let attributes = try? files.attributesOfItem(atPath: destination.path) else { return }
    let info = NSDictionary(
        contentsOf: destination.appendingPathComponent("Contents/Info.plist"))
    let madeByGoat =
        attributes[.type] as? FileAttributeType == .typeDirectory
        && (info?["CFBundleIdentifier"] as? String)?.hasPrefix(goatBundlePrefix) == true
    guard madeByGoat else { throw ExportError.destinationExists(destination) }
    try files.removeItem(at: destination)
}

func adHocSign(_ bundle: URL) throws {
    let codesign = Process()
    codesign.executableURL = URL(fileURLWithPath: "/usr/bin/codesign")
    codesign.arguments = ["--force", "--deep", "--sign", "-", bundle.path]
    let output = Pipe()
    codesign.standardError = output
    codesign.standardOutput = output
    try codesign.run()
    let text = output.fileHandleForReading.readDataToEndOfFile()
    codesign.waitUntilExit()
    guard codesign.terminationStatus == 0 else {
        throw ExportError.codesign(
            status: codesign.terminationStatus,
            output: String(decoding: text, as: UTF8.self))
    }
}
#endif
