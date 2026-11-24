#if os(macOS)
import Foundation

public enum ExportError: Error, Equatable {
    case destinationExists(URL)
    case codesign(status: Int32, output: String)
}

/// Copies the `.app` at `template` to `destination` and signs the copy ad hoc.
/// `destination` must sit in a folder the sandbox lets the app write: one the
/// user picked (`com.apple.security.files.user-selected.read-write`) with its
/// security scope open, or the app's container.
public func exportBundle(template: URL, to destination: URL) throws {
    let files = FileManager.default
    guard !files.fileExists(atPath: destination.path) else {
        throw ExportError.destinationExists(destination)
    }
    try files.copyItem(at: template, to: destination)
    do {
        try adHocSign(destination)
    } catch {
        try? files.removeItem(at: destination)
        throw error
    }
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
