import Foundation

/// Where the iOS app creates new documents: its own Documents folder ("On My
/// iPhone"), never iCloud Drive, so creating never waits on a sync.
public enum LocalDocuments {
    public static let fileExtension = "goat"

    public static func directory(fileManager: FileManager = .default) throws -> URL {
        try fileManager.url(for: .documentDirectory, in: .userDomainMask, appropriateFor: nil, create: true)
    }

    /// Writes `text` to `Untitled.goat` in `directory`, or `Untitled 2.goat` and so on
    /// when that name is taken, and returns the new file.
    public static func create(
        text: String = GoatDocument.starter, in directory: URL, fileManager: FileManager = .default
    ) throws -> URL {
        var attempt = 1
        while true {
            let name = attempt == 1 ? "Untitled" : "Untitled \(attempt)"
            let url = directory.appendingPathComponent(name).appendingPathExtension(fileExtension)
            if !fileManager.fileExists(atPath: url.path) {
                do {
                    try Data(text.utf8).write(to: url, options: .withoutOverwriting)
                    return url
                } catch let error as CocoaError where error.code == .fileWriteFileExists {
                    // Lost a race for this name; try the next one.
                }
            }
            attempt += 1
        }
    }
}
