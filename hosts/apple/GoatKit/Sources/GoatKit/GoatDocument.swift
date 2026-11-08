import SwiftUI
import UniformTypeIdentifiers

public extension UTType {
    /// Declared as an exported type in each app's Info.plist (project.yml).
    static let goatSource = UTType(exportedAs: "com.thejefflarson.goat.source", conformingTo: .plainText)
}

public struct GoatDocument: FileDocument {
    public static let readableContentTypes = [UTType.goatSource]

    public static let starter = """
        # Press Run to draw a spiral.
        color("purple");
        for side from 1 to 60 do
          forward(side * 3);
          right(89)
        done

        """

    public var text: String

    public init(text: String = GoatDocument.starter) {
        self.text = text
    }

    public init(configuration: ReadConfiguration) throws {
        guard let data = configuration.file.regularFileContents else {
            throw CocoaError(.fileReadCorruptFile)
        }
        self.text = try Self.decode(data)
    }

    public func fileWrapper(configuration: WriteConfiguration) throws -> FileWrapper {
        FileWrapper(regularFileWithContents: Data(text.utf8))
    }

    static func decode(_ data: Data) throws -> String {
        guard let text = String(data: data, encoding: .utf8) else {
            throw CocoaError(.fileReadInapplicableStringEncoding)
        }
        return text
    }
}
