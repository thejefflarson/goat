import Foundation

/// A checker error. `line` and `column` are 1-based and count characters
/// (Unicode scalars, as the checker does); line 0 means the message has no
/// place in the user's source.
public struct Diagnostic: Codable, Equatable, Sendable {
    public let line: Int
    public let column: Int
    public let length: Int
    public let message: String

    public init(line: Int, column: Int, length: Int, message: String) {
        self.line = line
        self.column = column
        self.length = length
        self.message = message
    }

    /// The span in `text`, clamped to its line; nil when the position is not in `text`.
    public func range(in text: String) -> NSRange? {
        guard line >= 1, column >= 1 else { return nil }
        let scalars = text.unicodeScalars
        var lineStart = scalars.startIndex
        for _ in 1..<line {
            guard let newline = scalars[lineStart...].firstIndex(of: "\n") else { return nil }
            lineStart = scalars.index(after: newline)
        }
        guard let start = scalars.index(lineStart, offsetBy: column - 1, limitedBy: scalars.endIndex) else {
            return nil
        }
        let lineEnd = scalars[start...].firstIndex(of: "\n") ?? scalars.endIndex
        let end = scalars.index(start, offsetBy: max(length, 1), limitedBy: lineEnd) ?? lineEnd
        return NSRange(start..<end, in: text)
    }
}
