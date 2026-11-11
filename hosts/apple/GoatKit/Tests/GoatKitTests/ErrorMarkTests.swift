#if os(macOS)
import XCTest

@testable import GoatKit

@MainActor
final class ErrorMarkTests: XCTestCase {
    func testErrorRangesUnderlineWithoutBackgroundFill() {
        let storage = NSTextStorage(string: "let x = oops")
        paint(storage, ranges: [NSRange(location: 8, length: 4)])
        XCTAssertNotNil(storage.attribute(.underlineStyle, at: 9, effectiveRange: nil))
        XCTAssertNotNil(storage.attribute(.underlineColor, at: 9, effectiveRange: nil))
        XCTAssertNil(storage.attribute(.backgroundColor, at: 9, effectiveRange: nil))
        XCTAssertNil(storage.attribute(.underlineStyle, at: 0, effectiveRange: nil))
    }

    func testRepaintClearsThePreviousMarks() {
        let storage = NSTextStorage(string: "let x = oops")
        paint(storage, ranges: [NSRange(location: 8, length: 4)])
        paint(storage, ranges: [])
        XCTAssertNil(storage.attribute(.underlineStyle, at: 9, effectiveRange: nil))
    }
}
#endif
