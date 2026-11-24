import XCTest

@testable import GoatKit

final class EngineMessageTests: XCTestCase {
    func testDecodesEachMessageTheEngineSends() {
        XCTAssertEqual(EngineMessage.decode(#"{"type":"ready"}"#), .ready)
        XCTAssertEqual(
            EngineMessage.decode(#"{"type":"output","lines":["hi","there"]}"#), .output(["hi", "there"]))
        XCTAssertEqual(
            EngineMessage.decode(#"{"type":"state","state":"failed","message":"stuck"}"#),
            .state(.failed, message: "stuck"))
        XCTAssertEqual(
            EngineMessage.decode(#"{"type":"state","state":"running"}"#), .state(.running, message: nil))
        XCTAssertEqual(
            EngineMessage.decode(
                #"{"type":"diagnostics","diagnostics":[{"line":2,"column":3,"length":4,"message":"bad"}]}"#),
            .diagnostics([Diagnostic(line: 2, column: 3, length: 4, message: "bad")]))
    }

    func testDecodesHowARerunReloaded() {
        XCTAssertEqual(
            EngineMessage.decode(#"{"type":"reloaded","outcome":"kept"}"#), .reloaded(Reload(reason: nil)))
        let reset = EngineMessage.decode(
            #"{"type":"reloaded","outcome":"reset","reason":{"kind":"field_added","args":["z"]}}"#)
        guard case .reloaded(let reload) = reset else { return XCTFail("\(String(describing: reset))") }
        XCTAssertFalse(reload.keptModel)
        XCTAssertEqual(reload.summary, "Reloaded: your program started over because the field z is new.")
        XCTAssertNil(EngineMessage.decode(#"{"type":"reloaded","outcome":"maybe"}"#))
    }

    func testRetiredBeatMessagesAreDropped() {
        XCTAssertNil(EngineMessage.decode(#"{"type":"beat","count":7,"call":"frame"}"#))
    }

    func testDropsAnythingMalformed() {
        XCTAssertNil(EngineMessage.decode(["type": "ready"]))
        XCTAssertNil(EngineMessage.decode("not json"))
        XCTAssertNil(EngineMessage.decode(#"{"type":"eval","code":"1"}"#))
        XCTAssertNil(EngineMessage.decode(#"{"type":"state","state":"exploded"}"#))
        XCTAssertNil(EngineMessage.decode(#"{"type":"output","lines":[1]}"#))
    }

    func testDropsOversizedBodies() {
        let line = String(repeating: "x", count: EngineMessage.maxBodyBytes)
        XCTAssertNil(EngineMessage.decode(#"{"type":"output","lines":["\#(line)"]}"#))
    }
}

final class DiagnosticRangeTests: XCTestCase {
    func testMapsLineAndColumnToTheUnderlinedSpan() {
        let text = "forward(1);\nforward(\"a\")"
        let range = Diagnostic(line: 2, column: 9, length: 3, message: "").range(in: text)
        XCTAssertEqual((text as NSString).substring(with: range!), "\"a\"")
    }

    func testColumnsCountCharactersNotUTF16Units() {
        let text = "# 🐐🐐\nfoo"
        let range = Diagnostic(line: 1, column: 4, length: 1, message: "").range(in: text)
        XCTAssertEqual((text as NSString).substring(with: range!), "🐐")
    }

    func testClampsToTheEndOfItsLine() {
        let text = "ab\ncd"
        let range = Diagnostic(line: 1, column: 2, length: 50, message: "").range(in: text)
        XCTAssertEqual((text as NSString).substring(with: range!), "b")
    }

    func testPositionsOutsideTheTextHaveNoRange() {
        let text = "ab"
        XCTAssertNil(Diagnostic(line: 0, column: 0, length: 0, message: "").range(in: text))
        XCTAssertNil(Diagnostic(line: 2, column: 1, length: 1, message: "").range(in: text))
        XCTAssertNil(Diagnostic(line: 1, column: 9, length: 1, message: "").range(in: text))
    }
}

final class GoatDocumentTests: XCTestCase {
    func testDecodesUTF8AndRejectsOtherBytes() throws {
        XCTAssertEqual(try GoatDocument.decode(Data("color(\"red\") # 🐐".utf8)), "color(\"red\") # 🐐")
        XCTAssertThrowsError(try GoatDocument.decode(Data([0xff, 0xfe, 0x00])))
    }

    func testStarterProgramIsNotEmpty() {
        XCTAssertTrue(GoatDocument().text.contains("forward"))
    }
}
