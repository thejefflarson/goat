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

    func testDecodesTheHeartbeatAroundACallIntoGoat() {
        XCTAssertEqual(
            EngineMessage.decode(#"{"type":"beat","count":7,"call":"frame"}"#), .beat(count: 7, call: .frame))
        XCTAssertEqual(
            EngineMessage.decode(#"{"type":"beat","count":2,"call":"once"}"#), .beat(count: 2, call: .once))
        XCTAssertNil(EngineMessage.decode(#"{"type":"beat","count":2,"call":"forever"}"#))
        XCTAssertNil(EngineMessage.decode(#"{"type":"beat","call":"frame"}"#))
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

final class AssetPathTests: XCTestCase {
    private var root: URL!

    override func setUpWithError() throws {
        root = FileManager.default.temporaryDirectory.appendingPathComponent("goat-assets-\(UUID())")
        try FileManager.default.createDirectory(at: root.appendingPathComponent("dist"), withIntermediateDirectories: true)
        try Data("page".utf8).write(to: root.appendingPathComponent("embed.html"))
        try Data("js".utf8).write(to: root.appendingPathComponent("dist/embed.js"))
    }

    override func tearDownWithError() throws {
        try? FileManager.default.removeItem(at: root)
    }

    func testResolvesBundledFiles() {
        XCTAssertNotNil(AssetPath.resolve(AssetScheme.url("embed.html"), under: root))
        XCTAssertNotNil(AssetPath.resolve(AssetScheme.url("dist/embed.js"), under: root))
    }

    func testRefusesAnythingOutsideTheBundle() throws {
        let outside = root.deletingLastPathComponent().appendingPathComponent("goat-secret-\(UUID())")
        try Data("secret".utf8).write(to: outside)
        defer { try? FileManager.default.removeItem(at: outside) }
        try FileManager.default.createSymbolicLink(at: root.appendingPathComponent("link"), withDestinationURL: outside)

        let escapes = [
            "../\(outside.lastPathComponent)", "dist/../../\(outside.lastPathComponent)",
            "%2e%2e/\(outside.lastPathComponent)", "link", "dist", "missing.js", "",
        ]
        for path in escapes {
            let url = URL(string: "\(AssetScheme.name)://\(AssetScheme.host)/\(path)")!
            XCTAssertNil(AssetPath.resolve(url, under: root), path)
        }
        XCTAssertNil(AssetPath.resolve(URL(string: "goat-app://evil/embed.html")!, under: root))
        XCTAssertNil(AssetPath.resolve(URL(string: "https://app/embed.html")!, under: root))
    }

    func testServesWasmAndModulesWithTheirTypes() {
        XCTAssertEqual(AssetPath.mimeType(for: URL(fileURLWithPath: "/a/goat_web.wasm")), "application/wasm")
        XCTAssertTrue(AssetPath.mimeType(for: URL(fileURLWithPath: "/a/embed.js")).hasPrefix("text/javascript"))
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
