import XCTest

@testable import GoatKit

final class LocalDocumentsTests: XCTestCase {
    private var directory: URL!

    override func setUpWithError() throws {
        directory = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: directory, withIntermediateDirectories: true)
    }

    override func tearDownWithError() throws {
        try FileManager.default.removeItem(at: directory)
    }

    func testCreatesTheStarterProgramAsUntitled() throws {
        let url = try LocalDocuments.create(in: directory)
        XCTAssertEqual(url.lastPathComponent, "Untitled.goat")
        XCTAssertEqual(try String(contentsOf: url, encoding: .utf8), GoatDocument.starter)
    }

    func testNeverOverwritesAnExistingDocument() throws {
        let first = try LocalDocuments.create(text: "one", in: directory)
        let second = try LocalDocuments.create(text: "two", in: directory)
        let third = try LocalDocuments.create(text: "three", in: directory)
        XCTAssertEqual(
            [first, second, third].map(\.lastPathComponent),
            ["Untitled.goat", "Untitled 2.goat", "Untitled 3.goat"])
        XCTAssertEqual(try String(contentsOf: first, encoding: .utf8), "one")
    }
}
