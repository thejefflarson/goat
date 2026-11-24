#if os(macOS)
import XCTest

@testable import GoatKit

final class ExportBundleTests: XCTestCase {
    private var scratch: URL!

    override func setUpWithError() throws {
        scratch = FileManager.default.temporaryDirectory
            .appendingPathComponent("goat-export-\(UUID().uuidString)")
        try FileManager.default.createDirectory(at: scratch, withIntermediateDirectories: true)
    }

    override func tearDown() {
        try? FileManager.default.removeItem(at: scratch)
    }

    /// A one-binary `.app`, signed the way a prebuilt player would be shipped.
    private func makeTemplate() throws -> URL {
        let app = scratch.appendingPathComponent("Template.app")
        let macOS = app.appendingPathComponent("Contents/MacOS")
        try FileManager.default.createDirectory(at: macOS, withIntermediateDirectories: true)
        try FileManager.default.copyItem(
            at: URL(fileURLWithPath: "/usr/bin/true"), to: macOS.appendingPathComponent("player"))
        let info: [String: Any] = [
            "CFBundleExecutable": "player",
            "CFBundleIdentifier": "local.goat.template",
            "CFBundleName": "Template",
            "CFBundlePackageType": "APPL",
        ]
        try (info as NSDictionary).write(to: app.appendingPathComponent("Contents/Info.plist"))
        try adHocSign(app)
        return app
    }

    private func verify(_ bundle: URL) throws -> Int32 {
        let codesign = Process()
        codesign.executableURL = URL(fileURLWithPath: "/usr/bin/codesign")
        codesign.arguments = ["--verify", "--deep", "--strict", bundle.path]
        try codesign.run()
        codesign.waitUntilExit()
        return codesign.terminationStatus
    }

    func testTheTestHostRunsSandboxedSoTheExportsAboveAreProvedInsideIt() throws {
        try XCTSkipUnless(Bundle.main.bundleIdentifier == "com.thejefflarson.goat.testhost")
        XCTAssertNotNil(ProcessInfo.processInfo.environment["APP_SANDBOX_CONTAINER_ID"])
    }

    func testAnExportedCopyVerifies() throws {
        let template = try makeTemplate()
        let exported = scratch.appendingPathComponent("Out.app")
        try exportBundle(template: template, to: exported)
        XCTAssertEqual(try verify(exported), 0)
    }

    func testAFileAddedAfterSigningBreaksTheSealUntilItIsSignedAgain() throws {
        let template = try makeTemplate()
        let exported = scratch.appendingPathComponent("Out.app")
        try exportBundle(template: template, to: exported)
        let resources = exported.appendingPathComponent("Contents/Resources")
        try FileManager.default.createDirectory(at: resources, withIntermediateDirectories: true)
        try "forward 10".write(
            to: resources.appendingPathComponent("program.goat"), atomically: true, encoding: .utf8)
        XCTAssertNotEqual(try verify(exported), 0)
        try adHocSign(exported)
        XCTAssertEqual(try verify(exported), 0)
    }

    func testAnExistingDestinationIsRefusedAndLeftAlone() throws {
        let template = try makeTemplate()
        let taken = scratch.appendingPathComponent("Taken.app")
        try FileManager.default.createDirectory(at: taken, withIntermediateDirectories: false)
        XCTAssertThrowsError(try exportBundle(template: template, to: taken)) {
            XCTAssertEqual($0 as? ExportError, .destinationExists(taken))
        }
    }
}
#endif
