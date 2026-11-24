#if os(macOS)
import XCTest

@testable import GoatKit

/// Export App… end to end except the save panel: the exports below go to a folder
/// under the temporary directory, which the sandbox always lets the test host write.
final class PlayerExportTests: XCTestCase {
    private var scratch: URL!
    private let program = "color(\"red\");\nforward(50)\n"

    override func setUpWithError() throws {
        scratch = FileManager.default.temporaryDirectory
            .appendingPathComponent("goat-player-\(UUID().uuidString)")
        try FileManager.default.createDirectory(at: scratch, withIntermediateDirectories: true)
    }

    override func tearDown() {
        try? FileManager.default.removeItem(at: scratch)
    }

    /// A stand-in for GoatPlayer.app: one binary and the Info.plist the real one has.
    private func makeTemplate(identifier: String = "local.goat.player") throws -> URL {
        let app = scratch.appendingPathComponent("GoatPlayer.app")
        try writeApp(app, identifier: identifier)
        try adHocSign(app)
        return app
    }

    private func writeApp(_ app: URL, identifier: String) throws {
        let macOS = app.appendingPathComponent("Contents/MacOS")
        try FileManager.default.createDirectory(at: macOS, withIntermediateDirectories: true)
        try FileManager.default.copyItem(
            at: URL(fileURLWithPath: "/usr/bin/true"), to: macOS.appendingPathComponent("GoatPlayer"))
        let info: [String: Any] = [
            "CFBundleExecutable": "GoatPlayer",
            "CFBundleIdentifier": identifier,
            "CFBundleName": "GoatPlayer",
            "CFBundleDisplayName": "GoatPlayer",
            "CFBundlePackageType": "APPL",
        ]
        try (info as NSDictionary).write(to: app.appendingPathComponent("Contents/Info.plist"))
    }

    private func info(of app: URL) throws -> [String: Any] {
        let data = try Data(contentsOf: app.appendingPathComponent("Contents/Info.plist"))
        return try XCTUnwrap(
            PropertyListSerialization.propertyList(from: data, format: nil) as? [String: Any])
    }

    private func verify(_ bundle: URL) throws -> Int32 {
        let codesign = Process()
        codesign.executableURL = URL(fileURLWithPath: "/usr/bin/codesign")
        codesign.arguments = ["--verify", "--deep", "--strict", bundle.path]
        try codesign.run()
        codesign.waitUntilExit()
        return codesign.terminationStatus
    }

    private func assertExported(_ app: URL, name: String, identifier: String) throws {
        XCTAssertEqual(try verify(app), 0)
        let source = try String(
            contentsOf: app.appendingPathComponent(PlayerExport.programPath), encoding: .utf8)
        XCTAssertEqual(source, program)
        let info = try info(of: app)
        XCTAssertEqual(info["CFBundleName"] as? String, name)
        XCTAssertEqual(info["CFBundleDisplayName"] as? String, name)
        XCTAssertEqual(info["CFBundleIdentifier"] as? String, identifier)
        let executable = try XCTUnwrap(info["CFBundleExecutable"] as? String)
        XCTAssertTrue(
            FileManager.default.isExecutableFile(
                atPath: app.appendingPathComponent("Contents/MacOS/\(executable)").path))
    }

    func testTheExportCarriesTheProgramAndTheNameAndVerifies() throws {
        let out = scratch.appendingPathComponent("My Game.app")
        try PlayerExport.export(program: program, template: try makeTemplate(), to: out)
        try assertExported(out, name: "My Game", identifier: "local.goat.my-game")
        XCTAssertEqual(try info(of: out)["CFBundleExecutable"] as? String, "GoatPlayer")
    }

    func testTheShippedPlayerExports() throws {
        try XCTSkipUnless(Bundle.main.bundleIdentifier == "com.thejefflarson.goat.testhost")
        let template = try XCTUnwrap(
            PlayerExport.templateURL(), "GoatPlayer.app is not in the test host's Resources")
        let out = scratch.appendingPathComponent("Spiral.app")
        try PlayerExport.export(program: program, template: template, to: out)
        try assertExported(out, name: "Spiral", identifier: "local.goat.spiral")
        XCTAssertEqual(try info(of: out)["CFBundleExecutable"] as? String, "GoatPlayer")
        XCTAssertTrue(
            FileManager.default.fileExists(
                atPath: out.appendingPathComponent("Contents/Frameworks/GoatKit.framework").path))
    }

    func testAForeignAppAtTheDestinationIsRefusedAndLeftAlone() throws {
        let foreign = scratch.appendingPathComponent("Safari.app")
        try writeApp(foreign, identifier: "com.apple.Safari")
        XCTAssertThrowsError(
            try PlayerExport.export(program: program, template: try makeTemplate(), to: foreign)
        ) {
            XCTAssertEqual($0 as? ExportError, .destinationExists(foreign))
        }
        XCTAssertEqual(try info(of: foreign)["CFBundleIdentifier"] as? String, "com.apple.Safari")
    }

    func testAFileOrASymlinkAtTheDestinationIsRefused() throws {
        let template = try makeTemplate()
        let file = scratch.appendingPathComponent("File.app")
        try "x".write(to: file, atomically: true, encoding: .utf8)
        XCTAssertThrowsError(try PlayerExport.export(program: program, template: template, to: file))

        let target = scratch.appendingPathComponent("Real.app")
        try writeApp(target, identifier: "local.goat.real")
        let link = scratch.appendingPathComponent("Link.app")
        try FileManager.default.createSymbolicLink(at: link, withDestinationURL: target)
        XCTAssertThrowsError(try PlayerExport.export(program: program, template: template, to: link))
        XCTAssertTrue(FileManager.default.fileExists(atPath: target.path))
    }

    func testAGoatMadeAppAtTheDestinationIsReplaced() throws {
        let template = try makeTemplate()
        let out = scratch.appendingPathComponent("Again.app")
        try PlayerExport.export(program: "forward(1)", template: template, to: out)
        try PlayerExport.export(program: program, template: template, to: out)
        try assertExported(out, name: "Again", identifier: "local.goat.again")
    }

    func testAMissingPlayerIsReported() {
        let out = scratch.appendingPathComponent("Out.app")
        XCTAssertThrowsError(
            try PlayerExport.export(
                program: program, template: scratch.appendingPathComponent("Nope.app"), to: out)
        ) { XCTAssertEqual($0 as? ExportError, .missingPlayer) }
    }

    func testBundleIdentifiersMatchTheCommandLineRule() {
        XCTAssertEqual(PlayerExport.bundleIdentifier(name: "Bounce"), "local.goat.bounce")
        XCTAssertEqual(PlayerExport.bundleIdentifier(name: "My  Cool_Game 2"), "local.goat.my-cool-game-2")
        XCTAssertEqual(PlayerExport.bundleIdentifier(name: "ÄÖ"), "local.goat.app")
        XCTAssertEqual(PlayerExport.bundleIdentifier(name: "…"), "local.goat.app")
    }

    func testTheCommandLineToolsAreDetectedByTheirCompiler() {
        XCTAssertTrue(NativeExport.toolsInstalled(clang: "/usr/bin/true"))
        XCTAssertFalse(NativeExport.toolsInstalled(clang: scratch.appendingPathComponent("clang").path))
        XCTAssertTrue(NativeExport.explanation(name: "Bounce").contains("goat build --native Bounce.goat -o Bounce.app"))
    }
}

final class PlayerProgramTests: XCTestCase {
    private var scratch: URL!

    override func setUpWithError() throws {
        scratch = FileManager.default.temporaryDirectory
            .appendingPathComponent("goat-program-\(UUID().uuidString)")
        try FileManager.default.createDirectory(at: scratch, withIntermediateDirectories: true)
    }

    override func tearDown() {
        try? FileManager.default.removeItem(at: scratch)
    }

    private func bundle(program: Data?, info: [String: Any]) throws -> Bundle {
        let app = scratch.appendingPathComponent("App.app")
        let resources = app.appendingPathComponent("Contents/Resources")
        try FileManager.default.createDirectory(at: resources, withIntermediateDirectories: true)
        if let program { try program.write(to: resources.appendingPathComponent("program.goat")) }
        try (info as NSDictionary).write(to: app.appendingPathComponent("Contents/Info.plist"))
        return try XCTUnwrap(Bundle(url: app))
    }

    func testTheProgramIsReadFromResources() throws {
        let bundle = try bundle(program: Data("forward(1)".utf8), info: ["CFBundleName": "Game"])
        XCTAssertEqual(PlayerProgram.load(from: bundle), .success("forward(1)"))
    }

    func testAMissingOrUnreadableProgramIsAMessage() throws {
        XCTAssertEqual(
            PlayerProgram.load(from: try bundle(program: nil, info: ["CFBundleName": "Game"])),
            .failure(.missing))
        try FileManager.default.removeItem(at: scratch.appendingPathComponent("App.app"))
        XCTAssertEqual(
            PlayerProgram.load(from: try bundle(program: Data([0xff, 0xfe]), info: ["CFBundleName": "Game"])),
            .failure(.unreadable))
        XCTAssertFalse(PlayerProgram.Failure.missing.message.isEmpty)
    }

    func testTheTitleIsTheDisplayNameThenTheName() throws {
        let both = try bundle(
            program: nil, info: ["CFBundleName": "Plain", "CFBundleDisplayName": "My Game"])
        XCTAssertEqual(PlayerProgram.appName(in: both), "My Game")
        try FileManager.default.removeItem(at: scratch.appendingPathComponent("App.app"))
        let nameOnly = try bundle(program: nil, info: ["CFBundleName": "Plain"])
        XCTAssertEqual(PlayerProgram.appName(in: nameOnly), "Plain")
    }
}

#if canImport(GoatEngine)
final class ExportGateTests: XCTestCase {
    private let problem = Diagnostic(line: 1, column: 1, length: 1, message: "nope")

    func testOnlyAProgramThatRanCleanAndIsUnchangedCanBeExported() {
        func can(
            _ ran: String?, _ now: String = "a", _ phase: Engine.Phase = .finished,
            _ diagnostics: [Diagnostic] = []
        ) -> Bool {
            ExportGate.canExport(ranSource: ran, current: now, phase: phase, diagnostics: diagnostics)
        }
        XCTAssertTrue(can("a"))
        XCTAssertTrue(can("a", "a", .running))
        XCTAssertFalse(can(nil))
        XCTAssertFalse(can("a", "b"))
        XCTAssertFalse(can("a", "a", .finished, [problem]))
        XCTAssertFalse(can("a", "a", .ready))
        XCTAssertFalse(can("a", "a", .loading))
        XCTAssertFalse(can("a", "a", .failed("stuck")))
    }

    func testThePlayerShowsTheFirstProblemOrTheFailure() {
        XCTAssertEqual(PlayerScreen.problem(phase: .running, diagnostics: []), nil)
        XCTAssertEqual(PlayerScreen.problem(phase: .running, diagnostics: [problem]), "1:1: nope")
        XCTAssertEqual(PlayerScreen.problem(phase: .failed("stuck"), diagnostics: []), "stuck")
    }
}
#endif
#endif
