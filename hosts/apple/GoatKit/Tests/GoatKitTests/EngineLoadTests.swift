import Combine
import WebKit
import XCTest

@testable import GoatKit

/// The load path: a page that never says `ready`, a web content process that
/// dies, and the phase transitions that follow. A page that loads but stays
/// silent stands in for a slow device, so none of this needs the staged engine.
@MainActor
final class EngineLoadTests: XCTestCase {
    private var silentPage: URL!

    override func setUpWithError() throws {
        silentPage = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: silentPage, withIntermediateDirectories: true)
        try "<!doctype html><title>silent</title>".write(
            to: silentPage.appendingPathComponent("embed.html"), atomically: true, encoding: .utf8)
    }

    override func tearDown() {
        try? FileManager.default.removeItem(at: silentPage)
    }

    private func engine(budget: Duration = .seconds(60)) -> Engine {
        Engine(assets: silentPage, loadBudget: budget)
    }

    private func wait(_ engine: Engine, until reached: (Engine.Phase) -> Bool) async {
        let deadline = Date().addingTimeInterval(10)
        while !reached(engine.phase), Date() < deadline {
            try? await Task.sleep(for: .milliseconds(10))
        }
    }

    private func send(_ engine: Engine, _ json: String) { engine.receive(json) }

    func testLoadingMovesToReadyThenRunningThenFinished() {
        let engine = engine()
        XCTAssertEqual(engine.phase, .loading)
        send(engine, #"{"type":"ready"}"#)
        XCTAssertEqual(engine.phase, .ready)
        send(engine, #"{"type":"state","state":"running"}"#)
        XCTAssertEqual(engine.phase, .running)
        send(engine, #"{"type":"state","state":"finished"}"#)
        XCTAssertEqual(engine.phase, .finished)
    }

    func testRunIsRefusedUntilReady() {
        XCTAssertFalse(Engine.Phase.loading.canRun)
        XCTAssertFalse(Engine.Phase.loadFailed("x").canRun)
        for phase in [Engine.Phase.ready, .running, .finished, .failed("x")] {
            XCTAssertTrue(phase.canRun, "\(phase)")
        }
    }

    func testAMissingEngineStillReportsAFailure() {
        XCTAssertEqual(
            Engine(assets: nil).phase, .failed("This copy of goat is missing its drawing engine."))
    }

    func testReadyNeverArrivingEntersTheLoadFailedStateAndRetryRebuildsTheWebView() async {
        let engine = engine(budget: .milliseconds(100))
        let first = engine.webView
        await wait(engine) { $0 != .loading }
        XCTAssertEqual(engine.phase, .loadFailed(Engine.loadStalledMessage))

        engine.retry()
        XCTAssertEqual(engine.phase, .loading)
        XCTAssertFalse(engine.webView === first, "Retry builds a fresh web view")

        await wait(engine) { $0 != .loading }
        XCTAssertEqual(engine.phase, .loadFailed(Engine.loadStalledMessage), "the new load has a budget too")
    }

    func testReadyWithinTheBudgetCancelsTheStall() async {
        let engine = engine(budget: .milliseconds(100))
        send(engine, #"{"type":"ready"}"#)
        try? await Task.sleep(for: .milliseconds(300))
        XCTAssertEqual(engine.phase, .ready)
    }

    func testTheWebContentProcessDyingEntersTheLoadFailedState() {
        let engine = engine()
        send(engine, #"{"type":"ready"}"#)
        send(engine, #"{"type":"state","state":"running"}"#)
        let dead = engine.webView
        engine.webViewWebContentProcessDidTerminate(dead)
        XCTAssertEqual(engine.phase, .loadFailed(Engine.loadCrashedMessage))

        engine.retry()
        XCTAssertEqual(engine.phase, .loading)
        XCTAssertFalse(engine.webView === dead)
    }

    func testAnExitFromAReplacedWebViewIsIgnored() {
        let engine = engine()
        let old = engine.webView
        engine.webViewWebContentProcessDidTerminate(old)
        engine.retry()
        engine.webViewWebContentProcessDidTerminate(old)
        XCTAssertEqual(engine.phase, .loading)
    }

    func testAFailedNavigationEntersTheLoadFailedState() {
        let engine = engine()
        engine.webView(engine.webView, didFailProvisionalNavigation: nil, withError: URLError(.cannotConnectToHost))
        XCTAssertEqual(engine.phase, .loadFailed(Engine.loadStalledMessage))
    }

    func testRetryDoesNothingOutsideALoadFailure() {
        let engine = engine()
        let view = engine.webView
        engine.retry()
        XCTAssertTrue(engine.webView === view)
        send(engine, #"{"type":"ready"}"#)
        engine.retry()
        XCTAssertTrue(engine.webView === view)
        XCTAssertEqual(engine.phase, .ready)
    }

    func testALateReadyDoesNotReviveThePhaseAfterALoadFailure() {
        let engine = engine()
        engine.webViewWebContentProcessDidTerminate(engine.webView)
        send(engine, #"{"type":"ready"}"#)
        XCTAssertEqual(engine.phase, .loadFailed(Engine.loadCrashedMessage))
    }
}

#if os(macOS)
/// Drives the real engine page: `ready` arrives within a generous budget and a
/// program inks the canvas. Skips unless `scripts/stage-web.sh` has filled `Resources/web`.
@MainActor
final class EngineReadyBudgetTests: XCTestCase {
    func testReadyArrivesWithinTheBudgetAndTheCanvasInks() async throws {
        let engine = Engine(assets: try stagedWeb())
        // An off-screen web view delivers no animation frames; a timer stands in.
        engine.webView.configuration.userContentController.addUserScript(
            WKUserScript(
                source: "window.requestAnimationFrame = (f) => setTimeout(() => f(performance.now()), 1);",
                injectionTime: .atDocumentStart, forMainFrameOnly: true))
        engine.webView.reload()

        let started = Date()
        try await wait(engine, for: .ready)
        XCTAssertLessThan(Date().timeIntervalSince(started), 30)

        engine.run(source: "color(\"purple\");\nfor side from 1 to 60 do forward(side * 3); right(89) done")
        try await wait(engine, for: .finished)

        let script = """
            const canvas = document.getElementById("canvas");
            const data = canvas.getContext("2d").getImageData(0, 0, canvas.width, canvas.height).data;
            let inked = 0;
            for (let i = 3; i < data.length; i += 4) if (data[i] !== 0) inked++;
            return inked;
            """
        let inked = try await engine.webView.callAsyncJavaScript(script, contentWorld: .page) as? Int
        XCTAssertGreaterThan(inked ?? 0, 100)
    }

    private func wait(_ engine: Engine, for phase: Engine.Phase) async throws {
        let deadline = Date().addingTimeInterval(30)
        while engine.phase != phase {
            switch engine.phase {
            case .failed(let message), .loadFailed(let message):
                XCTFail("the engine failed while waiting for \(phase): \(message)")
                throw CancellationError()
            default: break
            }
            if Date() > deadline {
                XCTFail("never reached \(phase), at \(engine.phase)")
                throw CancellationError()
            }
            try await Task.sleep(nanoseconds: 20_000_000)
        }
    }

    private func stagedWeb(file: StaticString = #filePath) throws -> URL {
        let hostsApple = URL(fileURLWithPath: "\(file)")
            .deletingLastPathComponent().deletingLastPathComponent().deletingLastPathComponent()
            .deletingLastPathComponent()
        let root = hostsApple.appendingPathComponent("Resources/web")
        guard FileManager.default.fileExists(atPath: root.appendingPathComponent("embed.html").path) else {
            throw XCTSkip("\(root.path) is not staged; run hosts/apple/scripts/stage-web.sh")
        }
        return root
    }
}
#endif
