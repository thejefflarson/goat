// Runs the real engine, so only under `xcodebuild test`, where the test host carries
// Goat-macOS's sandbox entitlements; an unsigned build is unsandboxed and proves less.
#if os(macOS) && canImport(GoatEngine)
import AppKit
import GoatCanvas
import XCTest

@testable import GoatKit

@MainActor
final class NativeEngineTests: XCTestCase {
    private let timeout: TimeInterval = 30

    private func waitFor(_ engine: Engine, _ what: String, until reached: () -> Bool) async {
        let deadline = Date().addingTimeInterval(timeout)
        while !reached(), Date() < deadline {
            try? await Task.sleep(for: .milliseconds(10))
        }
        XCTAssertTrue(reached(), "never saw \(what); phase \(engine.phase), \(engine.diagnostics)")
    }

    private func readyEngine() async -> Engine {
        let engine = Engine()
        await waitFor(engine, "the engine to be ready") { engine.phase == .ready }
        return engine
    }

    /// Draws a line as long as `n`, which each key press raises by one, or sends
    /// the program into a loop that never ends.
    private func presses(spinning: Bool = false) -> String {
        """
        init = {n: 0}
        update = program(m, e) do match e do KeyDown(k) then {n: \(spinning ? "spin(0)" : "m.n + 1")} else m done done
        draw = program(m) do [Line({x1: 0, y1: 0, x2: m.n, y2: 0, color: "red"})] done
        spin = program(n) do if n < 0 then n else spin(n + 1) done done
        """
    }

    private func lineEnd(_ engine: Engine) -> Double? {
        for case .line(_, let to, _) in engine.frames.current { return to.x }
        return nil
    }

    private func inkedPixels(_ engine: Engine) throws -> Int {
        let view = CanvasHostView(frames: engine.frames)
        view.frame = CGRect(origin: .zero, size: Painter.size)
        let rep = try XCTUnwrap(view.bitmapImageRepForCachingDisplay(in: view.bounds))
        view.cacheDisplay(in: view.bounds, to: rep)
        var inked = 0
        for y in 0..<rep.pixelsHigh {
            for x in 0..<rep.pixelsWide {
                guard let color = rep.colorAt(x: x, y: y)?.usingColorSpace(.sRGB) else { continue }
                if min(color.redComponent, color.greenComponent, color.blueComponent) < 0.9 { inked += 1 }
            }
        }
        return inked
    }

    func testTheStarterProgramDrawsItsSpiral() async throws {
        let engine = await readyEngine()

        engine.run(source: GoatDocument.starter)
        await waitFor(engine, "the program to finish") { engine.phase == .finished }

        XCTAssertGreaterThan(try inkedPixels(engine), 100, "the canvas is blank")
        XCTAssertTrue(engine.diagnostics.isEmpty)
    }

    func testAProgramWithAProblemReportsItInsteadOfDrawing() async throws {
        let engine = await readyEngine()

        engine.run(source: "forward(\"far\")")
        await waitFor(engine, "diagnostics") { !engine.diagnostics.isEmpty }

        XCTAssertEqual(try inkedPixels(engine), 0)
    }

    func testAStuckProgramShowsItsMessageAndRunWorksAgain() async {
        let engine = await readyEngine()
        engine.run(source: presses(spinning: true))
        await waitFor(engine, "the first frame") { !engine.frames.current.isEmpty }

        engine.key("a", down: true)
        await waitFor(engine, "the stuck program to be stopped") {
            if case .failed = engine.phase { true } else { false }
        }
        guard case .failed(let message) = engine.phase else { return }
        XCTAssertTrue(message.contains("looks stuck"), message)

        engine.run(source: presses())
        await waitFor(engine, "the new program to run") { engine.phase == .running && self.lineEnd(engine) == 0 }
        engine.key("a", down: true)
        await waitFor(engine, "the new program to answer a key") { self.lineEnd(engine) == 1 }
    }

    func testASecondRunKeepsTheModel() async {
        let engine = await readyEngine()
        engine.run(source: presses())
        await waitFor(engine, "the program to run") { engine.phase == .running && self.lineEnd(engine) == 0 }
        engine.key("a", down: true)
        await waitFor(engine, "a key to count") { self.lineEnd(engine) == 1 }

        engine.run(source: presses())
        await waitFor(engine, "the reload") { engine.reload != nil }

        XCTAssertEqual(engine.reload?.keptModel, true)
        XCTAssertEqual(engine.phase, .running)
        engine.key("a", down: true)
        await waitFor(engine, "the kept model to count on") { self.lineEnd(engine) == 2 }
    }
}
#endif
