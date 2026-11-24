import XCTest

// SwiftPM's `swift test` has no GoatEngine module; only the Xcode project links it.
#if canImport(GoatEngine)
import GoatEngine

private final class Heard {
    let lock = NSCondition()
    var controls: [String] = []
    var frames = 0
    var closed = false

    func hear(_ change: () -> Void) {
        lock.lock()
        change()
        lock.broadcast()
        lock.unlock()
    }

    func wait(timeout: TimeInterval = 20, until done: () -> Bool) -> Bool {
        let deadline = Date(timeIntervalSinceNow: timeout)
        lock.lock()
        defer { lock.unlock() }
        while !done() {
            if !lock.wait(until: deadline) { return done() }
        }
        return true
    }
}

final class EngineLinkTests: XCTestCase {
    func testLinkedEngineSaysReadyRunsAProgramAndFrees() {
        let heard = Heard()
        let context = Unmanaged.passRetained(heard)
        let callbacks = goat_engine_callbacks(
            context: context.toOpaque(),
            control: { context, json, len in
                let heard = Unmanaged<Heard>.fromOpaque(context!).takeUnretainedValue()
                let text = String(decoding: UnsafeBufferPointer(start: json, count: len), as: UTF8.self)
                heard.hear { heard.controls.append(text) }
            },
            frame: { context, _, _ in
                let heard = Unmanaged<Heard>.fromOpaque(context!).takeUnretainedValue()
                heard.hear { heard.frames += 1 }
            },
            closed: { context in
                let heard = Unmanaged<Heard>.fromOpaque(context!).takeUnretainedValue()
                heard.hear { heard.closed = true }
            })
        let engine = goat_engine_new(callbacks)
        XCTAssertNotNil(engine)

        XCTAssertTrue(heard.wait { heard.controls.contains { $0.contains(#""type":"ready""#) } })

        let source = Array(
            """
            init = {n: 0}
            update = program(m, e) do m done
            draw = program(m) do [Line({x1: 0, y1: 0, x2: 10, y2: 0, color: "red"})] done
            """.utf8)
        source.withUnsafeBufferPointer { goat_engine_run(engine, $0.baseAddress, $0.count) }
        XCTAssertTrue(heard.wait { heard.frames > 0 }, "heard \(heard.controls)")
        XCTAssertTrue(heard.controls.contains { $0.contains(#""state":"running""#) })

        goat_engine_free(engine)
        XCTAssertTrue(heard.closed)
        context.release()
    }
}
#endif
