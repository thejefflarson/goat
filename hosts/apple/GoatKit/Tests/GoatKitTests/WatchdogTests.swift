import XCTest

@testable import GoatKit

final class WatchdogTests: XCTestCase {
    private let limits = Watchdog.Limits(frame: 1, once: 10)

    func testAnOddCountOpensACallAndTheNextEvenCountClosesIt() {
        var watchdog = Watchdog(limits: limits)
        XCTAssertFalse(watchdog.isBusy)
        watchdog.beat(count: 1, call: .frame, at: 0)
        XCTAssertTrue(watchdog.isBusy)
        watchdog.beat(count: 2, call: .frame, at: 0.1)
        XCTAssertFalse(watchdog.isBusy)
    }

    func testAnIdleProgramIsNeverStopped() {
        var watchdog = Watchdog(limits: limits)
        watchdog.beat(count: 1, call: .frame, at: 0)
        watchdog.beat(count: 2, call: .frame, at: 0.1)
        XCTAssertNil(watchdog.expire(at: 10_000))
    }

    func testACallPastItsBudgetExpiresOnceWithItsKind() {
        var watchdog = Watchdog(limits: limits)
        watchdog.beat(count: 1, call: .frame, at: 5)
        XCTAssertNil(watchdog.expire(at: 5.9))
        XCTAssertEqual(watchdog.expire(at: 6), .frame)
        XCTAssertNil(watchdog.expire(at: 60), "reported once, not on every poll")
    }

    func testARunOnceCallGetsTheLongerBudget() {
        var watchdog = Watchdog(limits: limits)
        watchdog.beat(count: 1, call: .once, at: 0)
        XCTAssertNil(watchdog.expire(at: 9.9))
        XCTAssertEqual(watchdog.expire(at: 10), .once)
    }

    func testEachNewCallRestartsTheClock() {
        var watchdog = Watchdog(limits: limits)
        watchdog.beat(count: 1, call: .frame, at: 0)
        watchdog.beat(count: 2, call: .frame, at: 0.9)
        watchdog.beat(count: 3, call: .frame, at: 5)
        XCTAssertNil(watchdog.expire(at: 5.9))
        XCTAssertEqual(watchdog.expire(at: 6), .frame)
    }

    func testStaleAndRepeatedCountsAreIgnored() {
        var watchdog = Watchdog(limits: limits)
        watchdog.beat(count: 3, call: .frame, at: 0)
        watchdog.beat(count: 3, call: .frame, at: 0.5)
        watchdog.beat(count: 2, call: .frame, at: 0.6)
        XCTAssertTrue(watchdog.isBusy, "a late even count must not close the call that the odd 3 opened")
        XCTAssertEqual(watchdog.expire(at: 1), .frame, "the repeated 3 did not restart the clock")
    }

    func testEachCallKindHasItsOwnOverrunMessage() {
        XCTAssertNotEqual(BeatCall.frame.overrunMessage, BeatCall.once.overrunMessage)
        XCTAssertTrue(BeatCall.once.overrunMessage.hasPrefix("your program was stopped"))
    }
}

private final class Clock: @unchecked Sendable {
    private let lock = NSLock()
    private var time: TimeInterval = 0

    var now: TimeInterval { lock.withLock { time } }
    func advance(_ seconds: TimeInterval) { lock.withLock { time += seconds } }
}

@MainActor
final class WatchdogTimerTests: XCTestCase {
    private let clock = Clock()
    private var stuck: [BeatCall] = []
    private var fired: XCTestExpectation?

    private func makeTimer(expectingStuck: Bool) -> WatchdogTimer {
        fired = expectation(description: "stuck")
        fired?.isInverted = !expectingStuck
        return WatchdogTimer(
            limits: Watchdog.Limits(frame: 1, once: 10), poll: .milliseconds(5),
            now: { [clock] in clock.now },
            onStuck: { [unowned self] call in
                stuck.append(call)
                fired?.fulfill()
            })
    }

    func testACallThatNeverLeavesIsReportedStuck() async {
        let timer = makeTimer(expectingStuck: true)
        timer.beat(count: 1, call: .frame)
        clock.advance(1.5)
        await fulfillment(of: [fired!], timeout: 2)
        XCTAssertEqual(stuck, [.frame])
    }

    func testACallThatLeavesInTimeIsNeverReported() async {
        let timer = makeTimer(expectingStuck: false)
        timer.beat(count: 1, call: .frame)
        clock.advance(0.5)
        timer.beat(count: 2, call: .frame)
        clock.advance(100)
        await fulfillment(of: [fired!], timeout: 0.15)
        XCTAssertEqual(stuck, [])
    }

    func testAProgramBetweenCallsIsNotKilledHoweverLongItIdles() async {
        let timer = makeTimer(expectingStuck: false)
        for pair in 0..<20 {
            timer.beat(count: 2 * pair + 1, call: .frame)
            timer.beat(count: 2 * pair + 2, call: .frame)
            clock.advance(60)
        }
        await fulfillment(of: [fired!], timeout: 0.15)
        XCTAssertEqual(stuck, [])
    }

    func testAStuckCallIsReportedOnceNotOnEveryPoll() async {
        let timer = makeTimer(expectingStuck: true)
        timer.beat(count: 1, call: .once)
        clock.advance(11)
        await fulfillment(of: [fired!], timeout: 2)
        try? await Task.sleep(for: .milliseconds(50))
        XCTAssertEqual(stuck, [.once])
    }

    func testResetForgetsTheCallInFlightAndWatchesTheReplacementPageAfresh() async {
        let timer = makeTimer(expectingStuck: true)
        timer.beat(count: 1, call: .frame)
        timer.reset()
        clock.advance(100)
        try? await Task.sleep(for: .milliseconds(50))
        XCTAssertEqual(stuck, [], "the replaced page's call is forgotten")

        timer.beat(count: 1, call: .frame)
        clock.advance(2)
        await fulfillment(of: [fired!], timeout: 2)
        XCTAssertEqual(stuck, [.frame], "the new page counts from 1 again and is watched")
    }
}
