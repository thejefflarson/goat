import Foundation

/// The native half of host-owned preemption (ADR 0021) for a program that runs on
/// the web view's main thread, where nothing on the page can interrupt it. The
/// page reports each entry into and exit from goat as a count (odd while goat
/// runs, even while idle); this watches the clock, and a call that stays open
/// past its budget is the cue to tear the web view down.
struct Watchdog {
    struct Limits: Sendable {
        var frame: TimeInterval = 1
        var once: TimeInterval = 10

        func budget(for call: BeatCall) -> TimeInterval {
            call == .frame ? frame : once
        }
    }

    private struct Open {
        var call: BeatCall
        var since: TimeInterval
    }

    let limits: Limits
    private var latest = 0
    private var open: Open?

    init(limits: Limits = Limits()) {
        self.limits = limits
    }

    /// Whether goat is inside a call right now.
    var isBusy: Bool { open != nil }

    /// A count at or below the latest one is a stale or repeated message and is
    /// ignored; the page's count only restarts when its web view is replaced,
    /// and a replacement starts a new `Watchdog`.
    mutating func beat(count: Int, call: BeatCall, at now: TimeInterval) {
        guard count > latest else { return }
        latest = count
        open = count.isMultiple(of: 2) ? nil : Open(call: call, since: now)
    }

    /// The call that overran its budget, once. The watchdog goes quiet after
    /// reporting so one stuck call is not reported again while it is torn down.
    mutating func expire(at now: TimeInterval) -> BeatCall? {
        guard let open, now - open.since >= limits.budget(for: open.call) else { return nil }
        self.open = nil
        return open.call
    }
}

extension BeatCall {
    var overrunMessage: String {
        switch self {
        case .frame: "your program got stuck: it kept running without finishing, so it was stopped"
        case .once: "your program was stopped: it ran too long without finishing"
        }
    }
}

/// Polls a `Watchdog` on a timer, but only while goat is inside a call, so an
/// idle program (a hidden tab, a paused animation, nothing running) costs nothing
/// and is never killed.
@MainActor
final class WatchdogTimer {
    private var watchdog: Watchdog
    private let now: @Sendable () -> TimeInterval
    private let poll: Duration
    private let onStuck: (BeatCall) -> Void
    private var ticker: Task<Void, Never>?

    init(
        limits: Watchdog.Limits = Watchdog.Limits(),
        poll: Duration = .milliseconds(100),
        now: @escaping @Sendable () -> TimeInterval = { ProcessInfo.processInfo.systemUptime },
        onStuck: @escaping (BeatCall) -> Void
    ) {
        watchdog = Watchdog(limits: limits)
        self.poll = poll
        self.now = now
        self.onStuck = onStuck
    }

    deinit { ticker?.cancel() }

    func beat(count: Int, call: BeatCall) {
        watchdog.beat(count: count, call: call, at: now())
        if watchdog.isBusy { startTicking() } else { stopTicking() }
    }

    /// For a replaced web view, whose page counts from zero again.
    func reset() {
        stopTicking()
        watchdog = Watchdog(limits: watchdog.limits)
    }

    private func startTicking() {
        guard ticker == nil else { return }
        ticker = Task { [weak self, poll] in
            while !Task.isCancelled {
                try? await Task.sleep(for: poll)
                guard !Task.isCancelled, let self else { return }
                self.check()
            }
        }
    }

    private func stopTicking() {
        ticker?.cancel()
        ticker = nil
    }

    private func check() {
        if let call = watchdog.expire(at: now()) {
            stopTicking()
            onStuck(call)
        } else if !watchdog.isBusy {
            stopTicking()
        }
    }
}
