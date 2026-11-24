import Foundation
import GoatCanvas

/// The picture the engine last drew. The engine's thread puts frames in and the
/// canvas view takes the latest on the main thread, so a frame the view never got
/// to draw is simply replaced (latest wins).
public final class FrameSlot: @unchecked Sendable {
    private let lock = NSLock()
    private var shapes: [Shape] = []
    private var undrawn = false
    private var wake: (@MainActor () -> Void)?

    public init() {}

    /// The latest picture, without marking it drawn.
    public var current: [Shape] {
        lock.lock()
        defer { lock.unlock() }
        return shapes
    }

    /// Calls `wake` on the main actor when a picture arrives and the last one
    /// has been taken. Several puts before a take make one call.
    func onUndrawn(_ wake: @escaping @MainActor () -> Void) {
        lock.lock()
        self.wake = wake
        lock.unlock()
    }

    func put(_ picture: [Shape]) {
        lock.lock()
        shapes = picture
        let wake = undrawn ? nil : self.wake
        undrawn = true
        lock.unlock()
        if let wake { Task { @MainActor in wake() } }
    }

    func take() -> [Shape] {
        lock.lock()
        defer { lock.unlock() }
        undrawn = false
        return shapes
    }
}
