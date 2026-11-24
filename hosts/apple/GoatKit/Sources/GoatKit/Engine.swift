// SwiftPM's `swift test` has no GoatEngine module; only the Xcode project links it.
#if canImport(GoatEngine)
import Foundation
import GoatCanvas
import GoatEngine
import os

/// What the engine's thread hands the main actor: control messages queued in
/// order (a task per message could be reordered), and frames, decoded where they
/// arrive and left in a latest-wins slot.
private final class Link: @unchecked Sendable {
    let frames = FrameSlot()
    weak var engine: Engine?
    private let lock = NSLock()
    private var queued: [EngineMessage] = []
    private let log = Logger(subsystem: "com.thejefflarson.goat", category: "engine")

    func control(_ json: String) {
        guard let message = EngineMessage.decode(json) else {
            log.error("dropped an engine message that did not decode")
            return
        }
        lock.lock()
        queued.append(message)
        let first = queued.count == 1
        lock.unlock()
        if first {
            let engine = engine
            Task { @MainActor in engine?.drain() }
        }
    }

    func take() -> [EngineMessage] {
        lock.lock()
        defer { lock.unlock() }
        defer { queued = [] }
        return queued
    }

    func frame(_ bytes: [UInt8]) {
        do {
            frames.put(try Frame.decode(bytes))
        } catch {
            log.error("dropped a frame: \(String(describing: error), privacy: .public)")
        }
    }
}

/// The C engine. Freed when released, which waits for a callback in flight, so
/// the callbacks never wait on the main actor.
private final class Native: @unchecked Sendable {
    private let handle: OpaquePointer

    init?(link: Link) {
        let context = Unmanaged.passRetained(link)
        let callbacks = goat_engine_callbacks(
            context: context.toOpaque(),
            control: { context, json, len in
                let link = Unmanaged<Link>.fromOpaque(context!).takeUnretainedValue()
                link.control(String(decoding: UnsafeBufferPointer(start: json, count: len), as: UTF8.self))
            },
            frame: { context, bytes, len in
                let link = Unmanaged<Link>.fromOpaque(context!).takeUnretainedValue()
                link.frame(Array(UnsafeBufferPointer(start: bytes, count: len)))
            },
            closed: { context in Unmanaged<Link>.fromOpaque(context!).release() })
        guard let handle = goat_engine_new(callbacks) else {
            context.release()
            return nil
        }
        self.handle = handle
    }

    deinit { goat_engine_free(handle) }

    func run(_ source: String) {
        var source = source
        source.withUTF8 { goat_engine_run(handle, $0.baseAddress, $0.count) }
    }

    func stop() { goat_engine_stop(handle) }

    func key(_ key: String, down: Bool) {
        var key = key
        key.withUTF8 { goat_engine_key(handle, $0.baseAddress, $0.count, down) }
    }

    func pointer(_ kind: PointerKind, x: Double, y: Double) {
        goat_engine_pointer(handle, kind.rawValue, x, y)
    }
}

/// Runs goat programs in this process on the native engine (ADR 0043) and
/// reports what they do: a phase, problems, printed output, how a re-run
/// reloaded, and the picture in `frames`.
@MainActor
public final class Engine: ObservableObject {
    public enum Phase: Equatable {
        case loading, ready, running, finished
        case failed(String)
    }

    public static let maxOutputLines = 2000
    static let missingEngineMessage = "This copy of goat is missing its drawing engine."

    @Published public private(set) var phase = Phase.loading
    @Published public private(set) var diagnostics: [Diagnostic] = []
    @Published public private(set) var output: [String] = []
    @Published public private(set) var reload: Reload?

    public let frames: FrameSlot
    private let native: Native?
    private let link = Link()

    public init() {
        frames = link.frames
        native = Native(link: link)
        link.engine = self
        if native == nil { phase = .failed(Self.missingEngineMessage) }
    }

    /// Run while a program is running reloads it in place when it can (ADR 0035).
    public func run(source: String) {
        guard let native, phase.canRun else { return }
        diagnostics = []
        reload = nil
        if phase != .running {
            output = []
            frames.put([])
        }
        native.run(source)
    }

    public func stop() {
        native?.stop()
        if phase == .running { phase = .ready }
    }

    public func key(_ key: String, down: Bool) { native?.key(key, down: down) }

    public func pointer(_ kind: PointerKind, x: Double, y: Double) { native?.pointer(kind, x: x, y: y) }

    public func clearDiagnostics() {
        if !diagnostics.isEmpty { diagnostics = [] }
    }

    fileprivate func drain() {
        link.take().forEach(receive)
    }

    func receive(_ message: EngineMessage) {
        switch message {
        case .ready:
            if phase == .loading { phase = .ready }
        case .diagnostics(let found):
            diagnostics = found
        case .output(let lines):
            output = Array((output + lines).suffix(Self.maxOutputLines))
        case .state(.running, _):
            phase = .running
        case .state(.finished, _):
            phase = .finished
        case .state(.failed, let message):
            phase = .failed(message ?? "your program stopped")
        case .reloaded(let reloaded):
            reload = reloaded
        }
    }
}

extension Engine.Phase {
    var canRun: Bool {
        switch self {
        case .loading: false
        case .ready, .running, .finished, .failed: true
        }
    }
}
#endif
