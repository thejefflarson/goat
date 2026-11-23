import Foundation

/// The Swift side of a goat session (native/src/session.rs): starts the
/// program, decodes each picture it draws and forwards the host's events. The
/// callbacks arrive on goat's threads; `Link` never touches the main thread.
final class Link {
    /// A picture, or why the program's frame could not be read.
    var onPicture: (([Shape]) -> Void)?
    /// The program ended: `stuck` is false for a trap.
    var onStopped: ((_ message: String, _ stuck: Bool) -> Void)?
    var onBadFrame: ((String) -> Void)?

    private var session: OpaquePointer?

    func start() {
        var callbacks = GoatCallbacks(
            user: Unmanaged.passUnretained(self).toOpaque(),
            frame: { user, bytes, length in
                let link = Unmanaged<Link>.fromOpaque(user!).takeUnretainedValue()
                let frame = bytes.map { Array(UnsafeBufferPointer(start: $0, count: Int(length))) } ?? []
                do {
                    link.onPicture?(try Frame.decode(frame))
                } catch {
                    link.onBadFrame?("\(error)")
                }
            },
            stopped: { user, reason, bytes, length in
                let link = Unmanaged<Link>.fromOpaque(user!).takeUnretainedValue()
                let text = bytes.map { String(decoding: UnsafeBufferPointer(start: $0, count: Int(length)), as: UTF8.self) } ?? ""
                link.onStopped?(text, reason == Int32(GOAT_STOP_STUCK))
            })
        var program = goat_program
        let source = goat_source
        session = goat_session_start(&program, source.bytes, source.len, &callbacks)
    }

    func key(_ name: String, down: Bool) {
        guard let session else { return }
        let bytes = Array(name.utf8)
        goat_session_key(session, down ? 1 : 0, bytes, UInt64(bytes.count))
    }

    enum Pointer: Int32 {
        case move = 0
        case down = 1
        case up = 2
    }

    func pointer(_ kind: Pointer, x: Double, y: Double) {
        if let session { goat_session_pointer(session, kind.rawValue, x, y) }
    }
}
