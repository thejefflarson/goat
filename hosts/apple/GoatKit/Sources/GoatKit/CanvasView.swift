// SwiftPM's `swift test` has no GoatEngine module; only the Xcode project links it.
#if canImport(GoatEngine)
import SwiftUI

#if os(macOS)
struct CanvasView: NSViewRepresentable {
    let engine: Engine
    func makeNSView(context: Context) -> CanvasHostView {
        let view = CanvasHostView(frames: engine.frames)
        view.onKey = { [engine] in engine.key($0, down: $1) }
        view.onPointer = { [engine] in engine.pointer($0, x: $1, y: $2) }
        return view
    }
    func updateNSView(_ view: CanvasHostView, context: Context) {}
}
#else
struct CanvasView: UIViewRepresentable {
    let engine: Engine
    func makeUIView(context: Context) -> CanvasHostView {
        let view = CanvasHostView(frames: engine.frames)
        view.onKey = { [engine] in engine.key($0, down: $1) }
        view.onPointer = { [engine] in engine.pointer($0, x: $1, y: $2) }
        return view
    }
    func updateUIView(_ view: CanvasHostView, context: Context) {}
}
#endif
#endif
