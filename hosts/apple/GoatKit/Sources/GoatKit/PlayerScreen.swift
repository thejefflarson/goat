// SwiftPM's `swift test` has no GoatEngine module; only the Xcode project links it.
#if canImport(GoatEngine)
import SwiftUI

/// The exported app's window: the canvas, and one line of text when the program
/// cannot run or stops with a problem. It runs the program once the engine is ready.
public struct PlayerScreen: View {
    private let program: Result<String, PlayerProgram.Failure>
    @StateObject private var engine = Engine()
    @State private var started = false

    public init(program: Result<String, PlayerProgram.Failure>) {
        self.program = program
    }

    public var body: some View {
        VStack(spacing: 0) {
            CanvasView(engine: engine)
                .accessibilityLabel("drawing")
                .accessibilityValue(engine.phase.accessibilityValue)
                .overlay { LoadOverlay(phase: engine.phase) }
            if let problem {
                Text(problem)
                    .foregroundStyle(.red)
                    .font(.system(.body, design: .monospaced))
                    .textSelection(.enabled)
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .padding(8)
            }
        }
        .task(id: engine.phase) {
            guard engine.phase == .ready, !started, case .success(let source) = program else {
                return
            }
            started = true
            engine.run(source: source)
        }
    }

    private var problem: String? {
        if case .failure(let failure) = program { return failure.message }
        return Self.problem(phase: engine.phase, diagnostics: engine.diagnostics)
    }

    static func problem(phase: Engine.Phase, diagnostics: [Diagnostic]) -> String? {
        if let first = diagnostics.first {
            return first.line > 0
                ? "\(first.line):\(first.column): \(first.message)" : first.message
        }
        if case .failed(let message) = phase { return message }
        return nil
    }
}
#endif
