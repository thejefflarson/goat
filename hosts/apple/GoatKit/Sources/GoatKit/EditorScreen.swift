// SwiftPM's `swift test` has no GoatEngine module; only the Xcode project links it.
#if canImport(GoatEngine)
import SwiftUI

#if os(iOS)
/// Play mode: the canvas edge to edge on black, with a Close button that shows on
/// a touch and fades after a few seconds; swiping down closes too. The program
/// keeps running behind it, so leaving Play returns to the editor with the same
/// picture, not a restart.
private struct PlayCanvas: View {
    let engine: Engine
    let close: () -> Void
    @State private var closeVisible = true
    @State private var fade: Task<Void, Never>?

    var body: some View {
        ZStack(alignment: .topLeading) {
            Color.black
            CanvasView(
                engine: engine, margin: CGColor(gray: 0, alpha: 1), onTouchDown: reveal, onSwipeDown: close
            )
            .accessibilityLabel("drawing")
            .accessibilityValue(engine.phase.accessibilityValue)
            .accessibilityIdentifier("canvas")
            if closeVisible {
                Button(action: close) {
                    Image(systemName: "xmark.circle.fill")
                        .font(.largeTitle)
                        .symbolRenderingMode(.palette)
                        .foregroundStyle(.white, .black.opacity(0.6))
                        .padding(16)
                }
                .accessibilityLabel("Close")
                .accessibilityIdentifier("closePlay")
                .transition(.opacity)
            }
        }
        .ignoresSafeArea()
        .statusBarHidden()
        .persistentSystemOverlays(.hidden)
        .onAppear(perform: reveal)
        .onDisappear { fade?.cancel() }
    }

    private func reveal() {
        withAnimation { closeVisible = true }
        fade?.cancel()
        fade = Task {
            try? await Task.sleep(for: .seconds(3))
            guard !Task.isCancelled else { return }
            withAnimation { closeVisible = false }
        }
    }
}
#endif

/// The editor window: native source editor and Run control beside the
/// engine's canvas, with problems and printed output below. The editor stays
/// editable while a program runs.
public struct EditorScreen: View {
    @Binding var document: GoatDocument
    private let name: String
    @StateObject private var engine = Engine()
    @State private var ranSource: String?
    #if os(iOS)
    @State private var playing = false
    #endif

    public init(document: Binding<GoatDocument>, name: String = "Untitled") {
        _document = document
        self.name = name
    }

    init(document: Binding<GoatDocument>, engine: Engine) {
        _document = document
        name = "Untitled"
        _engine = StateObject(wrappedValue: engine)
    }

    public var body: some View {
        #if os(iOS)
        if playing {
            PlayCanvas(engine: engine) { playing = false }
                .toolbar(.hidden, for: .navigationBar)
        } else {
            editor
        }
        #else
        editor
        #endif
    }

    private var editor: some View {
        VStack(spacing: 0) {
            GeometryReader { geometry in
                let layout = geometry.size.width > geometry.size.height
                    ? AnyLayout(HStackLayout(spacing: 0)) : AnyLayout(VStackLayout(spacing: 0))
                layout {
                    CodeEditor(text: sourceBinding, highlights: highlights)
                    Divider()
                    CanvasView(engine: engine)
                        .accessibilityLabel("drawing")
                        .accessibilityValue(engine.phase.accessibilityValue)
                        .accessibilityIdentifier("canvas")
                        .overlay { LoadOverlay(phase: engine.phase) }
                }
            }
            Divider()
            ProblemsPanel(
                phase: engine.phase, diagnostics: engine.diagnostics, output: engine.output, reload: engine.reload)
        }
        #if os(macOS)
        .focusedSceneValue(\.exportMenu, exportMenu)
        #endif
        .toolbar {
            ToolbarItemGroup {
                Button {
                    ranSource = document.text
                    engine.run(source: document.text)
                } label: {
                    Label("Run", systemImage: "play.fill")
                }
                .keyboardShortcut("r", modifiers: .command)
                .disabled(!engine.phase.canRun)
                Button {
                    engine.stop()
                } label: {
                    Label("Stop", systemImage: "stop.fill")
                }
                .keyboardShortcut(".", modifiers: .command)
                .disabled(engine.phase != .running)
                #if os(iOS)
                Button {
                    engine.run(source: document.text)
                    playing = true
                } label: {
                    Label("Play", systemImage: "rectangle.expand.vertical")
                }
                .disabled(!engine.phase.canRun)
                #endif
            }
        }
    }

    #if os(macOS)
    private var exportMenu: ExportMenu {
        ExportMenu(
            canExport: ExportGate.canExport(
                ranSource: ranSource, current: document.text, phase: engine.phase,
                diagnostics: engine.diagnostics),
            exportApp: { [name, text = document.text] in ExportFlow.exportPlayer(name: name, program: text) },
            exportNativeApp: { [name] in ExportFlow.exportNative(name: name) })
    }
    #endif

    /// Editing makes the reported problems stale, so they clear with the first keystroke.
    private var sourceBinding: Binding<String> {
        Binding(
            get: { document.text },
            set: {
                document.text = $0
                engine.clearDiagnostics()
            })
    }

    private var highlights: [NSRange] {
        engine.diagnostics.compactMap { $0.range(in: document.text) }
    }
}

/// A program can be exported once it has run clean: the text on screen is the text
/// that last ran, it is running or finished, and it reported no problems.
enum ExportGate {
    static func canExport(
        ranSource: String?, current: String, phase: Engine.Phase, diagnostics: [Diagnostic]
    ) -> Bool {
        ranSource == current && diagnostics.isEmpty && (phase == .running || phase == .finished)
    }
}

extension Engine.Phase {
    /// What the canvas reports to assistive technology and to UI tests: `finished`
    /// means the program ran to the end and drew.
    var accessibilityValue: String {
        switch self {
        case .loading: "loading"
        case .ready: "ready"
        case .running: "running"
        case .finished: "finished"
        case .failed: "failed"
        }
    }
}

/// Covers the canvas until the engine is ready, so Run is never offered before it works.
struct LoadOverlay: View {
    let phase: Engine.Phase

    var body: some View {
        if phase == .loading {
            VStack(spacing: 12) {
                ProgressView()
                Text("Loading…")
            }
            .frame(maxWidth: .infinity, maxHeight: .infinity)
            .background(.background)
            .accessibilityElement(children: .combine)
        }
    }
}

private struct ProblemsPanel: View {
    let phase: Engine.Phase
    let diagnostics: [Diagnostic]
    let output: [String]
    let reload: Reload?

    var body: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 4) {
                ForEach(Array(diagnostics.enumerated()), id: \.offset) { _, diagnostic in
                    Text(describe(diagnostic))
                        .foregroundStyle(.red)
                        .accessibilityLabel("problem: \(describe(diagnostic))")
                }
                if diagnostics.isEmpty, case .failed(let message) = phase {
                    Text(message).foregroundStyle(.red)
                }
                if let reload {
                    Text(reload.summary)
                        .accessibilityLabel("reloaded: \(reload.keptModel ? "kept" : "reset")")
                }
                if !output.isEmpty {
                    Text(output.joined(separator: "\n"))
                        .accessibilityLabel("printed output")
                }
            }
            .font(.system(.body, design: .monospaced))
            .textSelection(.enabled)
            .frame(maxWidth: .infinity, alignment: .leading)
            .padding(8)
        }
        .frame(height: 110)
    }

    private func describe(_ diagnostic: Diagnostic) -> String {
        diagnostic.line > 0
            ? "\(diagnostic.line):\(diagnostic.column): \(diagnostic.message)" : diagnostic.message
    }
}
#endif
