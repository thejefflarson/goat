import SwiftUI

#if os(macOS)
private typealias PlatformView = NSView
#else
private typealias PlatformView = UIView
#endif

/// Hosts the engine's current web view, swapping it in place when the watchdog
/// replaces it.
private final class CanvasContainer: PlatformView {
    func show(_ webView: PlatformView) {
        guard subviews.first !== webView else { return }
        subviews.forEach { $0.removeFromSuperview() }
        webView.frame = bounds
        #if os(macOS)
        webView.autoresizingMask = [.width, .height]
        #else
        webView.autoresizingMask = [.flexibleWidth, .flexibleHeight]
        #endif
        addSubview(webView)
    }
}

#if os(macOS)
private struct CanvasView: NSViewRepresentable {
    let webView: NSView
    func makeNSView(context: Context) -> CanvasContainer {
        let container = CanvasContainer()
        container.show(webView)
        return container
    }
    func updateNSView(_ container: CanvasContainer, context: Context) { container.show(webView) }
}
#else
private struct CanvasView: UIViewRepresentable {
    let webView: UIView
    func makeUIView(context: Context) -> CanvasContainer {
        let container = CanvasContainer()
        container.show(webView)
        return container
    }
    func updateUIView(_ container: CanvasContainer, context: Context) { container.show(webView) }
}
#endif

/// The editor window: native source editor and Run control beside the web
/// view's canvas, with problems and printed output below. The editor stays
/// editable while a program runs.
public struct EditorScreen: View {
    @Binding var document: GoatDocument
    @StateObject private var engine = Engine(assets: Bundle.main.url(forResource: "web", withExtension: nil))

    public init(document: Binding<GoatDocument>) {
        _document = document
    }

    init(document: Binding<GoatDocument>, engine: Engine) {
        _document = document
        _engine = StateObject(wrappedValue: engine)
    }

    public var body: some View {
        VStack(spacing: 0) {
            GeometryReader { geometry in
                let layout = geometry.size.width > geometry.size.height
                    ? AnyLayout(HStackLayout(spacing: 0)) : AnyLayout(VStackLayout(spacing: 0))
                layout {
                    CodeEditor(text: sourceBinding, highlights: highlights)
                    Divider()
                    CanvasView(webView: engine.webView)
                        .accessibilityLabel("drawing")
                        .accessibilityValue(engine.phase.accessibilityValue)
                        .accessibilityIdentifier("canvas")
                        .overlay { LoadOverlay(phase: engine.phase, retry: engine.retry) }
                }
            }
            Divider()
            ProblemsPanel(phase: engine.phase, diagnostics: engine.diagnostics, output: engine.output)
        }
        .toolbar {
            ToolbarItemGroup {
                Button {
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
            }
        }
    }

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

extension Engine.Phase {
    /// What the canvas reports to assistive technology and to UI tests: `finished`
    /// means the program ran to the end and drew.
    var accessibilityValue: String {
        switch self {
        case .loading: "loading"
        case .ready: "ready"
        case .running: "running"
        case .finished: "finished"
        case .failed, .loadFailed: "failed"
        }
    }
}

/// Covers the canvas until the page is ready, so the user never sees a bare white web view.
struct LoadOverlay: View {
    let phase: Engine.Phase
    let retry: () -> Void

    var body: some View {
        switch phase {
        case .loading:
            VStack(spacing: 12) {
                ProgressView()
                Text("Loading…")
            }
            .frame(maxWidth: .infinity, maxHeight: .infinity)
            .background(.background)
            .accessibilityElement(children: .combine)
        case .loadFailed(let message):
            VStack(spacing: 12) {
                Text(message).multilineTextAlignment(.center)
                Button("Retry", action: retry)
                    .buttonStyle(.borderedProminent)
            }
            .padding()
            .frame(maxWidth: .infinity, maxHeight: .infinity)
            .background(.background)
        default:
            EmptyView()
        }
    }
}

private struct ProblemsPanel: View {
    let phase: Engine.Phase
    let diagnostics: [Diagnostic]
    let output: [String]

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
