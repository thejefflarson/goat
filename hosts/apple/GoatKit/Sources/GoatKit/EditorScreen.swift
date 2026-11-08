import SwiftUI

#if os(macOS)
private struct CanvasView: NSViewRepresentable {
    let webView: NSView
    func makeNSView(context: Context) -> NSView { webView }
    func updateNSView(_ view: NSView, context: Context) {}
}
#else
private struct CanvasView: UIViewRepresentable {
    let webView: UIView
    func makeUIView(context: Context) -> UIView { webView }
    func updateUIView(_ view: UIView, context: Context) {}
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
                .disabled(engine.phase == .loading)
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
