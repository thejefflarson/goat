#if os(iOS)
import GoatKit
import SwiftUI
import UIKit

/// A UIDocument over the same text `GoatDocument` reads and writes.
final class GoatUIDocument: UIDocument {
    var text = ""

    override func load(fromContents contents: Any, ofType typeName: String?) throws {
        guard let data = contents as? Data else { throw CocoaError(.fileReadCorruptFile) }
        text = try GoatDocument.decode(data)
    }

    override func contents(forType typeName: String) throws -> Any {
        Data(text.utf8)
    }
}

/// Creates into the app's local Documents and opens files in place, so creating
/// never goes through the Files import step and never waits on iCloud.
final class GoatBrowserController: UIDocumentBrowserViewController, UIDocumentBrowserViewControllerDelegate {
    init() {
        super.init(forOpening: [.goatSource])
        delegate = self
        allowsDocumentCreation = true
        allowsPickingMultipleItems = false
    }

    @available(*, unavailable)
    required init?(coder: NSCoder) { fatalError("init(coder:) is not used") }

    func documentBrowser(
        _ controller: UIDocumentBrowserViewController,
        didRequestDocumentCreationWithHandler importHandler: @escaping (URL?, UIDocumentBrowserViewController.ImportMode) -> Void
    ) {
        do {
            importHandler(try LocalDocuments.create(in: LocalDocuments.directory()), .none)
        } catch {
            importHandler(nil, .none)
        }
    }

    func documentBrowser(_ controller: UIDocumentBrowserViewController, didPickDocumentsAt documentURLs: [URL]) {
        if let url = documentURLs.first { open(url) }
    }

    func documentBrowser(
        _ controller: UIDocumentBrowserViewController, didImportDocumentAt sourceURL: URL,
        toDestinationURL destinationURL: URL
    ) {
        open(destinationURL)
    }

    func documentBrowser(
        _ controller: UIDocumentBrowserViewController, failedToImportDocumentAt documentURL: URL, error: Error?
    ) {
        alert("Could not create the document", message: error?.localizedDescription)
    }

    private func alert(_ title: String, message: String? = nil) {
        let alert = UIAlertController(title: title, message: message, preferredStyle: .alert)
        alert.addAction(UIAlertAction(title: "OK", style: .default))
        present(alert, animated: true)
    }

    private func open(_ url: URL) {
        guard presentedViewController == nil else { return }
        let document = GoatUIDocument(fileURL: url)
        document.open { [weak self] success in
            guard let self else { return }
            guard success else { return self.alert("Could not open \(url.lastPathComponent)") }
            let editor = UIHostingController(
                rootView: DocumentEditor(document: document) { [weak self] in
                    document.close { _ in self?.dismiss(animated: true) }
                })
            editor.modalPresentationStyle = .fullScreen
            self.present(editor, animated: true)
        }
    }
}

private struct DocumentEditor: View {
    let document: GoatUIDocument
    let close: () -> Void
    @State private var model: GoatDocument

    init(document: GoatUIDocument, close: @escaping () -> Void) {
        self.document = document
        self.close = close
        _model = State(initialValue: GoatDocument(text: document.text))
    }

    var body: some View {
        NavigationStack {
            EditorScreen(document: $model)
                .navigationTitle(document.localizedName)
                .navigationBarTitleDisplayMode(.inline)
                .toolbar {
                    ToolbarItem(placement: .navigationBarLeading) {
                        Button("Done", action: close)
                    }
                }
                .onChange(of: model.text) { text in
                    document.text = text
                    document.updateChangeCount(.done)
                }
        }
    }
}

struct DocumentBrowser: UIViewControllerRepresentable {
    func makeUIViewController(context: Context) -> GoatBrowserController { GoatBrowserController() }
    func updateUIViewController(_ controller: GoatBrowserController, context: Context) {}
}
#endif
