import SwiftUI

#if os(macOS)
import AppKit
typealias PlatformColor = NSColor
#else
import UIKit
typealias PlatformColor = UIColor
#endif

/// Marks `ranges` in `storage`, first clearing whatever the last call marked.
@MainActor
private func paint(_ storage: NSTextStorage, ranges: [NSRange]) {
    let whole = NSRange(location: 0, length: storage.length)
    storage.beginEditing()
    storage.removeAttribute(.backgroundColor, range: whole)
    for range in ranges where NSMaxRange(range) <= storage.length {
        storage.addAttribute(.backgroundColor, value: PlatformColor.systemRed.withAlphaComponent(0.3), range: range)
    }
    storage.endEditing()
}

#if os(macOS)
/// A plain-text editor for goat source. SwiftUI's `TextEditor` leaves the
/// system's smart quotes and dash substitution on, which would turn `"red"` into
/// curly quotes the parser rejects, so this wraps the platform text view.
struct CodeEditor: NSViewRepresentable {
    @Binding var text: String
    var highlights: [NSRange]

    func makeCoordinator() -> Coordinator { Coordinator(self) }

    func makeNSView(context: Context) -> NSScrollView {
        let scroll = NSTextView.scrollableTextView()
        let view = scroll.documentView as! NSTextView
        view.isRichText = false
        view.allowsUndo = true
        view.isAutomaticQuoteSubstitutionEnabled = false
        view.isAutomaticDashSubstitutionEnabled = false
        view.isAutomaticTextReplacementEnabled = false
        view.isAutomaticSpellingCorrectionEnabled = false
        view.isAutomaticLinkDetectionEnabled = false
        view.isAutomaticDataDetectionEnabled = false
        view.isContinuousSpellCheckingEnabled = false
        view.smartInsertDeleteEnabled = false
        view.font = .monospacedSystemFont(ofSize: 14, weight: .regular)
        view.textContainerInset = NSSize(width: 6, height: 8)
        view.setAccessibilityLabel("goat code")
        view.string = text
        view.delegate = context.coordinator
        return scroll
    }

    func updateNSView(_ scroll: NSScrollView, context: Context) {
        context.coordinator.parent = self
        let view = scroll.documentView as! NSTextView
        if view.string != text { view.string = text }
        if let storage = view.textStorage { paint(storage, ranges: highlights) }
    }

    final class Coordinator: NSObject, NSTextViewDelegate {
        var parent: CodeEditor
        init(_ parent: CodeEditor) { self.parent = parent }

        func textDidChange(_ notification: Notification) {
            guard let view = notification.object as? NSTextView else { return }
            parent.text = view.string
        }
    }
}
#else
/// A plain-text editor for goat source. The platform text view is wrapped
/// because SwiftUI's `TextEditor` leaves smart quotes on, which would turn
/// `"red"` into curly quotes the parser rejects.
struct CodeEditor: UIViewRepresentable {
    @Binding var text: String
    var highlights: [NSRange]

    func makeCoordinator() -> Coordinator { Coordinator(self) }

    func makeUIView(context: Context) -> UITextView {
        let view = UITextView()
        view.autocorrectionType = .no
        view.autocapitalizationType = .none
        view.smartQuotesType = .no
        view.smartDashesType = .no
        view.smartInsertDeleteType = .no
        view.spellCheckingType = .no
        view.keyboardDismissMode = .interactive
        view.adjustsFontForContentSizeCategory = true
        view.font = UIFontMetrics(forTextStyle: .body)
            .scaledFont(for: .monospacedSystemFont(ofSize: 15, weight: .regular))
        view.textContainerInset = UIEdgeInsets(top: 8, left: 6, bottom: 8, right: 6)
        view.accessibilityLabel = "goat code"
        view.text = text
        view.delegate = context.coordinator
        return view
    }

    func updateUIView(_ view: UITextView, context: Context) {
        context.coordinator.parent = self
        if view.text != text { view.text = text }
        paint(view.textStorage, ranges: highlights)
    }

    final class Coordinator: NSObject, UITextViewDelegate {
        var parent: CodeEditor
        init(_ parent: CodeEditor) { self.parent = parent }

        func textViewDidChange(_ view: UITextView) {
            parent.text = view.text
        }
    }
}
#endif
