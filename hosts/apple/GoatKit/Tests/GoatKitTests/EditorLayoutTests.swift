#if os(macOS) && canImport(GoatEngine)
import SwiftUI
import XCTest

@testable import GoatKit

/// Lays `EditorScreen` out at phone and iPad sizes (both orientations) and checks
/// that the editor and canvas each keep a usable area.
@MainActor
final class EditorLayoutTests: XCTestCase {
    private let sizes: [(name: String, size: CGSize)] = [
        ("phone portrait", CGSize(width: 390, height: 844)),
        ("phone landscape", CGSize(width: 844, height: 390)),
        ("iPad portrait", CGSize(width: 820, height: 1180)),
        ("iPad landscape", CGSize(width: 1366, height: 1024)),
    ]

    private func descendants(of view: NSView) -> [NSView] {
        view.subviews + view.subviews.flatMap(descendants)
    }

    private func laidOut(_ size: CGSize, engine: Engine) -> NSView {
        let screen = EditorScreen(document: .constant(GoatDocument()), engine: engine)
        let host = NSHostingView(rootView: screen)
        let window = NSWindow(
            contentRect: CGRect(origin: .zero, size: size), styleMask: [.titled], backing: .buffered, defer: false)
        window.contentView = host
        host.frame = CGRect(origin: .zero, size: size)
        host.layoutSubtreeIfNeeded()
        RunLoop.current.run(until: Date().addingTimeInterval(0.2))
        host.layoutSubtreeIfNeeded()
        return host
    }

    func testEditorAndCanvasKeepAUsableAreaAtPhoneAndPadSizes() {
        let engine = Engine()
        for (name, size) in sizes {
            let all = descendants(of: laidOut(size, engine: engine))
            let canvas = all.first { String(describing: type(of: $0)).contains("CanvasHostView") }
            let editor = all.first { $0 is NSTextView }
            XCTAssertNotNil(canvas, name)
            XCTAssertNotNil(editor, name)
            for (what, view) in [("canvas", canvas), ("editor", editor)] {
                guard let view else { continue }
                XCTAssertGreaterThanOrEqual(view.frame.width, 150, "\(name): \(what) too narrow")
                XCTAssertGreaterThanOrEqual(view.frame.height, 100, "\(name): \(what) too short")
                XCTAssertLessThanOrEqual(view.frame.maxX, size.width + 1, "\(name): \(what) overflows")
            }
        }
    }

    func testTheCanvasIsTheNativeView() {
        let host = laidOut(CGSize(width: 390, height: 844), engine: Engine())
        XCTAssertTrue(descendants(of: host).contains { $0 is CanvasHostView })
    }
}
#endif
