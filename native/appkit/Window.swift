import AppKit

/// The canvas: draws the latest picture scaled to fit and centered, and turns
/// the keyboard and mouse into goat events.
final class CanvasView: NSView {
    var link: Link?
    var shapes: [Shape] = [] {
        didSet { needsDisplay = true }
    }
    /// What a stopped program said, drawn over the picture.
    var message: String? {
        didSet { needsDisplay = true }
    }

    override var isFlipped: Bool { true }
    override var acceptsFirstResponder: Bool { true }

    override func updateTrackingAreas() {
        super.updateTrackingAreas()
        trackingAreas.forEach(removeTrackingArea)
        addTrackingArea(
            NSTrackingArea(rect: .zero, options: [.mouseMoved, .activeInKeyWindow, .inVisibleRect], owner: self))
    }

    /// Where the picture sits in the view.
    private var fit: (scale: CGFloat, origin: CGPoint) {
        let scale = min(bounds.width / Painter.size.width, bounds.height / Painter.size.height)
        return (
            scale,
            CGPoint(
                x: (bounds.width - Painter.size.width * scale) / 2,
                y: (bounds.height - Painter.size.height * scale) / 2)
        )
    }

    override func draw(_ dirtyRect: NSRect) {
        guard let context = NSGraphicsContext.current?.cgContext else { return }
        NSColor.windowBackgroundColor.setFill()
        bounds.fill()
        let (scale, origin) = fit
        context.saveGState()
        context.translateBy(x: origin.x, y: origin.y)
        context.scaleBy(x: scale, y: scale)
        context.setFillColor(.white)
        context.fill(CGRect(origin: .zero, size: Painter.size))
        context.clip(to: CGRect(origin: .zero, size: Painter.size))
        Painter.paint(shapes, in: context)
        context.restoreGState()
        if let message { drawBanner(message) }
    }

    private func drawBanner(_ message: String) {
        let style = NSMutableParagraphStyle()
        style.lineBreakMode = .byWordWrapping
        let attributes: [NSAttributedString.Key: Any] = [
            .font: NSFont.monospacedSystemFont(ofSize: 12, weight: .regular),
            .foregroundColor: NSColor.white,
            .paragraphStyle: style,
        ]
        let width = bounds.width - 24
        let text = NSAttributedString(string: message, attributes: attributes)
        let height = ceil(text.boundingRect(with: CGSize(width: width, height: .greatestFiniteMagnitude), options: .usesLineFragmentOrigin).height)
        let banner = CGRect(x: 0, y: max(0, bounds.height - height - 24), width: bounds.width, height: min(bounds.height, height + 24))
        NSColor(calibratedRed: 0.6, green: 0.1, blue: 0.1, alpha: 0.95).setFill()
        banner.fill()
        text.draw(in: banner.insetBy(dx: 12, dy: 12))
    }

    // MARK: Keyboard

    override func keyDown(with event: NSEvent) {
        if let name = Self.keyName(event) { link?.key(name, down: true) }
    }

    override func keyUp(with event: NSEvent) {
        if let name = Self.keyName(event) { link?.key(name, down: false) }
    }

    /// The browser's `KeyboardEvent.key` text for a key, which is what goat's
    /// event constructors decode.
    static func keyName(_ event: NSEvent) -> String? {
        switch event.keyCode {
        case 123: return "ArrowLeft"
        case 124: return "ArrowRight"
        case 125: return "ArrowDown"
        case 126: return "ArrowUp"
        case 36, 76: return "Enter"
        case 48: return "Tab"
        case 51: return "Backspace"
        case 53: return "Escape"
        default:
            guard let text = event.characters, let scalar = text.unicodeScalars.first,
                !(0xF700...0xF8FF).contains(scalar.value), !text.unicodeScalars.contains(where: { $0.value < 0x20 })
            else { return nil }
            return text
        }
    }

    // MARK: Pointer

    override func mouseMoved(with event: NSEvent) { send(.move, event) }
    override func mouseDragged(with event: NSEvent) { send(.move, event) }
    override func mouseDown(with event: NSEvent) {
        window?.makeFirstResponder(self)
        send(.down, event)
    }
    override func mouseUp(with event: NSEvent) { send(.up, event) }

    private func send(_ kind: Link.Pointer, _ event: NSEvent) {
        let point = convert(event.locationInWindow, from: nil)
        let (scale, origin) = fit
        link?.pointer(kind, x: (point.x - origin.x) / scale, y: (point.y - origin.y) / scale)
    }
}

/// Reports whether the process should exit with failure once the window closes.
final class AppDelegate: NSObject, NSApplicationDelegate {
    var failed = false

    func applicationShouldTerminateAfterLastWindowClosed(_ sender: NSApplication) -> Bool { true }

    func applicationWillTerminate(_ notification: Notification) {
        if failed { exit(1) }
    }
}

enum Window {
    static func run(title: String) -> Never {
        let app = NSApplication.shared
        app.setActivationPolicy(.regular)
        let delegate = AppDelegate()
        app.delegate = delegate
        app.mainMenu = menu(title: title)

        let view = CanvasView(frame: NSRect(origin: .zero, size: Painter.size))
        let window = NSWindow(
            contentRect: view.frame, styleMask: [.titled, .closable, .miniaturizable, .resizable],
            backing: .buffered, defer: false)
        window.title = title
        window.contentView = view
        window.contentMinSize = NSSize(width: 200, height: 150)
        window.acceptsMouseMovedEvents = true
        window.center()
        window.makeKeyAndOrderFront(nil)
        window.makeFirstResponder(view)

        let link = Link()
        view.link = link
        link.onPicture = { shapes in
            DispatchQueue.main.async { view.shapes = shapes }
        }
        let stop = { (message: String) in
            FileHandle.standardError.write(Data("goat: \(message)\n".utf8))
            DispatchQueue.main.async {
                delegate.failed = true
                view.message = message
            }
        }
        link.onStopped = { message, _ in stop(message) }
        link.onBadFrame = { message in stop("the picture could not be drawn: \(message)") }
        link.start()

        app.activate(ignoringOtherApps: true)
        app.run()
        exit(0)
    }

    private static func menu(title: String) -> NSMenu {
        let main = NSMenu()
        let item = NSMenuItem()
        main.addItem(item)
        let app = NSMenu()
        app.addItem(
            NSMenuItem(title: "Quit \(title)", action: #selector(NSApplication.terminate(_:)), keyEquivalent: "q"))
        item.submenu = app
        return main
    }
}
