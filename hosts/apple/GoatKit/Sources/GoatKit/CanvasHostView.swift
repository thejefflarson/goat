import CoreGraphics
import Foundation
import GoatCanvas

#if os(macOS)
import AppKit
#else
import UIKit
#endif

/// Where the canvas's own 400 by 300 units land in a view: the largest centered
/// rectangle with the canvas's proportions.
enum CanvasLayout {
    static func fit(_ bounds: CGSize) -> (origin: CGPoint, scale: CGFloat) {
        let scale = min(bounds.width / Painter.size.width, bounds.height / Painter.size.height)
        guard scale.isFinite, scale > 0 else { return (.zero, 0) }
        return (
            CGPoint(
                x: (bounds.width - Painter.size.width * scale) / 2,
                y: (bounds.height - Painter.size.height * scale) / 2), scale
        )
    }

    static func canvasPoint(_ point: CGPoint, in bounds: CGSize) -> CGPoint {
        let (origin, scale) = fit(bounds)
        guard scale > 0 else { return .zero }
        return CGPoint(x: (point.x - origin.x) / scale, y: (point.y - origin.y) / scale)
    }

    /// Paints `shapes` onto a white page in a context with y down; `margin` fills
    /// whatever the page does not cover.
    static func draw(
        _ shapes: [Shape], in context: CGContext, bounds: CGSize, margin: CGColor = CGColor(gray: 1, alpha: 1)
    ) {
        context.setFillColor(margin)
        context.fill(CGRect(origin: .zero, size: bounds))
        let (origin, scale) = fit(bounds)
        guard scale > 0 else { return }
        context.setFillColor(CGColor(gray: 1, alpha: 1))
        context.fill(
            CGRect(origin: origin, size: CGSize(width: Painter.size.width * scale, height: Painter.size.height * scale)))
        context.saveGState()
        defer { context.restoreGState() }
        context.translateBy(x: origin.x, y: origin.y)
        context.scaleBy(x: scale, y: scale)
        context.clip(to: CGRect(origin: .zero, size: Painter.size))
        Painter.paint(shapes, in: context)
    }
}

public enum PointerKind: UInt32 {
    case move = 0, down = 1, up = 2
}

/// Names keys the way `KeyboardEvent.key` does, which is what goat programs match on.
enum KeyName {
    private static let named: [UInt32: String] = [
        0xF700: "ArrowUp", 0xF701: "ArrowDown", 0xF702: "ArrowLeft", 0xF703: "ArrowRight",
        0x0D: "Enter", 0x03: "Enter", 0x1B: "Escape", 0x7F: "Backspace", 0x09: "Tab",
    ]

    /// `typed` is what the key types; AppKit gives the arrow keys private-use scalars.
    static func name(typed: String) -> String? {
        guard let first = typed.unicodeScalars.first else { return nil }
        if typed.unicodeScalars.count == 1, let name = named[first.value] { return name }
        return typed.unicodeScalars.contains { (0xF700...0xF8FF).contains($0.value) } ? nil : typed
    }
}

#if os(macOS)
/// Draws the engine's frames and sends the keyboard and pointer to it. Click the
/// picture to give it the keyboard.
final class CanvasHostView: NSView {
    private let frames: FrameSlot
    var onKey: (String, Bool) -> Void = { _, _ in }
    var onPointer: (PointerKind, Double, Double) -> Void = { _, _, _ in }

    init(frames: FrameSlot) {
        self.frames = frames
        super.init(frame: .zero)
        frames.onUndrawn { [weak self] in self?.needsDisplay = true }
    }

    required init?(coder: NSCoder) { fatalError("not loaded from a nib") }

    override var isFlipped: Bool { true }
    override var acceptsFirstResponder: Bool { true }

    override func draw(_ dirtyRect: NSRect) {
        guard let context = NSGraphicsContext.current?.cgContext else { return }
        CanvasLayout.draw(frames.take(), in: context, bounds: bounds.size)
    }

    override func updateTrackingAreas() {
        super.updateTrackingAreas()
        trackingAreas.forEach(removeTrackingArea)
        addTrackingArea(
            NSTrackingArea(rect: .zero, options: [.mouseMoved, .activeInKeyWindow, .inVisibleRect], owner: self))
    }

    override func keyDown(with event: NSEvent) { forward(event, down: true) }
    override func keyUp(with event: NSEvent) { forward(event, down: false) }

    private func forward(_ event: NSEvent, down: Bool) {
        if let key = KeyName.name(typed: event.characters ?? "") { onKey(key, down) }
    }

    override func mouseDown(with event: NSEvent) {
        window?.makeFirstResponder(self)
        point(.down, event)
    }
    override func mouseUp(with event: NSEvent) { point(.up, event) }
    override func mouseMoved(with event: NSEvent) { point(.move, event) }
    override func mouseDragged(with event: NSEvent) { point(.move, event) }

    private func point(_ kind: PointerKind, _ event: NSEvent) {
        let at = CanvasLayout.canvasPoint(convert(event.locationInWindow, from: nil), in: bounds.size)
        onPointer(kind, at.x, at.y)
    }
}
#else
final class CanvasHostView: UIView {
    private let frames: FrameSlot
    var onKey: (String, Bool) -> Void = { _, _ in }
    var onPointer: (PointerKind, Double, Double) -> Void = { _, _, _ in }
    var onSwipeDown: (() -> Void)?
    var margin = CGColor(gray: 1, alpha: 1)

    init(frames: FrameSlot) {
        self.frames = frames
        super.init(frame: .zero)
        contentMode = .redraw
        isOpaque = true
        frames.onUndrawn { [weak self] in self?.setNeedsDisplay() }
        let swipe = UISwipeGestureRecognizer(target: self, action: #selector(swiped))
        swipe.direction = .down
        swipe.cancelsTouchesInView = false
        addGestureRecognizer(swipe)
    }

    @objc private func swiped() { onSwipeDown?() }

    required init?(coder: NSCoder) { fatalError("not loaded from a nib") }

    override var canBecomeFirstResponder: Bool { true }

    override func draw(_ rect: CGRect) {
        guard let context = UIGraphicsGetCurrentContext() else { return }
        CanvasLayout.draw(frames.take(), in: context, bounds: bounds.size, margin: margin)
    }

    private static let named: [UIKeyboardHIDUsage: String] = [
        .keyboardUpArrow: "ArrowUp", .keyboardDownArrow: "ArrowDown",
        .keyboardLeftArrow: "ArrowLeft", .keyboardRightArrow: "ArrowRight",
        .keyboardReturnOrEnter: "Enter", .keyboardEscape: "Escape",
        .keyboardDeleteOrBackspace: "Backspace", .keyboardTab: "Tab",
    ]

    override func pressesBegan(_ presses: Set<UIPress>, with event: UIPressesEvent?) {
        forward(presses, down: true) { super.pressesBegan(presses, with: event) }
    }
    override func pressesEnded(_ presses: Set<UIPress>, with event: UIPressesEvent?) {
        forward(presses, down: false) { super.pressesEnded(presses, with: event) }
    }
    override func pressesCancelled(_ presses: Set<UIPress>, with event: UIPressesEvent?) {
        forward(presses, down: false) { super.pressesCancelled(presses, with: event) }
    }

    private func forward(_ presses: Set<UIPress>, down: Bool, passOn: () -> Void) {
        var unhandled = false
        for press in presses {
            guard let key = press.key else { unhandled = true; continue }
            if let name = Self.named[key.keyCode] ?? KeyName.name(typed: key.characters) {
                onKey(name, down)
            } else {
                unhandled = true
            }
        }
        if unhandled { passOn() }
    }

    override func touchesBegan(_ touches: Set<UITouch>, with event: UIEvent?) {
        becomeFirstResponder()
        point(.down, touches)
    }
    override func touchesMoved(_ touches: Set<UITouch>, with event: UIEvent?) { point(.move, touches) }
    override func touchesEnded(_ touches: Set<UITouch>, with event: UIEvent?) { point(.up, touches) }
    override func touchesCancelled(_ touches: Set<UITouch>, with event: UIEvent?) { point(.up, touches) }

    private func point(_ kind: PointerKind, _ touches: Set<UITouch>) {
        guard let touch = touches.first else { return }
        let at = CanvasLayout.canvasPoint(touch.location(in: self), in: bounds.size)
        onPointer(kind, at.x, at.y)
    }
}
#endif
