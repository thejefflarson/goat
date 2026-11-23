import CoreGraphics
import CoreText
import Foundation

/// Draws a picture with Core Graphics the way `web/scene.ts` draws it on a
/// canvas: origin top left with y down, one-point round-capped lines, circles
/// and rectangles filled, text filled from its top left corner in 16-point
/// sans-serif.
enum Painter {
    /// The picture's size in its own units; every goat canvas is this big.
    static let size = CGSize(width: 400, height: 300)

    private static let font = CTFontCreateWithName("Helvetica" as CFString, 16, nil)

    /// Paints `shapes` into `context`, which already maps the picture's units
    /// onto its pixels with y down.
    static func paint(_ shapes: [Shape], in context: CGContext) {
        context.saveGState()
        defer { context.restoreGState() }
        context.setLineWidth(1)
        context.setLineCap(.round)
        context.setLineJoin(.round)
        for shape in shapes {
            switch shape {
            case .line(let from, let to, let color):
                guard from.isFinite, to.isFinite else { continue }
                context.setStrokeColor(Color.parse(color) ?? .black)
                context.move(to: from.cg)
                context.addLine(to: to.cg)
                context.strokePath()
            case .polyline(let points, let color):
                guard let first = points.first, points.allSatisfy(\.isFinite) else { continue }
                context.setStrokeColor(Color.parse(color) ?? .black)
                context.move(to: first.cg)
                for point in points.dropFirst() { context.addLine(to: point.cg) }
                context.strokePath()
            case .circle(let center, let radius, let color):
                guard center.isFinite, radius.isFinite, radius >= 0 else { continue }
                context.setFillColor(Color.parse(color) ?? .black)
                context.fillEllipse(
                    in: CGRect(x: center.x - radius, y: center.y - radius, width: 2 * radius, height: 2 * radius))
            case .rect(let origin, let size, let color):
                guard origin.isFinite, size.isFinite else { continue }
                context.setFillColor(Color.parse(color) ?? .black)
                context.fill(CGRect(x: origin.x, y: origin.y, width: size.x, height: size.y))
            case .text(let origin, let text, let color):
                guard origin.isFinite else { continue }
                draw(text, at: origin, color: Color.parse(color) ?? .black, in: context)
            }
        }
    }

    private static func draw(_ text: String, at origin: Point, color: CGColor, in context: CGContext) {
        let attributes: [CFString: Any] = [kCTFontAttributeName: font, kCTForegroundColorFromContextAttributeName: true]
        let line = CTLineCreateWithAttributedString(
            CFAttributedStringCreate(nil, text as CFString, attributes as CFDictionary))
        context.setFillColor(color)
        context.textMatrix = CGAffineTransform(scaleX: 1, y: -1)
        context.textPosition = CGPoint(x: origin.x, y: origin.y + CTFontGetAscent(font))
        CTLineDraw(line, context)
    }
}

extension Point {
    fileprivate var cg: CGPoint { CGPoint(x: x, y: y) }
    fileprivate var isFinite: Bool { x.isFinite && y.isFinite }
}

extension CGColor {
    fileprivate static let black = CGColor(srgbRed: 0, green: 0, blue: 0, alpha: 1)
}
