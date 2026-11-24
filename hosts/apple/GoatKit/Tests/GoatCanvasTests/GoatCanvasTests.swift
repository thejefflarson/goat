import CoreGraphics
import XCTest

import GoatCanvas

final class GoatCanvasTests: XCTestCase {
    func testAnEmptyFrameIsABlankPicture() throws {
        XCTAssertEqual(try Frame.decode([]), [])
    }

    func testAnUnsupportedVersionIsAnError() {
        XCTAssertThrowsError(try Frame.decode([Frame.version + 1, 0]))
    }

    func testColorsParseNamesAndHexCodes() {
        XCTAssertEqual(Color.parse("red")?.components, [1, 0, 0, 1])
        XCTAssertEqual(Color.parse("#00f")?.components, [0, 0, 1, 1])
        XCTAssertNil(Color.parse("not-a-color"))
    }

    func testThePainterFillsACircleOnItsCanvas() throws {
        let (width, height) = (Int(Painter.size.width), Int(Painter.size.height))
        let context = try XCTUnwrap(
            CGContext(
                data: nil, width: width, height: height, bitsPerComponent: 8, bytesPerRow: 0,
                space: CGColorSpace(name: CGColorSpace.sRGB)!,
                bitmapInfo: CGImageAlphaInfo.premultipliedLast.rawValue))
        context.translateBy(x: 0, y: Painter.size.height)
        context.scaleBy(x: 1, y: -1)
        Painter.paint([.circle(Point(x: 10, y: 10), radius: 5, color: "red")], in: context)
        let pixels = try XCTUnwrap(context.data).assumingMemoryBound(to: UInt8.self)
        let at = (10 * width + 10) * 4
        XCTAssertEqual([pixels[at], pixels[at + 1], pixels[at + 2], pixels[at + 3]], [255, 0, 0, 255])
    }
}
