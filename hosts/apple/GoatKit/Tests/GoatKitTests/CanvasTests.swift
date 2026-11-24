import CoreGraphics
import XCTest

import GoatCanvas

@testable import GoatKit

final class FrameSlotTests: XCTestCase {
    private let line = Shape.line(Point(x: 0, y: 0), Point(x: 1, y: 1), color: "red")
    private let circle = Shape.circle(Point(x: 5, y: 5), radius: 2, color: "blue")

    @MainActor
    func testTheLatestPictureWinsAndSeveralPutsWakeTheViewOnce() async {
        let slot = FrameSlot()
        var wakes = 0
        slot.onUndrawn { wakes += 1 }

        slot.put([line])
        slot.put([circle])
        slot.put([line, circle])
        try? await Task.sleep(for: .milliseconds(50))
        XCTAssertEqual(wakes, 1)
        XCTAssertEqual(slot.take(), [line, circle])

        slot.put([circle])
        try? await Task.sleep(for: .milliseconds(50))
        XCTAssertEqual(wakes, 2)
        XCTAssertEqual(slot.current, [circle])
    }
}

final class CanvasLayoutTests: XCTestCase {
    func testTheCanvasIsCenteredAtItsOwnProportions() {
        let (origin, scale) = CanvasLayout.fit(CGSize(width: 800, height: 900))
        XCTAssertEqual(scale, 2)
        XCTAssertEqual(origin, CGPoint(x: 0, y: 150))
    }

    func testViewPointsMapBackToCanvasUnits() {
        let size = CGSize(width: 800, height: 900)
        XCTAssertEqual(CanvasLayout.canvasPoint(CGPoint(x: 400, y: 450), in: size), CGPoint(x: 200, y: 150))
        XCTAssertEqual(CanvasLayout.canvasPoint(CGPoint(x: 0, y: 150), in: size), .zero)
    }

    func testTheMarginAroundThePageTakesTheGivenColor() throws {
        let size = CGSize(width: 800, height: 900)
        let context = try XCTUnwrap(
            CGContext(
                data: nil, width: 800, height: 900, bitsPerComponent: 8, bytesPerRow: 0,
                space: CGColorSpaceCreateDeviceRGB(), bitmapInfo: CGImageAlphaInfo.premultipliedLast.rawValue))
        CanvasLayout.draw([], in: context, bounds: size, margin: CGColor(gray: 0, alpha: 1))
        let data = try XCTUnwrap(context.data).assumingMemoryBound(to: UInt8.self)
        let stride = context.bytesPerRow
        XCTAssertEqual(data[0], 0)
        XCTAssertEqual(data[450 * stride + 400 * 4], 255)
    }

    func testAnEmptyViewMapsEverythingToTheOrigin() {
        XCTAssertEqual(CanvasLayout.canvasPoint(CGPoint(x: 5, y: 5), in: .zero), .zero)
    }
}

final class KeyNameTests: XCTestCase {
    func testNamesKeysAsKeyboardEventDoes() {
        XCTAssertEqual(KeyName.name(typed: "a"), "a")
        XCTAssertEqual(KeyName.name(typed: " "), " ")
        XCTAssertEqual(KeyName.name(typed: "\u{F700}"), "ArrowUp")
        XCTAssertEqual(KeyName.name(typed: "\u{F703}"), "ArrowRight")
        XCTAssertEqual(KeyName.name(typed: "\r"), "Enter")
        XCTAssertEqual(KeyName.name(typed: "\u{1B}"), "Escape")
    }

    func testKeysThatTypeNothingHaveNoName() {
        XCTAssertNil(KeyName.name(typed: ""))
        XCTAssertNil(KeyName.name(typed: "\u{F704}"))
    }
}
