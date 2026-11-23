import CoreGraphics
import Foundation

// Tests for the frame decoder, colors and painter. They compile with
// Color.swift, Frame.swift and Painter.swift alone (native/tests/appkit.rs runs
// them), so there is no XCTest: each check records a failure and the exit code
// says whether any happened.

var failures = 0

func check(_ ok: Bool, _ what: @autoclosure () -> String, line: Int = #line) {
    if !ok {
        failures += 1
        FileHandle.standardError.write(Data("FAIL line \(line): \(what())\n".utf8))
    }
}

func decodeError(_ bytes: [UInt8]) -> String? {
    do {
        _ = try Frame.decode(bytes)
        return nil
    } catch {
        return "\(error)"
    }
}

func le(_ x: Double) -> [UInt8] { (0..<8).map { UInt8(truncatingIfNeeded: x.bitPattern >> (8 * UInt64($0))) } }
func le32(_ x: UInt32) -> [UInt8] { (0..<4).map { UInt8(truncatingIfNeeded: x >> (8 * UInt32($0))) } }

/// A frame declaring `calls` (name, wire letters) and holding `records`.
func frame(_ calls: [(String, String)], _ records: [[UInt8]], version: UInt8 = 1) -> [UInt8] {
    var out: [UInt8] = [version, UInt8(calls.count)]
    for (name, wires) in calls {
        out += [UInt8(name.utf8.count)] + Array(name.utf8) + [UInt8(wires.utf8.count)] + Array(wires.utf8)
    }
    return out + records.flatMap { $0 }
}

func string(_ text: String) -> [UInt8] { le32(UInt32(text.utf8.count)) + Array(text.utf8) }

let circle = ("circle", "fffs")
let circleRecord: [UInt8] = [0] + le(10) + le(20) + le(5) + string("red")

// A frame replays the calls it declares.
let whole = frame([circle], [circleRecord])
check(
    (try? Frame.decode(whole)) == [.circle(Point(x: 10, y: 20), radius: 5, color: "red")],
    "a circle frame decodes")
check((try? Frame.decode([])) == [], "an empty frame is a blank picture")

// A truncated frame is rejected whatever the cut: only the header alone and the
// whole frame are whole.
let headerOnly = frame([circle], []).count
for length in 0..<whole.count {
    let cut = Array(whole[..<length])
    let decodes = decodeError(cut) == nil || length == 0
    check(decodes == (length == headerOnly || length == 0), "a frame cut at \(length) decodes: \(decodes)")
}

// A string longer than the frame is rejected, without allocating it.
var huge = whole
huge.replaceSubrange((whole.count - 7)..<(whole.count - 3), with: le32(UInt32.max))
check(decodeError(huge) != nil, "a string longer than the frame is rejected")

check(
    decodeError(frame([circle], [[9] + circleRecord.dropFirst()]))?.contains("did not declare") == true,
    "an undeclared call is rejected")
check(
    decodeError(frame([("circle", "ff?s")], []))?.contains("unknown value type") == true,
    "an unknown wire is rejected")
check(decodeError(frame([circle], [circleRecord], version: 2))?.contains("version 2") == true, "a wrong version is rejected")

var badName = whole
badName[3] = 0xFF
check(decodeError(badName)?.contains("not text") == true, "a call name that is not text is rejected")
check(decodeError([1, 200]) != nil, "a header with more calls than bytes is rejected")
check(
    decodeError([UInt8](repeating: 0, count: Frame.limit + 1))?.contains("too big") == true,
    "a frame past the limit is rejected")

// What a frame may ask for is checked.
check(
    decodeError(frame([("circle", "fffs")], [[0] + le(1) + le(1) + le(1) + string("red\"><script>")]))?.contains("color wants") == true,
    "a color that is not a name or a code is rejected")
check(
    decodeError(frame([("circle", "ff")], [[0] + le(1) + le(1)]))?.contains("bad call to scene.circle") == true,
    "a call of the wrong shape is rejected")
check(
    decodeError(frame([("system", "s")], [[0] + string("rm")]))?.contains("bad call to scene.system") == true,
    "an unknown scene call is rejected")

// A polyline gathers its vertices.
let poly = frame(
    [("polyline_begin", "s"), ("vertex", "ff"), ("polyline_end", "")],
    [[0] + string("blue"), [1] + le(0) + le(0), [1] + le(5) + le(5), [2]])
check(
    (try? Frame.decode(poly)) == [.polyline([Point(x: 0, y: 0), Point(x: 5, y: 5)], color: "blue")],
    "a polyline decodes")
check(decodeError(frame([("vertex", "ff")], [[0] + le(0) + le(0)])) != nil, "a vertex outside a polyline is rejected")

// Colors.
func rgba(_ name: String) -> [Double]? {
    Color.parse(name)?.components?.map { Double($0) }
}
check(rgba("#f00") == [1, 0, 0, 1], "#f00 is red")
check(rgba("tomato")?.map { ($0 * 255).rounded() } == [255, 99, 71, 1 * 255], "tomato")
check(rgba("#ff000080")?.last.map { abs($0 - 128.0 / 255) < 1e-9 } == true, "#rrggbbaa carries alpha")
check(rgba("RED") == [1, 0, 0, 1], "names ignore case")
check(rgba("notacolor") == nil, "an unknown name is no color")
check(rgba("#12") == nil, "a code of two digits is no color")

// The painter: pixels in a y-down 400 by 300 bitmap.
func pixels(_ shapes: [Shape]) -> (Int, Int) -> [UInt8] {
    let width = 400
    let height = 300
    var data = [UInt8](repeating: 0, count: width * height * 4)
    data.withUnsafeMutableBytes { raw in
        let context = CGContext(
            data: raw.baseAddress, width: width, height: height, bitsPerComponent: 8, bytesPerRow: width * 4,
            space: CGColorSpace(name: CGColorSpace.sRGB)!, bitmapInfo: CGImageAlphaInfo.premultipliedLast.rawValue)!
        context.translateBy(x: 0, y: 300)
        context.scaleBy(x: 1, y: -1)
        context.setFillColor(CGColor(srgbRed: 1, green: 1, blue: 1, alpha: 1))
        context.fill(CGRect(x: 0, y: 0, width: 400, height: 300))
        Painter.paint(shapes, in: context)
    }
    return { x, y in Array(data[(y * width + x) * 4..<(y * width + x) * 4 + 3]) }
}

let drawn = pixels([
    .circle(Point(x: 100, y: 50), radius: 20, color: "tomato"),
    .rect(origin: Point(x: 200, y: 200), size: Point(x: 50, y: 20), color: "navy"),
    .line(Point(x: 0, y: 150), Point(x: 399, y: 150), color: "#00ff00"),
    .text(Point(x: 10, y: 250), "hello", color: "black"),
    .circle(Point(x: .nan, y: 0), radius: 5, color: "red"),
    .rect(origin: Point(x: 300, y: 10), size: Point(x: .infinity, y: 10), color: "red"),
])
check(drawn(100, 50) == [255, 99, 71], "a circle is filled at its center, with y down: \(drawn(100, 50))")
check(drawn(100, 100) == [255, 255, 255], "the picture is white elsewhere")
check(drawn(225, 210) == [0, 0, 128], "a rect is filled from its top left corner: \(drawn(225, 210))")
check(drawn(225, 230) == [255, 255, 255], "a rect stops at its height")
check(drawn(50, 150)[1] > 200 && drawn(50, 150)[0] < 200, "a line is stroked: \(drawn(50, 150))")
check(drawn(350, 15) == [255, 255, 255], "a rect with a non-finite size draws nothing")
var inked = false
for y in 245..<275 { for x in 10..<60 where drawn(x, y) != [255, 255, 255] { inked = true } }
check(inked, "text draws below its top left corner")
var above = false
for y in 235..<248 { for x in 10..<60 where drawn(x, y) != [255, 255, 255] { above = true } }
check(!above, "text does not draw above its top")

if failures > 0 {
    FileHandle.standardError.write(Data("\(failures) failed\n".utf8))
    exit(1)
}
print("ok")
