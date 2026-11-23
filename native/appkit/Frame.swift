import Foundation

// A Swift port of the frame decoder in mir/src/frame.rs (ADR 0015, second
// addendum): the bytes a compiled `draw` hands the host once per frame. The
// buffer is the program's output, so every read is bounds-checked and a bad
// frame is an error, never a crash.

struct Point: Equatable {
    var x: Double
    var y: Double
}

enum Shape: Equatable {
    case line(Point, Point, color: String)
    case polyline([Point], color: String)
    case circle(Point, radius: Double, color: String)
    case rect(origin: Point, size: Point, color: String)
    case text(Point, String, color: String)
}

struct FrameError: Error, Equatable, CustomStringConvertible {
    let description: String
    init(_ description: String) { self.description = description }
}

enum Frame {
    static let version: UInt8 = 1

    /// The most bytes one frame may hold, as in `frame.rs`.
    static let limit = 1 << 24

    private enum Wire: UInt8 {
        case int = 0x69  // i
        case float = 0x66  // f
        case bool = 0x62  // b
        case str = 0x73  // s
    }

    fileprivate enum Value {
        case int(Int64)
        case float(Double)
        case bool(Bool)
        case str(String)
    }

    private struct Reader {
        let bytes: [UInt8]
        var at = 0

        mutating func take(_ count: Int) throws -> ArraySlice<UInt8> {
            let (end, overflow) = at.addingReportingOverflow(count)
            guard count >= 0, !overflow, end <= bytes.count else {
                throw FrameError("the frame ends in the middle of a value")
            }
            defer { at = end }
            return bytes[at..<end]
        }

        mutating func byte() throws -> UInt8 { try take(1).first! }

        mutating func word(_ width: Int) throws -> UInt64 {
            try take(width).reversed().reduce(0) { $0 << 8 | UInt64($1) }
        }
    }

    /// The shapes `bytes` draws, in order. An empty frame is a blank picture.
    static func decode(_ bytes: [UInt8]) throws -> [Shape] {
        guard bytes.count <= limit else { throw FrameError("this picture is too big") }
        if bytes.isEmpty { return [] }
        var reader = Reader(bytes: bytes)
        let calls = try header(&reader)
        var scene = Scene()
        while reader.at < bytes.count {
            let index = Int(try reader.byte())
            guard index < calls.count else {
                throw FrameError("the frame calls a scene call it did not declare")
            }
            let (name, wires) = calls[index]
            var args: [Value] = []
            for wire in wires {
                switch wire {
                case .int: args.append(.int(Int64(bitPattern: try reader.word(8))))
                case .float: args.append(.float(Double(bitPattern: try reader.word(8))))
                case .bool: args.append(.bool(try reader.byte() != 0))
                case .str:
                    let length = Int(try reader.word(4))
                    let text = String(decoding: try reader.take(length), as: UTF8.self)
                    args.append(.str(text))
                }
            }
            try scene.call(name, args)
        }
        return scene.shapes
    }

    private static func header(_ reader: inout Reader) throws -> [(String, [Wire])] {
        let found = try reader.byte()
        guard found == version else {
            throw FrameError("the frame is version \(found), not \(version)")
        }
        var calls: [(String, [Wire])] = []
        for _ in 0..<Int(try reader.byte()) {
            let nameLength = Int(try reader.byte())
            let nameBytes = try reader.take(nameLength)
            guard let name = String(bytes: nameBytes, encoding: .utf8) else {
                throw FrameError("a scene call name in the frame is not text")
            }
            let count = Int(try reader.byte())
            let wires = try reader.take(count).map { code -> Wire in
                guard let wire = Wire(rawValue: code) else {
                    throw FrameError("the frame has an unknown value type")
                }
                return wire
            }
            calls.append((name, wires))
        }
        return calls
    }

    /// Color names and `#hex` codes of at most 32 characters, as
    /// `check_color` in `mir/src/host.rs` allows.
    static func isColor(_ text: String) -> Bool {
        (1...32).contains(text.utf8.count)
            && text.utf8.allSatisfy { byte in
                [0x30...0x39, 0x41...0x5a, 0x61...0x7a, 0x23...0x23].contains { $0.contains(byte) }
            }
    }

    private struct Scene {
        var shapes: [Shape] = []
        private var open: (points: [Point], color: String)?

        mutating func call(_ name: String, _ args: [Value]) throws {
            if ["begin", "end", "frame", "span", "edit", "swatch"].contains(name) { return }
            switch (name, args) {
            case ("line", let a) where a.count == 5:
                if let x1 = a[0].float, let y1 = a[1].float, let x2 = a[2].float, let y2 = a[3].float,
                    let color = try a[4].color
                {
                    shapes.append(.line(Point(x: x1, y: y1), Point(x: x2, y: y2), color: color))
                    return
                }
            case ("polyline_begin", let a) where a.count == 1:
                if let color = try a[0].color {
                    open = ([], color)
                    return
                }
            case ("vertex", let a) where a.count == 2:
                if let x = a[0].float, let y = a[1].float, open != nil {
                    open?.points.append(Point(x: x, y: y))
                    return
                }
            case ("polyline_end", let a) where a.isEmpty:
                if let line = open {
                    shapes.append(.polyline(line.points, color: line.color))
                    open = nil
                    return
                }
            case ("circle", let a) where a.count == 4:
                if let x = a[0].float, let y = a[1].float, let r = a[2].float, let color = try a[3].color {
                    shapes.append(.circle(Point(x: x, y: y), radius: r, color: color))
                    return
                }
            case ("rect", let a) where a.count == 5:
                if let x = a[0].float, let y = a[1].float, let w = a[2].float, let h = a[3].float,
                    let color = try a[4].color
                {
                    shapes.append(.rect(origin: Point(x: x, y: y), size: Point(x: w, y: h), color: color))
                    return
                }
            case ("text", let a) where a.count == 4:
                if let x = a[0].float, let y = a[1].float, case .str(let text) = a[2], let color = try a[3].color {
                    shapes.append(.text(Point(x: x, y: y), text, color: color))
                    return
                }
            default:
                break
            }
            throw FrameError("bad call to scene.\(name)")
        }
    }
}

fileprivate extension Frame.Value {
    var float: Double? {
        if case .float(let x) = self { return x }
        return nil
    }

    var color: String? {
        get throws {
            guard case .str(let text) = self else { return nil }
            guard Frame.isColor(text) else {
                throw FrameError("color wants a name like \"red\" or a code like \"#ff8800\", not \"\(text)\"")
            }
            return text
        }
    }
}
