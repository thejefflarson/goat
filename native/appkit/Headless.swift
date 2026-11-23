import Foundation
import ImageIO

/// `--headless FRAMES [--key NAME]... [--png FILE]` runs the program with no window: it
/// sends each key once after the first picture, waits for `FRAMES` more
/// pictures, prints the last one a shape to a line (and writes it to `FILE` as a PNG) and exits zero. A program
/// that traps or gets stuck prints its message to stderr and exits one. This is
/// what the tests drive, since a window needs a display.
enum Headless {
    struct Options {
        var frames: Int
        var keys: [String]
        var png: String?
    }

    static func options(_ arguments: [String]) -> Options? {
        guard let at = arguments.firstIndex(of: "--headless"), at + 1 < arguments.count,
            let frames = Int(arguments[at + 1])
        else { return nil }
        var keys: [String] = []
        var png: String?
        var rest = arguments[(at + 2)...].makeIterator()
        while let argument = rest.next() {
            if argument == "--key", let key = rest.next() { keys.append(key) }
            if argument == "--png" { png = rest.next() }
        }
        return Options(frames: frames, keys: keys, png: png)
    }

    static func run(_ options: Options) -> Never {
        let link = Link()
        let queue = DispatchQueue(label: "goat.headless")
        var seen = 0
        var keysSent = false
        var target = options.frames
        link.onPicture = { shapes in
            queue.sync {
                seen += 1
                if !keysSent {
                    keysSent = true
                    for key in options.keys {
                        link.key(key, down: true)
                        link.key(key, down: false)
                    }
                    target = seen + options.frames
                }
                if seen >= target {
                    print(describe(shapes), terminator: "")
                    if let png = options.png, !writePNG(shapes, to: png) {
                        FileHandle.standardError.write(Data("goat: cannot write \(png)\n".utf8))
                        exit(1)
                    }
                    exit(0)
                }
            }
        }
        link.onBadFrame = { message in
            FileHandle.standardError.write(Data("goat: \(message)\n".utf8))
            exit(1)
        }
        link.onStopped = { message, _ in
            FileHandle.standardError.write(Data("goat: \(message)\n".utf8))
            exit(1)
        }
        link.start()
        DispatchQueue.main.asyncAfter(deadline: .now() + 30) {
            FileHandle.standardError.write(Data("goat: no picture in 30 seconds\n".utf8))
            exit(2)
        }
        dispatchMain()
    }

    /// The picture as the window shows it, white background and all.
    static func writePNG(_ shapes: [Shape], to path: String) -> Bool {
        let (width, height) = (Int(Painter.size.width), Int(Painter.size.height))
        guard
            let context = CGContext(
                data: nil, width: width, height: height, bitsPerComponent: 8, bytesPerRow: 0,
                space: CGColorSpace(name: CGColorSpace.sRGB)!, bitmapInfo: CGImageAlphaInfo.premultipliedLast.rawValue)
        else { return false }
        context.translateBy(x: 0, y: Painter.size.height)
        context.scaleBy(x: 1, y: -1)
        context.setFillColor(.white)
        context.fill(CGRect(origin: .zero, size: Painter.size))
        Painter.paint(shapes, in: context)
        guard let image = context.makeImage(),
            let target = CGImageDestinationCreateWithURL(URL(fileURLWithPath: path) as CFURL, "public.png" as CFString, 1, nil)
        else { return false }
        CGImageDestinationAddImage(target, image, nil)
        return CGImageDestinationFinalize(target)
    }

    static func describe(_ shapes: [Shape]) -> String {
        func number(_ x: Double) -> String { String(format: "%.1f", x) }
        return shapes.map { shape in
            switch shape {
            case .line(let a, let b, let color):
                "line \(number(a.x)) \(number(a.y)) \(number(b.x)) \(number(b.y)) \(color)\n"
            case .polyline(let points, let color):
                "polyline \(points.count) \(color)\n"
            case .circle(let c, let r, let color):
                "circle \(number(c.x)) \(number(c.y)) \(number(r)) \(color)\n"
            case .rect(let o, let s, let color):
                "rect \(number(o.x)) \(number(o.y)) \(number(s.x)) \(number(s.y)) \(color)\n"
            case .text(let o, let text, let color):
                "text \(number(o.x)) \(number(o.y)) \(text) \(color)\n"
            }
        }.joined()
    }
}
