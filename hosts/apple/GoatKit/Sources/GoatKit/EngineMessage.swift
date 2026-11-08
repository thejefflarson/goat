import Foundation

/// Which budget applies to the call into goat that a `beat` brackets: one frame's
/// `setup`/`update`/`draw`, or a whole run-once program.
public enum BeatCall: String, Decodable, Sendable {
    case frame, once
}

/// What the web view's engine (web/embed.ts) reports to the native side.
public enum EngineMessage: Equatable, Sendable {
    public enum State: String, Decodable, Sendable {
        case running, finished, failed
    }

    case ready
    case diagnostics([Diagnostic])
    case output([String])
    case state(State, message: String?)
    /// Odd `count` means goat was entered, even means it was left (web/beat.ts).
    case beat(count: Int, call: BeatCall)

    /// The page is not trusted to be well-formed, so anything oversized or
    /// unrecognized decodes to nil.
    public static let maxBodyBytes = 4 * 1024 * 1024

    public static func decode(_ body: Any) -> EngineMessage? {
        guard let json = body as? String, json.utf8.count <= maxBodyBytes else { return nil }
        return try? JSONDecoder().decode(EngineMessage.self, from: Data(json.utf8))
    }
}

extension EngineMessage: Decodable {
    private enum Keys: String, CodingKey {
        case type, diagnostics, lines, state, message, count, call
    }

    public init(from decoder: Decoder) throws {
        let values = try decoder.container(keyedBy: Keys.self)
        switch try values.decode(String.self, forKey: .type) {
        case "ready":
            self = .ready
        case "diagnostics":
            self = .diagnostics(try values.decode([Diagnostic].self, forKey: .diagnostics))
        case "output":
            self = .output(try values.decode([String].self, forKey: .lines))
        case "state":
            self = .state(
                try values.decode(State.self, forKey: .state),
                message: try values.decodeIfPresent(String.self, forKey: .message))
        case "beat":
            self = .beat(
                count: try values.decode(Int.self, forKey: .count),
                call: try values.decode(BeatCall.self, forKey: .call))
        case let other:
            throw DecodingError.dataCorruptedError(
                forKey: .type, in: values, debugDescription: "unknown message type \(other)")
        }
    }
}
