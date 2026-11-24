import Foundation

/// What running a program again did to the one already live: the model was kept,
/// or the program started over for `reason` (ADR 0035).
public struct Reload: Equatable, Sendable {
    public struct Reason: Decodable, Equatable, Sendable {
        public let kind: String
        public let args: [String]
    }

    /// Nil when the model was kept.
    public let reason: Reason?

    public var keptModel: Bool { reason == nil }

    public var summary: String {
        guard let reason else { return "Reloaded: your program's data was kept." }
        return "Reloaded: your program started over because \(reason.explanation)."
    }
}

extension Reload.Reason {
    var explanation: String {
        switch (kind, args.count) {
        case ("field_added", 1): "the field \(args[0]) is new"
        case ("type_changed", 3): "\(args[0]) changed from \(args[1]) to \(args[2])"
        case ("method_lost", 1): "the method \(args[0]) is gone"
        case ("method_added", 1): "the method \(args[0]) is new"
        case ("reshaped", _): "its data changed shape"
        default: ([kind] + args).joined(separator: " ")
        }
    }
}

/// What the native engine (hosts/apple/engine, goat_engine.h) reports to the app.
public enum EngineMessage: Equatable, Sendable {
    public enum State: String, Decodable, Sendable {
        case running, finished, failed
    }

    case ready
    case diagnostics([Diagnostic])
    case output([String])
    case state(State, message: String?)
    case reloaded(Reload)

    /// Anything oversized or unrecognized decodes to nil.
    public static let maxBodyBytes = 4 * 1024 * 1024

    public static func decode(_ body: Any) -> EngineMessage? {
        guard let json = body as? String, json.utf8.count <= maxBodyBytes else { return nil }
        return try? JSONDecoder().decode(EngineMessage.self, from: Data(json.utf8))
    }
}

extension EngineMessage: Decodable {
    private enum Keys: String, CodingKey {
        case type, diagnostics, lines, state, message, outcome, reason
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
        case "reloaded":
            switch try values.decode(String.self, forKey: .outcome) {
            case "kept":
                self = .reloaded(Reload(reason: nil))
            case "reset":
                let reason = try values.decodeIfPresent(Reload.Reason.self, forKey: .reason)
                self = .reloaded(Reload(reason: reason ?? Reload.Reason(kind: "its code changed", args: [])))
            case let other:
                throw DecodingError.dataCorruptedError(
                    forKey: .outcome, in: values, debugDescription: "unknown reload outcome \(other)")
            }
        case let other:
            throw DecodingError.dataCorruptedError(
                forKey: .type, in: values, debugDescription: "unknown message type \(other)")
        }
    }
}
