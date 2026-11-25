import Foundation

/// What an exported player runs: `Contents/Resources/program.goat` in its own bundle.
public enum PlayerProgram {
    public enum Failure: Error, Equatable {
        case missing, unreadable

        public var message: String {
            switch self {
            case .missing: "This app has no program to run."
            case .unreadable: "This app's program could not be read."
            }
        }
    }

    public static func load(from bundle: Bundle = .main) -> Result<String, Failure> {
        guard let url = bundle.url(forResource: "program", withExtension: "goat") else {
            return .failure(.missing)
        }
        guard let data = try? Data(contentsOf: url), let text = try? GoatDocument.decode(data)
        else { return .failure(.unreadable) }
        return .success(text)
    }

    /// The window title: the app's name.
    public static func appName(in bundle: Bundle = .main) -> String {
        for key in ["CFBundleDisplayName", "CFBundleName"] {
            if let name = bundle.object(forInfoDictionaryKey: key) as? String, !name.isEmpty {
                return name
            }
        }
        return "goat"
    }
}
