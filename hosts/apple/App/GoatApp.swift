import GoatKit
import SwiftUI

struct GoatApp: App {
    var body: some Scene {
        DocumentGroup(newDocument: GoatDocument()) { file in
            EditorScreen(document: file.$document)
        }
    }
}

#if DEBUG
/// The UI tests launch with this argument to land in the editor on the starter
/// program, skipping the document browser (whose Create Document flow is
/// unreliable in the simulator; see README).
let uiSmokeArgument = "-goat-ui-smoke"

struct SmokeApp: App {
    @State private var document = GoatDocument()

    var body: some Scene {
        WindowGroup {
            NavigationStack {
                EditorScreen(document: $document)
            }
        }
    }
}
#endif

@main
enum Entry {
    static func main() {
        #if DEBUG
        if CommandLine.arguments.contains(uiSmokeArgument) {
            return SmokeApp.main()
        }
        #endif
        GoatApp.main()
    }
}
