import GoatKit
import SwiftUI

@main
struct GoatApp: App {
    var body: some Scene {
        DocumentGroup(newDocument: GoatDocument()) { file in
            EditorScreen(document: file.$document)
        }
    }
}
