import AppKit
import GoatKit
import SwiftUI

final class QuitWhenClosed: NSObject, NSApplicationDelegate {
    func applicationShouldTerminateAfterLastWindowClosed(_ sender: NSApplication) -> Bool { true }
}

@main
struct PlayerApp: App {
    @NSApplicationDelegateAdaptor(QuitWhenClosed.self) private var delegate

    var body: some Scene {
        WindowGroup(PlayerProgram.appName()) {
            PlayerScreen(program: PlayerProgram.load())
        }
        .commands { CommandGroup(replacing: .newItem) {} }
    }
}
