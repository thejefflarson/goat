#if os(macOS)
import AppKit
import SwiftUI
import UniformTypeIdentifiers

/// What the front editor window offers the File menu: whether its program can be
/// exported now, and the two exports.
public struct ExportMenu {
    public var canExport: Bool
    public var exportApp: () -> Void
    public var exportNativeApp: () -> Void
}

private struct ExportMenuKey: FocusedValueKey {
    typealias Value = ExportMenu
}

extension FocusedValues {
    var exportMenu: ExportMenu? {
        get { self[ExportMenuKey.self] }
        set { self[ExportMenuKey.self] = newValue }
    }
}

/// File > Export App… (and Export Native App… when the Command Line Tools are installed).
public struct ExportCommands: Commands {
    @FocusedValue(\.exportMenu) private var menu

    public init() {}

    public var body: some Commands {
        CommandGroup(after: .saveItem) {
            Button("Export App…") { menu?.exportApp() }
                .disabled(menu?.canExport != true)
            if NativeExport.toolsInstalled() {
                Button("Export Native App…") { menu?.exportNativeApp() }
                    .disabled(menu?.canExport != true)
            }
        }
    }
}

@MainActor
enum ExportFlow {
    static func exportPlayer(name: String, program: String) {
        guard let template = PlayerExport.templateURL() else {
            return show(ExportError.missingPlayer)
        }
        let panel = NSSavePanel()
        panel.allowedContentTypes = [.applicationBundle]
        panel.nameFieldStringValue = name + ".app"
        panel.message = "Save your program as an app that runs without goat."
        guard panel.runModal() == .OK, let destination = panel.url else { return }
        // The scope must stay open until codesign, a child of this process, exits.
        let scoped = destination.startAccessingSecurityScopedResource()
        defer { if scoped { destination.stopAccessingSecurityScopedResource() } }
        do {
            try PlayerExport.export(program: program, template: template, to: destination)
            NSWorkspace.shared.activateFileViewerSelecting([destination])
        } catch {
            show(error)
        }
    }

    static func exportNative(name: String) {
        let alert = NSAlert()
        alert.messageText = "Export Native App"
        alert.informativeText = NativeExport.explanation(name: name)
        alert.runModal()
    }

    private static func show(_ error: Error) {
        let alert = NSAlert()
        alert.messageText = "The app could not be exported"
        alert.informativeText = error.localizedDescription
        alert.alertStyle = .warning
        alert.runModal()
    }
}
#endif
