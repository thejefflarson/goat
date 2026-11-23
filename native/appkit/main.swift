import Foundation

if let options = Headless.options(CommandLine.arguments) {
    Headless.run(options)
}
Window.run(title: URL(fileURLWithPath: CommandLine.arguments[0]).lastPathComponent)
