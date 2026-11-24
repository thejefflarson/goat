import SwiftUI

@main
struct PulleyBenchApp: App {
    var body: some Scene {
        WindowGroup { ContentView() }
    }
}

struct ContentView: View {
    @State private var report = "Tap Run."

    var body: some View {
        VStack(spacing: 16) {
            Button("Run the Pulley bench") { run() }
            ScrollView { Text(report).font(.system(.caption, design: .monospaced)) }
        }
        .padding()
    }

    private func run() {
        // The bench sets GOAT_RUNTIME, so it runs on the main thread. iOS has
        // no JIT, so only the Pulley lane can run on a device.
        report = bench()
    }

    private func bench() -> String {
        var buffer = [UInt8](repeating: 0, count: 4096)
        let n = goat_pulley_bench(true, &buffer, buffer.count)
        return String(decoding: buffer[..<n], as: UTF8.self)
    }
}
