// swift-tools-version: 5.9
import PackageDescription

let package = Package(
    name: "GoatKit",
    platforms: [.macOS(.v13), .iOS(.v16)],
    products: [
        .library(name: "GoatKit", targets: ["GoatKit"]),
        .library(name: "GoatCanvas", targets: ["GoatCanvas"]),
    ],
    targets: [
        .target(name: "GoatCanvas"),
        .target(name: "GoatKit", dependencies: ["GoatCanvas"]),
        .testTarget(name: "GoatCanvasTests", dependencies: ["GoatCanvas"]),
        .testTarget(name: "GoatKitTests", dependencies: ["GoatKit", "GoatCanvas"]),
    ]
)
