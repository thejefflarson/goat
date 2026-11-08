// swift-tools-version: 5.9
import PackageDescription

let package = Package(
    name: "GoatKit",
    platforms: [.macOS(.v13), .iOS(.v16)],
    products: [.library(name: "GoatKit", targets: ["GoatKit"])],
    targets: [
        .target(name: "GoatKit"),
        .testTarget(name: "GoatKitTests", dependencies: ["GoatKit"]),
    ]
)
