// swift-tools-version: 6.0
// The app's host: Cairn's AppKit host, linking .cairn/lib/libpairs.a, which
// `cairn build` makes from the Lean code (bin/cairn-link).
import PackageDescription

let lib = Context.packageDirectory + "/.cairn/lib"

let package = Package(
    name: "pairs",
    platforms: [.macOS("27.0")],
    dependencies: [.package(url: "https://cairn.registry.nexthub.sh/git/iamnbutler/cairn.git", from: "0.2.5")],
    targets: [
        // The Lean exports Cairn's CLean doesn't declare: the app's initializer.
        .target(name: "CPairs", dependencies: [.product(name: "CLean", package: "cairn")]),
        .executableTarget(
            name: "Pairs",
            dependencies: ["CPairs",
                           .product(name: "CLean", package: "cairn"),
                           .product(name: "CairnFrame", package: "cairn"),
                           .product(name: "CairnHost", package: "cairn"),
                           .product(name: "CairnRender", package: "cairn")],
            // The bundled packs' images, drawn by tools/packs/draw.swift.
            resources: [.copy("packs")],
            linkerSettings: [.unsafeFlags(["-L" + lib, "-lpairs"])]),
    ]
)
