import CPairs
import CairnFrame
import CairnHost
import CairnRender
import ImageIO
import UniformTypeIdentifiers
import Foundation

// Pairs on Cairn's host (Cairn's docs/package.md). The host only performs effects; the game is
// Lean's (lean/Pairs).
//   Pairs               open the window
//   Pairs --selftest    run the app headlessly with the real host world (files, images, timers):
//                       turn a card, open a folder that isn't there, switch to Patterns
//   Pairs --shots <dir> render frames offscreen as PNGs (no window, no screen capture): the
//                       first board, a mismatch, Patterns while loading and loaded

let app = LeanApp(
    module: runtime_initialize_pairs_Pairs_Abi,
    initialize: { w, h, scale in cairn_app_init(w, h, scale) },
    step: { cairn_app_step($0, $1) },
    frame: { cairn_app_frame($0) },
    codec: FrameV1Codec())

let size = Size(w: 560, h: 640)

// The bundled packs' images are `packs/<id>/<face>.png`, relative to the resource bundle.
guard let resources = Bundle.module.resourcePath, FileManager.default.changeCurrentDirectoryPath(resources) else {
    FileHandle.standardError.write(Data("Pairs: no resource bundle\n".utf8))
    exit(1)
}

/// Offscreen PNGs of a few states, rendered from the frames the real host world produces.
if let i = CommandLine.arguments.firstIndex(of: "--shots"), i + 1 < CommandLine.arguments.count {
    let dir = URL(fileURLWithPath: CommandLine.arguments[i + 1], isDirectory: true)
    try? FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
    let engine = Engine(size: size, scalePercent: 200) { LeanCore(app) }
    engine.start()
    _ = engine.wait(through: 0)
    let renderer = try! Renderer()
    func shot(_ name: String, after seconds: Double = 0.6) {
        Thread.sleep(forTimeInterval: seconds)
        guard let f = engine.latest?.frame, let img = try? renderer.image(f, scale: 2) else { return }
        let url = dir.appendingPathComponent(name + ".png")
        let d = CGImageDestinationCreateWithURL(url as CFURL, UTType.png.identifier as CFString, 1, nil)!
        CGImageDestinationAddImage(d, img.cgImage(), nil)
        CGImageDestinationFinalize(d)
        print(url.path)
    }
    func press(_ ref: ControlRef) {
        guard let n = engine.latest?.frame.ax.first(where: { $0.control == ref }) else { return }
        let p = Point(x: n.rect.x + n.rect.w / 2, y: n.rect.y + n.rect.h / 2)
        engine.send([.pointerMove(p), .pointerDown(p, .primary, clicks: 1, Mods()), .pointerUp(p, .primary, Mods())])
    }
    shot("1-board", after: 1)
    press(ControlRef(claim: 2, key: 0)); press(ControlRef(claim: 2, key: 1))
    shot("2-two-up", after: 0.4)
    engine.send([.menuSelect(place: 6, ControlRef(claim: 10, key: 1))])
    shot("3-loading", after: 0.01)
    shot("4-patterns", after: 2)
    engine.stop()
    exit(0)
}

if CommandLine.arguments.contains("--selftest") {
    func fail(_ message: String) -> Never {
        FileHandle.standardError.write(Data("selftest: FAIL: \(message)\n".utf8))
        exit(1)
    }
    let engine = Engine(size: size, scalePercent: 200) { LeanCore(app) }
    engine.start()
    guard let first = engine.wait(through: 0) else { fail("no first frame") }
    func card(_ f: Frame, _ k: UInt32) -> AxNode? { f.ax.first { $0.control == ControlRef(claim: 2, key: k) } }
    func texts(_ f: Frame) -> [String] { f.ax.map(\.label) }
    /// Polls the latest frame until `ok` holds, for up to `seconds`.
    func until(_ seconds: Double, _ what: String, _ ok: (Frame) -> Bool) -> Frame {
        let end = Date().addingTimeInterval(seconds)
        while Date() < end {
            if let p = engine.latest, ok(p.frame) { return p.frame }
            Thread.sleep(forTimeInterval: 0.05)
        }
        fail("\(what) (after \(seconds) s; texts: \(engine.latest.map { texts($0.frame) } ?? []); field: \(String(describing: engine.latest?.frame.ax.first { $0.role == .textField }))")
    }
    let cards = (0..<16).filter { card(first.frame, UInt32($0)) != nil }.count
    guard cards == 16 else { fail("the first frame has \(cards) cards, not 16") }
    // Turn card 0: it stops being a control, and its image loads (no failure words).
    guard let c0 = card(first.frame, 0) else { fail("no card ^2#0") }
    let p = Point(x: c0.rect.x + c0.rect.w / 2, y: c0.rect.y + c0.rect.h / 2)
    engine.send([.pointerMove(p), .pointerDown(p, .primary, clicks: 1, Mods()), .pointerUp(p, .primary, Mods())])
    _ = until(2, "card ^2#0 is still a control after a press") { card($0, 0) == nil }
    Thread.sleep(forTimeInterval: 0.5)
    if let bad = engine.latest?.frame.ax.first(where: { ["Not found", "No access", "Not an image", "Failed"].contains($0.label) }) {
        fail("card 0's image didn't load: \(bad.label)")
    }
    // A folder that isn't there: the problem line says so, and the game goes on.
    guard let field = engine.latest?.frame.ax.first(where: { $0.control == ControlRef(claim: 4) }) else { fail("no pack field (^4)") }
    let q = Point(x: field.rect.x + field.rect.w / 2, y: field.rect.y + field.rect.h / 2)
    engine.send([.pointerMove(q), .pointerDown(q, .primary, clicks: 1, Mods()), .pointerUp(q, .primary, Mods()),
                 .insertText("/nonexistent/pairs-selftest"), .key(.enter, Mods())])
    _ = until(5, "no problem line for a missing folder") { f in texts(f).contains { $0.hasPrefix("Couldn't open") } }
    // Patterns from the menu: its images load from the bundle, and a game of it is dealt.
    engine.send([.menuOpen(place: 6), .menuSelect(place: 6, ControlRef(claim: 10, key: 1)), .menuClose(place: 6)])
    let after = until(10, "Patterns didn't load") { f in texts(f).contains("Patterns") }
    guard (0..<16).allSatisfy({ card(after, UInt32($0)) != nil }) else { fail("Patterns's board isn't 16 face-down cards") }
    engine.stop()
    print("selftest: PASS (Pairs: 16 cards, a card turned with its image, a missing folder refused, Patterns loaded)")
    exit(0)
}

MainActor.assumeIsolated {
    CairnApp.main(CairnApp.Config(title: "Pairs", size: size) { LeanCore(app) })
}
