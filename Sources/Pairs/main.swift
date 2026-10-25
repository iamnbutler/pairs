import CPairs
import CairnFrame
import CairnHost
import Foundation

// Pairs on Cairn's host (Cairn's docs/package.md). The host only performs effects; the game is
// Lean's (lean/Pairs). The modes besides the window drive the app headlessly (Drive.swift):
//   Pairs                    open the window
//   Pairs --selftest         turn a card, refuse a missing folder, switch to Patterns, win a game
//   Pairs --urltest <base>   open packs from the stub server at <base> (make urltest)
//   Pairs --shots <dir>      render a few states offscreen as PNGs (no window, no screen capture)
//   Pairs --bench            load a 100-face pack: time and memory (make bench; Bench.swift)

let app = LeanApp(
    module: runtime_initialize_pairs_Pairs_Abi,
    initialize: { w, h, scale in cairn_app_init(w, h, scale) },
    step: { cairn_app_step($0, $1) },
    frame: { cairn_app_frame($0) },
    codec: FrameV1Codec())

let size = Size(w: 560, h: 640)
let args = CommandLine.arguments

// The bundled packs' images are `packs/<id>/<face>.png`, relative to the resource bundle.
guard let resources = Bundle.module.resourcePath, FileManager.default.changeCurrentDirectoryPath(resources) else {
    FileHandle.standardError.write(Data("Pairs: no resource bundle\n".utf8))
    exit(1)
}

func argument(after flag: String) -> String? {
    guard let i = args.firstIndex(of: flag), i + 1 < args.count else { return nil }
    return args[i + 1]
}

func makeDriver(_ name: String) -> Driver { Driver(name, size: size) { LeanCore(app) } }

if args.contains("--selftest") {
    let d = makeDriver("selftest")
    guard d.cardCount() == 16 else { d.fail("the first frame has \(d.cardCount()) cards, not 16") }
    // Turn card 0: it stops being a control, and its image shows.
    d.press(ControlRef(claim: 2, key: 0))
    d.until(2, "card 0's image didn't show") { d.card(0, in: $0) == nil && !$0.imageSources.isEmpty }
    // A folder that isn't there: the problem line says so, and the game goes on.
    d.open("/nonexistent/pairs-selftest")
    d.until(5, "no problem line for a missing folder") { _ in d.has("Couldn't open") }
    // Patterns from the menu: its images load from the bundle, and a game of it is dealt.
    d.menu(ControlRef(claim: 10, key: 1))
    d.until(10, "Patterns didn't load") { f in f.ax.contains { $0.label == "Patterns" } && d.cardCount(f) == 16 }
    // Win it: the win screen, and a best score for Patterns.
    let turned = d.win()
    d.until(3, "no win screen") { _ in d.has("You won!") }
    guard !d.has("No best yet") else { d.fail("no best score after a win") }
    d.stop()
    print("selftest: PASS (16 cards, a card's image, a missing folder refused, Patterns loaded and won in \(turned) turns)")
    exit(0)
}

if let base = argument(after: "--urltest") {
    let d = makeDriver("urltest")
    let shapes = { (f: Frame) in f.ax.contains { $0.label == "Shapes" } }
    d.until(2, "doesn't start on Shapes", shapes)
    // A pack over http from the stub: the manifest, then every image, then a game of it.
    d.open("\(base)/good")
    d.until(10, "the good pack didn't load") { f in f.ax.contains { $0.label == "Numbers" } && d.cardCount(f) == 16 }
    d.press(ControlRef(claim: 2, key: 0))
    d.until(3, "a Numbers card's image didn't show") { f in f.imageSources.contains { $0.hasPrefix("\(base)/good/") } }
    print("urltest: ok good pack")
    // Failures leave the game alone and say what went wrong.
    for (path, words) in [("missing", "404"), ("badjson", "isn't valid JSON"), ("broken", "Number 7 didn't load")] {
        let before = d.frame.ax.filter { $0.control?.claim == 2 }.map(\.rect)
        d.open("\(base)/\(path)")
        d.until(15, "\(path): no problem line saying \(words)") { _ in d.texts.contains { $0.hasPrefix("Couldn't open") && $0.contains(words) } }
        guard d.frame.ax.contains(where: { $0.label == "Numbers" }),
              d.frame.ax.filter({ $0.control?.claim == 2 }).map(\.rect) == before
        else { d.fail("\(path) changed the game") }
        print("urltest: ok \(path) refused: \(d.texts.first { $0.hasPrefix("Couldn't") } ?? "")")
    }
    // Switching packs while one loads: the slow pack's images answer after 3 s; Shapes from the
    // menu cancels them, loads, and stays when the slow replies would have arrived.
    d.open("\(base)/slow")
    d.until(5, "the slow pack didn't start loading") { _ in d.has("Loading Slow") }
    guard d.node(ControlRef(claim: 5)) != nil else { d.fail("no Cancel while loading") }
    d.menu(ControlRef(claim: 10, key: 0))
    d.until(5, "Shapes didn't load while Slow was loading", shapes)
    guard !d.has("Loading Slow") else { d.fail("Slow is still loading after the switch") }
    Thread.sleep(forTimeInterval: 4)
    guard shapes(d.frame), !d.has("Loading"), !d.has("Couldn't") else { d.fail("a late Slow reply changed the game: \(d.texts)") }
    print("urltest: ok switching packs while loading")
    // Cancel: the load stops, the game goes on.
    d.open("\(base)/slow")
    d.until(5, "the slow pack didn't start loading again") { _ in d.has("Loading Slow") }
    d.press(ControlRef(claim: 5))
    d.until(2, "Cancel didn't stop the load") { _ in !d.has("Loading") }
    Thread.sleep(forTimeInterval: 4)
    guard shapes(d.frame) else { d.fail("a cancelled load changed the game") }
    print("urltest: ok cancel")
    d.stop()
    print("urltest: PASS")
    exit(0)
}

if args.contains("--bench") {
    let env = ProcessInfo.processInfo.environment
    guard let packs = env["PAIRS_BENCH_PACKS"] else {
        FileHandle.standardError.write(Data("bench: set PAIRS_BENCH_PACKS to the stub packs folder (make bench)\n".utf8))
        exit(2)
    }
    Bench.run(makeDriver("bench"), packs: packs, url: env["PAIRS_BENCH_URL"])
}

if let dir = argument(after: "--shots") {
    // PAIRS_SHOTS_URL, the stub server (make shots starts it), adds a pack loading over http and
    // one that fails.
    let out = URL(fileURLWithPath: dir, isDirectory: true)
    try? FileManager.default.createDirectory(at: out, withIntermediateDirectories: true)
    let d = makeDriver("shots")
    func shot(_ name: String) { d.shot(out.appendingPathComponent(name + ".png")); print(out.appendingPathComponent(name + ".png").path) }
    d.until(3, "doesn't start on Shapes") { $0.ax.contains { $0.label == "Shapes" } }
    Thread.sleep(forTimeInterval: 0.5)
    shot("1-board")
    // Three pairs matched, then two more cards up: usually a mismatch.
    d.win(pairs: 3)
    let down = (0..<16).filter { d.card($0) != nil }
    for k in down.prefix(2) { d.press(ControlRef(claim: 2, key: UInt32(k))) }
    Thread.sleep(forTimeInterval: 0.3)
    shot("2-mid-game")
    d.resize(Size(w: 920, h: 640))
    Thread.sleep(forTimeInterval: 0.3)
    shot("3-wide")
    d.resize(size)
    if let url = ProcessInfo.processInfo.environment["PAIRS_SHOTS_URL"] {
        d.open("\(url)/slow")
        d.until(5, "the slow pack didn't start loading") { _ in d.has("Loading Slow") }
        Thread.sleep(forTimeInterval: 0.3)
        shot("4-loading")
        d.press(ControlRef(claim: 5))
        d.open("\(url)/broken")
        d.until(15, "no problem for the broken pack") { _ in d.has("Couldn't open Broken") }
        shot("5-problem")
    }
    d.menu(ControlRef(claim: 10, key: 1))
    d.until(10, "Patterns didn't load") { f in f.ax.contains { $0.label == "Patterns" } && d.cardCount(f) == 16 }
    d.win(pairs: 5)
    Thread.sleep(forTimeInterval: 1.2)
    shot("6-patterns")
    d.win()
    d.until(3, "no win screen") { _ in d.has("You won!") }
    shot("7-won")
    d.stop()
    exit(0)
}

MainActor.assumeIsolated {
    CairnApp.main(CairnApp.Config(title: "Pairs", size: size) { LeanCore(app) })
}
