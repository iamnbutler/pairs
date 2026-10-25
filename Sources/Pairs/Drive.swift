import CairnFrame
import CairnHost
import CairnRender
import Foundation
import ImageIO
import UniformTypeIdentifiers

/// Drives the app headlessly through Cairn's `Engine` and the real host world (files, http,
/// images, timers), as a person would: clicks at controls' centres, typing, menu choices. The
/// selftest, the URL tests, the offscreen shots and the bench use it. It reads only the frame
/// (controls, texts, image draws), never the Lean state.
final class Driver {
    let engine: Engine
    let name: String
    private lazy var renderer = try! Renderer()

    init(_ name: String, size: Size, core: @escaping () -> AppCore) {
        self.name = name
        engine = Engine(size: size, scalePercent: 200, makeCore: core)
        engine.start()
        guard engine.wait(through: 0) != nil else { fail("no first frame") }
    }

    func fail(_ message: String) -> Never {
        FileHandle.standardError.write(Data("\(name): FAIL: \(message)\n".utf8))
        exit(1)
    }

    var frame: Frame { engine.latest!.frame }
    var texts: [String] { frame.ax.map(\.label) }

    func node(_ ref: ControlRef, in f: Frame? = nil) -> AxNode? { (f ?? frame).ax.first { $0.control == ref } }
    func card(_ k: Int, in f: Frame? = nil) -> AxNode? { node(ControlRef(claim: 2, key: UInt32(k)), in: f) }
    func cardCount(_ f: Frame? = nil) -> Int { (f ?? frame).ax.filter { $0.control?.claim == 2 }.count }
    func has(_ prefix: String) -> Bool { texts.contains { $0.hasPrefix(prefix) } }

    /// Polls the latest frame until `ok` holds, for up to `seconds`; fails with `what` if not.
    @discardableResult
    func until(_ seconds: Double, _ what: String, _ ok: (Frame) -> Bool) -> Frame {
        let end = Date().addingTimeInterval(seconds)
        while Date() < end {
            if let p = engine.latest, ok(p.frame) { return p.frame }
            Thread.sleep(forTimeInterval: 0.02)
        }
        fail("\(what) (after \(seconds) s; texts: \(texts))")
    }

    func click(_ n: AxNode) {
        let p = Point(x: n.rect.x + n.rect.w / 2, y: n.rect.y + n.rect.h / 2)
        engine.send([.pointerMove(p), .pointerDown(p, .primary, clicks: 1, Mods()), .pointerUp(p, .primary, Mods())])
    }

    func press(_ ref: ControlRef) {
        guard let n = node(ref) else { fail("no control \(ref.label)") }
        click(n)
    }

    /// Types `text` into the pack field and presses Enter.
    func open(_ text: String) {
        guard let field = node(ControlRef(claim: 4)) else { fail("no pack field (^4)") }
        click(field)
        engine.send([.selectAll, .insertText(text), .key(.enter, Mods())])
    }

    /// Chooses an item of the menu bar item's menu (place 6).
    func menu(_ ref: ControlRef) {
        engine.send([.menuOpen(place: 6), .menuSelect(place: 6, ref), .menuClose(place: 6)])
    }

    /// The image drawn inside `rect`, if any.
    func image(in rect: Rect, _ f: Frame? = nil) -> String? {
        for d in (f ?? frame).draws {
            if case let .image(r, _, source) = d,
               r.x >= rect.x, r.y >= rect.y, r.x + r.w <= rect.x + rect.w, r.y + r.h <= rect.y + rect.h {
                return source
            }
        }
        return nil
    }

    /// Wins the game on the board, playing as someone with a perfect memory: turn unknown cards,
    /// remember their faces (the image each shows), and turn a pair as soon as both are known.
    /// Returns the number of cards turned.
    @discardableResult
    func win(timeout: Double = 30) -> Int {
        let start = frame
        let n = cardCount(start)
        let rects = (0..<n).map { k -> Rect in
            guard let c = card(k, in: start) else { fail("card \(k) isn't face down at the start") }
            return c.rect
        }
        var known: [Int: String] = [:]
        var done: Set<Int> = []
        var turned = 0
        func turn(_ k: Int) -> String {
            guard let c = card(k) else { fail("card \(k) can't be turned") }
            click(c)
            turned += 1
            let f = until(5, "card \(k)'s image didn't show") { image(in: rects[k], $0) != nil || won($0) }
            let src = image(in: rects[k], f) ?? ""
            known[k] = src
            return src
        }
        let end = Date().addingTimeInterval(timeout)
        while done.count < n && !won(frame) {
            if Date() > end { fail("didn't win in \(timeout) s") }
            let open = known.filter { !done.contains($0.key) }
            if let (a, b) = pairIn(open) {
                _ = turn(a); _ = turn(b); done.formUnion([a, b]); continue
            }
            guard let u = (0..<n).first(where: { known[$0] == nil }) else { fail("no unknown card left") }
            let su = turn(u)
            if let m = open.first(where: { $0.value == su })?.key {
                _ = turn(m); done.formUnion([u, m]); continue
            }
            guard let v = (0..<n).first(where: { known[$0] == nil }) else { fail("no unknown card left") }
            if turn(v) == su { done.formUnion([u, v]) }
        }
        return turned
    }

    func won(_ f: Frame) -> Bool { f.ax.contains { $0.label == "You won!" } }

    private func pairIn(_ open: [Int: String]) -> (Int, Int)? {
        var seen: [String: Int] = [:]
        for k in open.keys.sorted() {
            if let j = seen[open[k]!] { return (j, k) }
            seen[open[k]!] = k
        }
        return nil
    }

    /// The latest frame, rendered offscreen at 2×, as a PNG.
    func shot(_ url: URL) {
        guard let img = try? renderer.image(frame, scale: 2) else { fail("couldn't render \(url.lastPathComponent)") }
        let d = CGImageDestinationCreateWithURL(url as CFURL, UTType.png.identifier as CFString, 1, nil)!
        CGImageDestinationAddImage(d, img.cgImage(), nil)
        guard CGImageDestinationFinalize(d) else { fail("couldn't write \(url.path)") }
    }

    func resize(_ s: Size) { engine.send([.resize(s)]) }

    func stop() { engine.stop() }
}
