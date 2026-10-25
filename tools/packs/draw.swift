// Draws Pairs's pack images (PNG, 256 × 256 pixels).
//
//   swift tools/packs/draw.swift bundled <dir>         Shapes and Patterns: <dir>/shapes/*.png,
//                                                      <dir>/patterns/*.png (the app's bundled packs)
//   swift tools/packs/draw.swift cairns <dir>          the demo pack the cairn site serves: twelve
//                                                      cairns of stones, with its pack.json
//   swift tools/packs/draw.swift numbered <dir> <n> [name]
//                                                      a pack of n numbered faces with its pack.json
//                                                      (tests, the bench, the demo pack)
//
// The bundled faces' names must match lean/Pairs/Bundled.lean.

import CoreGraphics
import CoreText
import Foundation
import ImageIO
import UniformTypeIdentifiers

let side = 256
let S = CGFloat(side)

func rgb(_ r: Int, _ g: Int, _ b: Int) -> CGColor {
    CGColor(srgbRed: CGFloat(r) / 255, green: CGFloat(g) / 255, blue: CGFloat(b) / 255, alpha: 1)
}

func png(_ path: String, _ draw: (CGContext) -> Void) {
    let cs = CGColorSpace(name: CGColorSpace.sRGB)!
    let ctx = CGContext(data: nil, width: side, height: side, bitsPerComponent: 8, bytesPerRow: 0,
                        space: cs, bitmapInfo: CGImageAlphaInfo.premultipliedLast.rawValue)!
    ctx.setAllowsAntialiasing(true)
    ctx.setShouldAntialias(true)
    draw(ctx)
    let url = URL(fileURLWithPath: path)
    try? FileManager.default.createDirectory(at: url.deletingLastPathComponent(), withIntermediateDirectories: true)
    let dest = CGImageDestinationCreateWithURL(url as CFURL, UTType.png.identifier as CFString, 1, nil)!
    CGImageDestinationAddImage(dest, ctx.makeImage()!, nil)
    guard CGImageDestinationFinalize(dest) else { fatalError("couldn't write \(path)") }
}

func polygon(_ ctx: CGContext, _ n: Int, _ r: CGFloat, rotate: CGFloat = -.pi / 2, inner: CGFloat? = nil) {
    let c = CGPoint(x: S / 2, y: S / 2)
    let k = inner == nil ? n : 2 * n
    for i in 0..<k {
        let a = rotate + CGFloat(i) * 2 * .pi / CGFloat(k)
        let rr = (inner != nil && i % 2 == 1) ? inner! : r
        let p = CGPoint(x: c.x + rr * cos(a), y: c.y - rr * sin(a))
        if i == 0 { ctx.move(to: p) } else { ctx.addLine(to: p) }
    }
    ctx.closePath()
    ctx.fillPath()
}

// MARK: Shapes: one coloured shape on white each.

let shapes: [(String, CGColor, (CGContext) -> Void)] = [
    ("red-circle", rgb(220, 50, 47), { $0.fillEllipse(in: CGRect(x: 40, y: 40, width: 176, height: 176)) }),
    ("orange-square", rgb(240, 130, 30), { $0.fill(CGRect(x: 52, y: 52, width: 152, height: 152)) }),
    ("yellow-triangle", rgb(235, 190, 20), { polygon($0, 3, 104) }),
    ("green-diamond", rgb(60, 160, 70), { polygon($0, 4, 96, rotate: 0) }),
    ("teal-hexagon", rgb(30, 160, 160), { polygon($0, 6, 92, rotate: 0) }),
    ("blue-star", rgb(40, 100, 220), { polygon($0, 5, 104, rotate: .pi / 2, inner: 44) }),
    ("indigo-ring", rgb(80, 60, 180), { ctx in
        ctx.addEllipse(in: CGRect(x: 40, y: 40, width: 176, height: 176))
        ctx.addEllipse(in: CGRect(x: 84, y: 84, width: 88, height: 88))
        ctx.fillPath(using: .evenOdd) }),
    ("purple-cross", rgb(150, 60, 170), { ctx in
        ctx.fill(CGRect(x: 100, y: 40, width: 56, height: 176))
        ctx.fill(CGRect(x: 40, y: 100, width: 176, height: 56)) }),
    ("pink-heart", rgb(230, 90, 150), { ctx in
        ctx.fillEllipse(in: CGRect(x: 44, y: 104, width: 90, height: 90))
        ctx.fillEllipse(in: CGRect(x: 122, y: 104, width: 90, height: 90))
        ctx.move(to: CGPoint(x: 50, y: 136)); ctx.addLine(to: CGPoint(x: 206, y: 136))
        ctx.addLine(to: CGPoint(x: 128, y: 44)); ctx.closePath(); ctx.fillPath() }),
    ("brown-pentagon", rgb(140, 90, 50), { polygon($0, 5, 96) }),
    ("grey-moon", rgb(120, 125, 135), { ctx in
        ctx.fillEllipse(in: CGRect(x: 40, y: 40, width: 176, height: 176))
        ctx.setFillColor(rgb(255, 255, 255))
        ctx.fillEllipse(in: CGRect(x: 96, y: 64, width: 150, height: 150)) }),
    ("black-arrow", rgb(30, 30, 34), { ctx in
        ctx.fill(CGRect(x: 40, y: 104, width: 110, height: 48))
        ctx.move(to: CGPoint(x: 140, y: 56)); ctx.addLine(to: CGPoint(x: 220, y: 128))
        ctx.addLine(to: CGPoint(x: 140, y: 200)); ctx.closePath(); ctx.fillPath() }),
]

// MARK: Patterns: one pattern in its own colour each, over a pale ground.

func tile(_ ctx: CGContext, _ step: CGFloat, _ body: (CGFloat, CGFloat, Int, Int) -> Void) {
    var j = 0
    var y: CGFloat = 0
    while y < S + step { var i = 0; var x: CGFloat = 0
        while x < S + step { body(x, y, i, j); x += step; i += 1 }
        y += step; j += 1 }
}

let patterns: [(String, CGColor, (CGContext) -> Void)] = [
    ("stripes", rgb(220, 50, 47), { ctx in tile(ctx, 32) { x, _, i, j in if j == 0 && i % 2 == 0 { ctx.fill(CGRect(x: x, y: 0, width: 16, height: S)) } } }),
    ("dots", rgb(40, 100, 220), { ctx in tile(ctx, 32) { x, y, _, _ in ctx.fillEllipse(in: CGRect(x: x + 6, y: y + 6, width: 20, height: 20)) } }),
    ("checks", rgb(60, 160, 70), { ctx in tile(ctx, 32) { x, y, i, j in if (i + j) % 2 == 0 { ctx.fill(CGRect(x: x, y: y, width: 32, height: 32)) } } }),
    ("waves", rgb(30, 160, 160), { ctx in
        ctx.setLineWidth(9); ctx.setStrokeColor(rgb(30, 160, 160))
        for row in stride(from: CGFloat(16), to: S, by: 36) {
            ctx.move(to: CGPoint(x: 0, y: row))
            for x in stride(from: CGFloat(0), through: S, by: 4) { ctx.addLine(to: CGPoint(x: x, y: row + 10 * sin(x / 16))) }
            ctx.strokePath() } }),
    ("zigzag", rgb(240, 130, 30), { ctx in
        ctx.setLineWidth(10); ctx.setStrokeColor(rgb(240, 130, 30)); ctx.setLineJoin(.miter)
        for row in stride(from: CGFloat(20), to: S, by: 40) {
            ctx.move(to: CGPoint(x: 0, y: row))
            for (k, x) in stride(from: CGFloat(0), through: S, by: 20).enumerated() { ctx.addLine(to: CGPoint(x: x, y: row + (k % 2 == 0 ? 0 : 16))) }
            ctx.strokePath() } }),
    ("grid", rgb(80, 60, 180), { ctx in tile(ctx, 32) { x, y, _, _ in ctx.fill(CGRect(x: x, y: 0, width: 4, height: S)); ctx.fill(CGRect(x: 0, y: y, width: S, height: 4)) } }),
    ("diamonds", rgb(150, 60, 170), { ctx in tile(ctx, 40) { x, y, _, _ in
        ctx.move(to: CGPoint(x: x + 20, y: y + 4)); ctx.addLine(to: CGPoint(x: x + 36, y: y + 20))
        ctx.addLine(to: CGPoint(x: x + 20, y: y + 36)); ctx.addLine(to: CGPoint(x: x + 4, y: y + 20))
        ctx.closePath(); ctx.fillPath() } }),
    ("rings", rgb(230, 90, 150), { ctx in
        ctx.setLineWidth(8); ctx.setStrokeColor(rgb(230, 90, 150))
        for r in stride(from: CGFloat(16), to: 190, by: 24) { ctx.strokeEllipse(in: CGRect(x: S / 2 - r, y: S / 2 - r, width: 2 * r, height: 2 * r)) } }),
    ("triangles", rgb(235, 170, 20), { ctx in tile(ctx, 40) { x, y, _, _ in
        ctx.move(to: CGPoint(x: x + 4, y: y + 6)); ctx.addLine(to: CGPoint(x: x + 36, y: y + 6))
        ctx.addLine(to: CGPoint(x: x + 20, y: y + 34)); ctx.closePath(); ctx.fillPath() } }),
    ("crosses", rgb(30, 30, 34), { ctx in tile(ctx, 40) { x, y, _, _ in
        ctx.fill(CGRect(x: x + 16, y: y + 6, width: 8, height: 28)); ctx.fill(CGRect(x: x + 6, y: y + 16, width: 28, height: 8)) } }),
    ("bricks", rgb(170, 70, 40), { ctx in
        for (j, y) in stride(from: CGFloat(0), to: S, by: 32).enumerated() {
            for x in stride(from: CGFloat(j % 2 == 0 ? 0 : -32), to: S, by: 64) {
                ctx.fill(CGRect(x: x + 2, y: y + 2, width: 60, height: 28)) } } }),
    ("scales", rgb(120, 125, 135), { ctx in
        ctx.setLineWidth(6); ctx.setStrokeColor(rgb(120, 125, 135))
        tile(ctx, 32) { x, y, _, j in
            let ox: CGFloat = j % 2 == 0 ? 0 : 16
            ctx.addArc(center: CGPoint(x: x + ox, y: y), radius: 16, startAngle: 0, endAngle: .pi, clockwise: false)
            ctx.strokePath() } }),
]

func drawBundled(_ dir: String) {
    for (slug, color, draw) in shapes {
        png("\(dir)/shapes/\(slug).png") { ctx in
            ctx.setFillColor(rgb(255, 255, 255)); ctx.fill(CGRect(x: 0, y: 0, width: S, height: S))
            ctx.setFillColor(color); draw(ctx)
        }
    }
    for (slug, color, draw) in patterns {
        png("\(dir)/patterns/\(slug).png") { ctx in
            ctx.setFillColor(rgb(250, 248, 242)); ctx.fill(CGRect(x: 0, y: 0, width: S, height: S))
            ctx.setFillColor(color); draw(ctx)
        }
    }
}

// MARK: Numbered packs: a big numeral on a colour from a wheel.

func drawNumbered(_ dir: String, _ n: Int, _ name: String) {
    var faces: [String] = []
    for i in 1...n {
        let hue = CGFloat(i * 37 % 360) / 360
        let file = String(format: "face-%03d.png", i)
        png("\(dir)/\(file)") { ctx in
            let c = hsb(hue)
            ctx.setFillColor(c); ctx.fill(CGRect(x: 0, y: 0, width: S, height: S))
            let text = "\(i)" as CFString
            let font = CTFontCreateWithName("Helvetica-Bold" as CFString, 120, nil)
            let attrs = [kCTFontAttributeName: font, kCTForegroundColorAttributeName: rgb(255, 255, 255)] as CFDictionary
            let line = CTLineCreateWithAttributedString(CFAttributedStringCreate(nil, text, attrs))
            let b = CTLineGetBoundsWithOptions(line, .useGlyphPathBounds)
            ctx.textPosition = CGPoint(x: (S - b.width) / 2 - b.minX, y: (S - b.height) / 2 - b.minY)
            CTLineDraw(line, ctx)
        }
        faces.append("    {\"name\": \"Number \(i)\", \"image\": \"\(file)\"}")
    }
    let json = "{\n  \"name\": \"\(name)\",\n  \"faces\": [\n" + faces.joined(separator: ",\n") + "\n  ]\n}\n"
    try! json.write(toFile: "\(dir)/pack.json", atomically: true, encoding: .utf8)
}

// MARK: Cairns: stacks of one to four stones in three palettes, on a sky and a hill.

func drawCairns(_ dir: String) {
    let palettes: [(String, [CGColor])] = [
        ("grey", [rgb(120, 124, 130), rgb(150, 154, 160), rgb(105, 108, 114), rgb(170, 172, 176)]),
        ("sandstone", [rgb(196, 140, 88), rgb(214, 168, 112), rgb(176, 120, 72), rgb(226, 190, 140)]),
        ("slate", [rgb(70, 86, 110), rgb(96, 112, 138), rgb(58, 72, 94), rgb(122, 138, 160)]),
    ]
    let words = ["One", "Two", "Three", "Four"]
    var faces: [String] = []
    for (pname, colors) in palettes {
        for n in 1...4 {
            let file = "\(pname)-\(n).png"
            png("\(dir)/\(file)") { ctx in
                ctx.setFillColor(rgb(214, 232, 244)); ctx.fill(CGRect(x: 0, y: 0, width: S, height: S))
                ctx.setFillColor(rgb(150, 190, 120)); ctx.fillEllipse(in: CGRect(x: -60, y: -150, width: S + 120, height: 210))
                var y: CGFloat = 44
                for i in 0..<n {
                    let w: CGFloat = 150 - CGFloat(i) * 26 - CGFloat(4 - n) * 6
                    let h: CGFloat = 46 - CGFloat(i) * 4
                    ctx.setFillColor(colors[i])
                    ctx.fillEllipse(in: CGRect(x: (S - w) / 2 + CGFloat(i % 2 == 0 ? 0 : 6), y: y, width: w, height: h))
                    y += h - 8
                }
            }
            let stones = n == 1 ? "stone" : "stones"
            faces.append("    {\"name\": \"\(words[n - 1]) \(pname) \(stones)\", \"image\": \"\(file)\"}")
        }
    }
    let json = "{\n  \"name\": \"Cairns\",\n  \"pairs\": 8,\n  \"faces\": [\n" + faces.joined(separator: ",\n") + "\n  ]\n}\n"
    try! json.write(toFile: "\(dir)/pack.json", atomically: true, encoding: .utf8)
}

func hsb(_ h: CGFloat) -> CGColor {
    let s: CGFloat = 0.55, v: CGFloat = 0.78
    let i = Int(h * 6) % 6, f = h * 6 - CGFloat(Int(h * 6))
    let p = v * (1 - s), q = v * (1 - f * s), t = v * (1 - (1 - f) * s)
    let (r, g, b): (CGFloat, CGFloat, CGFloat) = [(v, t, p), (q, v, p), (p, v, t), (p, q, v), (t, p, v), (v, p, q)][i]
    return CGColor(srgbRed: r, green: g, blue: b, alpha: 1)
}

let args = CommandLine.arguments
switch (args.count > 1 ? args[1] : "", args.count) {
case ("bundled", 3): drawBundled(args[2])
case ("cairns", 3): drawCairns(args[2])
case ("numbered", 4), ("numbered", 5):
    drawNumbered(args[2], Int(args[3])!, args.count == 5 ? args[4] : "Numbers")
default:
    FileHandle.standardError.write(Data("usage: draw.swift bundled <dir> | cairns <dir> | numbered <dir> <n> [name]\n".utf8))
    exit(2)
}
