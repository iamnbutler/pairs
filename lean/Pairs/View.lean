module

public import Pairs.Model

/-! The window's view and the menu bar item's menu.

The window is a column: the pack's name, the counters and New Game; the field to open a pack
with Cancel beside it while one loads; a line for what's loading or what went wrong; and the
board, a `Grid` of cards that fills the rest of the window and reflows when it is resized. A
face-down card is a back; a face-up one shows its face's image (`Node.image`, from the images the
model loaded). Once the game is won, the board's box shows the result and New Game instead.

The window's smallest size (`minSize`) is the chrome plus `Grid.minBox` for the board, so every
card keeps at least `cardMin` points of width at every size the window can take: nothing
scrolls. Every text sits in a fixed-height clipping box, so long names are cut, never spill. -/

@[expose] public section

namespace Pairs
open Cairn

def white : Color := ⟨255, 255, 255, 255⟩
def paper : Color := ⟨246, 245, 241, 255⟩
def ink : Color := ⟨28, 28, 30, 255⟩
def muted : Color := ⟨110, 110, 118, 255⟩
def line : Color := ⟨214, 212, 206, 255⟩
def green : Color := ⟨48, 150, 84, 255⟩
def paleGreen : Color := ⟨228, 244, 232, 255⟩
def red : Color := ⟨196, 43, 28, 255⟩
def back : Color := ⟨70, 86, 200, 255⟩
def backInner : Color := ⟨98, 114, 222, 255⟩
def accent : Color := ⟨40, 40, 46, 255⟩

/-! ## Sizes -/

def pad : Nat := 20
def gapY : Nat := 10
def headerH : Nat := 36
def fieldH : Nat := 32
def statusH : Nat := 18
/-- The narrowest a card gets. -/
def cardMin : Nat := 64

/-- The board's grid: square cards at least `cardMin` wide, 10 points apart. -/
def grid : Grid := { minWidth := cardMin, gap := 10 }

/-- The columns the window is sized for with `n` cards: a squarish board. -/
def columnsFor (n : Nat) : Nat := if n ≤ 16 then 4 else if n ≤ 36 then 6 else 8

/-- The window's chrome around the board: padding, the three rows and their gaps. -/
def chromeH : Nat := 2 * pad + headerH + fieldH + statusH + 3 * gapY

/-- The narrowest the chrome fits in: the counters, New Game, the field and Cancel. -/
def chromeW : Nat := 480

/-- **The smallest window**: the chrome plus the board's `Grid.minBox`, so every card is at least
`cardMin` wide there (`Grid.minW_le_cardW`). -/
def minSize (s : State) : Size :=
  let n := s.core.game.deck.length
  let b := grid.minBox n (columnsFor n)
  ⟨max chromeW (b.1 + 2 * pad), b.2 + chromeH⟩

/-- The board's box in a window of `ui.size`. -/
def boardBox (ui : UI) : Nat × Nat :=
  ((ui.size.w - 2 * pad).toNat, (ui.size.h - chromeH).toNat)

/-! ## Text -/

/-- One line of text in a clipping box `w` wide and `h` high. -/
def textBox (w : Sizing) (h : Nat) (st : TextStyle) (t : String) (align : Align := .start) :
    Node :=
  .box { width := w, height := .fixed h, clip := true, axis := .row, justify := align,
         align := .center } none
    [.text st t]

def body : Font := { size := 13 }

/-- `ms` as `m:ss`. -/
def clock (ms : Nat) : String :=
  let t := ms / 1000
  let sec := t % 60
  s!"{t / 60}:{if sec < 10 then "0" else ""}{sec}"

/-- The time this game has run: from the first card turned to the last match, or to now. -/
def elapsed (c : Core) : Nat :=
  match c.game.started with
  | some a => c.game.finished.getD c.now - a
  | none => 0

def bestText (c : Core) : String :=
  match c.scores.get c.pack.source with
  | some b => s!"Best {b.moves} · {clock b.ms}"
  | none => "No best yet"

def counters (c : Core) : String :=
  s!"Moves {c.game.moves} · {clock (elapsed c)} · {bestText c}"

/-! ## Buttons -/

def button (r : ControlRef) (t : String) (w : Nat) (fill : Color) (fg : Color := white) : Node :=
  .box { width := .fixed w, height := .fixed 30, radius := 7, align := .center, justify := .center,
         clip := true, background := some fill, corner := .continuous }
    (some { ref := r, label := t })
    [.text { font := { size := 13, weight := 600 }, color := fg } t]

def newGameButton : Node := button ⟨3, 0⟩ "New Game" 110 accent

def cancelButton : Node := button ⟨5, 0⟩ "Cancel" 80 white ink

/-! ## Rows -/

def header (s : State) : Node :=
  let c := s.core
  .box { axis := .row, width := .fill, height := .fixed headerH, gap := 12, align := .center } none
    ([textBox .fill 26 { font := { size := 20, weight := 700 }, color := ink } c.pack.name,
      textBox (.fixed 230) 20 { font := body, color := muted } (counters c) .finish] ++
     (if c.game.won then [] else [newGameButton]))

def fieldRef : ControlRef := ⟨4, 0⟩

def placeholder : String := "Open a pack: a folder (~/… or /…) or an https:// URL, then Enter"

def fieldRow (s : State) (ui : UI) : Node :=
  let fv := s.core.field.view (ui.focus = some fieldRef)
  .box { axis := .row, width := .fill, height := .fixed fieldH, gap := 8, align := .center } none
    ([.field { width := .fill, padding := ⟨6, 8, 6, 8⟩, background := some white, radius := 6,
               border := some ⟨1, line⟩ }
        { font := body, color := ink }
        { ref := fieldRef, role := .textField, label := "Pack folder or URL" }
        { fv with placeholder }] ++
     (if s.core.loading.isSome then [cancelButton] else []))

/-- What's loading, or what went wrong, or nothing. -/
def statusText (c : Core) : Option (String × Color) :=
  match c.loading with
  | some l =>
    match l.stage with
    | .manifest _ => some (s!"Reading {l.source}…", muted)
    | .images p seen => some (s!"Loading {p.name}: {seen.length} of {p.faces.length} images…", muted)
  | none => c.problem.map (·, red)

def statusRow (c : Core) : Node :=
  match statusText c with
  | some (t, col) => textBox .fill statusH { font := { size := 12 }, color := col } t
  | none => .box { width := .fill, height := .fixed statusH } none []

/-! ## The board -/

/-- A card `w × h`: its back, or its face's image on white (green-edged once matched). A card
that can be turned is a control. -/
def card (s : State) (w h i : Nat) : Node :=
  let g := s.core.game
  let ctl : Option Control :=
    if g.canFlip i then some { ref := ⟨2, i⟩, label := s!"Card {i + 1}" } else none
  if g.faceUp i then
    let matched := g.isMatched i
    let src := s.core.imageAt i
    .box { width := .fixed w, height := .fixed h, padding := ⟨6, 6, 6, 6⟩, radius := 10,
           corner := .continuous, clip := true, align := .center, justify := .center,
           background := some (if matched then paleGreen else white),
           border := some ⟨2, if matched then green else line⟩ } ctl
      [.image { source := src, width := w - 12, height := h - 12, fit := .contain,
                state := s.reqs.img.state src, backdrop := some (if matched then paleGreen else white),
                placeholder := paper }]
  else
    .box { width := .fixed w, height := .fixed h, padding := ⟨7, 7, 7, 7⟩, radius := 10,
           corner := .continuous, clip := true, background := some back } ctl
      [.box { width := .fill, height := .fill, radius := 6, corner := .continuous,
              background := some backInner } none []]

/-- The board's grid in a `W`-wide box: cards as wide as `columnsFor n` columns allow, never
narrower than `grid`'s (so at the smallest window it is `grid`). -/
def gridFor (n W : Nat) : Grid :=
  { grid with minWidth := max grid.minWidth ((W + grid.gap) / columnsFor n - grid.gap) }

def board (s : State) (W H : Nat) : Node :=
  let n := s.core.game.deck.length
  (gridFor n W).node W H (fun w h i => card s w h i) (List.range n)

/-- The board's box once the game is won: the result, the best, and New Game. -/
def winPanel (c : Core) (W H : Nat) : Node :=
  let pairs := c.game.deck.length / 2
  .box { width := .fixed W, height := .fixed H, gap := 10, align := .center, justify := .center,
         radius := 12, background := some white, clip := true } none
    [textBox .fill 40 { font := { size := 30, weight := 700 }, color := green } "You won!" .center,
     textBox .fill 20 { font := { size := 14 }, color := ink }
       s!"All {pairs} pairs of {c.pack.name} in {c.game.moves} moves and {clock (elapsed c)}." .center,
     textBox .fill 20 { font := body, color := muted } (bestText c) .center,
     newGameButton]

def view (s : State) (ui : UI) : Node :=
  let (W, H) := boardBox ui
  .box { width := .fill, height := .fill, padding := ⟨pad, pad, pad, pad⟩, gap := gapY,
         background := some paper, clip := true } none
    [header s, fieldRow s ui, statusRow s.core,
     if s.core.game.won then winPanel s.core W H else board s W H]

/-! ## The menu bar item -/

def packsItems (c : Core) : List MenuItem :=
  (bundled.zipIdx.map fun (p, k) => MenuItem.check ⟨10, k⟩ p.name (c.pack.source == p.source)) ++
  [.separator] ++
  (if c.found.isEmpty then [.info "No packs in the packs folder"]
   else c.found.zipIdx.map fun (f, k) => MenuItem.button ⟨11, k⟩ f)

def statusItem (s : State) : StatusItem :=
  { symbol := "square.grid.2x2", label := "Pairs", control := ⟨8, 0⟩,
    menu := [MenuItem.button ⟨9, 0⟩ "New Game",
             .submenu "Packs" (some 7) (packsItems s.core),
             .separator,
             MenuItem.button ⟨12, 0⟩ "Open Packs Folder"] }

end Pairs
