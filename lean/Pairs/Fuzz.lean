import Pairs.Claims
import Cairn.Fuzz.Rng

/-! # Pairs on `cairn fuzz`'s host

`cairn fuzz` plays a person (clicks, keys, typing, resizes, the menu) and the host (Cairn's
docs/fuzz.md, "The host": replies late and in any order, to cancelled requests and stray ids,
timers, the clock, image loads and evictions). Pairs adds what the host can't know, through
`Pairs.fuzz : Cairn.Fuzz.Custom State`:

- `edits`: typing a pack's folder or URL into the field (^4), good packs and broken ones.
- `replies`: the packs' manifests, images (a third of them 64 MiB decoded, so the 192 MiB cache
  evicts), the packs folder and the scores file, sometimes failing.
- `relations`: ^20–^29 over every step, including the replies the runtime drops.
- `outstanding`: ^27, the ids the app waits on are exactly those the runtime still holds.
- `drained`: ^27, once the host has answered everything, no pack is loading and nothing waits. -/

namespace Pairs.Fuzz

open Pairs Cairn Cairn.Fuzz Reqs

/-! ## Packs the host knows -/

def faceJson (name img : String) : String := s!"\{\"name\": \"{name}\", \"image\": \"{img}\"}"

def manifestJson (name : String) (pairs : Option Nat) (faces : List (String × String)) : String :=
  let ps := match pairs with | some n => s!"\"pairs\": {n}, " | none => ""
  s!"\{\"name\": \"{name}\", {ps}\"faces\": [" ++
    ", ".intercalate (faces.map fun (n, i) => faceJson n i) ++ "]}"

def numbered (n : Nat) (pre : String) : List (String × String) :=
  (List.range n).map fun i => (s!"{pre} {i}", s!"{pre}{i}.png")

/-- Pack folders (and URLs): name → manifest text, or none for no file. -/
def manifests : List (String × Option String) := [
  ("good", some (manifestJson "Good" (some 6) (numbered 10 "g"))),
  ("small", some (manifestJson "Small" none (numbered 3 "s"))),
  ("big", some (manifestJson "Big" (some 32) (numbered 100 "b"))),
  ("brokenimg", some (manifestJson "Broken image" (some 2) [("ok", "ok.png"), ("broken", "broken.png")])),
  ("badjson", some "{\"name\": \"Bad\", \"faces\": [}"),
  ("badpath", some (manifestJson "Bad path" none [("a", "../a.png"), ("b", "b.png")])),
  ("few", some (manifestJson "Few" none [("a", "a.png")])),
  ("dup", some (manifestJson "Dup" none [("a", "a.png"), ("b", "a.png")])),
  ("toomany", some (manifestJson "Too many" (some 9) (numbered 4 "t"))),
  ("missing", none) ]

/-- What a person types to open a pack. -/
def typed : List String :=
  (manifests.map fun (n, _) => s!"~/Packs/{n}") ++
  (manifests.map fun (n, _) => s!"https://packs.test/{n}") ++
  [ "https://packs.test/good/pack.json", "http://packs.test/good", "relative/good", "",
    "ftp://packs.test/good", "  ~/Packs/good  " ]

def nameOf (path : String) : String :=
  let parts := (path.splitOn "/").filter (· != "")
  match parts.reverse with
  | "pack.json" :: n :: _ => n
  | n :: _ => n
  | [] => ""

def manifestText (path : String) : Option String :=
  (manifests.lookup (nameOf path)).join

def scoresText : Gen String := Gen.elem [
  "{\"version\": 1, \"packs\": [{\"source\": \"bundled:shapes\", \"moves\": 9, \"ms\": 30000}]}",
  "{\"version\": 1, \"packs\": []}", "not json", "{\"packs\": [{\"source\": 3}]}" ]

def failed : Gen Reply := do
  let f ← Gen.elem [Fault.notFound, .denied, .timeout, .network, .invalid, .other]
  return .failed f "fuzz"

/-- A plausible answer to `r`, sometimes a failure, rarely the wrong shape. -/
def answer (r : Request) : Gen Reply := do
  if ← Gen.chance 1 40 then return .done
  match r with
  | .readFile p =>
    if p == scoresPath then
      if ← Gen.chance 1 3 then return .failed .notFound "no file"
      return .bytes (← scoresText).toUTF8
    match manifestText p with
    | some t => if ← Gen.chance 1 12 then return (← failed) else return .bytes t.toUTF8
    | none => return .failed .notFound "no such file"
  | .http _ url .. =>
    if ← Gen.chance 1 10 then return (← failed)
    else match manifestText url with
      | some t => return .http 200 [] t.toUTF8
      | none => return .http 404 [] "not found".toUTF8
  | .listDir _ =>
    if ← Gen.chance 1 6 then return .failed .notFound "no folder"
    let ns := (manifests.map (·.1)) ++ [".DS_Store"]
    let k ← Gen.range 0 ns.length
    return .names (ns.take k)
  | .loadImage src _ =>
    if (src.splitOn "broken").length > 1 then return .failed .invalid "not an image"
    if ← Gen.chance 1 15 then return (← failed)
    return .image (← Gen.range 64 512) (← Gen.range 64 512)
  | _ => if ← Gen.chance 1 8 then return (← failed) else return .done

def boardCheck (c : Core) : Bool :=
  decide c.pack.Ok && c.chosen.length == c.pack.pairs &&
    c.chosen.all (· < c.pack.faces.length) && decide c.chosen.Nodup &&
    decide (c.game.deck.Perm (ordered c.pack.pairs)) && decide c.game.Inv &&
    (match c.loading with
     | some { stage := .images p _, .. } => decide p.Ok
     | _ => true)

def sameReqs (a b : Reqs) : Bool :=
  a.next == b.next && a.answered == b.answered && a.cancelled == b.cancelled &&
    a.other == b.other && a.img.known == b.img.known && a.img.pending == b.img.pending

def completes (c : Core) (id : Nat) (rep : Reply) : Bool :=
  match c.loading, rep with
  | some { stage := .images .., since, .. }, .image .. => decide (since ≤ id)
  | _, _ => false

end Pairs.Fuzz

namespace Pairs

open Cairn Cairn.Fuzz Pairs.Fuzz

def fuzz : Cairn.Fuzz.Custom State where
  edits := fun _ c => if c == 4 then some (do
      let t ← Gen.elem typed
      return [.selectAll, .insert t]) else none
  -- Some images big enough (64 MiB decoded) that the 192 MiB cache budget evicts.
  replies := fun _ _ r => some (match r with
    | .loadImage src _ => do
      if (src.splitOn "broken").length == 1 && (← Gen.chance 1 3) then return .image 4096 4096
      answer r
    | _ => answer r)
  relations :=
    let on (f : Core → Core → Bool) : Transition State → Bool := fun t => f t.before.core t.after.core
    [ (20, on fun _ c' => boardCheck c'),
      (21, on fun _ c' => c'.game.up.length ≤ 2 && c'.game.up.all (!c'.game.isMatched ·)),
      (22, on fun _ c' => c'.game.won == c'.game.allMatched),
      (23, on fun _ c' => (c'.game.flipAll (c'.game.solve c'.now) c'.now).won),
      (24, on fun _ c' => 2 * c'.game.moves + c'.game.up.length % 2 == c'.game.flips),
      (25, on fun c c' => c'.deals != c.deals || c.game.matched.all c'.game.matched.contains),
      (26, on fun c c' => c.scores.all fun (k, b) => match c'.scores.get k with
        | some b' => decide (b'.le b)
        | none => false),
      -- Only `Reqs.Ok`: the frame's effects are the runtime's, which holds requests back past six
      -- at a time and sends them later, so their ids needn't be new to the step.
      (27, fun t => decide t.after.reqs.Ok),
      (28, fun t => match t.msg with
        | some (.reply id _) => t.before.reqs.isLive id ||
            (t.after.core == t.before.core && sameReqs t.after.reqs t.before.reqs)
        | _ => true),
      (29, fun t => match t.msg with
        | some (.reply id rep) => t.after.core.board == t.before.core.board || completes t.before.core id rep
        | _ => true) ]
  -- Once the host has answered everything: no pack still loading, nothing still awaited.
  outstanding := [(27, fun s ids => ids.mergeSort == s.reqs.live.mergeSort)]
  drained := [(27, fun s => s.core.loading.isNone && s.reqs.live.isEmpty)]

end Pairs
