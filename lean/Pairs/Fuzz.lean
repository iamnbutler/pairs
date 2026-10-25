import Pairs.Claims
import Cairn.Fuzz.Rng

/-! # Pairs against a random host

`cairn fuzz` drives an app through its controls only: clicks, keys and resizes, with no host.
Pairs's claims are as much about the host's side (replies slow, failed, out of order,
duplicated, for requests long cancelled; timers; the image cache dropping pixels), so this plays
a random host against the machine the app runs (`Pairs.machine`: its moves and `receive`).

Each step is one of: a person's action (turning cards, enabled or not; New Game; typing a
folder or URL and pressing Enter; Cancel; the menu and its packs), the clock moving on, a timer
the app set coming due, a reply to any request the host holds (a pending one, in any order; one
the app cancelled; one already answered, again; or an id never issued), or the host dropping an
image's pixels. Packs come from a fixed table: good ones, one with 100 faces, and broken ones
(bad JSON, a missing file, a 404, a bad image path, too few faces, an image that never loads).

After every step it checks the claims as runnable predicates on the states before and after:
^20–^24 (the board), ^25 (matched stays), ^26 (scores), ^27 (requests: `Reqs.Ok`, and the
host's own count of what is outstanding equals the app's `live`), ^28 (a reply to an id not
live changes nothing) and ^29 (a reply changes the board only by completing the load). At the
end of each sequence the host answers everything outstanding, well: then no pack is still
loading (`drain`). -/

namespace Pairs.Fuzz

open Pairs Cairn Cairn.Fuzz Reqs

inductive Step where
  | acts (as : List Action)
  | tick (ms : Nat)
  | fire (name : String)
  | reply (id : Nat) (r : Reply)
  | evict (src : String)
deriving Repr, Inhabited

def cacheSub : Sub := .imageCache (256 * 1024 * 1024)

def Step.run (s : State) : Step → State × List Effect
  | .acts as => as.foldl (fun (s, es) a => let (s', e) := machine.update s a; (s', es ++ e)) (s, [])
  | .tick _ => (s, [])
  | .fire n => machine.receive s (.timer n)
  | .reply id r => machine.receive s (.reply id r)
  | .evict src => machine.receive s (.sub cacheSub (.evicted src))

/-! ## The host -/

structure Host where
  mono : Nat := 5000
  wall : Int := 1792749600000
  /-- Issued and neither answered nor cancelled. -/
  pending : List (Nat × Request) := []
  /-- Cancelled; the host may still answer them (late). -/
  cancelled : List (Nat × Request) := []
  /-- Answered; the host may answer them again. -/
  answered : List (Nat × Request) := []
  timers : List String := []
  /-- Sources the host holds pixels for. -/
  held : List String := []
deriving Inhabited

/-- What the host does with the effects of a step. -/
def Host.take (h : Host) (es : List Effect) : Host :=
  es.foldl (fun h e => match e with
    | .request id r => { h with pending := h.pending ++ [(id, r)] }
    | .cancelRequest id =>
      match h.pending.find? (·.1 == id) with
      | some p => { h with pending := h.pending.filter (·.1 != id), cancelled := p :: h.cancelled }
      | none => h
    | .setTimer n _ => { h with timers := n :: h.timers.filter (· != n) }
    | .cancelTimer n => { h with timers := h.timers.filter (· != n) }
    | _ => h) h

/-- The host after delivering step `st`. -/
def Host.deliver (h : Host) : Step → Host
  | .tick ms => { h with mono := h.mono + ms, wall := h.wall + ms }
  | .fire n => { h with timers := h.timers.filter (· != n) }
  | .reply id r =>
    let req := (h.pending ++ h.cancelled ++ h.answered).find? (·.1 == id)
    let h := { h with pending := h.pending.filter (·.1 != id) }
    let h := match req with
      | some p => if h.answered.any (·.1 == id) then h else { h with answered := p :: h.answered }
      | none => h
    match req, r with
    | some (_, .loadImage src _), .image .. => { h with held := src :: h.held.filter (· != src) }
    | _, _ => h
  | .evict src => { h with held := h.held.filter (· != src) }
  | .acts _ => h

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

/-- A good answer to `r`, for draining at the end. -/
def goodAnswer (r : Request) : Reply :=
  match r with
  | .readFile p => match manifestText p with
    | some t => .bytes t.toUTF8
    | none => .failed .notFound "no such file"
  | .http _ url .. => match manifestText url with
    | some t => .http 200 [] t.toUTF8
    | none => .http 404 [] ByteArray.empty
  | .listDir _ => .names []
  | .loadImage src _ =>
    if (src.splitOn "broken").length > 1 then .failed .invalid "not an image" else .image 256 256
  | _ => .done

def press (claim key : Nat) : Action := .press ⟨claim, key⟩

def nextStep (s : State) (h : Host) : Gen Step := do
  let n := s.core.game.deck.length
  let held : List Nat := (List.range n).filter s.core.game.canFlip
  Gen.weighted [
    (30, do
      if held.isEmpty || (← Gen.chance 1 5) then return .acts [press 2 (← Gen.below (n + 3))]
      return .acts [press 2 (← Gen.elem held)]),
    (2, return .acts [press 3 0]),
    (1, return .acts [press 9 0]),
    (5, do
      let t ← Gen.elem typed
      return .acts [.edit ⟨4, 0⟩ .selectAll, .edit ⟨4, 0⟩ (.insert t), .submit ⟨4, 0⟩]),
    (1, return .acts [.edit ⟨4, 0⟩ (← Gen.elem [.deleteBackward, .moveLeft false, .insert "x", .undo])]),
    (2, return .acts [press 5 0]),
    (2, return .acts [press 8 0]),
    (3, return .acts [press 10 (← Gen.below 3)]),
    (2, return .acts [press 11 (← Gen.below (s.core.found.length + 1))]),
    (1, return .acts [press 12 0]),
    (8, return .tick (← Gen.elem [16, 250, 1000, 5000])),
    (6, if h.timers.isEmpty then return .tick 100 else return .fire (← Gen.elem h.timers)),
    (30, do
      if h.pending.isEmpty then return .tick 50
      -- Any pending request, not only the oldest: replies come in any order.
      let (id, r) ← Gen.elem h.pending
      return .reply id (← answer r)),
    (4, do
      if h.cancelled.isEmpty then return .tick 10
      let (id, r) ← Gen.elem h.cancelled
      return .reply id (← answer r)),
    (3, do
      if h.answered.isEmpty then return .tick 10
      let (id, r) ← Gen.elem h.answered
      return .reply id (← answer r)),
    (1, return .reply (s.reqs.next + (← Gen.below 5)) .done),
    (3, do
      if h.held.isEmpty then return .tick 10
      return .evict (← Gen.elem h.held)) ]

/-! ## The checks -/

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

def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

def sorted (l : List Nat) : List Nat := l.foldr insertSorted []

/-- The checks of one step, from `s` to `s'` by `st` with effects `es`; `h'` is the host after. -/
def checks (s : State) (st : Step) (s' : State) (es : List Effect) (h' : Host) :
    List (Nat × Bool) :=
  let c := s.core
  let c' := s'.core
  let g := c'.game
  [ (20, boardCheck c'),
    (21, g.up.length ≤ 2 && g.up.all (!g.isMatched ·)),
    (22, g.won == g.allMatched),
    (23, (g.flipAll (g.solve c'.now) c'.now).won),
    (24, 2 * g.moves + g.up.length % 2 == g.flips),
    (25, c'.deals != c.deals || c.game.matched.all c'.game.matched.contains),
    (26, c.scores.all fun (k, b) => match c'.scores.get k with
      | some b' => decide (b'.le b)
      | none => false),
    (27, decide s'.reqs.Ok &&
      sorted (h'.pending.map (·.1)) == sorted s'.reqs.live &&
      es.all fun e => match e with
        | .request id _ => decide (s.reqs.next ≤ id)
        | .cancelRequest id => s.reqs.isLive id
        | _ => true),
    (28, match st with
      | .reply id _ => s.reqs.isLive id || (c' == c && sameReqs s'.reqs s.reqs && es.isEmpty)
      | _ => true),
    (29, match st with
      | .reply id rep => c'.board == c.board || completes c id rep
      | _ => true) ]

/-! ## Running -/

def tickMsg (h : Host) : Msg := .clock { mono := h.mono, wall := h.wall, zone := 0 }

/-- Run a step: the clock first when it moved (as the runtime delivers it), then the step. -/
def runStep (s : State) (h : Host) (st : Step) : State × List Effect × Host :=
  let h1 := h.deliver st
  let (s0, e0) := match st with
    | .tick _ => machine.receive s (tickMsg h1)
    | _ => (s, [])
  let (s1, e1) := st.run s0
  (s1, e0 ++ e1, h1.take (e0 ++ e1))

structure Failure where
  seed : Nat
  step : Nat
  claim : Nat
  trace : List Step

structure Stats where
  sequences : Nat := 0
  steps : Nat := 0
  replies : Nat := 0
  stale : Nat := 0
  loadsDone : Nat := 0
  checked : List (Nat × Nat) := []

def Stats.count (st : Stats) (id : Nat) : Stats :=
  { st with checked := match st.checked.lookup id with
    | some n => (id, n + 1) :: st.checked.filter (·.1 != id)
    | none => (id, 1) :: st.checked }

/-- Answer everything outstanding, well, until nothing is (or a bound). -/
def drain (s : State) (h : Host) : Nat → State × Host
  | 0 => (s, h)
  | fuel + 1 =>
    match h.pending with
    | [] => (s, h)
    | (id, r) :: _ =>
      let (s', _, h') := runStep s h (.reply id (goodAnswer r))
      drain s' h' fuel

def runSeq (seed steps : Nat) (stats : Stats) : Stats × Option Failure := Id.run do
  let mut g := Rng.ofSeed seed
  let mut s := initial
  let mut h : Host := ({} : Host).take boot.2
  let mut trace : Array Step := #[]
  let mut stats := { stats with sequences := stats.sequences + 1 }
  -- The first clock.
  let (s0, e0) := machine.receive s (tickMsg h)
  s := s0
  h := h.take e0
  for i in [0:steps] do
    let (st, g') := (nextStep s h).run g
    g := g'
    trace := trace.push st
    let (s', es, h') := runStep s h st
    stats := { stats with steps := stats.steps + 1 }
    match st with
    | .reply id _ =>
      stats := { stats with replies := stats.replies + 1,
                            stale := stats.stale + (if s.reqs.isLive id then 0 else 1) }
    | _ => pure ()
    if s.core.loading.isSome && s'.core.loading.isNone && s'.core.deals != s.core.deals then
      stats := { stats with loadsDone := stats.loadsDone + 1 }
    for (id, ok) in checks s st s' es h' do
      stats := stats.count id
      if !ok then return (stats, some ⟨seed, i, id, trace.toList⟩)
    s := s'
    h := h'
  let (sd, hd) := drain s h 2000
  stats := stats.count 0
  if sd.core.loading.isSome || !hd.pending.isEmpty then
    return (stats, some ⟨seed, steps, 0, trace.toList⟩)
  return (stats, none)

def claimName : Nat → String
  | 0 => "drain: every load finishes once the host answers"
  | 20 => "^20 the board is a deal of the pack"
  | 21 => "^21 at most two unmatched up"
  | 22 => "^22 won iff all matched"
  | 23 => "^23 can be won"
  | 24 => "^24 moves count pairs"
  | 25 => "^25 matched stays matched"
  | 26 => "^26 best scores only improve"
  | 27 => "^27 no request lost"
  | 28 => "^28 a late reply changes nothing"
  | 29 => "^29 only a finished pack changes the board"
  | n => s!"^{n}"

structure Opts where
  seed : Nat := 0
  iterations : Nat := 200
  steps : Nat := 300
  out : Option String := none

def parseArgs (o : Opts) : List String → Option Opts
  | [] => some o
  | "--seed" :: v :: rest => v.toNat?.bind fun n => parseArgs { o with seed := n } rest
  | "--iterations" :: v :: rest => v.toNat?.bind fun n => parseArgs { o with iterations := n } rest
  | "--steps" :: v :: rest => v.toNat?.bind fun n => parseArgs { o with steps := n } rest
  | "--out" :: v :: rest => parseArgs { o with out := some v } rest
  | _ => none

def main (args : List String) : IO UInt32 := do
  let some o := parseArgs {} args
    | IO.eprintln "usage: pairsfuzz [--seed S] [--iterations N] [--steps K] [--out DIR]"; return 2
  let t0 ← IO.monoMsNow
  let mut stats : Stats := {}
  let mut fail : Option Failure := none
  for i in [0:o.iterations] do
    let (st, f) := runSeq (o.seed + i) o.steps stats
    stats := st
    if f.isSome then
      fail := f
      break
  let ms := (← IO.monoMsNow) - t0
  let lines := (stats.checked.toArray.qsort (·.1 < ·.1)).toList.map fun (id, n) =>
    s!"  {claimName id}: {n} checks"
  let summary := s!"pairsfuzz: {stats.sequences} sequences, {stats.steps} steps, {stats.replies} replies ({stats.stale} to ids not awaited), {stats.loadsDone} packs loaded, {ms} ms\n" ++
    "\n".intercalate lines
  IO.println summary
  if let some dir := o.out then
    IO.FS.createDirAll dir
    let status := match fail with | some _ => "fail" | none => "pass"
    let claims := ", ".intercalate (stats.checked.map fun (id, n) => s!"\"{id}\": {n}")
    IO.FS.writeFile (dir ++ "/pairs.json")
      s!"\{\"status\": \"{status}\", \"seed\": {o.seed}, \"iterations\": {o.iterations}, \"steps\": {o.steps}, \"sequences\": {stats.sequences}, \"stepsRun\": {stats.steps}, \"replies\": {stats.replies}, \"stale\": {stats.stale}, \"packsLoaded\": {stats.loadsDone}, \"ms\": {ms}, \"checks\": \{{claims}}}\n"
  match fail with
  | some f =>
    IO.eprintln s!"pairsfuzz: FAIL {claimName f.claim} at step {f.step} of seed {f.seed}"
    for (st, i) in f.trace.zipIdx do
      if i + 12 ≥ f.trace.length then IO.eprintln s!"  {i}: {repr st}"
    return 1
  | none => return 0

end Pairs.Fuzz
