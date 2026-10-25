module

public import Pairs.Game
public import Pairs.Bundled
public import Pairs.Scores
public import Pairs.Reqs

/-! # The app's model

The state is the board (the pack, the faces it deals, the game), the pack being loaded if any,
the best scores, the field to type a folder or URL into, and the requests in flight (`Reqs`).

Everything the app does is a `Plan`: from the core state and the requests it decides a new core
state and a list of `Reqs.Op`s, which `State.go` applies. A plan never touches the requests
itself, so whatever it decides, no request is lost (`Reqs.run_ok`).

* **Packs load beside the game.** Opening a pack (typed, bundled or from the packs folder)
  cancels whatever pack was loading, then reads the manifest and loads every face's image. The
  board is replaced only when every image has answered ready, by replies to requests made after
  the load began (`Loading.since`); a manifest that doesn't parse, or an image that fails, ends
  the load with a message (`problem`) and leaves the game as it was.
* **Images on the board** are loaded when a game is dealt, and again whenever a card shows a face
  whose image the host dropped (`Sub.imageCache`, `need`).
* **The clock** seeds every deal: the first one when it first ticks (the launch state deals with
  seed 0 so the app shows a board at once), then each New Game.
* **Scores** are read at launch and written after each win that improves them. -/

@[expose] public section

namespace Pairs

open Cairn

def scoresPath : String := "~/Library/Application Support/Pairs/scores.json"
def packsDir : String := "~/Library/Application Support/Pairs/Packs/"

/-- How long a mismatch stays up. -/
def flipBackMs : Nat := 1000
def flipTimer : String := "flipBack"
def manifestTimeoutMs : Nat := 15000

/-- The request that reads a manifest. -/
def Where.request : Where → Request
  | .file m _ => .readFile m
  | .web m _ => .http "GET" m [] ByteArray.empty manifestTimeoutMs

inductive Stage where
  /-- Waiting for the manifest. -/
  | manifest (w : Where)
  /-- The manifest is read; waiting for its images. `seen`: the sources that answered ready. -/
  | images (p : Pack) (seen : List String)
deriving Repr, DecidableEq, Inhabited

structure Loading where
  /-- Which load this is (the app counts them). -/
  load : Nat
  /-- What was opened, as typed (or `bundled:<id>`). -/
  source : String
  /-- The id of the load's first request: only replies to ids from here on count. -/
  since : Nat
  stage : Stage
deriving Repr, DecidableEq, Inhabited

-- region: model-core
structure Core where
  /-- The host's monotonic clock, in milliseconds. -/
  now : Nat := 0
  /-- Wall-clock milliseconds, for the seed. -/
  wall : Nat := 0
  /-- Whether the clock has ticked (the first deal with a real seed is done). -/
  booted : Bool := false
  pack : Pack := shapes
  /-- The pack's faces this game deals: face `f` of the game is `pack.faces[chosen[f]]`. -/
  chosen : List Nat := []
  game : Game := {}
  /-- Games dealt so far. -/
  deals : Nat := 0
  /-- Loads begun so far. -/
  loads : Nat := 0
  loading : Option Loading := none
  /-- What went wrong with the last pack, if it did. -/
  problem : Option String := none
  scores : Scores := []
  /-- Whether the scores file was read (only then is it written). -/
  scoresRead : Bool := false
  /-- The field to type a folder or URL into. -/
  field : Text.Field := {}
  /-- The folders in the packs folder. -/
  found : List String := []
deriving DecidableEq, Inhabited
-- endregion: model-core

structure State where
  core : Core := {}
  reqs : Reqs := {}
deriving Inhabited

namespace Core

/-- The board: what a reply must not change unless it completes a load. -/
def board (c : Core) : Pack × List Nat × Game := (c.pack, c.chosen, c.game)

def sources (p : Pack) : List String := p.faces.map (·.image)

/-- The image source of the face on position `i`. -/
def imageAt (c : Core) (i : Nat) : String :=
  match c.chosen[c.game.face i]? with
  | some j => (c.pack.faces[j]?.map (·.image)).getD ""
  | none => ""

/-- The name of the face on position `i`. -/
def nameAt (c : Core) (i : Nat) : String :=
  match c.chosen[c.game.face i]? with
  | some j => (c.pack.faces[j]?.map (·.name)).getD ""
  | none => ""

/-- The images this game deals. -/
def boardSources (c : Core) : List String :=
  c.chosen.filterMap fun j => c.pack.faces[j]?.map (·.image)

/-- The images on cards showing their face. -/
def shownSources (c : Core) : List String :=
  (((List.range c.game.deck.length).filter c.game.faceUp).map c.imageAt).eraseDups

/-- The seed for the next deal: the clock, and how many games were dealt. -/
def seed (c : Core) : Nat := c.wall * 1000003 + c.now * 31 + c.deals

end Core

/-- The `k` faces a game of a pack of `n` deals. -/
def chooseFaces (seed n k : Nat) : List Nat := (shuffle seed (List.range n)).take k

namespace Core

/-- A new game of pack `p`, dealt with `seed`. -/
def dealt (c : Core) (p : Pack) (seed : Nat) : Core :=
  { c with pack := p, chosen := chooseFaces seed p.faces.length p.pairs,
           game := Game.new (deal (nextSeed seed) p.pairs), deals := c.deals + 1 }

end Core

open Reqs (Op)

/-- What the app does: a new core state and the ops on its requests. -/
abbrev Plan := Core → Reqs → Core × List Op

/-- Images this game shows, the host doesn't hold, and the app isn't waiting for. -/
def need (c : Core) (r : Reqs) : List String :=
  c.shownSources.filter fun src =>
    r.img.state src == .loading && !r.img.pending.any (·.2 == src)

/-- Load this game's images that aren't ready and aren't on their way. -/
def preload (c : Core) (r : Reqs) : List Op :=
  (c.boardSources.eraseDups.filter fun src =>
    !r.img.isReady src && !r.img.pending.any (·.2 == src)).map .load

namespace State

/-- Run a plan: apply its ops, then load any shown image the host dropped. -/
def go (s : State) (f : Plan) : State × List Effect :=
  let (c, os) := f s.core s.reqs
  let (r1, e1) := s.reqs.run os
  let (r2, e2) := r1.run ((need c r1).map .load)
  ({ core := c, reqs := r2 }, e1 ++ e2)

end State

/-! ## Plans -/

/-- Save the scores, once they were read. -/
def saveScores (c : Core) : List Op :=
  if c.scoresRead then [.issue .writeScores (.writeFile scoresPath c.scores.encode)] else []

/-- Deal a new game of `p` (New Game, or a pack that finished loading). -/
def dealPlan (p : Pack) : Plan := fun c r =>
  let c1 := c.dealt p c.seed
  (c1, .cancelTimer flipTimer :: preload c1 r)

/-- Turn card `k`; a mismatch turns back after `flipBackMs`, and a win records the score. -/
def flipPlan (k : Nat) : Plan := fun c _ =>
  if c.game.canFlip k then
    let g' := c.game.flip k c.now
    let c1 := { c with game := g' }
    let t1 : List Op := if c.game.up.length == 2 then [.cancelTimer flipTimer] else []
    let t2 : List Op := if g'.up.length == 2 then [.setTimer flipTimer flipBackMs] else []
    if g'.won && !c.game.won then
      match g'.score with
      | some (m, t) =>
        let c2 := { c1 with scores := c1.scores.record c.pack.source ⟨m, t⟩ }
        (c2, t1 ++ t2 ++ saveScores c2)
      | none => (c1, t1 ++ t2)
    else (c1, t1 ++ t2)
  else (c, [])

/-- The host's timer: a mismatch turns back. -/
def flipBackPlan : Plan := fun c _ => ({ c with game := c.game.flipBack }, [])

/-- Stop the pack being loaded: cancel its manifest and the images only it wanted. -/
def stopOps (c : Core) : List Op :=
  match c.loading with
  | none => []
  | some l =>
    .cancelOther (· == .manifest l.load) ::
    match l.stage with
    | .images p _ =>
      [.cancelImages fun src => (Core.sources p).contains src && !c.boardSources.contains src]
    | .manifest _ => []

/-- Begin loading a pack from `source`, ending any load in progress. -/
def startLoad (c : Core) (r : Reqs) (source : String) (stage : Stage) : Core × List Op :=
  let l : Loading := { load := c.loads, source, since := r.next, stage }
  let start : List Op := match stage with
    | .manifest w => [.issue (.manifest c.loads) w.request]
    | .images p _ => (Core.sources p).map .load
  ({ c with loads := c.loads + 1, loading := some l, problem := none }, stopOps c ++ start)

/-- Open what is typed in the field. -/
def openTypedPlan : Plan := fun c r =>
  let t := c.field.textString.trimAscii.toString
  match Where.parse t with
  | .error e => ({ c with problem := some e }, [])
  | .ok w => startLoad c r t (.manifest w)

/-- Open bundled pack `k`. -/
def openBundledPlan (k : Nat) : Plan := fun c r =>
  match bundled[k]? with
  | some p => startLoad c r p.source (.images p [])
  | none => (c, [])

/-- Open the `k`th folder of the packs folder. -/
def openFoundPlan (k : Nat) : Plan := fun c r =>
  match c.found[k]? with
  | some name =>
    let t := packsDir ++ name
    match Where.parse t with
    | .error e => ({ c with problem := some e }, [])
    | .ok w => startLoad c r t (.manifest w)
  | none => (c, [])

/-- Stop loading. -/
def cancelLoadPlan : Plan := fun c _ => ({ c with loading := none }, stopOps c)

/-- Type in the field. -/
def editPlan (op : TextOp) : Plan := fun c _ =>
  let (f, es) := Text.Field.apply op c.field
  ({ c with field := f }, es.map .pass)

/-- Look in the packs folder again (opening the menu). -/
def listPlan : Plan := fun c r =>
  (c, if r.waitingFor .listPacks then [] else [.issue .listPacks (.listDir packsDir)])

/-- Show the packs folder in the Finder. -/
def revealPlan : Plan := fun c _ =>
  (c, [.issue .chore (.makeDir packsDir), .issue .chore (.openItem packsDir)])

/-- The launch: read the scores and the packs folder. -/
def bootPlan : Plan := fun c _ =>
  (c, [.issue .readScores (.readFile scoresPath), .issue .chore (.makeDir packsDir),
       .issue .listPacks (.listDir packsDir)])

/-! ## Replies -/

/-- A manifest's bytes, or what went wrong getting them. -/
def manifestData : Where → Reply → Except String ByteArray
  | .file .., .bytes d => .ok d
  | .web .., .http 200 _ body => .ok body
  | .web .., .http st _ _ => .error s!"the server answered {st}"
  | _, .failed .notFound _ => .error "there is no pack.json there"
  | _, .failed _ msg => .error msg
  | _, _ => .error "unexpected reply"

/-- `e` ending in one full stop. -/
def sentence (e : String) : String := if e.endsWith "." then e else e ++ "."

def onManifest (id n : Nat) (rep : Reply) : Plan := fun c _ =>
  match c.loading with
  | some l =>
    match l.stage with
    | .manifest w =>
      if l.load = n ∧ l.since ≤ id then
        match manifestData w rep >>= parse l.source w with
        | .ok p =>
          ({ c with loading := some { l with stage := .images p [] } },
           .answer id rep :: (Core.sources p).map .load)
        | .error e =>
          ({ c with loading := none, problem := some s!"Couldn't open {l.source}: {sentence e}" },
           [.answer id rep])
      else (c, [.answer id rep])
    | .images .. => (c, [.answer id rep])
  | none => (c, [.answer id rep])

-- region: model-image
/-- An image's reply. If it is one the pack being loaded asked for since the load began, it
counts toward the load: ready, it is seen, and when every image was seen the pack replaces the
board; failed, the load ends with a message and the board stays. -/
def onImage (id : Nat) (rep : Reply) : Plan := fun c r =>
  match r.img.pending.lookup id, c.loading with
  | some src, some l =>
    match l.stage with
    | .images p seen =>
      if l.since ≤ id ∧ (Core.sources p).contains src then
        match rep with
        | .image .. =>
          let seen' := if seen.contains src then seen else src :: seen
          if (Core.sources p).all seen'.contains then
            let (c1, os) := dealPlan p { c with loading := none, problem := none } r
            (c1, .answer id rep :: os)
          else ({ c with loading := some { l with stage := .images p seen' } }, [.answer id rep])
        | .failed _ msg =>
          let name := ((p.faces.find? (·.image == src)).map (·.name)).getD src
          ({ c with loading := none,
                    problem := some s!"Couldn't open {p.name}: the image for {name} didn't load ({msg})." },
           .answer id rep :: stopOps c)
        | _ =>
          ({ c with loading := none, problem := some s!"Couldn't open {p.name}: an image didn't load." },
           .answer id rep :: stopOps c)
      else (c, [.answer id rep])
    | .manifest _ => (c, [.answer id rep])
  | _, _ => (c, [.answer id rep])
-- endregion: model-image

def onScores (id : Nat) (rep : Reply) : Plan := fun c _ =>
  let read := match rep with
    | .bytes d => Scores.decode d
    | _ => []
  let c1 := { c with scores := c.scores.merge read, scoresRead := true }
  (c1, .answer id rep :: (if c.scores.isEmpty then [] else saveScores c1))

def onList (id : Nat) (rep : Reply) : Plan := fun c _ =>
  let found := match rep with
    | .names ns => ns.filter fun n => !n.startsWith "."
    | _ => []
  ({ c with found }, [.answer id rep])

def onReply (id : Nat) (rep : Reply) : Plan := fun c r =>
  match r.purpose id with
  | some (.manifest n) => onManifest id n rep c r
  | some .readScores => onScores id rep c r
  | some .listPacks => onList id rep c r
  | some _ => (c, [.answer id rep])
  | none => onImage id rep c r

/-- The host dropped `src`'s pixels. Forget them; if the pack being loaded still waits for that
image, ask for it again. (A card showing it asks again through `need`.) -/
def onEvicted (src : String) : Plan := fun c r =>
  let again : List Op := match c.loading with
    | some { stage := .images p seen, .. } =>
      if (Core.sources p).contains src && !seen.contains src && r.img.pending.any (·.2 == src)
      then [.load src] else []
    | _ => []
  (c, .evicted src :: again)

/-- The clock: the first reading deals the first real game, unless a card was turned already. -/
def onClock (t : Time) : Plan := fun c r =>
  let c1 := { c with now := t.mono, wall := t.wall.toNat }
  if c.booted then (c1, [])
  else if c.game.flips = 0 then dealPlan c.pack { c1 with booted := true } r
  else ({ c1 with booted := true }, preload c1 r)

namespace State

-- region: model-receive
def receive (s : State) : Msg → State × List Effect
  | .clock t => s.go (onClock t)
  | .timer n => if n = flipTimer then s.go flipBackPlan else (s, [])
  | .reply id rep => if s.reqs.isLive id then s.go (onReply id rep) else (s, [])
  | .sub _ (.evicted src) => s.go (onEvicted src)
  | .sub _ _ => (s, [])
-- endregion: model-receive

end State

/-- The launch state: Shapes dealt with seed 0, the scores and the packs folder asked for. -/
def initialCore : Core := ({} : Core).dealt shapes 0

def boot : State × List Effect := ({ core := initialCore } : State).go bootPlan

def initial : State := boot.1

end Pairs
