import Pairs

/-! Tests of the parts the proofs don't pin down: what text opens what, which manifests are
refused and why, scores on disk, and a pack load from start to finish through `receive`. -/

namespace Pairs.Tests
open Pairs Cairn

/-! ## Where a pack is -/

#guard (Where.parse "~/Packs/space").toOption = some (.file "~/Packs/space/pack.json" "~/Packs/space/")
#guard (Where.parse "/tmp/p/").toOption = some (.file "/tmp/p/pack.json" "/tmp/p/")
#guard (Where.parse "/tmp/p/mine.json").toOption = some (.file "/tmp/p/mine.json" "/tmp/p/")
#guard (Where.parse "https://x.test/packs/space").toOption = some (.web "https://x.test/packs/space/pack.json" "https://x.test/packs/space/")
#guard (Where.parse "https://x.test/a.json").toOption = some (.web "https://x.test/a.json" "https://x.test/")
#guard (Where.parse "  ~/p  ").toOption = some (.file "~/p/pack.json" "~/p/")
#guard (Where.parse "http://x.test/p").toOption.isNone
#guard (Where.parse "ftp://x.test/p").toOption.isNone
#guard (Where.parse "relative/p").toOption.isNone
#guard (Where.parse "").toOption.isNone

/-! ## Manifests -/

def web : Where := .web "https://x.test/p/pack.json" "https://x.test/p/"

def parseText (t : String) : Except String Pack := parse "https://x.test/p" web t.toUTF8

def expected : Pack :=
  { name := "P", source := "https://x.test/p", pairs := 2,
    faces := [⟨"a", "https://x.test/p/a.png"⟩, ⟨"b", "https://x.test/p/img/b.png"⟩] }

#guard (parseText "{\"name\": \"P\", \"faces\": [{\"name\": \"a\", \"image\": \"a.png\"}, {\"name\": \"b\", \"image\": \"img/b.png\"}]}").toOption = some expected

def refused (t : String) : Bool := (parseText t).toOption.isNone

#guard refused "{\"name\": \"P\", \"faces\": [}"
#guard refused "{\"faces\": []}"
#guard refused "{\"name\": \"P\", \"faces\": [{\"name\": \"a\", \"image\": \"a.png\"}]}"
#guard refused "{\"name\": \"P\", \"faces\": [{\"name\": \"a\", \"image\": \"../a.png\"}, {\"name\": \"b\", \"image\": \"b.png\"}]}"
#guard refused "{\"name\": \"P\", \"faces\": [{\"name\": \"a\", \"image\": \"/a.png\"}, {\"name\": \"b\", \"image\": \"b.png\"}]}"
#guard refused "{\"name\": \"P\", \"faces\": [{\"name\": \"a\", \"image\": \"https://e.test/a.png\"}, {\"name\": \"b\", \"image\": \"b.png\"}]}"
#guard refused "{\"name\": \"P\", \"faces\": [{\"name\": \"a\", \"image\": \"a.png\"}, {\"name\": \"b\", \"image\": \"a.png\"}]}"
#guard refused "{\"name\": \"P\", \"pairs\": 3, \"faces\": [{\"name\": \"a\", \"image\": \"a.png\"}, {\"name\": \"b\", \"image\": \"b.png\"}]}"
#guard refused "{\"name\": \"P\", \"pairs\": 1.5, \"faces\": [{\"name\": \"a\", \"image\": \"a.png\"}, {\"name\": \"b\", \"image\": \"b.png\"}]}"

/-! ## Scores on disk -/

def sample : Scores := [("bundled:shapes", ⟨9, 31000⟩), ("https://x.test/p", ⟨12, 60000⟩)]

#guard Scores.decode sample.encode = sample
#guard Scores.decode "garbage".toUTF8 = []
#guard (sample.record "bundled:shapes" ⟨11, 20000⟩).get "bundled:shapes" = some ⟨9, 20000⟩

/-! ## A pack load, start to finish -/

def deliver (s : State) (ms : List Msg) : State := ms.foldl (fun s m => (machine.receive s m).1) s

def act (s : State) (as : List Action) : State := as.foldl (fun s a => (machine.update s a).1) s

/-- Patterns from the Packs menu: its twelve images load; when the last answers, a game of
Patterns is dealt. -/
def loaded : State :=
  let s := act initial [.press ⟨10, 1⟩]
  let ids := s.reqs.img.pending.map (·.1)
  deliver s (ids.map fun id => .reply id (.image 256 256))

#guard loaded.core.pack.name = "Patterns"
#guard loaded.core.loading.isNone
#guard loaded.core.deals = initial.core.deals + 1

/-- The same, but one image fails: the board stays Shapes and the problem names the face. -/
def oneFails : State :=
  let s := act initial [.press ⟨10, 1⟩]
  match s.reqs.img.pending.map (·.1) with
  | id :: rest => deliver s ((.reply id (.failed .notFound "gone")) :: rest.map fun i => .reply i (.image 1 1))
  | [] => s

#guard oneFails.core.pack.name = "Shapes"
#guard oneFails.core.loading.isNone
#guard oneFails.core.problem.isSome
#guard oneFails.core.board = initial.core.board

/-- Switching to Shapes while Patterns loads: Patterns's replies, arriving late, change nothing. -/
def switched : State :=
  let s := act initial [.press ⟨10, 1⟩]
  let old := s.reqs.img.pending.map (·.1)
  let s := act s [.press ⟨10, 0⟩]
  deliver s (old.map fun id => .reply id (.image 256 256))

#guard switched.core.loading.map (·.source) = some "bundled:shapes"
#guard switched.core.board = initial.core.board

/-- A mismatch turns back when the timer fires. -/
def mismatch : State := deliver (act initial [.press ⟨2, 0⟩, .press ⟨2, 1⟩]) [.timer flipTimer]

#guard mismatch.core.game.up = []
#guard mismatch.core.game.moves = 1

end Pairs.Tests
