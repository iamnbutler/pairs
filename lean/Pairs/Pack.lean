module

public import CairnJson

/-! # Packs

A theme pack is a JSON manifest and the images it names: a folder holding `pack.json`, or an
`https` URL. This file reads what the person typed into a place to load from (`Where`), and a
manifest into a `Pack` (`parse`), refusing anything it can't use with a message the app shows.

```json
{ "name": "Shapes", "pairs": 8,
  "faces": [ { "name": "Red circle", "image": "red-circle.png" }, … ] }
```

`pairs` (optional, 2 to 32, at most the number of faces; 8 or every face if fewer) is how many
pairs a game deals. Image paths are relative to the manifest, never absolute, never `..`, never
a URL. -/

@[expose] public section

namespace Pairs

open CairnJson

/-- One face: its name (for the card's label) and the image source the host loads. -/
structure Face where
  name : String
  image : String
deriving Repr, DecidableEq, Inhabited

structure Pack where
  /-- The pack's name, from its manifest. -/
  name : String
  /-- Where it came from, as the person typed it (or `bundled:<id>`): the key its best scores
  are saved under. -/
  source : String
  faces : List Face
  /-- How many pairs a game deals: `2 ≤ pairs ≤ faces.length`. -/
  pairs : Nat
deriving Repr, DecidableEq, Inhabited

/-- Where a manifest is: a file on disk or an `https` URL, and the prefix its images' relative
paths are joined to. -/
inductive Where where
  | file (manifest dir : String)
  | web (manifest base : String)
deriving Repr, DecidableEq, Inhabited

def Where.manifest : Where → String
  | .file m _ | .web m _ => m

def Where.base : Where → String
  | .file _ d | .web _ d => d

/-- The most pairs a pack deals (an 8 × 8 grid). -/
def maxPairs : Nat := 32

/-- The most faces a manifest lists. -/
def maxFaces : Nat := 200

/-- The text up to and including its last `/` (empty if it has none). -/
def dirOf (s : String) : String :=
  let cs := s.toList
  String.ofList ((cs.reverse.dropWhile (· != '/')).reverse)

/-- `s` with a `/` at the end. -/
def slashed (s : String) : String := if s.endsWith "/" then s else s ++ "/"

/-- What the person typed, as a place to load a manifest from. -/
def Where.parse (text : String) : Except String Where :=
  let t := text.trimAscii.toString
  if t.isEmpty then .error "Type a folder (/… or ~/…) or an https:// URL."
  else if t.startsWith "https://" then
    if t.endsWith ".json" then .ok (.web t (dirOf t))
    else .ok (.web (slashed t ++ "pack.json") (slashed t))
  else if t.startsWith "http://" then .error "Only https:// URLs are allowed."
  else if (t.splitOn "://").length > 1 then .error "Only folders and https:// URLs can be opened."
  else if t.startsWith "/" || t.startsWith "~/" then
    if t.endsWith ".json" then .ok (.file t (dirOf t))
    else .ok (.file (slashed t ++ "pack.json") (slashed t))
  else .error "Use a full path (starting with / or ~/) or an https:// URL."

/-- An image path a manifest may name: relative, inside the pack, not a URL. -/
def safePath (p : String) : Bool :=
  !p.isEmpty && !p.startsWith "/" && !p.startsWith "~" && !p.contains '\\' &&
    (p.splitOn "://").length == 1 && !((p.splitOn "/").contains "..") &&
    !((p.splitOn "/").contains "")

/-- One face from the manifest, or what is wrong with it. -/
def parseFace (base : String) (i : Nat) (j : Json) : Except String Face :=
  match j.field "name" >>= Json.getStr, j.field "image" >>= Json.getStr with
  | some n, some img =>
    if n.isEmpty then .error s!"Face {i + 1} has an empty name."
    else if !safePath img then
      .error s!"Face {i + 1} (\"{n}\"): \"{img}\" isn't a relative path inside the pack."
    else .ok ⟨n, base ++ img⟩
  | none, _ => .error s!"Face {i + 1} has no \"name\" string."
  | _, none => .error s!"Face {i + 1} has no \"image\" string."

def parseFaces (base : String) : Nat → List Json → Except String (List Face)
  | _, [] => .ok []
  | i, j :: js => do
    let f ← parseFace base i j
    let fs ← parseFaces base (i + 1) js
    .ok (f :: fs)

/-- The first image named twice, if any. -/
def dupImage : List Face → Option String
  | [] => none
  | f :: fs => if fs.any (·.image == f.image) then some f.image else dupImage fs

/-- A manifest's text into a pack, or the reason it can't be used (`parse` adds the final
check). -/
def read (source : String) (w : Where) (data : ByteArray) : Except String Pack :=
  match decodeBytes data with
  | none => .error "pack.json isn't valid JSON."
  | some j =>
    match j.field "name" >>= Json.getStr, j.field "faces" >>= Json.getArr with
    | none, _ => .error "pack.json has no \"name\" string."
    | _, none => .error "pack.json has no \"faces\" list."
    | some name, some fs =>
      if name.isEmpty then .error "The pack's name is empty."
      else if fs.length < 2 then .error s!"A pack needs at least 2 faces; this one has {fs.length}."
      else if fs.length > maxFaces then .error s!"A pack has at most {maxFaces} faces; this one has {fs.length}."
      else
        match parseFaces w.base 0 fs with
        | .error e => .error e
        | .ok faces =>
          match dupImage faces with
          | some img => .error s!"Two faces use the same image, \"{img}\"."
          | none =>
            let dflt := min 8 faces.length
            match j.field "pairs" with
            | none => .ok ⟨name, source, faces, dflt⟩
            | some p =>
              match p.getInt with
              | some n =>
                if n < 2 then .error "\"pairs\" must be at least 2."
                else if n > faces.length then
                  .error s!"\"pairs\" is {n} but there are only {faces.length} faces."
                else if n > maxPairs then .error s!"\"pairs\" is at most {maxPairs}."
                else .ok ⟨name, source, faces, n.toNat⟩
              | none => .error "\"pairs\" must be a whole number."

/-- A pack `parse` returns deals between 2 and 32 pairs, at most its number of faces. -/
structure Pack.Ok (p : Pack) : Prop where
  two : 2 ≤ p.pairs
  le : p.pairs ≤ p.faces.length
  max : p.pairs ≤ maxPairs

instance (p : Pack) : Decidable p.Ok :=
  decidable_of_iff (2 ≤ p.pairs ∧ p.pairs ≤ p.faces.length ∧ p.pairs ≤ maxPairs)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-- The last guard: a pack that isn't `Ok` is refused. -/
def validate (p : Pack) : Except String Pack :=
  if p.Ok then .ok p else .error "The pack's \"pairs\" doesn't fit its faces."

/-- A manifest's text into a pack, or the reason it can't be used. -/
def parse (source : String) (w : Where) (data : ByteArray) : Except String Pack :=
  read source w data >>= validate

/-- **Every pack `parse` accepts is `Ok`.** -/
theorem parse_ok {source : String} {w : Where} {data : ByteArray} {p : Pack}
    (h : parse source w data = .ok p) : p.Ok := by
  unfold parse at h
  cases hr : read source w data with
  | error e => rw [hr] at h; cases h
  | ok q =>
    rw [hr] at h
    change validate q = .ok p at h
    unfold validate at h
    split at h
    · cases h; assumption
    · cases h

end Pairs
