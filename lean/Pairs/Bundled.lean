module

public import Pairs.Pack

/-! # The bundled packs

Two packs ship inside the app: Shapes and Patterns, twelve faces each, eight pairs a game. Their
images are PNGs in the app's resources (`packs/<id>/<face>.png`, relative to the resource folder
the host starts in), drawn by `tools/packs/draw.swift`. They are `Pack`s written in Lean, so the
app has a game the moment it starts, before any file is read. -/

@[expose] public section

namespace Pairs

/-- A bundled pack: its id (`packs/<id>/`), name and faces' names; each face's image is
`packs/<id>/<slug>.png`. -/
def bundledPack (id name : String) (faces : List (String × String)) : Pack :=
  { name, source := s!"bundled:{id}", pairs := 8,
    faces := faces.map fun (n, slug) => ⟨n, s!"packs/{id}/{slug}.png"⟩ }

def shapes : Pack := bundledPack "shapes" "Shapes" [
  ("Red circle", "red-circle"), ("Orange square", "orange-square"),
  ("Yellow triangle", "yellow-triangle"), ("Green diamond", "green-diamond"),
  ("Teal hexagon", "teal-hexagon"), ("Blue star", "blue-star"),
  ("Indigo ring", "indigo-ring"), ("Purple cross", "purple-cross"),
  ("Pink heart", "pink-heart"), ("Brown pentagon", "brown-pentagon"),
  ("Grey moon", "grey-moon"), ("Black arrow", "black-arrow") ]

def patterns : Pack := bundledPack "patterns" "Patterns" [
  ("Stripes", "stripes"), ("Dots", "dots"), ("Checks", "checks"), ("Waves", "waves"),
  ("Zigzag", "zigzag"), ("Grid", "grid"), ("Diamonds", "diamonds"), ("Rings", "rings"),
  ("Triangles", "triangles"), ("Crosses", "crosses"), ("Bricks", "bricks"),
  ("Scales", "scales") ]

/-- The bundled packs, in the order the Packs menu lists them. -/
def bundled : List Pack := [shapes, patterns]

theorem bundled_ok : ∀ p ∈ bundled, p.Ok := by decide

theorem shapes_ok : shapes.Ok := bundled_ok shapes (List.mem_cons_self)

end Pairs
