module

public import CairnJson

/-! # Best scores

Per pack (keyed by `Pack.source`), the fewest moves and the shortest time of any game won with
it, each on its own. They are saved as JSON under the app's Application Support folder and read
back at launch. A pack's best only ever improves: recording a game (`record_le`) or merging what
was read from disk (`merge_le`) never makes a kept best worse, and never forgets one. -/

@[expose] public section

namespace Pairs

open CairnJson

structure Best where
  moves : Nat
  ms : Nat
deriving Repr, DecidableEq, Inhabited

/-- `a` is at least as good as `b` in both. -/
def Best.le (a b : Best) : Prop := a.moves ≤ b.moves ∧ a.ms ≤ b.ms

instance (a b : Best) : Decidable (a.le b) := inferInstanceAs (Decidable (_ ∧ _))

/-- The better of each. -/
def Best.min (a b : Best) : Best := ⟨Nat.min a.moves b.moves, Nat.min a.ms b.ms⟩

theorem Best.min_le_right (a b : Best) : (a.min b).le b :=
  ⟨Nat.min_le_right _ _, Nat.min_le_right _ _⟩

theorem Best.min_le_left (a b : Best) : (a.min b).le a :=
  ⟨Nat.min_le_left _ _, Nat.min_le_left _ _⟩

abbrev Scores := List (String × Best)

def Scores.get (t : Scores) (k : String) : Option Best := t.lookup k

/-- Record a won game: the pack's best becomes the better of what it was and `b`. -/
def Scores.record : Scores → String → Best → Scores
  | [], k, b => [(k, b)]
  | (k', b') :: t, k, b => if k' = k then (k, b'.min b) :: t else (k', b') :: Scores.record t k b

/-- Every entry of `u`, recorded into `t`. -/
def Scores.merge (t u : Scores) : Scores := u.foldl (fun t p => t.record p.1 p.2) t

theorem Scores.get_record (t : Scores) (k : String) (b : Best) :
    ∃ b', (t.record k b).get k = some b' ∧ b'.le b ∧ ∀ old, t.get k = some old → b'.le old := by
  induction t with
  | nil => exact ⟨b, by simp only [record, get, List.lookup, beq_self_eq_true], ⟨Nat.le_refl _, Nat.le_refl _⟩,
      fun _ h => by simp only [get, List.lookup] at h; cases h⟩
  | cons p t ih =>
    obtain ⟨k', b'⟩ := p
    by_cases hk : k' = k
    · subst hk
      refine ⟨b'.min b, by simp only [record, ↓reduceIte, get, List.lookup, beq_self_eq_true],
        Best.min_le_right _ _, fun old h => ?_⟩
      simp only [get, List.lookup, beq_self_eq_true] at h
      cases h
      exact Best.min_le_left _ _
    · have hne : (k == k') = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => hk e.symm
      obtain ⟨c, hc, hcb, hco⟩ := ih
      refine ⟨c, ?_, hcb, fun old h => hco old ?_⟩
      · simp only [record, hk, ↓reduceIte, get, List.lookup, hne]; exact hc
      · simp only [get, List.lookup, hne] at h; exact h

theorem Scores.get_record_ne (t : Scores) (k k2 : String) (b : Best) (h : k ≠ k2) :
    (t.record k b).get k2 = t.get k2 := by
  induction t with
  | nil =>
    have : (k2 == k) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => h e.symm
    simp only [record, get, List.lookup, this]
  | cons p t ih =>
    obtain ⟨k', b'⟩ := p
    by_cases hk : k' = k
    · subst hk
      have : (k2 == k') = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => h e.symm
      simp only [record, ↓reduceIte, get, List.lookup, this]
    · simp only [record, hk, ↓reduceIte, get, List.lookup]
      split
      · rfl
      · exact ih

/-- **Recording a game never makes a pack's best worse or forgets it.** -/
theorem Scores.record_le (t : Scores) (k : String) (b : Best) (k2 : String) (old : Best)
    (h : t.get k2 = some old) : ∃ b', (t.record k b).get k2 = some b' ∧ b'.le old := by
  by_cases hk : k = k2
  · subst hk
    obtain ⟨b', h1, _, h3⟩ := t.get_record k b
    exact ⟨b', h1, h3 old h⟩
  · exact ⟨old, by rw [t.get_record_ne k k2 b hk]; exact h, ⟨Nat.le_refl _, Nat.le_refl _⟩⟩

/-- **Merging scores read from disk never makes a pack's best worse or forgets it.** -/
theorem Scores.merge_le (u t : Scores) (k : String) (old : Best) (h : t.get k = some old) :
    ∃ b', (t.merge u).get k = some b' ∧ b'.le old := by
  induction u generalizing t old with
  | nil => exact ⟨old, h, ⟨Nat.le_refl _, Nat.le_refl _⟩⟩
  | cons p u ih =>
    obtain ⟨b1, h1, l1⟩ := t.record_le p.1 p.2 k old h
    obtain ⟨b2, h2, l2⟩ := ih (t.record p.1 p.2) b1 h1
    exact ⟨b2, h2, ⟨Nat.le_trans l2.1 l1.1, Nat.le_trans l2.2 l1.2⟩⟩

/-! ## On disk -/

def Scores.toJson (t : Scores) : Json :=
  .obj [("version", .int 1),
        ("packs", .arr (t.map fun (k, b) =>
          .obj [("source", .str k), ("moves", .int b.moves), ("ms", .int b.ms)]))]

def Scores.encode (t : Scores) : ByteArray := (CairnJson.pretty t.toJson).toUTF8

/-- A non-negative whole number. -/
def natOf (j : Json) : Option Nat := j.getInt >>= fun n => if n < 0 then none else some n.toNat

def entryOf (j : Json) : Option (String × Best) := do
  let k ← j.field "source" >>= Json.getStr
  let m ← j.field "moves" >>= natOf
  let t ← j.field "ms" >>= natOf
  pure (k, ⟨m, t⟩)

/-- The scores in a file; entries it can't read are skipped, and a file that isn't scores
reads as none. -/
def Scores.decode (d : ByteArray) : Scores :=
  match decodeBytes d >>= (·.field "packs") >>= Json.getArr with
  | some xs => xs.filterMap entryOf
  | none => []

end Pairs
