module

/-! # The deal

A game deals `k` pairs: faces `0 … k-1`, each twice, shuffled by a seed the host supplies (the
clock's reading when the game starts, `Pairs.Model`). The shuffle draws each position in turn
from the cards not yet placed, so whatever the seed, the deal is a permutation of
`range k ++ range k` (`deal_perm`) and every face is there exactly twice (`count_deal`).

The generator is a 64-bit linear congruential generator (Knuth's MMIX constants); its quality
only matters to how the game feels, not to anything proved. -/

@[expose] public section

namespace Pairs

/-- The next state of the generator. -/
def nextSeed (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- A draw below `n` from state `s`, from its high bits. -/
def draw (s n : Nat) : Nat := (s / 2 ^ 33) % n

/-- Take the element at index `j` out of a list: it, and the list without it. -/
def pick {α : Type} [Inhabited α] : Nat → List α → α × List α
  | _, [] => (default, [])
  | 0, a :: l => (a, l)
  | j + 1, a :: l => let r := pick j l; (r.1, a :: r.2)

theorem pick_perm {α : Type} [Inhabited α] : ∀ (j : Nat) (l : List α), j < l.length →
    List.Perm ((pick j l).1 :: (pick j l).2) l
  | _, [], h => absurd h (Nat.not_lt_zero _)
  | 0, a :: l, _ => List.Perm.refl _
  | j + 1, a :: l, h => by
    have ih := pick_perm j l (by simp only [List.length_cons] at h; omega)
    show List.Perm ((pick j l).1 :: a :: (pick j l).2) (a :: l)
    exact (List.Perm.swap a (pick j l).1 (pick j l).2).trans (List.Perm.cons a ih)

theorem pick_length {α : Type} [Inhabited α] : ∀ (j : Nat) (l : List α), j < l.length →
    (pick j l).2.length + 1 = l.length := by
  intro j l h
  have := (pick_perm j l h).length_eq
  simp only [List.length_cons] at this
  exact this

/-- Shuffle `l` from seed `s`: draw a position among the cards left, place that card, go on with
the next seed. `fuel` bounds the recursion; `shuffle` gives it the list's length. -/
def shuffleAux {α : Type} [Inhabited α] : Nat → Nat → List α → List α
  | 0, _, l => l
  | _ + 1, _, [] => []
  | fuel + 1, s, a :: l =>
    let r := pick (draw s (l.length + 1)) (a :: l)
    r.1 :: shuffleAux fuel (nextSeed s) r.2

def shuffle {α : Type} [Inhabited α] (s : Nat) (l : List α) : List α := shuffleAux l.length s l

theorem shuffleAux_perm {α : Type} [Inhabited α] :
    ∀ (fuel s : Nat) (l : List α), List.Perm (shuffleAux fuel s l) l
  | 0, _, l => List.Perm.refl l
  | _ + 1, _, [] => List.Perm.refl []
  | fuel + 1, s, a :: l => by
    have hj : draw s (l.length + 1) < (a :: l).length := by
      simp only [draw, List.length_cons]; exact Nat.mod_lt _ (Nat.succ_pos _)
    show List.Perm ((pick _ (a :: l)).1 :: shuffleAux fuel (nextSeed s) (pick _ (a :: l)).2) (a :: l)
    exact (List.Perm.cons _ (shuffleAux_perm fuel (nextSeed s) _)).trans (pick_perm _ _ hj)

/-- **A shuffle is a permutation**, whatever the seed. -/
theorem shuffle_perm {α : Type} [Inhabited α] (s : Nat) (l : List α) : List.Perm (shuffle s l) l :=
  shuffleAux_perm _ _ _

/-- The cards before shuffling: every face below `k`, twice. -/
def ordered (k : Nat) : List Nat := List.range k ++ List.range k

-- region: deal
/-- The deal of `k` pairs from seed `s`. -/
def deal (s k : Nat) : List Nat := shuffle s (ordered k)

/-- **The deal is a permutation** of every face below `k`, twice. -/
theorem deal_perm (s k : Nat) : List.Perm (deal s k) (ordered k) := shuffle_perm s _

/-- **Every face is dealt exactly twice**: a face below `k` is on two cards, any other on none. -/
theorem count_deal (s k f : Nat) : (deal s k).count f = if f < k then 2 else 0 := by
  rw [(deal_perm s k).count_eq, ordered, List.count_append]
  by_cases h : f < k
  · have : (List.range k).count f = 1 :=
      List.nodup_range.count_of_mem (List.mem_range.mpr h)
    simp only [this, h, ↓reduceIte]
  · have : (List.range k).count f = 0 :=
      List.count_eq_zero_of_not_mem (fun m => h (List.mem_range.mp m))
    simp only [this, h, ↓reduceIte]
-- endregion: deal

theorem length_deal (s k : Nat) : (deal s k).length = 2 * k := by
  rw [(deal_perm s k).length_eq, ordered, List.length_append, List.length_range]; omega

end Pairs
