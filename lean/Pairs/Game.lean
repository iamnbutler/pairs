module

public import Pairs.Deal

/-! # The game

A `Game` is the board: the deal (a face for each position), the faces matched so far, the
positions turned up and not yet matched, and the counts. It knows nothing of packs, images or the
host; `Pairs.Model` puts it in the app.

* **Flip** (`flip`). A card can be turned when it is on the board, not matched, and not already
  up, or when two unmatched cards are showing (a mismatch waiting to turn back). Turning the
  second card of a pair is a move: if the faces agree the face is matched and both stay up; if
  not, both stay up until the host's timer turns them back (`flipBack`), or until the next card
  is turned, which turns them back at once.
* **Matched is by face.** Every face is dealt exactly twice, so a matched face means both its
  cards are matched; nothing can match one without the other.
* **Won** is recorded (`finished`, the time of the last match) when the last face is matched.

What is proved here, for every game `Inv` holds of (every game the app deals, `inv_deal`, and
every game it reaches from one, `inv_flip`, `inv_flipBack`):

* at most two unmatched cards are face up (`Inv.upBound`, `Inv.upValid`);
* a matched card stays matched (`matched_flip`, `matched_flipBack`);
* the game is won exactly when every card is matched (`Inv.wonIff`);
* it can always be won: `solve` turns the cards that win it (`solve_wins`);
* the move count is half the cards turned, rounded down (`Inv.moveCount`). -/

@[expose] public section

namespace Pairs

-- region: game
structure Game where
  /-- The face on each position, in reading order. -/
  deck : List Nat := []
  /-- The faces matched so far. -/
  matched : List Nat := []
  /-- The positions face up and not matched, in the order they were turned: at most two. -/
  up : List Nat := []
  /-- Pairs turned: one for every second card. -/
  moves : Nat := 0
  /-- Cards turned. -/
  flips : Nat := 0
  /-- When the first card was turned (the host's monotonic milliseconds). -/
  started : Option Nat := none
  /-- When the last face was matched: the game is won. -/
  finished : Option Nat := none
deriving Repr, DecidableEq, Inhabited
-- endregion: game

namespace Game

/-- A new game on deal `deck`. -/
def new (deck : List Nat) : Game := { deck }

/-- The face at position `i` (0 off the board). -/
def face (g : Game) (i : Nat) : Nat := g.deck.getD i 0

/-- Whether position `i`'s face is matched. -/
def isMatched (g : Game) (i : Nat) : Bool := g.matched.contains (g.face i)

/-- Whether every card on the board is matched (and there is a board). -/
def allMatched (g : Game) : Bool := !g.deck.isEmpty && g.deck.all (g.matched.contains ·)

/-- Whether the game is won. -/
def won (g : Game) : Bool := g.finished.isSome

/-- Whether position `i` shows its face: matched, or turned up. -/
def faceUp (g : Game) (i : Nat) : Bool := g.isMatched i || g.up.contains i

/-- Two unmatched cards are up: a mismatch, waiting to turn back. -/
def mismatched (g : Game) : Bool := g.up.length == 2

-- region: game-flip
/-- Whether position `k` can be turned: on the board, not matched, and not up, unless two cards
are up (turning a third turns those two back first). -/
def canFlip (g : Game) (k : Nat) : Bool :=
  decide (k < g.deck.length) && !g.isMatched k && (g.up.length == 2 || !g.up.contains k)

/-- Turn position `k` at time `now`. -/
def flip (g : Game) (k now : Nat) : Game :=
  if g.canFlip k then
    let g1 := { g with flips := g.flips + 1, started := some (g.started.getD now) }
    match g.up with
    | [j] =>
      if g.face j = g.face k then
        let g2 := { g1 with moves := g.moves + 1, up := [], matched := g.face k :: g.matched }
        if g2.allMatched then { g2 with finished := some now } else g2
      else { g1 with moves := g.moves + 1, up := [j, k] }
    | _ => { g1 with up := [k] }
  else g

/-- The host's timer: two mismatched cards turn back. -/
def flipBack (g : Game) : Game := if g.up.length = 2 then { g with up := [] } else g
-- endregion: game-flip

/-- Turn the positions `ks` in order, all at time `now`. -/
def flipAll (g : Game) (ks : List Nat) (now : Nat) : Game := ks.foldl (fun g k => g.flip k now) g

/-- The moves of a won game, and how long it took. -/
def score (g : Game) : Option (Nat × Nat) :=
  match g.started, g.finished with
  | some a, some b => some (g.moves, b - a)
  | _, _ => none

/-! ## The invariant -/

-- region: game-inv
/-- What holds of every game the app plays (`inv_deal`, `inv_flip`, `inv_flipBack`). -/
structure Inv (g : Game) : Prop where
  /-- Every face on the board is on exactly two cards. -/
  pairs : ∀ f ∈ g.deck, g.deck.count f = 2
  /-- At most two cards are up and unmatched… -/
  upBound : g.up.length ≤ 2
  /-- …each on the board, unmatched, -/
  upValid : ∀ i ∈ g.up, i < g.deck.length ∧ g.isMatched i = false
  /-- …and distinct. -/
  upNodup : g.up.Nodup
  /-- Two cards up are a mismatch. -/
  upMismatch : ∀ a b, g.up = [a, b] → g.face a ≠ g.face b
  /-- A move is two cards turned: the count is half the cards turned, rounded down. -/
  moveCount : 2 * g.moves + g.up.length % 2 = g.flips
  /-- The game is won exactly when every card is matched. -/
  wonIff : g.won = g.allMatched
-- endregion: game-inv

/-- `Inv` as a check the fuzzer can run. -/
def check (g : Game) : Bool :=
  g.deck.all (fun f => g.deck.count f == 2) && decide (g.up.length ≤ 2) &&
    g.up.all (fun i => decide (i < g.deck.length) && !g.isMatched i) && decide g.up.Nodup &&
    (match g.up with | [a, b] => g.face a != g.face b | _ => true) &&
    decide (2 * g.moves + g.up.length % 2 = g.flips) && g.won == g.allMatched

theorem check_iff (g : Game) : g.check = true ↔ g.Inv := by
  constructor
  · intro h
    simp only [check, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq,
      Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    refine ⟨h1, h2, h3, h4, ?_, h6, h7⟩
    intro a b e
    rw [e] at h5
    simpa only [bne_iff_ne, ne_eq] using h5
  · intro h
    simp only [check, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq,
      Bool.not_eq_true']
    refine ⟨⟨⟨⟨⟨⟨h.pairs, h.upBound⟩, h.upValid⟩, h.upNodup⟩, ?_⟩, h.moveCount⟩, h.wonIff⟩
    split
    · next a b e => simpa only [bne_iff_ne, ne_eq] using h.upMismatch a b e
    · rfl

instance (g : Game) : Decidable g.Inv := decidable_of_iff _ (check_iff g)

/-! ## Lemmas -/

theorem face_eq (g : Game) (i : Nat) (h : i < g.deck.length) : g.face i = g.deck[i] := by
  simp only [face, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem face_mem (g : Game) (i : Nat) (h : i < g.deck.length) : g.face i ∈ g.deck := by
  rw [face_eq g i h]; exact List.getElem_mem h

/-- A game with a card not matched is not all matched. -/
theorem not_allMatched (g : Game) (i : Nat) (h : i < g.deck.length) (hm : g.isMatched i = false) :
    g.allMatched = false := by
  simp only [allMatched, Bool.and_eq_false_iff]
  right
  simp only [List.all_eq_false]
  refine ⟨g.face i, face_mem g i h, ?_⟩
  simp only [isMatched, Bool.not_eq_true] at hm ⊢
  exact hm

/-- Every card is matched exactly when no position on the board is unmatched. -/
theorem allMatched_iff (g : Game) (hne : g.deck ≠ []) :
    g.allMatched = true ↔ ∀ i, i < g.deck.length → g.isMatched i = true := by
  simp only [allMatched, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true]
  constructor
  · intro ⟨_, h⟩ i hi
    exact h _ (face_mem g i hi)
  · intro h
    refine ⟨hne, fun f hf => ?_⟩
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp hf
    have := h i hi
    simp only [isMatched, face_eq g i hi, e] at this
    exact this

/-- In a list where `a` is on two cards, a card holding `a` has another holding `a`. -/
theorem exists_other {l : List Nat} {a : Nat} :
    ∀ (j : Nat), j < l.length → l[j]? = some a → 2 ≤ l.count a →
      ∃ p, p < l.length ∧ p ≠ j ∧ l[p]? = some a := by
  induction l with
  | nil => intro j h; exact absurd h (Nat.not_lt_zero _)
  | cons b t ih =>
    intro j hj hja hc
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hja
      subst hja
      simp only [List.count_cons_self] at hc
      have hm : b ∈ t := List.count_pos_iff.mp (by omega)
      obtain ⟨q, hq, e⟩ := List.mem_iff_getElem.mp hm
      exact ⟨q + 1, by simp only [List.length_cons]; omega, by omega,
        by simp only [List.getElem?_cons_succ, List.getElem?_eq_getElem hq, e]⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hja
      by_cases hb : b = a
      · exact ⟨0, by simp only [List.length_cons]; omega, by omega,
          by simp only [List.getElem?_cons_zero, hb]⟩
      · have hc' : 2 ≤ t.count a := by
          rw [List.count_cons] at hc
          have : (b == a) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact hb
          simp only [this] at hc
          simpa only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using hc
        obtain ⟨p, hp, hpj, e⟩ := ih j (by simp only [List.length_cons] at hj; omega) hja hc'
        exact ⟨p + 1, by simp only [List.length_cons]; omega, by omega,
          by simp only [List.getElem?_cons_succ, e]⟩

/-- Under `Inv`, every card on the board has a partner: another card with its face. -/
theorem partner_exists (g : Game) (h : g.Inv) (j : Nat) (hj : j < g.deck.length) :
    ∃ p, p < g.deck.length ∧ p ≠ j ∧ g.face p = g.face j := by
  have hm := face_mem g j hj
  have hc := h.pairs _ hm
  have hja : g.deck[j]? = some (g.face j) := by rw [face_eq g j hj, List.getElem?_eq_getElem hj]
  obtain ⟨p, hp, hpj, e⟩ := exists_other j hj hja (by omega)
  refine ⟨p, hp, hpj, ?_⟩
  simp only [face, List.getD_eq_getElem?_getD, e, Option.getD_some]

/-! ## Flips keep the invariant -/

theorem upLength (g : Game) (h : g.Inv) : g.up = [] ∨ (∃ j, g.up = [j]) ∨ ∃ a b, g.up = [a, b] := by
  have hb := h.upBound
  match e : g.up with
  | [] => exact Or.inl rfl
  | [j] => exact Or.inr (Or.inl ⟨j, rfl⟩)
  | [a, b] => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
  | _ :: _ :: _ :: _ => rw [e] at hb; simp only [List.length_cons] at hb; omega

theorem flip_noop (g : Game) (k now : Nat) (h : g.canFlip k = false) : g.flip k now = g := by
  simp only [flip, h, Bool.false_eq_true, ↓reduceIte]

/-- The canFlip conditions, unpacked. -/
theorem canFlip_true {g : Game} {k : Nat} (h : g.canFlip k = true) :
    k < g.deck.length ∧ g.isMatched k = false ∧ (g.up.length = 2 ∨ k ∉ g.up) := by
  simp only [canFlip, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.or_eq_true,
    beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  rcases h3 with h3 | h3
  · exact Or.inl h3
  · exact Or.inr fun m => by rw [List.contains_iff_mem.mpr m] at h3; cases h3

-- region: inv-flip
theorem inv_flip (g : Game) (k now : Nat) (h : g.Inv) : (g.flip k now).Inv := by
  by_cases hf : g.canFlip k = true
  · obtain ⟨hk, hkm, hku⟩ := canFlip_true hf
    unfold flip
    simp only [hf, ↓reduceIte]
    split
    · next j e =>
      have hj := h.upValid j (by rw [e]; exact List.mem_singleton_self j)
      have hkj : k ≠ j := by
        rcases hku with hku | hku
        · rw [e] at hku; simp only [List.length_cons, List.length_nil] at hku; omega
        · intro ekj; rw [e, ekj] at hku; exact hku (List.mem_singleton_self j)
      have hmc := h.moveCount
      rw [e] at hmc
      simp only [List.length_cons, List.length_nil] at hmc
      split
      · next hjk =>
        -- a match
        have hw : g.won = false := by rw [h.wonIff]; exact not_allMatched g j hj.1 hj.2
        split
        · next ha =>
          exact { pairs := h.pairs, upBound := by simp only [List.length_nil]; omega,
                  upValid := (fun _ m => nomatch m), upNodup := List.nodup_nil,
                  upMismatch := (fun _ _ e => nomatch e),
                  moveCount := by simp only [List.length_nil]; omega,
                  wonIff := by simp only [won, Option.isSome_some]; exact ha.symm }
        · next ha =>
          exact { pairs := h.pairs, upBound := by simp only [List.length_nil]; omega,
                  upValid := (fun _ m => nomatch m), upNodup := List.nodup_nil,
                  upMismatch := (fun _ _ e => nomatch e),
                  moveCount := by simp only [List.length_nil]; omega,
                  wonIff := by
                    simp only [Bool.not_eq_true] at ha
                    rw [ha]; simp only [won] at hw ⊢; exact hw }
      · next hjk =>
        -- a mismatch
        exact { pairs := h.pairs, upBound := by simp only [List.length_cons, List.length_nil]; omega,
                upValid := by
                  intro i m
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at m
                  rcases m with m | m
                  · subst m; exact ⟨hj.1, by simpa only [isMatched, face] using hj.2⟩
                  · subst m; exact ⟨hk, by simpa only [isMatched, face] using hkm⟩,
                upNodup := by
                  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
                    List.nodup_nil, and_true, not_false_eq_true]
                  exact fun e => hkj e.symm,
                upMismatch := by
                  intro a b e'
                  simp only [List.cons.injEq, and_true] at e'
                  obtain ⟨rfl, rfl⟩ := e'
                  simpa only [face] using hjk,
                moveCount := by simp only [List.length_cons, List.length_nil]; omega,
                wonIff := by simpa only [won, allMatched] using h.wonIff }
    · next hne =>
      have hmc := h.moveCount
      have hlen : g.up.length % 2 = 0 := by
        rcases upLength g h with e | ⟨j, e⟩ | ⟨a, b, e⟩
        · rw [e]; rfl
        · exact absurd e (hne j)
        · rw [e]; simp only [List.length_cons, List.length_nil]
      exact { pairs := h.pairs, upBound := by simp only [List.length_cons, List.length_nil]; omega,
              upValid := by
                intro i m
                simp only [List.mem_cons, List.not_mem_nil, or_false] at m
                subst m; exact ⟨hk, by simpa only [isMatched, face] using hkm⟩,
              upNodup := List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
              upMismatch := (fun _ _ e => nomatch e),
              moveCount := by simp only [List.length_cons, List.length_nil]; omega,
              wonIff := by simpa only [won, allMatched] using h.wonIff }
  · rw [flip_noop g k now (by simpa only [Bool.not_eq_true] using hf)]; exact h
-- endregion: inv-flip

theorem inv_flipBack (g : Game) (h : g.Inv) : g.flipBack.Inv := by
  unfold flipBack
  split
  · next e =>
    have hmc := h.moveCount
    rw [e] at hmc
    exact { pairs := h.pairs, upBound := by simp only [List.length_nil]; omega,
            upValid := (fun _ m => nomatch m), upNodup := List.nodup_nil,
            upMismatch := (fun _ _ e => nomatch e),
            moveCount := by simp only [List.length_nil]; omega,
            wonIff := h.wonIff }
  · exact h

theorem inv_flipAll (g : Game) (now : Nat) : ∀ ks : List Nat, g.Inv → (g.flipAll ks now).Inv
  | [], h => h
  | k :: ks, h => inv_flipAll (g.flip k now) now ks (inv_flip g k now h)

/-- A new game on any deal with every face on exactly two cards. -/
theorem inv_new (deck : List Nat) (hp : ∀ f ∈ deck, deck.count f = 2) (hne : deck ≠ []) :
    (Game.new deck).Inv where
  pairs := hp
  upBound := by simp only [new, List.length_nil]; omega
  upValid := fun _ m => nomatch m
  upNodup := List.nodup_nil
  upMismatch := fun _ _ e => nomatch e
  moveCount := rfl
  wonIff := by
    obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil deck hne
    have := not_allMatched (Game.new deck) (deck.idxOf f) (List.idxOf_lt_length_of_mem hf)
      (by simp only [isMatched, new, List.contains_nil])
    rw [this]; rfl

/-- **The app's deals are games**: a deal of at least one pair satisfies `Inv`. -/
theorem inv_deal (s k : Nat) (hk : 0 < k) : (Game.new (deal s k)).Inv :=
  inv_new _ (fun f hf => by
      rw [count_deal]
      have : f < k := by
        have := (deal_perm s k).mem_iff.mp hf
        simp only [ordered, List.mem_append, List.mem_range, or_self] at this
        exact this
      simp only [this, ↓reduceIte])
    (fun e => by have := length_deal s k; rw [e] at this; simp only [List.length_nil] at this; omega)

/-! ## Matched stays matched -/

-- region: matched-mono
/-- **A flip never unmatches a face.** -/
theorem matched_flip (g : Game) (k now : Nat) : ∀ f ∈ g.matched, f ∈ (g.flip k now).matched := by
  intro f hf
  unfold flip
  dsimp only
  split
  · split
    · split
      · split
        · exact List.mem_cons_of_mem _ hf
        · exact List.mem_cons_of_mem _ hf
      · exact hf
    · exact hf
  · exact hf

theorem matched_flipBack (g : Game) : g.flipBack.matched = g.matched := by
  unfold flipBack; split <;> rfl

theorem deck_flip (g : Game) (k now : Nat) : (g.flip k now).deck = g.deck := by
  unfold flip
  dsimp only
  split
  · split
    · split
      · split <;> rfl
      · rfl
    · rfl
  · rfl

theorem deck_flipBack (g : Game) : g.flipBack.deck = g.deck := by
  unfold flipBack; split <;> rfl
theorem deck_flipAll (g : Game) (now : Nat) : ∀ ks, (g.flipAll ks now).deck = g.deck
  | [] => rfl
  | k :: ks => (deck_flipAll (g.flip k now) now ks).trans (deck_flip g k now)
-- endregion: matched-mono

/-! ## It can always be won -/

/-- How many cards are not matched. -/
def unmatched (g : Game) : Nat := (g.deck.filter fun f => !g.matched.contains f).length

/-- The first position not matched, if any. -/
def firstUnmatched (g : Game) : Option Nat := (List.range g.deck.length).find? fun i => !g.isMatched i

/-- The other position with `j`'s face. -/
def partner (g : Game) (j : Nat) : Nat :=
  ((List.range g.deck.length).find? fun p => p != j && g.face p == g.face j).getD 0

/-- The cards that match one more face: `j`'s partner when one card `j` is up; otherwise the
first unmatched card and its partner. -/
def round (g : Game) : List Nat :=
  match g.up with
  | [j] => [g.partner j]
  | _ => match g.firstUnmatched with
    | some i => [i, g.partner i]
    | none => []

/-- `n` rounds. -/
def rounds (g : Game) (now : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => g.round ++ rounds (g.flipAll g.round now) now n

/-- **The cards that win the game**: a round for every face. -/
def solve (g : Game) (now : Nat) : List Nat := g.rounds now (g.deck.length + 1)

theorem flipAll_append (g : Game) (now : Nat) (a b : List Nat) :
    g.flipAll (a ++ b) now = (g.flipAll a now).flipAll b now := by
  simp only [flipAll, List.foldl_append]

theorem partner_spec (g : Game) (h : g.Inv) (j : Nat) (hj : j < g.deck.length) :
    g.partner j < g.deck.length ∧ g.partner j ≠ j ∧ g.face (g.partner j) = g.face j := by
  obtain ⟨p, hp, hpj, e⟩ := partner_exists g h j hj
  have hs : ((List.range g.deck.length).find? fun p => p != j && g.face p == g.face j).isSome := by
    rw [List.find?_isSome]
    exact ⟨p, List.mem_range.mpr hp, by
      rw [e]; simp only [beq_self_eq_true, Bool.and_true, bne_iff_ne, ne_eq]; exact hpj⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hs
  have hm := List.mem_of_find?_eq_some hq
  have hpq := List.find?_some hq
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hpq
  simp only [partner, hq, Option.getD_some]
  exact ⟨List.mem_range.mp hm, hpq.1, hpq.2⟩

theorem filter_le {l : List Nat} {p q : Nat → Bool} (hpq : ∀ x, q x = true → p x = true) :
    (l.filter q).length ≤ (l.filter p).length := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons c u ihu =>
    cases hc : q c
    · rw [List.filter_cons_of_neg (by rw [hc]; exact Bool.false_ne_true)]
      cases hp : p c
      · rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true)]; exact ihu
      · rw [List.filter_cons_of_pos hp, List.length_cons]; omega
    · rw [List.filter_cons_of_pos hc, List.filter_cons_of_pos (hpq c hc), List.length_cons,
        List.length_cons]
      omega

theorem filter_lt {l : List Nat} {p q : Nat → Bool} (hpq : ∀ x, q x = true → p x = true)
    (a : Nat) (ha : a ∈ l) (hp : p a = true) (hq : q a = false) :
    (l.filter q).length < (l.filter p).length := by
  induction l with
  | nil => cases ha
  | cons b t ih =>
    rcases List.mem_cons.mp ha with e | e
    · subst e
      rw [List.filter_cons_of_neg (by rw [hq]; exact Bool.false_ne_true), List.filter_cons_of_pos hp,
        List.length_cons]
      have := filter_le (l := t) hpq; omega
    · have := ih e
      cases hc : q b
      · rw [List.filter_cons_of_neg (by rw [hc]; exact Bool.false_ne_true)]
        cases hpb : p b
        · rw [List.filter_cons_of_neg (by rw [hpb]; exact Bool.false_ne_true)]; exact this
        · rw [List.filter_cons_of_pos hpb, List.length_cons]; omega
      · rw [List.filter_cons_of_pos hc, List.filter_cons_of_pos (hpq b hc), List.length_cons,
          List.length_cons]
        omega

/-- Matching a face that wasn't matched leaves fewer cards unmatched. -/
theorem unmatched_lt (g g' : Game) (hd : g'.deck = g.deck)
    (hm : ∀ f ∈ g.matched, f ∈ g'.matched) (j : Nat) (hj : j < g.deck.length)
    (hu : g.isMatched j = false) (hn : g.face j ∈ g'.matched) : g'.unmatched < g.unmatched := by
  unfold unmatched
  rw [hd]
  refine filter_lt (fun x hx => ?_) (g.face j) (face_mem g j hj)
    (by simp only [isMatched] at hu; rw [hu]; rfl)
    (by rw [List.contains_iff_mem.mpr hn]; rfl)
  cases hc : g.matched.contains x
  · rfl
  · have hx' : g'.matched.contains x = true := List.contains_iff_mem.mpr (hm x (List.contains_iff_mem.mp hc))
    rw [hx'] at hx; cases hx

/-- One card `j` up: turning its partner matches `j`'s face. -/
theorem flip_partner (g : Game) (h : g.Inv) (j now : Nat) (e : g.up = [j]) :
    g.face j ∈ (g.flip (g.partner j) now).matched := by
  have hj := h.upValid j (by rw [e]; exact List.mem_singleton_self j)
  obtain ⟨hp, hpj, hpf⟩ := partner_spec g h j hj.1
  have hpm : g.isMatched (g.partner j) = false := by
    simp only [isMatched, hpf]; simpa only [isMatched] using hj.2
  have hcf : g.canFlip (g.partner j) = true := by
    simp only [canFlip, hp, decide_true, hpm, Bool.not_false, Bool.true_and, e,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, Bool.false_or,
      List.contains_cons, List.contains_nil, Bool.or_false, Bool.not_eq_true', beq_eq_false_iff_ne,
      ne_eq]
    exact hpj
  unfold flip
  simp only [hcf, ↓reduceIte, e, hpf]
  split
  · exact List.mem_cons_self ..
  · exact List.mem_cons_self ..

/-- **A round matches one more face**, when any card is unmatched. -/
theorem round_progress (g : Game) (h : g.Inv) (now : Nat) (hu : g.allMatched = false)
    (hne : g.deck ≠ []) : (g.flipAll g.round now).unmatched < g.unmatched := by
  have hmono : ∀ (ks : List Nat) (g0 : Game), (∀ f ∈ g0.matched, f ∈ (g0.flipAll ks now).matched) ∧
      (g0.flipAll ks now).deck = g0.deck := by
    intro ks
    induction ks with
    | nil => intro g0; exact ⟨fun _ m => m, rfl⟩
    | cons k ks ih =>
      intro g0
      obtain ⟨a, b⟩ := ih (g0.flip k now)
      exact ⟨fun f m => a f (matched_flip g0 k now f m),
        show ((g0.flip k now).flipAll ks now).deck = g0.deck by rw [b, deck_flip]⟩
  unfold round
  split
  · next j e =>
    have hj := h.upValid j (by rw [e]; exact List.mem_singleton_self j)
    exact unmatched_lt g _ (hmono _ g).2 (hmono _ g).1 j hj.1 hj.2 (flip_partner g h j now e)
  · next hne1 =>
    split
    · next i hi =>
      have hm := List.mem_of_find?_eq_some hi
      have hi' := List.find?_some hi
      simp only [Bool.not_eq_true'] at hi'
      have hil := List.mem_range.mp hm
      -- turn i: it is the one card up
      have hcf : g.canFlip i = true := by
        have hl : g.up.length = 0 ∨ g.up.length = 2 := by
          rcases upLength g h with e | ⟨j, e⟩ | ⟨a, b, e⟩
          · rw [e]; exact Or.inl rfl
          · exact absurd e (hne1 j)
          · rw [e]; exact Or.inr rfl
        rcases hl with hl | hl
        · simp only [canFlip, hil, decide_true, hi', List.length_eq_zero_iff.mp hl, Bool.not_false,
            Bool.true_and, List.contains_nil, Bool.or_true]
        · simp only [canFlip, hil, decide_true, hi', hl, Bool.not_false, Bool.true_and,
            beq_self_eq_true, Bool.true_or]
      have hup : (g.flip i now).up = [i] := by
        unfold flip
        simp only [hcf, ↓reduceIte]
      have g1d : (g.flip i now).deck = g.deck := deck_flip g i now
      have g1f : (g.flip i now).face i = g.face i := by simp only [face, g1d]
      have g1m : (g.flip i now).matched = g.matched := by
        unfold flip
        simp only [hcf, ↓reduceIte]
      have hpartner : (g.flip i now).partner i = g.partner i := by
        simp only [partner, g1d, face]
      have h1 := inv_flip g i now h
      have hfin := flip_partner (g.flip i now) h1 i now hup
      rw [hpartner, g1f] at hfin
      have hall := (hmono [g.partner i] (g.flip i now))
      refine unmatched_lt g (g.flipAll [i, g.partner i] now) ?_ ?_ i hil hi' ?_
      · show ((g.flip i now).flipAll [g.partner i] now).deck = g.deck
        rw [hall.2, g1d]
      · intro f m
        show f ∈ ((g.flip i now).flipAll [g.partner i] now).matched
        exact hall.1 f (by rw [g1m]; exact m)
      · exact hfin
    · next hn =>
      exfalso
      unfold firstUnmatched at hn
      rw [List.find?_eq_none] at hn
      have : g.allMatched = true := (allMatched_iff g hne).mpr fun i hi => by
        have := hn i (List.mem_range.mpr hi)
        simpa only [Bool.not_eq_true', Bool.not_eq_false] using this
      rw [this] at hu; cases hu

theorem unmatched_le (g : Game) : g.unmatched ≤ g.deck.length := by
  unfold unmatched; exact List.length_filter_le _ _

/-- `n` rounds win a game with at most `n` cards unmatched. -/
theorem rounds_win (now : Nat) : ∀ (n : Nat) (g : Game), g.Inv → g.deck ≠ [] → g.unmatched < n →
    (g.flipAll (g.rounds now n) now).allMatched = true
  | 0, _, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, g, h, hne, hn => by
    by_cases hw : g.allMatched = true
    · -- every further round turns nothing
      have hr : ∀ m (g0 : Game), g0.allMatched = true → g0.Inv → g0.deck ≠ [] →
          (g0.flipAll (g0.rounds now m) now) = g0 := by
        intro m
        induction m with
        | zero => intro g0 _ _ _; rfl
        | succ m ihm =>
          intro g0 hw0 h0 hne0
          have hround : g0.round = [] := by
            unfold round
            have hup : g0.up = [] := by
              rcases upLength g0 h0 with e | ⟨j, e⟩ | ⟨a, b, e⟩
              · exact e
              · have := h0.upValid j (by rw [e]; exact List.mem_singleton_self j)
                rw [not_allMatched g0 j this.1 this.2] at hw0; cases hw0
              · have := h0.upValid a (by rw [e]; exact List.mem_cons_self ..)
                rw [not_allMatched g0 a this.1 this.2] at hw0; cases hw0
            rw [hup]
            have hf : g0.firstUnmatched = none := by
              unfold firstUnmatched
              rw [List.find?_eq_none]
              intro i hi
              have := (allMatched_iff g0 hne0).mp hw0 i (List.mem_range.mp hi)
              simp only [this, Bool.not_true, Bool.false_eq_true, not_false_eq_true]
            simp only [hf]
          show g0.flipAll (g0.round ++ rounds (g0.flipAll g0.round now) now m) now = g0
          rw [hround]
          exact ihm g0 hw0 h0 hne0
      rw [hr (n + 1) g hw h hne]; exact hw
    · have hlt := round_progress g h now (by simpa only [Bool.not_eq_true] using hw) hne
      show (g.flipAll (g.round ++ rounds (g.flipAll g.round now) now n) now).allMatched = true
      rw [flipAll_append]
      have h' := inv_flipAll g now g.round h
      have hd : (g.flipAll g.round now).deck = g.deck := deck_flipAll g now _
      exact rounds_win now n _ h' (by rw [hd]; exact hne) (by omega)

-- region: solve-wins
/-- **Every game can be won**: from any game `Inv` holds of, turning `solve`'s cards wins it. -/
theorem solve_wins (g : Game) (now : Nat) (h : g.Inv) (hne : g.deck ≠ []) :
    (g.flipAll (g.solve now) now).won = true := by
  have hi := inv_flipAll g now (g.solve now) h
  rw [hi.wonIff]
  exact rounds_win now _ g h hne (Nat.lt_succ_of_le (unmatched_le g))
-- endregion: solve-wins

end Game

end Pairs
