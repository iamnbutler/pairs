module

public import Pairs.Model

/-! # What the model keeps

Lemmas about the plans of `Pairs.Model`, for the claims in `Pairs.Claims`:

* `BoardOk`: the pack is usable, the game deals `pack.pairs` distinct faces of it, the deal is a
  permutation of every face twice, and the game's `Inv` holds; and a pack being loaded is usable.
  Every plan keeps it (`boardOk_go`).
* Each plan either leaves the board alone or deals a new game (`Settled`), and a flip or a
  mismatch turning back never unmatches a face.
* Scores only improve (`ScoresMono`).
* A reply changes the board only when it is an image reply that completes the pack being loaded,
  to a request made since that load began (`reply_board`). -/

@[expose] public section

namespace Pairs

open Cairn Reqs

/-! ## The board is always a game -/

/-- A pack being loaded is usable. -/
def LoadOk (c : Core) : Prop :=
  ∀ l, c.loading = some l → ∀ p seen, l.stage = .images p seen → p.Ok

structure BoardOk (c : Core) : Prop where
  pack : c.pack.Ok
  chosen : c.chosen.length = c.pack.pairs
  chosenIn : ∀ i ∈ c.chosen, i < c.pack.faces.length
  chosenNodup : c.chosen.Nodup
  dealt : c.game.deck.Perm (ordered c.pack.pairs)
  inv : c.game.Inv
  load : LoadOk c

/-- `LoadOk`, computed. -/
def loadCheck (c : Core) : Bool :=
  match c.loading with
  | some { stage := .images p _, .. } => decide p.Ok
  | _ => true

theorem loadCheck_iff (c : Core) : loadCheck c = true ↔ LoadOk c := by
  unfold loadCheck LoadOk
  split
  · next l p seen e =>
    simp only [decide_eq_true_eq]
    constructor
    · intro h l' hl p' seen' hs
      rw [e] at hl
      cases hl
      cases hs
      exact h
    · intro h
      exact h _ e p seen rfl
  · next h =>
    simp only [true_iff]
    intro l hl p seen hs
    obtain ⟨a, b, d, st⟩ := l
    simp only at hs
    subst hs
    exact (h a b d p seen hl).elim

instance (c : Core) : Decidable (LoadOk c) := decidable_of_iff _ (loadCheck_iff c)

instance (c : Core) : Decidable (BoardOk c) :=
  decidable_of_iff (c.pack.Ok ∧ c.chosen.length = c.pack.pairs ∧
      (∀ i ∈ c.chosen, i < c.pack.faces.length) ∧ c.chosen.Nodup ∧
      c.game.deck.Perm (ordered c.pack.pairs) ∧ c.game.Inv ∧ LoadOk c)
    ⟨fun ⟨a, b, d, e, f, g, h⟩ => ⟨a, b, d, e, f, g, h⟩,
     fun ⟨a, b, d, e, f, g, h⟩ => ⟨a, b, d, e, f, g, h⟩⟩

theorem chooseFaces_length (seed n k : Nat) (h : k ≤ n) : (chooseFaces seed n k).length = k := by
  simp only [chooseFaces, List.length_take, (shuffle_perm seed (List.range n)).length_eq,
    List.length_range]
  omega

theorem chooseFaces_lt (seed n k : Nat) : ∀ i ∈ chooseFaces seed n k, i < n := by
  intro i hi
  have := (shuffle_perm seed (List.range n)).subset (List.mem_of_mem_take hi)
  exact List.mem_range.mp this

theorem chooseFaces_nodup (seed n k : Nat) : (chooseFaces seed n k).Nodup :=
  ((shuffle_perm seed (List.range n)).nodup_iff.mpr List.nodup_range).sublist (List.take_sublist _ _)

theorem boardOk_dealt (c : Core) (p : Pack) (seed : Nat) (hp : p.Ok) (hl : LoadOk c) :
    BoardOk (c.dealt p seed) where
  pack := hp
  chosen := chooseFaces_length _ _ _ hp.le
  chosenIn := chooseFaces_lt _ _ _
  chosenNodup := chooseFaces_nodup _ _ _
  dealt := deal_perm _ _
  inv := Game.inv_deal _ _ (by have := hp.two; omega)
  load := hl

/-- A core with the same board and pack loading keeps `BoardOk`. -/
theorem boardOk_of {c c' : Core} (h : BoardOk c) (hb : c'.board = c.board)
    (hl : LoadOk c') : BoardOk c' := by
  simp only [Core.board, Prod.mk.injEq] at hb
  obtain ⟨h1, h2, h3⟩ := hb
  exact ⟨h1 ▸ h.pack, h1 ▸ h2 ▸ h.chosen, h1 ▸ h2 ▸ h.chosenIn, h2 ▸ h.chosenNodup,
    h1 ▸ h3 ▸ h.dealt, h3 ▸ h.inv, hl⟩

/-- Same board, game changed by `f`, which keeps the deck and `Inv`. -/
theorem boardOk_game {c c' : Core} (h : BoardOk c) (hp : c'.pack = c.pack) (hc : c'.chosen = c.chosen)
    (hd : c'.game.deck = c.game.deck) (hi : c'.game.Inv) (hl : LoadOk c') : BoardOk c' :=
  ⟨hp ▸ h.pack, hp ▸ hc ▸ h.chosen, hp ▸ hc ▸ h.chosenIn, hc ▸ h.chosenNodup,
    hp ▸ hd ▸ h.dealt, hi, hl⟩

theorem loadOk_none (c : Core) (h : c.loading = none) : LoadOk c :=
  fun l hl => by rw [h] at hl; cases hl

theorem loadOk_same {c c' : Core} (h : LoadOk c) (e : c'.loading = c.loading) : LoadOk c' :=
  fun l hl => h l (e ▸ hl)

/-! ## Each plan -/

/-- What a plan keeps: the board ok, the board itself unless it deals (counting the deal), and
matched faces within a game. -/
def Settled (c c' : Core) : Prop :=
  BoardOk c' ∧ (c'.deals = c.deals → c'.board = c.board ∨
    (c'.pack = c.pack ∧ c'.chosen = c.chosen ∧ ∀ f ∈ c.game.matched, f ∈ c'.game.matched))

/-- A plan that leaves the board alone. -/
theorem settled_calm {c c' : Core} (h : BoardOk c) (hb : c'.board = c.board) (hl : LoadOk c') :
    Settled c c' :=
  ⟨boardOk_of h hb hl, fun _ => Or.inl hb⟩

theorem settled_dealt (c : Core) (p : Pack) (seed : Nat) (hp : p.Ok) (hl : LoadOk c) :
    Settled c (c.dealt p seed) :=
  ⟨boardOk_dealt c p seed hp hl, fun e => by simp only [Core.dealt] at e; omega⟩

theorem settled_dealt' (c c' : Core) (p : Pack) (seed : Nat) (hp : p.Ok) (hl : LoadOk c')
    (hd : c'.deals = c.deals) : Settled c (c'.dealt p seed) :=
  ⟨boardOk_dealt c' p seed hp hl, fun e => by simp only [Core.dealt] at e; omega⟩

theorem settled_dealPlan (c : Core) (r : Reqs) (p : Pack) (hp : p.Ok) (hl : LoadOk c) :
    Settled c (dealPlan p c r).1 :=
  settled_dealt c p c.seed hp hl

theorem settled_flip (c : Core) (r : Reqs) (k : Nat) (h : BoardOk c) :
    Settled c (flipPlan k c r).1 := by
  have key : ∀ c' : Core, c'.pack = c.pack → c'.chosen = c.chosen → c'.loading = c.loading →
      c'.game = c.game.flip k c.now → Settled c c' := fun c' hp hc hl hg =>
    ⟨boardOk_game h hp hc (by rw [hg, Game.deck_flip]) (hg ▸ Game.inv_flip _ _ _ h.inv)
        (loadOk_same h.load hl),
      fun _ => Or.inr ⟨hp, hc, fun f hf => hg ▸ Game.matched_flip _ _ _ f hf⟩⟩
  unfold flipPlan
  split
  · dsimp only
    split
    · split
      · exact key _ rfl rfl rfl rfl
      · exact key _ rfl rfl rfl rfl
    · exact key _ rfl rfl rfl rfl
  · exact settled_calm h rfl h.load

theorem settled_flipBack (c : Core) (r : Reqs) (h : BoardOk c) : Settled c (flipBackPlan c r).1 :=
  ⟨boardOk_game h rfl rfl (Game.deck_flipBack _) (Game.inv_flipBack _ h.inv) h.load,
    fun _ => Or.inr ⟨rfl, rfl, fun f hf => by
      simp only [flipBackPlan, Game.matched_flipBack]; exact hf⟩⟩

theorem settled_startLoad (c : Core) (r : Reqs) (src : String) (st : Stage) (h : BoardOk c)
    (hst : ∀ p seen, st = .images p seen → p.Ok) : Settled c (startLoad c r src st).1 :=
  settled_calm h rfl (fun l hl p seen hs => by
    simp only [startLoad, Option.some.injEq] at hl
    subst hl
    exact hst p seen hs)

theorem settled_openTyped (c : Core) (r : Reqs) (h : BoardOk c) :
    Settled c (openTypedPlan c r).1 := by
  unfold openTypedPlan
  dsimp only
  split
  · exact settled_calm h rfl h.load
  · exact settled_startLoad _ _ _ _ h (fun _ _ e => nomatch e)

theorem settled_openBundled (c : Core) (r : Reqs) (k : Nat) (h : BoardOk c) :
    Settled c (openBundledPlan k c r).1 := by
  unfold openBundledPlan
  split
  · next p hp =>
    exact settled_startLoad _ _ _ _ h (fun p' _ e => by
      cases e; exact bundled_ok p (List.mem_of_getElem? hp))
  · exact settled_calm h rfl h.load

theorem settled_openFound (c : Core) (r : Reqs) (k : Nat) (h : BoardOk c) :
    Settled c (openFoundPlan k c r).1 := by
  unfold openFoundPlan
  split
  · dsimp only
    split
    · exact settled_calm h rfl h.load
    · exact settled_startLoad _ _ _ _ h (fun _ _ e => nomatch e)
  · exact settled_calm h rfl h.load

theorem settled_cancelLoad (c : Core) (r : Reqs) (h : BoardOk c) :
    Settled c (cancelLoadPlan c r).1 :=
  settled_calm h rfl (loadOk_none _ rfl)

theorem settled_edit (c : Core) (r : Reqs) (op : TextOp) (h : BoardOk c) :
    Settled c (editPlan op c r).1 :=
  settled_calm h rfl h.load

theorem settled_list (c : Core) (r : Reqs) (h : BoardOk c) : Settled c (listPlan c r).1 :=
  settled_calm h rfl h.load

theorem settled_reveal (c : Core) (r : Reqs) (h : BoardOk c) : Settled c (revealPlan c r).1 :=
  settled_calm h rfl h.load

theorem settled_newGame (c : Core) (r : Reqs) (h : BoardOk c) :
    Settled c (dealPlan c.pack c r).1 :=
  settled_dealPlan c r c.pack h.pack h.load

/-! ## Replies -/

theorem settled_onManifest (c : Core) (r : Reqs) (id n : Nat) (rep : Reply) (h : BoardOk c) :
    Settled c (onManifest id n rep c r).1 := by
  unfold onManifest
  split
  · next l hl =>
    split
    · next w hs =>
      split
      · split
        · next p hp =>
          refine settled_calm h rfl (fun l' hl' p' seen e => ?_)
          simp only [Option.some.injEq] at hl'
          subst hl'
          simp only [Stage.images.injEq] at e
          obtain ⟨rfl, -⟩ := e
          cases hb : manifestData w rep with
          | error _ => rw [hb] at hp; cases hp
          | ok d =>
            rw [hb] at hp
            exact parse_ok hp
        · exact settled_calm h rfl (loadOk_none _ rfl)
      · exact settled_calm h rfl h.load
    · exact settled_calm h rfl h.load
  · exact settled_calm h rfl h.load

theorem settled_onImage (c : Core) (r : Reqs) (id : Nat) (rep : Reply) (h : BoardOk c) :
    Settled c (onImage id rep c r).1 := by
  unfold onImage
  split
  · next src l _ hl =>
    split
    · next p seen hs =>
      split
      · split
        · dsimp only
          generalize (if seen.contains src then seen else src :: seen) = seen'
          split
          · exact settled_dealt' c _ p _ (h.load l hl p seen hs) (loadOk_none _ rfl) rfl
          · refine settled_calm h rfl (fun l' hl' p' seen' e => ?_)
            simp only [Option.some.injEq] at hl'
            subst hl'
            simp only [Stage.images.injEq] at e
            obtain ⟨rfl, -⟩ := e
            exact h.load l hl p seen hs
        · exact settled_calm h rfl (loadOk_none _ rfl)
        · exact settled_calm h rfl (loadOk_none _ rfl)
      · exact settled_calm h rfl h.load
    · exact settled_calm h rfl h.load
  · exact settled_calm h rfl h.load

theorem settled_onScores (c : Core) (r : Reqs) (id : Nat) (rep : Reply) (h : BoardOk c) :
    Settled c (onScores id rep c r).1 :=
  settled_calm h rfl h.load

theorem settled_onList (c : Core) (r : Reqs) (id : Nat) (rep : Reply) (h : BoardOk c) :
    Settled c (onList id rep c r).1 :=
  settled_calm h rfl h.load

theorem settled_onReply (c : Core) (r : Reqs) (id : Nat) (rep : Reply) (h : BoardOk c) :
    Settled c (onReply id rep c r).1 := by
  unfold onReply
  split
  · exact settled_onManifest c r id _ rep h
  · exact settled_onScores c r id rep h
  · exact settled_onList c r id rep h
  · exact settled_calm h rfl h.load
  · exact settled_onImage c r id rep h

theorem settled_onEvicted (c : Core) (r : Reqs) (src : String) (h : BoardOk c) :
    Settled c (onEvicted src c r).1 :=
  settled_calm h rfl h.load

theorem settled_onClock (c : Core) (r : Reqs) (t : Time) (h : BoardOk c) :
    Settled c (onClock t c r).1 := by
  unfold onClock
  dsimp only
  split
  · exact settled_calm h rfl h.load
  · split
    · exact settled_dealt' c _ c.pack _ h.pack h.load rfl
    · exact settled_calm h rfl h.load

/-! ## Scores only improve -/

/-- Every best `c` keeps is kept by `c'`, as good or better. -/
def ScoresMono (c c' : Core) : Prop :=
  ∀ k old, c.scores.get k = some old → ∃ b, c'.scores.get k = some b ∧ b.le old

theorem mono_eq {c c' : Core} (e : c'.scores = c.scores) : ScoresMono c c' :=
  fun _ old h => ⟨old, e ▸ h, ⟨Nat.le_refl _, Nat.le_refl _⟩⟩

theorem mono_flip (c : Core) (r : Reqs) (k : Nat) : ScoresMono c (flipPlan k c r).1 := by
  unfold flipPlan
  split
  · dsimp only
    split
    · split
      · exact fun k2 old h => Scores.record_le _ _ _ k2 old h
      · exact mono_eq rfl
    · exact mono_eq rfl
  · exact mono_eq rfl

theorem mono_onImage (c : Core) (r : Reqs) (id : Nat) (rep : Reply) :
    ScoresMono c (onImage id rep c r).1 := by
  unfold onImage
  split
  · next src l _ hl =>
    split
    · next p seen hs =>
      split
      · split
        · dsimp only
          generalize (if seen.contains src then seen else src :: seen) = seen'
          split
          · exact mono_eq rfl
          · exact mono_eq rfl
        · exact mono_eq rfl
        · exact mono_eq rfl
      · exact mono_eq rfl
    · exact mono_eq rfl
  · exact mono_eq rfl

theorem mono_onManifest (c : Core) (r : Reqs) (id n : Nat) (rep : Reply) :
    ScoresMono c (onManifest id n rep c r).1 := by
  unfold onManifest
  split
  · split
    · split
      · split
        · exact mono_eq rfl
        · exact mono_eq rfl
      · exact mono_eq rfl
    · exact mono_eq rfl
  · exact mono_eq rfl

theorem mono_onReply (c : Core) (r : Reqs) (id : Nat) (rep : Reply) :
    ScoresMono c (onReply id rep c r).1 := by
  unfold onReply
  split
  · exact mono_onManifest c r id _ rep
  · exact fun k old h => Scores.merge_le _ _ k old h
  · exact mono_eq rfl
  · exact mono_eq rfl
  · exact mono_onImage c r id rep

theorem mono_onClock (c : Core) (r : Reqs) (t : Time) : ScoresMono c (onClock t c r).1 := by
  unfold onClock
  dsimp only
  split
  · exact mono_eq rfl
  · split
    · exact mono_eq rfl
    · exact mono_eq rfl

theorem mono_startLoad (c : Core) (r : Reqs) (src : String) (st : Stage) :
    ScoresMono c (startLoad c r src st).1 := mono_eq rfl

theorem mono_openTyped (c : Core) (r : Reqs) : ScoresMono c (openTypedPlan c r).1 := by
  unfold openTypedPlan
  dsimp only
  split
  · exact mono_eq rfl
  · exact mono_eq rfl

theorem mono_openBundled (c : Core) (r : Reqs) (k : Nat) : ScoresMono c (openBundledPlan k c r).1 := by
  unfold openBundledPlan
  split
  · exact mono_eq rfl
  · exact mono_eq rfl

theorem mono_openFound (c : Core) (r : Reqs) (k : Nat) : ScoresMono c (openFoundPlan k c r).1 := by
  unfold openFoundPlan
  split
  · dsimp only
    split
    · exact mono_eq rfl
    · exact mono_eq rfl
  · exact mono_eq rfl

/-! ## Replies and the board -/

/-- A reply that completes the pack being loaded: an image, to a request made since the load
began. -/
def Completes (c : Core) (id : Nat) (rep : Reply) : Prop :=
  ∃ l p seen w h, c.loading = some l ∧ l.stage = .images p seen ∧ l.since ≤ id ∧ rep = .image w h

theorem board_onManifest (c : Core) (r : Reqs) (id n : Nat) (rep : Reply) :
    (onManifest id n rep c r).1.board = c.board := by
  unfold onManifest
  split
  · split
    · split
      · split
        · rfl
        · rfl
      · rfl
    · rfl
  · rfl

theorem board_onImage (c : Core) (r : Reqs) (id : Nat) (rep : Reply) :
    (onImage id rep c r).1.board = c.board ∨ Completes c id rep := by
  unfold onImage
  split
  · next src l _ hl =>
    split
    · next p seen hs =>
      split
      · next hc =>
        split
        · next w hh =>
          exact Or.inr ⟨l, p, seen, w, hh, hl, hs, hc.1, rfl⟩
        · exact Or.inl rfl
        · exact Or.inl rfl
      · exact Or.inl rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

theorem board_onReply (c : Core) (r : Reqs) (id : Nat) (rep : Reply) :
    (onReply id rep c r).1.board = c.board ∨ Completes c id rep := by
  unfold onReply
  split
  · exact Or.inl (board_onManifest c r id _ rep)
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact board_onImage c r id rep

/-! ## Through `go` -/

theorem go_core (s : State) (f : Plan) : (s.go f).1.core = (f s.core s.reqs).1 := rfl

theorem go_ok (s : State) (f : Plan) (h : s.reqs.Ok) : (s.go f).1.reqs.Ok :=
  run_ok (run_ok h _) _

/-- **A reply changes the board only by completing the pack being loaded**: an image reply to a
request made since that load began. A late reply to a cancelled request, to anything asked for
before the load began, a failure or a manifest that doesn't parse never does. -/
theorem reply_board (s : State) (id : Nat) (rep : Reply) :
    (s.receive (.reply id rep)).1.core.board = s.core.board ∨ Completes s.core id rep := by
  simp only [State.receive]
  split
  · exact board_onReply _ _ id rep
  · exact Or.inl rfl

/-- **A reply to a request the app isn't waiting for changes nothing**: a late reply to a
cancelled request (the runtime drops those anyway), or a duplicate. -/
theorem reply_stale (s : State) (id : Nat) (rep : Reply) (h : s.reqs.isLive id = false) :
    s.receive (.reply id rep) = (s, []) := by
  simp only [State.receive, h, Bool.false_eq_true, ↓reduceIte]

end Pairs
