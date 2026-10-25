module

public import Pairs.Proofs
public import Pairs.View
meta import Cairn.Claims.Elab

/-! # Pairs's claims

| Id | Kind | What |
|---|---|---|
| ^1 | place | the window: the board, the pack field, New Game |
| ^2 | move, keyed | turn a card |
| ^3 | move | New Game (window) |
| ^4 | move | the pack field: type a folder or URL; Enter opens it |
| ^5 | move | Cancel a pack that is loading |
| ^6 | place | the menu bar item's menu |
| ^7 | place | the Packs submenu, in ^6 |
| ^8 | move | open the menu (looks in the packs folder again) |
| ^9 | move | New Game (menu) |
| ^10 | move, keyed | a bundled pack |
| ^11 | move, keyed | a pack in the packs folder |
| ^12 | move | Open Packs Folder |
| ^20 | invariant | the board is a deal of the pack: every face twice |
| ^21 | invariant | at most two unmatched cards face up |
| ^22 | invariant | won exactly when every card is matched |
| ^23 | invariant | the game can always be won |
| ^24 | invariant | moves count pairs turned |
| ^25 | invariant | a matched card stays matched for the rest of its game |
| ^26 | invariant | best scores only improve |
| ^27 | invariant | no request is lost |
| ^28 | invariant | a reply to a request not waited for changes nothing |
| ^29 | invariant | a reply changes the board only by completing the pack being loaded |
| ^30–^32 | flow | find a pair; a mismatch; win the first game |
-/

@[expose] public section

namespace Pairs
open Cairn Cairn.Claims Reqs

/-! ## Places -/

place ^1 window "Pairs window" where
  does "The game's window: the pack's name and the counters, the cards in a grid, the field to open a pack from a folder or an https URL, and New Game; when the game is won, the result and New Game in place of the grid."

place ^6 menu "Pairs menu" where
  does "The menu of Pairs's menu bar item: New Game, the Packs submenu and Open Packs Folder."

place ^7 packsMenu "Packs submenu" in ^6 where
  does "The packs Pairs can open: the bundled ones, then each folder in the packs folder; the pack being played is checked."

/-! ## Moves -/

theorem flipPlan_game (c : Core) (r : Reqs) (k : Nat) (h : c.game.canFlip k = true) :
    (flipPlan k c r).1.game = c.game.flip k c.now := by
  unfold flipPlan
  simp only [h, ↓reduceIte]
  split
  · split <;> rfl
  · rfl

theorem flipPlan_pack (c : Core) (r : Reqs) (k : Nat) : (flipPlan k c r).1.pack = c.pack := by
  unfold flipPlan
  split
  · dsimp only
    split
    · split <;> rfl
    · rfl
  · rfl

move ^2 flipMove (s : State) (k : Nat) "Turn a card" in ^1 where
  does "Click a face-down card."
  sees "The card turns face up. If it is the second card turned and the faces match, both stay up; if they don't, both turn back after a second, or at once when a third card is turned. A turned pair counts a move; the last match wins the game."
  enabled := s.core.game.canFlip k
  on press
    emit := s.go (flipPlan k)
    post s' := s'.core.game = s.core.game.flip k s.core.now ∧ s'.core.pack = s.core.pack
    sound := by
      intro s k h
      exact ⟨flipPlan_game s.core s.reqs k h, flipPlan_pack s.core s.reqs k⟩

move ^3 newGame (s : State) "New Game" in ^1 where
  does "Press New Game."
  sees "A new game of the same pack: the cards dealt again, face down, the moves and time back to zero."
  on press
    emit := s.go (dealPlan s.core.pack)
    post s' := s'.core.pack = s.core.pack ∧ s'.core.deals = s.core.deals + 1 ∧
      s'.core.game.moves = 0 ∧ s'.core.game.matched = []
    sound := by intro s; exact ⟨rfl, rfl, rfl, rfl⟩

theorem board_startLoad (c : Core) (r : Reqs) (src : String) (st : Stage) :
    (startLoad c r src st).1.board = c.board := rfl

theorem board_openTyped (c : Core) (r : Reqs) : (openTypedPlan c r).1.board = c.board := by
  unfold openTypedPlan
  dsimp only
  split <;> rfl

move ^4 packField (s : State) "Open a pack" in ^1 where
  does "Type a folder (/… or ~/…) or an https:// URL into the pack field, and press Enter."
  sees "The text appears in the field. On Enter, the pack starts loading beside the game, and any pack still loading stops; the game goes on until every image of the new pack has loaded, then a new game of it is dealt. A path or URL that can't be used, a pack.json that doesn't parse, or an image that fails says what went wrong and leaves the game as it was."
  on edit (op : TextOp)
    emit := s.go (editPlan op)
    post s' := s'.core.field = (Text.Field.apply op s.core.field).1 ∧ s'.core.board = s.core.board
    sound := by intro s op; exact ⟨rfl, rfl⟩
  on submit
    emit := s.go openTypedPlan
    post s' := s'.core.board = s.core.board ∧ (s'.core.loading.isSome ∨ s'.core.problem.isSome)
    sound := by
      intro s
      refine ⟨board_openTyped _ _, ?_⟩
      show ((openTypedPlan s.core s.reqs).1.loading.isSome ∨
        (openTypedPlan s.core s.reqs).1.problem.isSome)
      unfold openTypedPlan
      dsimp only
      split
      · exact Or.inr rfl
      · exact Or.inl rfl

move ^5 cancelLoad (s : State) "Cancel loading" in ^1 where
  does "While a pack is loading, press Cancel."
  sees "The pack stops loading: its requests are cancelled, and the game goes on."
  enabled := s.core.loading.isSome
  on press
    emit := s.go cancelLoadPlan
    post s' := s'.core.loading = none ∧ s'.core.board = s.core.board
    sound := by intro s _; exact ⟨rfl, rfl⟩

move ^8 openMenu (s : State) "Open the menu" in ^6 where
  does "Click Pairs's menu bar item."
  sees "The menu opens; Pairs looks in the packs folder again, and the Packs submenu lists what it finds. The game doesn't change."
  on press
    emit := s.go listPlan
    post s' := s'.core.board = s.core.board
    sound := by intro s; rfl

move ^9 menuNewGame (s : State) "New Game" in ^6 where
  does "Choose New Game."
  sees "A new game of the same pack, as New Game in the window."
  on press
    emit := s.go (dealPlan s.core.pack)
    post s' := s'.core.pack = s.core.pack ∧ s'.core.deals = s.core.deals + 1 ∧
      s'.core.game.moves = 0 ∧ s'.core.game.matched = []
    sound := by intro s; exact ⟨rfl, rfl, rfl, rfl⟩

theorem loading_openBundled (c : Core) (r : Reqs) (k : Nat) (p : Pack) (h : bundled[k]? = some p) :
    ∃ l, (openBundledPlan k c r).1.loading = some l ∧ l.source = p.source ∧ l.since = r.next := by
  simp only [openBundledPlan, h, startLoad]
  exact ⟨_, rfl, rfl, rfl⟩

move ^10 bundledMove (s : State) (k : Nat) "A bundled pack" in ^7 where
  does "Choose a bundled pack (Shapes, Patterns) in the Packs submenu."
  sees "The pack loads beside the game, stopping any pack still loading; then a new game of it is dealt."
  enabled := decide (k < bundled.length)
  on press
    emit := s.go (openBundledPlan k)
    post s' := s'.core.board = s.core.board ∧ ∀ p, bundled[k]? = some p →
      ∃ l, s'.core.loading = some l ∧ l.source = p.source ∧ l.since = s.reqs.next
    sound := by
      intro s k _
      refine ⟨?_, fun p h => loading_openBundled s.core s.reqs k p h⟩
      show (openBundledPlan k s.core s.reqs).1.board = s.core.board
      unfold openBundledPlan
      split <;> rfl

move ^11 foundMove (s : State) (k : Nat) "A pack in the packs folder" in ^7 where
  does "Choose a pack listed from the packs folder (~/Library/Application Support/Pairs/Packs) in the Packs submenu."
  sees "The pack loads beside the game, stopping any pack still loading; then a new game of it is dealt, or what went wrong is shown."
  enabled := decide (k < s.core.found.length)
  on press
    emit := s.go (openFoundPlan k)
    post s' := s'.core.board = s.core.board
    sound := by
      intro s k _
      show (openFoundPlan k s.core s.reqs).1.board = s.core.board
      unfold openFoundPlan
      split
      · dsimp only
        split <;> rfl
      · rfl

move ^12 revealPacks (s : State) "Open Packs Folder" in ^6 where
  does "Choose Open Packs Folder."
  sees "The Finder shows the packs folder (created if it wasn't there); a folder put in it with a pack.json and its images is listed in the Packs submenu the next time the menu opens."
  on press
    emit := s.go revealPlan
    post s' := s'.core.board = s.core.board
    sound := by intro s; rfl

def machine : Machine State := { init := initial, moves := moves%, receive := State.receive }

/-! ## Invariants -/

/-- Every move's handlers, as plans: what `machine.update` can do. -/
theorem update_plan (s : State) (a : Action) :
    (machine.update s a).1 = s ∨ ∃ f : Plan, (machine.update s a).1 = (s.go f).1 ∧
      (f = flipPlan a.key ∨ f = dealPlan s.core.pack ∨ (∃ op, f = editPlan op) ∨
       f = openTypedPlan ∨ f = cancelLoadPlan ∨ f = listPlan ∨ f = openBundledPlan a.key ∨
       f = openFoundPlan a.key ∨ f = revealPlan) := by
  rcases dispatch_cases machine.moves s a with h0 | ⟨m, hm, h, hh, -, -, -, e⟩
  · exact Or.inl (by rw [Machine.update, h0])
  · rw [Machine.update, e]
    simp only [machine, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [flipMove, newGame, packField, cancelLoad, openMenu, menuNewGame, bundledMove,
        foundMove, revealPacks] at hh
    all_goals obtain rfl | hh := List.mem_cons.mp hh
    all_goals first
      | exact Or.inr ⟨_, rfl, by simp only [true_or, or_true]⟩
      | (cases a with
          | edit c op => exact Or.inr ⟨_, rfl, Or.inr (Or.inr (Or.inl ⟨op, rfl⟩))⟩
          | _ => exact Or.inl rfl)
      | (obtain rfl | hh := List.mem_cons.mp hh
         · exact Or.inr ⟨_, rfl, by simp only [true_or, or_true]⟩
         · exact absurd hh List.not_mem_nil)
      | exact absurd hh List.not_mem_nil

theorem settled_refl (c : Core) (h : BoardOk c) : Settled c c := settled_calm h rfl h.load

theorem settled_update (s : State) (a : Action) (h : BoardOk s.core) :
    Settled s.core (machine.update s a).1.core := by
  rcases update_plan s a with e | ⟨f, e, hf⟩
  · rw [e]; exact settled_refl _ h
  · rw [e, go_core]
    rcases hf with rfl | rfl | ⟨op, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl
    · exact settled_flip _ _ _ h
    · exact settled_newGame _ _ h
    · exact settled_edit _ _ _ h
    · exact settled_openTyped _ _ h
    · exact settled_cancelLoad _ _ h
    · exact settled_list _ _ h
    · exact settled_openBundled _ _ _ h
    · exact settled_openFound _ _ _ h
    · exact settled_reveal _ _ h

theorem settled_receive (s : State) (m : Msg) (h : BoardOk s.core) :
    Settled s.core (machine.receive s m).1.core := by
  show Settled s.core (s.receive m).1.core
  cases m with
  | clock t => exact settled_onClock _ _ t h
  | timer n =>
    simp only [State.receive]
    split
    · exact settled_flipBack s.core s.reqs h
    · exact settled_refl _ h
  | reply id rep =>
    simp only [State.receive]
    split
    · exact settled_onReply _ _ id rep h
    · exact settled_refl _ h
  | sub sb e =>
    cases e with
    | evicted src => exact settled_onEvicted s.core s.reqs src h
    | _ => exact settled_refl _ h

theorem ok_update (s : State) (a : Action) (h : s.reqs.Ok) : (machine.update s a).1.reqs.Ok := by
  rcases update_plan s a with e | ⟨f, e, -⟩
  · rw [e]; exact h
  · rw [e]; exact go_ok s f h

theorem ok_receive (s : State) (m : Msg) (h : s.reqs.Ok) : (machine.receive s m).1.reqs.Ok := by
  show (s.receive m).1.reqs.Ok
  cases m with
  | clock t => exact go_ok _ _ h
  | timer n =>
    simp only [State.receive]
    split
    · exact go_ok _ _ h
    · exact h
  | reply id rep =>
    simp only [State.receive]
    split
    · exact go_ok _ _ h
    · exact h
  | sub sb e =>
    cases e with
    | evicted src => exact go_ok _ _ h
    | _ => exact h

theorem mono_refl (c : Core) : ScoresMono c c := mono_eq rfl

theorem mono_update (s : State) (a : Action) : ScoresMono s.core (machine.update s a).1.core := by
  rcases update_plan s a with e | ⟨f, e, hf⟩
  · rw [e]; exact mono_refl _
  · rw [e, go_core]
    rcases hf with rfl | rfl | ⟨op, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mono_flip _ _ _
    · exact mono_eq rfl
    · exact mono_eq rfl
    · exact mono_openTyped _ _
    · exact mono_eq rfl
    · exact mono_eq rfl
    · exact mono_openBundled _ _ _
    · exact mono_openFound _ _ _
    · exact mono_eq rfl

theorem mono_receive (s : State) (m : Msg) : ScoresMono s.core (machine.receive s m).1.core := by
  show ScoresMono s.core (s.receive m).1.core
  cases m with
  | clock t => exact mono_onClock _ _ t
  | timer n =>
    simp only [State.receive]
    split
    · exact mono_eq rfl
    · exact mono_refl _
  | reply id rep =>
    simp only [State.receive]
    split
    · exact mono_onReply _ _ id rep
    · exact mono_refl _
  | sub sb e =>
    cases e with
    | evicted src => exact mono_eq rfl
    | _ => exact mono_refl _

theorem boardOk_initial : BoardOk initial.core :=
  boardOk_dealt {} shapes 0 shapes_ok (loadOk_none _ rfl)

-- region: claims-board
invariant ^20 dealt "The board is a deal of the pack" for machine where
  does "The game deals the pack's number of pairs, from distinct faces of the pack; the cards are those faces, each on exactly two cards, in an order the clock's seed shuffled."
  holds s := BoardOk s.core
  init := boardOk_initial
  step := fun s a h => (settled_update s a h).1
  receive := fun s m h => (settled_receive s m h).1

invariant ^21 twoUp "At most two unmatched cards face up" for machine where
  does "At most two cards are face up and unmatched at any time: turning a third turns the mismatched two back first."
  holds s := BoardOk s.core ∧ s.core.game.up.length ≤ 2 ∧
    ∀ i ∈ s.core.game.up, s.core.game.isMatched i = false
  init := ⟨boardOk_initial, boardOk_initial.inv.upBound, fun i hi => (boardOk_initial.inv.upValid i hi).2⟩
  step := fun s a h => by
    have b := (settled_update s a h.1).1
    exact ⟨b, b.inv.upBound, fun i hi => (b.inv.upValid i hi).2⟩
  receive := fun s m h => by
    have b := (settled_receive s m h.1).1
    exact ⟨b, b.inv.upBound, fun i hi => (b.inv.upValid i hi).2⟩

invariant ^22 wonIff "Won exactly when every card is matched" for machine where
  does "The game is won, and its time recorded, exactly when every card on the board is matched."
  holds s := BoardOk s.core ∧ s.core.game.won = s.core.game.allMatched
  init := ⟨boardOk_initial, boardOk_initial.inv.wonIff⟩
  step := fun s a h => by
    have b := (settled_update s a h.1).1
    exact ⟨b, b.inv.wonIff⟩
  receive := fun s m h => by
    have b := (settled_receive s m h.1).1
    exact ⟨b, b.inv.wonIff⟩

theorem winnable (c : Core) (h : BoardOk c) :
    (c.game.flipAll (c.game.solve c.now) c.now).won = true :=
  Game.solve_wins _ _ h.inv (fun e => by
    have := h.dealt.length_eq
    rw [e] at this
    have := h.pack.two
    simp only [List.length_nil, ordered, List.length_append, List.length_range] at *
    omega)

invariant ^23 canWin "The game can always be won" for machine where
  does "From every state the app reaches, some sequence of cards to turn wins the game: the cards of every face not yet matched, a pair at a time (Game.solve)."
  holds s := BoardOk s.core ∧ (s.core.game.flipAll (s.core.game.solve s.core.now) s.core.now).won = true
  init := ⟨boardOk_initial, winnable _ boardOk_initial⟩
  step := fun s a h => by
    have b := (settled_update s a h.1).1
    exact ⟨b, winnable _ b⟩
  receive := fun s m h => by
    have b := (settled_receive s m h.1).1
    exact ⟨b, winnable _ b⟩

invariant ^24 moveCount "Moves count pairs turned" for machine where
  does "The move counter is the number of pairs of cards turned this game: half the cards turned, rounded down."
  holds s := BoardOk s.core ∧ 2 * s.core.game.moves + s.core.game.up.length % 2 = s.core.game.flips
  init := ⟨boardOk_initial, boardOk_initial.inv.moveCount⟩
  step := fun s a h => by
    have b := (settled_update s a h.1).1
    exact ⟨b, b.inv.moveCount⟩
  receive := fun s m h => by
    have b := (settled_receive s m h.1).1
    exact ⟨b, b.inv.moveCount⟩
-- endregion: claims-board

-- region: claims-steps
/-- Within a game (no new deal), every face matched stays matched, whatever the person or the
host does. -/
def MatchedStays : Prop :=
  ∀ s : State, BoardOk s.core →
    (∀ a, (machine.update s a).1.core.deals = s.core.deals →
      ∀ f ∈ s.core.game.matched, f ∈ (machine.update s a).1.core.game.matched) ∧
    (∀ m, (machine.receive s m).1.core.deals = s.core.deals →
      ∀ f ∈ s.core.game.matched, f ∈ (machine.receive s m).1.core.game.matched)

theorem matched_of_settled {c c' : Core} (h : Settled c c') (e : c'.deals = c.deals) :
    ∀ f ∈ c.game.matched, f ∈ c'.game.matched := by
  rcases h.2 e with b | ⟨-, -, m⟩
  · simp only [Core.board, Prod.mk.injEq] at b
    rw [b.2.2]
    exact fun _ hf => hf
  · exact m

theorem matched_stays : MatchedStays := fun s h =>
  ⟨fun a e => matched_of_settled (settled_update s a h) e,
   fun m e => matched_of_settled (settled_receive s m h) e⟩

invariant ^25 matchedStays "A matched card stays matched" for machine where
  does "Once a pair is matched it stays matched, face up, until a new game is dealt; nothing the person clicks and nothing the host answers turns it back."
  holds _s := MatchedStays
  init := matched_stays
  step := fun _ _ _ => matched_stays
  receive := fun _ _ _ => matched_stays

/-- No step makes a pack's best score worse or forgets it. -/
def BestImproves : Prop :=
  ∀ s : State, (∀ a, ScoresMono s.core (machine.update s a).1.core) ∧
    ∀ m, ScoresMono s.core (machine.receive s m).1.core

theorem best_improves : BestImproves := fun s => ⟨mono_update s, mono_receive s⟩

invariant ^26 bestImproves "Best scores only improve" for machine where
  does "A pack's best moves and best time only ever get better: a win records the better of each, and scores read from disk are merged the same way, never overwriting a better one."
  holds _s := BestImproves
  init := best_improves
  step := fun _ _ _ => best_improves
  receive := fun _ _ _ => best_improves
-- endregion: claims-steps

-- region: claims-requests
theorem reqsOk_initial : initial.reqs.Ok := go_ok _ _ ok_empty

invariant ^27 noneLost "No request is lost" for machine where
  does "Every request Pairs makes (manifests, images, the scores file, the packs folder) is answered, cancelled or still awaited, exactly once; ids awaited are distinct and were issued. Cairn's runtime sends at most six network requests at a time and drops replies to cancelled ones."
  holds s := s.reqs.Ok
  init := reqsOk_initial
  step := ok_update
  receive := ok_receive

/-- A reply to an id the app isn't waiting for changes nothing and does nothing. -/
def StaleIgnored : Prop :=
  ∀ (s : State) (id : Nat) (rep : Reply), s.reqs.isLive id = false →
    machine.receive s (.reply id rep) = (s, [])

theorem stale_ignored : StaleIgnored := fun s id rep h => reply_stale s id rep h

invariant ^28 staleIgnored "A late reply changes nothing" for machine where
  does "A reply to a request Pairs isn't waiting for (cancelled when a pack switch stopped it, superseded, or a duplicate) leaves everything as it was."
  holds _s := StaleIgnored
  init := stale_ignored
  step := fun _ _ _ => stale_ignored
  receive := fun _ _ _ => stale_ignored

/-- A reply changes the board only by completing the pack being loaded. -/
def ReplyBoard : Prop :=
  ∀ (s : State) (id : Nat) (rep : Reply),
    (machine.receive s (.reply id rep)).1.core.board = s.core.board ∨ Completes s.core id rep

theorem reply_board_all : ReplyBoard := fun s id rep => reply_board s id rep

invariant ^29 replyBoard "Only a finished pack changes the board" for machine where
  does "A reply changes the board only when it is an image answering ready, to a request the pack being loaded made since it began loading: a failure, a pack.json that doesn't parse, a reply for a pack that was switched away from, or any reply while no pack is loading leaves the game as it was."
  holds _s := ReplyBoard
  init := reply_board_all
  step := fun _ _ _ => reply_board_all
  receive := fun _ _ _ => reply_board_all
-- endregion: claims-requests

/-! ## Flows -/

flow ^30 findPair "Find a pair" for machine where
  does "Turn two cards with the same face."
  sees "Both stay face up, matched; the move counter says 1."
  goal s := s.core.game.matched.length = 1 ∧ s.core.game.moves = 1
  witness press ^2#0, press ^2#13

flow ^31 mismatch "A mismatch" for machine where
  does "Turn two cards with different faces."
  sees "Both are face up, unmatched, until they turn back; the move counter says 1."
  goal s := s.core.game.up.length = 2 ∧ s.core.game.moves = 1
  witness press ^2#0, press ^2#1

set_option maxRecDepth 8000 in
flow ^32 winGame "Win a game" for machine where
  does "Turn the cards of each face in turn, a pair at a time."
  sees "Every card is matched and the game is won, in eight moves."
  goal s := s.core.game.won = true ∧ s.core.game.moves = 8
  witness press ^2#8, press ^2#11, press ^2#1, press ^2#14, press ^2#7,
    press ^2#12, press ^2#5, press ^2#10, press ^2#3, press ^2#6,
    press ^2#4, press ^2#15, press ^2#2, press ^2#9, press ^2#0, press ^2#13

def claimInfos : List ClaimInfo := claims%

-- region: app
/-- The host keeps at most this many bytes of decoded images (a pack of 100 faces at 256×256
points on a 2× screen is about 100 MiB). -/
def imageBudget : Nat := 192 * 1024 * 1024

def app : App State :=
  { machine.toApp [.window 1 "Pairs" view, .statusItem 6 (some ∘ statusItem)] claimInfos with
    initEffects := boot.2
    subscriptions := fun s =>
      .imageCache imageBudget ::
        (if s.core.game.started.isSome && !s.core.game.won then [.every 1000] else [])
    minSize
    initFocus := some fieldRef }
-- endregion: app

/-- For `cairn fuzz`: the window's smallest size is the app's `minSize` (the fuzzer otherwise
measures the view), and the menu bar item's moves have no control in the window's frame (the
menu is the host's; Cairn's fuzzer checks presence in the window only, cairn#176). -/
def fuzz : Cairn.Fuzz.Custom State where
  minSize := fun s => some (minSize s)
  noControl := [8, 9, 10, 11, 12]

end Pairs
