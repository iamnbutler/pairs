module

public import Cairn

/-! # Requests: none lost

Pairs asks the host for manifests, images, its scores file and its packs folder. Cairn's runtime
caps how many network requests are with the host at once (`App.maxInFlight`) and drops the reply
to a request the app cancelled (`Effect.cancelRequest`); this file is the app's side of that
bookkeeping.

`Reqs` holds every request the app still waits for (`live`): images in Cairn's `Images` table,
the rest in `other` with what each was for. The app changes it only through `Op`s that `run`
applies: issue a request, load an image, take a reply, cancel. Each op keeps `Ok`: every id the
app ever issued is answered, cancelled or still live, exactly once (`count`), live ids are
distinct and were issued (`fresh`). So no request is lost, whatever order the host's replies
come in (`run_ok`), and a reply to an id that isn't live changes nothing (`answer_stale`). -/

@[expose] public section

namespace Pairs

open Cairn

/-- What a request other than an image load is for. -/
inductive Purpose where
  /-- The manifest of pack load number `load`. -/
  | manifest (load : Nat)
  | readScores
  | writeScores
  /-- The names in the packs folder. -/
  | listPacks
  /-- A request whose answer only matters as an answer: creating the packs folder, opening it
  in the Finder. -/
  | chore
deriving Repr, DecidableEq, Inhabited

structure Reqs where
  /-- The id the next request gets: how many the app has issued. -/
  next : Nat := 0
  /-- How many replies the app took. -/
  answered : Nat := 0
  /-- How many requests the app cancelled. -/
  cancelled : Nat := 0
  other : List (Nat × Purpose) := []
  img : Images := {}
deriving Repr, Inhabited

namespace Reqs

/-- The ids the app is waiting on. -/
def live (r : Reqs) : List Nat := r.other.map (·.1) ++ r.img.pending.map (·.1)

def isLive (r : Reqs) (id : Nat) : Bool := (r.live.contains id)

/-- What a live non-image request is for. -/
def purpose (r : Reqs) (id : Nat) : Option Purpose := r.other.lookup id

/-- Whether a request for `p` is live. -/
def waitingFor (r : Reqs) (p : Purpose) : Bool := r.other.any (·.2 == p)

structure Ok (r : Reqs) : Prop where
  count : r.next = r.answered + r.cancelled + r.live.length
  nodup : r.live.Nodup
  fresh : ∀ id ∈ r.live, id < r.next

instance (r : Reqs) : Decidable r.Ok :=
  decidable_of_iff (r.next = r.answered + r.cancelled + r.live.length ∧ r.live.Nodup ∧
      ∀ id ∈ r.live, id < r.next)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

theorem ok_empty : (({} : Reqs)).Ok :=
  ⟨rfl, List.nodup_nil, fun _ h => by simp only [live, List.map_nil, List.append_nil,
    List.not_mem_nil] at h⟩

/-! ## The ops -/

inductive Op where
  /-- Ask the host for `req`, for `p`. -/
  | issue (p : Purpose) (req : Request)
  /-- Load an image: cancel any load of the same source still live, then load it afresh. -/
  | load (src : String)
  /-- Take the reply to `id`. -/
  | answer (id : Nat) (rep : Reply)
  /-- Cancel every live non-image request whose purpose `p` picks. -/
  | cancelOther (p : Purpose → Bool)
  /-- Cancel every live image load whose source `p` picks. -/
  | cancelImages (p : String → Bool)
  /-- The host dropped `src`'s pixels (`Images.evicted`). -/
  | evicted (src : String)
  | setTimer (name : String) (ms : Nat)
  | cancelTimer (name : String)
  /-- Any other effect (a text field's clipboard, focus); requests and cancels can't pass. -/
  | pass (e : Effect)
deriving Inhabited

/-- The effects `Op.pass` lets through: anything but a request or a cancel. -/
def passes : Effect → Bool
  | .request .. | .cancelRequest .. => false
  | _ => true

def issue (r : Reqs) (p : Purpose) (req : Request) : Reqs × List Effect :=
  ({ r with next := r.next + 1, other := (r.next, p) :: r.other }, [.request r.next req])

def cancelSrc (r : Reqs) (src : String) : Reqs × List Effect :=
  let (i, cs) := r.img.cancel src
  ({ r with img := i, cancelled := r.cancelled + (r.img.pending.length - i.pending.length) }, cs)

def loadFresh (r : Reqs) (src : String) : Reqs × List Effect :=
  let (i, e) := r.img.load r.next src
  ({ r with img := i, next := r.next + 1 }, [e])

def load (r : Reqs) (src : String) : Reqs × List Effect :=
  let (r1, cs) := r.cancelSrc src
  let (r2, es) := r1.loadFresh src
  (r2, cs ++ es)

def answer (r : Reqs) (id : Nat) (rep : Reply) : Reqs :=
  if r.other.any (·.1 == id) then
    let o := r.other.filter (·.1 != id)
    { r with other := o, answered := r.answered + (r.other.length - o.length) }
  else if r.img.waiting id then
    let i := r.img.receive id rep
    { r with img := i, answered := r.answered + (r.img.pending.length - i.pending.length) }
  else r

def cancelOther (r : Reqs) (p : Purpose → Bool) : Reqs × List Effect :=
  let o := r.other.filter (fun q => !p q.2)
  ({ r with other := o, cancelled := r.cancelled + (r.other.length - o.length) },
   (r.other.filter (fun q => p q.2)).map fun q => .cancelRequest q.1)

def cancelImages (r : Reqs) (p : String → Bool) : Reqs × List Effect :=
  let (i, cs) := r.img.cancelWhere p
  ({ r with img := i, cancelled := r.cancelled + (r.img.pending.length - i.pending.length) }, cs)

def evicted (r : Reqs) (src : String) : Reqs × List Effect :=
  let (i, cs) := r.img.evicted src
  ({ r with img := i, cancelled := r.cancelled + (r.img.pending.length - i.pending.length) }, cs)

def step (r : Reqs) : Op → Reqs × List Effect
  | .issue p req => r.issue p req
  | .load src => r.load src
  | .answer id rep => (r.answer id rep, [])
  | .cancelOther p => r.cancelOther p
  | .cancelImages p => r.cancelImages p
  | .evicted src => r.evicted src
  | .setTimer n ms => (r, [.setTimer n ms])
  | .cancelTimer n => (r, [.cancelTimer n])
  | .pass e => (r, if passes e then [e] else [])

/-- Apply ops in order: the requests after, and the effects to run. -/
def run (r : Reqs) : List Op → Reqs × List Effect
  | [] => (r, [])
  | o :: os =>
    let (r1, e1) := r.step o
    let (r2, e2) := r1.run os
    (r2, e1 ++ e2)

/-! ## Each op keeps `Ok` -/

theorem live_length (r : Reqs) : r.live.length = r.other.length + r.img.pending.length := by
  simp only [live, List.length_append, List.length_map]

/-- Dropping live entries, each counted as answered or cancelled, keeps `Ok`. -/
theorem ok_of_sub {r r' : Reqs} (h : r.Ok) (hn : r'.next = r.next)
    (hs : r'.live.Sublist r.live)
    (hc : r'.answered + r'.cancelled + r'.live.length = r.answered + r.cancelled + r.live.length) :
    r'.Ok :=
  ⟨by have := h.count; omega, h.nodup.sublist hs, fun id hi => hn ▸ h.fresh id (hs.subset hi)⟩

/-- Adding the next id as live keeps `Ok`. -/
theorem ok_of_add {r r' : Reqs} (h : r.Ok) (hn : r'.next = r.next + 1)
    (hp : r'.live.Perm (r.next :: r.live)) (ha : r'.answered = r.answered)
    (hc : r'.cancelled = r.cancelled) : r'.Ok := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hp.length_eq, hn, ha, hc, h.count]; simp only [List.length_cons]; omega
  · refine hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨fun hm => ?_, h.nodup⟩)
    exact Nat.lt_irrefl _ (h.fresh _ hm)
  · intro id hi
    rcases List.mem_cons.mp (hp.subset hi) with e | hm
    · omega
    · have := h.fresh id hm; omega

theorem ok_issue {r : Reqs} (h : r.Ok) (p : Purpose) (req : Request) : (r.issue p req).1.Ok :=
  ok_of_add h rfl (by simp only [issue, live, List.map_cons, List.cons_append]; exact .refl _)
    rfl rfl

theorem pending_sub (r : Reqs) (i : Images) (o : List (Nat × Purpose))
    (ho : o.Sublist r.other) (hi : i.pending.Sublist r.img.pending) :
    ({ r with other := o, img := i } : Reqs).live.Sublist r.live :=
  (ho.map _).append (hi.map _)

theorem ok_cancelSrc {r : Reqs} (h : r.Ok) (src : String) : (r.cancelSrc src).1.Ok := by
  have hs : (r.img.pending.filter (·.2 != src)).Sublist r.img.pending := List.filter_sublist
  refine ok_of_sub h rfl ?_ ?_
  · exact pending_sub r _ r.other (.refl _) hs
  · have := hs.length_le
    simp only [cancelSrc, Images.cancel, live_length] at this ⊢
    omega

theorem filter_idem {α : Type} (f : α → Bool) (l : List α) : (l.filter f).filter f = l.filter f := by
  rw [List.filter_filter]; simp only [Bool.and_self]

theorem ok_load {r : Reqs} (h : r.Ok) (src : String) : (r.load src).1.Ok := by
  have h1 := ok_cancelSrc h src
  refine ok_of_add h1 rfl ?_ rfl rfl
  simp only [load, loadFresh, cancelSrc, Images.cancel, Images.load, live, List.map_cons,
    filter_idem]
  exact List.perm_middle

theorem ok_answer {r : Reqs} (h : r.Ok) (id : Nat) (rep : Reply) : (r.answer id rep).Ok := by
  unfold answer
  split
  · have hs : (r.other.filter (·.1 != id)).Sublist r.other := List.filter_sublist
    refine ok_of_sub h rfl (pending_sub r r.img _ hs (.refl _)) ?_
    have := hs.length_le
    simp only [live_length]
    omega
  · split
    · have hs : (r.img.receive id rep).pending.Sublist r.img.pending := by
        unfold Images.receive
        split
        · exact List.filter_sublist
        · exact .refl _
      refine ok_of_sub h rfl (pending_sub r _ r.other (.refl _) hs) ?_
      have := hs.length_le
      simp only [live_length]
      omega
    · exact h

theorem ok_cancelOther {r : Reqs} (h : r.Ok) (p : Purpose → Bool) : (r.cancelOther p).1.Ok := by
  have hs : (r.other.filter (fun q => !p q.2)).Sublist r.other := List.filter_sublist
  refine ok_of_sub h rfl (pending_sub r r.img _ hs (.refl _)) ?_
  have := hs.length_le
  simp only [cancelOther, live_length]
  omega

theorem ok_cancelImages {r : Reqs} (h : r.Ok) (p : String → Bool) :
    (r.cancelImages p).1.Ok := by
  have hs : (r.img.pending.filter fun q => !p q.2).Sublist r.img.pending := List.filter_sublist
  refine ok_of_sub h rfl (pending_sub r _ r.other (.refl _) hs) ?_
  have := hs.length_le
  simp only [cancelImages, Images.cancelWhere, live_length] at this ⊢
  omega

theorem ok_evicted {r : Reqs} (h : r.Ok) (src : String) : (r.evicted src).1.Ok := by
  have hs : (r.img.pending.filter (·.2 != src)).Sublist r.img.pending := List.filter_sublist
  refine ok_of_sub h rfl ?_ ?_
  · simp only [evicted, Images.evicted, Images.cancel]
    exact pending_sub r _ r.other (.refl _) hs
  · have := hs.length_le
    simp only [evicted, Images.evicted, Images.cancel, live_length] at this ⊢
    omega

theorem ok_step {r : Reqs} (h : r.Ok) (o : Op) : (r.step o).1.Ok := by
  cases o with
  | issue p req => exact ok_issue h p req
  | load src => exact ok_load h src
  | answer id rep => exact ok_answer h id rep
  | cancelOther p => exact ok_cancelOther h p
  | cancelImages p => exact ok_cancelImages h p
  | evicted src => exact ok_evicted h src
  | setTimer => exact h
  | cancelTimer => exact h
  | pass => exact h

/-- **No request is lost**: any ops, in any order, keep every issued request answered, cancelled
or live, each once. -/
theorem run_ok {r : Reqs} (h : r.Ok) (os : List Op) : (r.run os).1.Ok := by
  induction os generalizing r with
  | nil => exact h
  | cons o os ih => exact ih (ok_step h o)

theorem mem_of_lookup : ∀ (xs : List (Nat × String)) (k : Nat) (v : String),
    xs.lookup k = some v → (k, v) ∈ xs
  | [], _, _, h => by simp only [List.lookup] at h; cases h
  | (a, b) :: xs, k, v, h => by
    simp only [List.lookup] at h
    split at h
    · next e =>
      cases h
      simp only [beq_iff_eq] at e
      subst e
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup xs k v h)

/-- **A reply to an id the app isn't waiting for changes nothing.** -/
theorem answer_stale (r : Reqs) (id : Nat) (rep : Reply) (h : r.isLive id = false) :
    r.answer id rep = r := by
  have h' : id ∉ r.live := fun hm => by
    have e := List.contains_iff_mem.mpr hm
    simp only [isLive] at h
    rw [e] at h
    cases h
  simp only [live, List.mem_append, List.mem_map, not_or, not_exists, not_and] at h'
  have h1 : r.other.any (·.1 == id) = false := by
    simp only [List.any_eq_false, beq_iff_eq]
    exact fun x hx e => h'.1 x hx e
  have h2 : r.img.waiting id = false := by
    unfold Images.waiting
    cases hl : r.img.pending.lookup id with
    | none => rfl
    | some s =>
      exact absurd rfl (h'.2 (id, s) (mem_of_lookup _ _ _ hl))
  simp only [answer, h1, h2, Bool.false_eq_true, ↓reduceIte]

end Reqs

end Pairs
