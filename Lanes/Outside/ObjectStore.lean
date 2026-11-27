/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Rpc

/-!
# An object store

Puts, gets and deletes by key, as S3 and the stores that copy it give them: a read sees the last
write that was answered, and none older (read-after-write, S3's promise since 2020). What makes
it a model and not a map is the calls whose answer is not known: a write that timed out, or was
refused with an error that may come after it took effect, may take effect at any moment after
it was sent, or never. So a key may hold any of several objects: the one the last answered write
left, and what each write still uncertain would leave.

A head asks whether a key holds an object, and not which. A write may also be someone else's
that the system let make, such as a browser's put through a presigned link (`granted`): the
system never hears it answered, so it may take effect at any moment, or never.

`server` is that as an `Rpc.Server`, and `Rpc.outside port server` what the store may answer.
Proved, in every run the model allows: a get is answered only with an object a put sent under
that key (`ObjectStore.read_sent`), and a head says a key holds an object only when a put sent
one under it (`ObjectStore.held_sent`). Not modelled: listing, ranges, conditional writes,
versions, and the time a write takes.

The state keeps no history it does not need: a key's settled outcomes replace its earlier ones,
and the objects sent and read are sets, each pair once, so a run that writes and reads the same
objects again reaches the same state, and a model check stays small.
-/

@[expose] public section

namespace Lanes.ObjectStore

inductive Request (K V : Type) where
  | put (key : K) (value : V)
  | get (key : K)
  /-- Whether `key` holds an object. -/
  | head (key : K)
  | delete (key : K)
  /-- A put by someone else that the system let make, never answered to it. -/
  | granted (key : K) (value : V)
  deriving DecidableEq, Repr, Hashable

inductive Answer (V : Type) where
  | stored
  | found (value : V)
  /-- To a head: the key holds an object. -/
  | present
  | missing
  | deleted
  /-- An error, which may have come after the request took effect. -/
  | refused
  deriving DecidableEq, Repr, Hashable

def Request.key {K V : Type} : Request K V → K
  | .put key _ | .get key | .head key | .delete key | .granted key _ => key

/-- What a write leaves under its key: the object, or none. -/
def Request.leaves {K V : Type} : Request K V → Option (Option V)
  | .put _ value | .granted _ value => some (some value)
  | .delete _ => some none
  | .get _ | .head _ => none

/-- A call sent and not answered, or a write refused, which may still take effect. -/
structure Pending (K V : Type) where
  call : Nat
  request : Request K V
  /-- What each write to its key answered while it was open left: that one may have taken
  effect after it. -/
  overlaps : List (Option V)
  deriving DecidableEq, Repr, Hashable

structure State (K V : Type) where
  open_ : List (Pending K V)
  /-- What a key may hold after its last answered write: what that write left, or what one
  that overlapped it did. One entry a key. -/
  settled : List (K × List (Option V))
  /-- Every object a put sent, under its key, once each. -/
  sent : List (K × V)
  /-- Every object a get was answered with, under its key, once each. -/
  read : List (K × V)
  /-- Every key a head was answered `present` for, once each. -/
  held : List K
  deriving DecidableEq, Repr, Hashable

variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-- `x` added to a list kept as a set. -/
def insertNew {α : Type} [DecidableEq α] (x : α) (l : List α) : List α :=
  if x ∈ l then l else x :: l

omit [DecidableEq K] [DecidableEq V] in
theorem mem_insertNew {α : Type} [DecidableEq α] {x y : α} {l : List α} :
    y ∈ insertNew x l ↔ y = x ∨ y ∈ l := by
  unfold insertNew
  split
  · next h => exact ⟨.inr, fun | .inl rfl => h | .inr h => h⟩
  · exact List.mem_cons

/-- What `key` may hold now. -/
def State.possible (d : State K V) (key : K) : List (Option V) :=
  (d.settled.lookup key).getD [none] ++
    d.open_.filterMap fun p => if p.request.key = key then p.request.leaves else none

/-- `call`, answered as having left `left` under `key`. -/
def State.settle (d : State K V) (call : Nat) (key : K) (left : Option V) (overlaps : List (Option V)) :
    State K V :=
  { d with
    open_ := (d.open_.filter (·.call != call)).map fun p =>
      if p.request.key = key then { p with overlaps := insertNew left p.overlaps } else p
    settled := (key, left :: overlaps) :: d.settled.filter (·.1 != key) }

def server : Rpc.Server (State K V) (Request K V) (Answer V) Empty where
  init := ⟨[], [], [], [], []⟩
  receive d call :=
    { d with open_ := ⟨call.id, call.request, []⟩ :: d.open_,
             sent := match call.request with
               | .put key value | .granted key value => insertNew (key, value) d.sent
               | _ => d.sent }
  answer d call a := do
    let p ← d.open_.find? (·.call == call)
    let rest := d.open_.filter (·.call != call)
    match p.request, a with
    | .put key value, .stored => some (d.settle call key (some value) p.overlaps)
    | .delete key, .deleted => some (d.settle call key none p.overlaps)
    | .get key, .found value =>
      if some value ∈ d.possible key then
        some { d with open_ := rest, read := insertNew (key, value) d.read }
      else none
    | .get key, .missing => if none ∈ d.possible key then some { d with open_ := rest } else none
    | .get _, .refused => some { d with open_ := rest }
    | .head key, .present =>
      if (d.possible key).any Option.isSome then
        some { d with open_ := rest, held := insertNew key d.held }
      else none
    | .head key, .missing => if none ∈ d.possible key then some { d with open_ := rest } else none
    | .head _, .refused => some { d with open_ := rest }
    | .granted .., _ => none
    | _, .refused => some d
    | _, _ => none

/-- Every object a key may hold, settled on or read was sent by a put under that key. -/
def Sound (d : State K V) : Prop :=
  (∀ kv ∈ d.read, kv ∈ d.sent)
    ∧ (∀ key outcomes, (key, outcomes) ∈ d.settled → ∀ value, some value ∈ outcomes → (key, value) ∈ d.sent)
    ∧ ∀ p ∈ d.open_, (∀ value, p.request.leaves = some (some value) → (p.request.key, value) ∈ d.sent)
      ∧ ∀ value, some value ∈ p.overlaps → (p.request.key, value) ∈ d.sent

omit [DecidableEq V] in
private theorem sent_of_possible {d : State K V} {key : K} {value : V} (hd : Sound d)
    (h : some value ∈ d.possible key) : (key, value) ∈ d.sent := by
  simp only [State.possible, List.mem_append, List.mem_filterMap] at h
  rcases h with h | ⟨p, hp, hleaves⟩
  · cases hl : d.settled.lookup key with
    | none => simp [hl] at h
    | some outcomes =>
      simp only [hl, Option.getD_some] at h
      obtain ⟨l₁, l₂, heq, -⟩ := List.lookup_eq_some_iff.mp hl
      exact hd.2.1 key outcomes (by simp [heq]) value h
  · split at hleaves
    · next hkey => exact hkey ▸ (hd.2.2 p hp).1 value hleaves
    · simp at hleaves

private theorem sound_settle {d : State K V} {p : Pending K V} (hd : Sound d) (hp : p ∈ d.open_)
    (key : K) (left : Option V) (hkey : p.request.key = key)
    (hleft : p.request.leaves = some left) :
    Sound (d.settle p.call key left p.overlaps) := by
  obtain ⟨hread, hsettled, hopen⟩ := hd
  have hl : ∀ value, left = some value → (key, value) ∈ d.sent := fun value h =>
    hkey ▸ (hopen p hp).1 value (h ▸ hleft)
  refine ⟨hread, ?_, ?_⟩
  · intro k outcomes hmem value hv
    simp only [State.settle, List.mem_cons, Prod.mk.injEq, List.mem_filter] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem
    · rcases List.mem_cons.mp hv with h | h
      · exact hl value h.symm
      · exact hkey ▸ (hopen p hp).2 value h
    · exact hsettled k outcomes hmem.1 value hv
  · intro q hq
    simp only [State.settle, List.mem_map, List.mem_filter] at hq
    obtain ⟨q', ⟨hq', -⟩, rfl⟩ := hq
    split
    · next hk =>
      refine ⟨(hopen q' hq').1, fun value hv => ?_⟩
      rcases mem_insertNew.mp hv with h | h
      · exact hk ▸ hl value h.symm
      · exact (hopen q' hq').2 value h
    · exact hopen q' hq'

private theorem sound_receive (d : State K V) (call : Rpc.Call (Request K V)) (hd : Sound d) :
    Sound (server.receive d call) := by
  obtain ⟨hread, hsettled, hopen⟩ := hd
  have grow : ∀ kv ∈ d.sent, kv ∈ (server.receive d call).sent := by
    intro kv h
    simp only [server]
    split <;> first | exact mem_insertNew.mpr (.inr h) | exact h
  refine ⟨fun kv h => grow kv (hread kv h), fun k o h v hv => grow _ (hsettled k o h v hv), ?_⟩
  intro q hq
  simp only [server, List.mem_cons] at hq
  rcases hq with rfl | hq
  · refine ⟨fun value h => ?_, by simp⟩
    simp only [server]
    cases hr : call.request <;> simp_all [Request.leaves, Request.key, mem_insertNew]
  · exact ⟨fun v h => grow _ ((hopen q hq).1 v h), fun v h => grow _ ((hopen q hq).2 v h)⟩

omit [DecidableEq K] [DecidableEq V] in
private theorem sound_drop {d : State K V} (hd : Sound d) (call : Nat) :
    Sound { d with open_ := d.open_.filter (·.call != call) } :=
  ⟨hd.1, hd.2.1, fun p hp => hd.2.2 p (List.mem_filter.mp hp).1⟩

/-- Every key a head said holds an object, a put sent one under. -/
def HeldSent (d : State K V) : Prop := ∀ key ∈ d.held, ∃ value, (key, value) ∈ d.sent

/-- What an answer to a call changes besides the open calls, the settled outcomes and the
objects read: the keys held, only when a head is answered `present` for a key that may hold an
object; and never the objects sent. -/
private theorem answer_held (d : State K V) (call : Nat) (a : Answer V) (d' : State K V)
    (h : server.answer d call a = some d') :
    d'.sent = d.sent ∧ (d'.held = d.held
      ∨ ∃ key value, d'.held = insertNew key d.held ∧ some value ∈ d.possible key) := by
  simp only [server, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨p, -, h⟩ := h
  split at h
  · cases h; exact ⟨rfl, .inl rfl⟩
  · cases h; exact ⟨rfl, .inl rfl⟩
  · split at h
    · cases h; exact ⟨rfl, .inl rfl⟩
    · simp at h
  · split at h
    · cases h; exact ⟨rfl, .inl rfl⟩
    · simp at h
  · cases h; exact ⟨rfl, .inl rfl⟩
  · next key _ =>
    split at h
    · next hany =>
      cases h
      obtain ⟨o, ho, hsome⟩ := List.any_eq_true.mp hany
      obtain ⟨value, rfl⟩ := Option.isSome_iff_exists.mp hsome
      exact ⟨rfl, .inr ⟨key, value, rfl, ho⟩⟩
    · simp at h
  · split at h
    · cases h; exact ⟨rfl, .inl rfl⟩
    · simp at h
  · cases h; exact ⟨rfl, .inl rfl⟩
  · simp at h
  · cases h; exact ⟨rfl, .inl rfl⟩
  · simp at h

private theorem sound_answer (d : State K V) (call : Nat) (a : Answer V) (d' : State K V)
    (hd : Sound d) (h : server.answer d call a = some d') : Sound d' := by
  simp only [server, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨p, hfind, h⟩ := h
  have hp : p ∈ d.open_ := List.mem_of_find?_eq_some hfind
  have hcall : p.call = call := by simpa using List.find?_some hfind
  subst hcall
  split at h
  · next key value hr =>
    cases h
    exact sound_settle hd hp key _ (by simp [hr, Request.key]) (by simp [hr, Request.leaves])
  · next key hr =>
    cases h
    exact sound_settle hd hp key _ (by simp [hr, Request.key]) (by simp [hr, Request.leaves])
  · next key value hr =>
    split at h
    · next hv =>
      cases h
      have hsent := sent_of_possible hd hv
      obtain ⟨hread, hsettled, hopen⟩ := sound_drop hd p.call
      refine ⟨?_, hsettled, hopen⟩
      intro kv hkv
      rcases mem_insertNew.mp hkv with rfl | hkv
      · exact hsent
      · exact hread kv hkv
    · simp at h
  · split at h
    · cases h
      exact sound_drop hd _
    · simp at h
  · cases h
    exact sound_drop hd _
  · split at h
    · cases h
      exact ⟨hd.1, hd.2.1, fun q hq => hd.2.2 q (List.mem_filter.mp hq).1⟩
    · simp at h
  · split at h
    · cases h
      exact sound_drop hd _
    · simp at h
  · cases h
    exact sound_drop hd _
  · simp at h
  · cases h
    exact hd
  · simp at h

private theorem held_answer (d : State K V) (call : Nat) (a : Answer V) (d' : State K V)
    (hd : Sound d ∧ HeldSent d) (h : server.answer d call a = some d') : HeldSent d' := by
  obtain ⟨hsent, hheld⟩ := answer_held d call a d' h
  intro key hkey
  rw [hsent]
  rcases hheld with hh | ⟨k, value, hh, hv⟩
  · exact hd.2 key (hh ▸ hkey)
  · rw [hh] at hkey
    rcases mem_insertNew.mp hkey with rfl | hkey
    · exact ⟨value, sent_of_possible hd.1 hv⟩
    · exact hd.2 key hkey

private theorem held_receive (d : State K V) (call : Rpc.Call (Request K V)) (hd : HeldSent d) :
    HeldSent (server.receive d call) := by
  intro key hkey
  obtain ⟨value, hv⟩ := hd key hkey
  refine ⟨value, ?_⟩
  simp only [server]
  split <;> first | exact mem_insertNew.mpr (.inr hv) | exact hv

private theorem invariant {σ : Signature} (port : Rpc.Port σ (Request K V) (Answer V) Empty)
    {events : List (Event σ)} {d : Rpc.State (State K V)}
    (h : (Rpc.outside port server).after events = some d) : Sound d.server ∧ HeldSent d.server :=
  Rpc.server_invariant port server (fun _ => True) (fun d => Sound d ∧ HeldSent d)
    (by simp [Sound, HeldSent, server])
    (fun s c hs _ => ⟨sound_receive s c hs.1, held_receive s c hs.2⟩)
    (fun s c a s' hs h => ⟨sound_answer s c a s' hs.1 h, held_answer s c a s' hs h⟩)
    (fun _ e => e.elim) (fun _ _ _ _ => trivial) h

/-- A get is answered only with an object that a put sent under its key, in every run the model
allows: the store invents nothing, whatever timed out. -/
theorem read_sent {σ : Signature} (port : Rpc.Port σ (Request K V) (Answer V) Empty)
    {events : List (Event σ)} {d : Rpc.State (State K V)}
    (h : (Rpc.outside port server).after events = some d) :
    ∀ kv ∈ d.server.read, kv ∈ d.server.sent :=
  (invariant port h).1.1

/-- A head says a key holds an object only when a put, the system's or one it let someone else
make, sent one under it, in every run the model allows. -/
theorem held_sent {σ : Signature} (port : Rpc.Port σ (Request K V) (Answer V) Empty)
    {events : List (Event σ)} {d : Rpc.State (State K V)}
    (h : (Rpc.outside port server).after events = some d) :
    ∀ key ∈ d.server.held, ∃ value, (key, value) ∈ d.server.sent :=
  (invariant port h).2

end Lanes.ObjectStore
