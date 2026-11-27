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

`server` is that as an `Rpc.Server`, and `Rpc.outside port server` what the store may answer.
Proved: a get is answered only with an object a put sent under that key, in every run the model
allows (`ObjectStore.read_sent`). Not modelled: listing, ranges, conditional writes, versions,
and the time a write takes.
-/

@[expose] public section

namespace Lanes.ObjectStore

inductive Request (K V : Type) where
  | put (key : K) (value : V)
  | get (key : K)
  | delete (key : K)
  deriving DecidableEq, Repr, Hashable

inductive Answer (V : Type) where
  | stored
  | found (value : V)
  | missing
  | deleted
  /-- An error, which may have come after the request took effect. -/
  | refused
  deriving DecidableEq, Repr, Hashable

def Request.key {K V : Type} : Request K V → K
  | .put key _ | .get key | .delete key => key

/-- What a write leaves under its key: the object, or none. -/
def Request.leaves {K V : Type} : Request K V → Option (Option V)
  | .put _ value => some (some value)
  | .delete _ => some none
  | .get _ => none

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
  that overlapped it did. -/
  settled : List (K × List (Option V))
  /-- Every object a put sent, under its key. -/
  sent : List (K × V)
  /-- Every object a get was answered with, under its key. -/
  read : List (K × V)
  deriving DecidableEq, Repr, Hashable

variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-- What `key` may hold now. -/
def State.possible (d : State K V) (key : K) : List (Option V) :=
  (d.settled.lookup key).getD [none] ++
    d.open_.filterMap fun p => if p.request.key = key then p.request.leaves else none

/-- `call`, answered as having left `left` under `key`. -/
def State.settle (d : State K V) (call : Nat) (key : K) (left : Option V) (overlaps : List (Option V)) :
    State K V :=
  { d with
    open_ := (d.open_.filter (·.call != call)).map fun p =>
      if p.request.key = key then { p with overlaps := left :: p.overlaps } else p
    settled := (key, left :: overlaps) :: d.settled }

def server : Rpc.Server (State K V) (Request K V) (Answer V) Empty where
  init := ⟨[], [], [], []⟩
  receive d call :=
    { d with open_ := ⟨call.id, call.request, []⟩ :: d.open_,
             sent := match call.request with
               | .put key value => (key, value) :: d.sent
               | _ => d.sent }
  answer d call a := do
    let p ← d.open_.find? (·.call == call)
    let rest := d.open_.filter (·.call != call)
    match p.request, a with
    | .put key value, .stored => some (d.settle call key (some value) p.overlaps)
    | .delete key, .deleted => some (d.settle call key none p.overlaps)
    | .get key, .found value =>
      if some value ∈ d.possible key then some { d with open_ := rest, read := (key, value) :: d.read }
      else none
    | .get key, .missing => if none ∈ d.possible key then some { d with open_ := rest } else none
    | .get _, .refused => some { d with open_ := rest }
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

omit [DecidableEq V] in
private theorem sound_settle {d : State K V} {p : Pending K V} (hd : Sound d) (hp : p ∈ d.open_)
    (key : K) (left : Option V) (hkey : p.request.key = key)
    (hleft : p.request.leaves = some left) :
    Sound (d.settle p.call key left p.overlaps) := by
  obtain ⟨hread, hsettled, hopen⟩ := hd
  have hl : ∀ value, left = some value → (key, value) ∈ d.sent := fun value h =>
    hkey ▸ (hopen p hp).1 value (h ▸ hleft)
  refine ⟨hread, ?_, ?_⟩
  · intro k outcomes hmem value hv
    simp only [State.settle, List.mem_cons, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem
    · rcases List.mem_cons.mp hv with h | h
      · exact hl value h.symm
      · exact hkey ▸ (hopen p hp).2 value h
    · exact hsettled k outcomes hmem value hv
  · intro q hq
    simp only [State.settle, List.mem_map, List.mem_filter] at hq
    obtain ⟨q', ⟨hq', -⟩, rfl⟩ := hq
    split
    · next hk =>
      refine ⟨(hopen q' hq').1, fun value hv => ?_⟩
      rcases List.mem_cons.mp hv with h | h
      · exact hk ▸ hl value h.symm
      · exact (hopen q' hq').2 value h
    · exact hopen q' hq'

private theorem sound_receive (d : State K V) (call : Rpc.Call (Request K V)) (hd : Sound d) :
    Sound (server.receive d call) := by
  obtain ⟨hread, hsettled, hopen⟩ := hd
  have grow : ∀ kv ∈ d.sent, kv ∈ (server.receive d call).sent := by
    intro kv h
    simp only [server]
    split <;> simp [h]
  refine ⟨fun kv h => grow kv (hread kv h), fun k o h v hv => grow _ (hsettled k o h v hv), ?_⟩
  intro q hq
  simp only [server, List.mem_cons] at hq
  rcases hq with rfl | hq
  · refine ⟨fun value h => ?_, by simp⟩
    simp only [server]
    cases hr : call.request <;> simp_all [Request.leaves, Request.key]
  · exact ⟨fun v h => grow _ ((hopen q hq).1 v h), fun v h => grow _ ((hopen q hq).2 v h)⟩

omit [DecidableEq K] [DecidableEq V] in
private theorem sound_drop {d : State K V} (hd : Sound d) (call : Nat) :
    Sound { d with open_ := d.open_.filter (·.call != call) } :=
  ⟨hd.1, hd.2.1, fun p hp => hd.2.2 p (List.mem_filter.mp hp).1⟩

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
      rcases List.mem_cons.mp hkv with rfl | hkv
      · exact hsent
      · exact hread kv hkv
    · simp at h
  · split at h
    · cases h
      exact sound_drop hd _
    · simp at h
  · cases h
    exact sound_drop hd _
  · cases h
    exact hd
  · simp at h

/-- A get is answered only with an object that a put sent under its key, in every run the model
allows: the store invents nothing, whatever timed out. -/
theorem read_sent {σ : Signature} (port : Rpc.Port σ (Request K V) (Answer V) Empty)
    {events : List (Event σ)} {d : Rpc.State (State K V)}
    (h : (Rpc.outside port server).after events = some d) :
    ∀ kv ∈ d.server.read, kv ∈ d.server.sent :=
  (Rpc.server_invariant port server (fun _ => True) Sound (by simp [Sound, server])
    (fun s c hs _ => sound_receive s c hs) sound_answer (fun _ e => e.elim)
    (fun _ _ _ _ => trivial) h).1

end Lanes.ObjectStore
