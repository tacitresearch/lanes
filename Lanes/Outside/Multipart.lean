/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Rpc

/-!
# A store's multipart uploads

S3's multipart upload as a model: an upload is begun for a key and given an id; parts are sent
under it by number, in any order and any number of times; a Complete lists parts by number and
tag (S3's ETag, a digest of the part), in ascending order, and the object is then those parts,
in that order. An abort ends an upload.

What makes it a model is what is not known. A part sent may have been stored whatever its answer
(late, `unknown`, an error), so a part number may hold any part sent under it; and a Complete
sent may take effect whatever its answer, so a read may see the object it lists. A Complete is
answered `completed` only for a listing whose every part was sent, with that tag, and only with
one listing an upload: a Complete sent again with the same listing is answered as the first, and
one with another listing is refused. After an abort answered, nothing of the upload completes.

Proved, in every run the model allows (`Multipart.read_listed`): an object a read is answered
with consists exactly of the parts some Complete of its key listed, in order, each one sent as
that part of that upload, with the tag listed; and a Complete is answered `completed` only for
such a listing (`Multipart.completed_sent`). Not modelled: ListParts, the order between two
uploads of one key (a read may see either), part sizes, and the time a call takes.
-/

@[expose] public section

namespace Lanes.Multipart

inductive Request (K V T : Type) where
  | create (key : K)
  | part (upload number : Nat) (value : V)
  | complete (key : K) (upload : Nat) (parts : List (Nat × T))
  | abort (upload : Nat)
  | get (key : K)
  deriving DecidableEq, Repr, Hashable

inductive Answer (V T : Type) where
  | created (upload : Nat)
  | stored (tag : T)
  | completed
  | aborted
  | found (object : List V)
  | missing
  /-- An error, which may have come after the request took effect. -/
  | refused
  deriving DecidableEq, Repr, Hashable

structure State (K V T : Type) where
  /-- The calls sent and not answered. -/
  open_ : List (Nat × Request K V T)
  /-- Each upload begun, with its key. -/
  uploads : List (Nat × K)
  /-- Every part sent: its upload, its number and what it holds. -/
  sent : List (Nat × Nat × V)
  /-- Every Complete sent, which may take effect: its upload, its key and its listing. -/
  completions : List (Nat × K × List (Nat × T))
  /-- The listing each upload's Complete was answered `completed` with. -/
  completed : List (Nat × List (Nat × T))
  /-- The uploads whose abort was answered. -/
  aborted : List Nat
  /-- Every object a read was answered with, under its key. -/
  read : List (K × List V)
  deriving DecidableEq, Repr, Hashable

variable {K V T : Type} [DecidableEq K] [DecidableEq V] [DecidableEq T]

/-- Whether `vs` are the parts `listing` names, in order: each sent as that part of `upload`,
with the tag listed. -/
def State.matches (d : State K V T) (tag : V → T) (upload : Nat) :
    List (Nat × T) → List V → Bool
  | [], [] => true
  | (n, t) :: listing, v :: vs =>
    (upload, n, v) ∈ d.sent && tag v == t && d.matches tag upload listing vs
  | _, _ => false

/-- Whether a part of each number `listing` names was sent under `upload` with its tag. -/
def State.held (d : State K V T) (tag : V → T) (upload : Nat) (listing : List (Nat × T)) : Bool :=
  listing.all fun (n, t) => d.sent.any fun (u, m, v) => u == upload && m == n && tag v == t

/-- A listing S3 takes: at least one part, in ascending order of number. -/
def ordered (listing : List (Nat × T)) : Bool :=
  !listing.isEmpty && decide ((listing.map (·.1)).Pairwise (· < ·))

/-- Whether a Complete of `upload` for `key` with `listing` may take effect. -/
def State.valid (d : State K V T) (tag : V → T) (key : K) (upload : Nat)
    (listing : List (Nat × T)) : Bool :=
  (upload, key) ∈ d.uploads && upload ∉ d.aborted && ordered listing && d.held tag upload listing

/-- Whether a read of `key` may see `vs`: what a Complete of it sent lists. -/
def State.readable (d : State K V T) (tag : V → T) (key : K) (vs : List V) : Bool :=
  d.completions.any fun (u, k, listing) =>
    k == key && d.valid tag key u listing && d.matches tag u listing vs

/-- Whether a Complete of `key` was answered `completed`, so a read cannot find nothing. -/
def State.done (d : State K V T) (key : K) : Bool :=
  d.completed.any fun (u, _) => (u, key) ∈ d.uploads

def server (tag : V → T) : Rpc.Server (State K V T) (Request K V T) (Answer V T) Empty where
  init := ⟨[], [], [], [], [], [], []⟩
  receive d call :=
    let d := { d with open_ := (call.id, call.request) :: d.open_ }
    match call.request with
    | .part u n v => { d with sent := (u, n, v) :: d.sent }
    | .complete k u listing => { d with completions := (u, k, listing) :: d.completions }
    | _ => d
  answer d call a := do
    let (_, request) ← d.open_.find? (·.1 == call)
    let d' := { d with open_ := d.open_.filter (·.1 != call) }
    match request, a with
    | .create key, .created u =>
      if d.uploads.any (·.1 == u) then none else some { d' with uploads := (u, key) :: d.uploads }
    | .part u n v, .stored t =>
      if d.uploads.any (·.1 == u) && u ∉ d.aborted && 1 ≤ n && n ≤ 10000 && tag v == t then some d'
      else none
    | .complete key u listing, .completed =>
      if d.valid tag key u listing && d.completed.all (fun (u', l) => u' != u || l == listing) then
        some { d' with completed := (u, listing) :: d.completed }
      else none
    | .abort u, .aborted =>
      if d.uploads.any (·.1 == u) && !d.completed.any (·.1 == u) then
        some { d' with aborted := u :: d.aborted }
      else none
    | .get key, .found vs =>
      if d.readable tag key vs then some { d' with read := (key, vs) :: d.read } else none
    | .get key, .missing => if d.done key then none else some d'
    | _, .refused => some d'
    | _, _ => none

/-- `vs` are the parts `listing` names, one for each, in order: each sent as that part of
`upload`, with the tag listed. -/
def Parts (d : State K V T) (tag : V → T) (upload : Nat) (listing : List (Nat × T))
    (vs : List V) : Prop :=
  listing.length = vs.length ∧ ∀ q ∈ listing.zip vs, (upload, q.1.1, q.2) ∈ d.sent ∧ tag q.2 = q.1.2

/-- What a read was answered with is what a Complete of its key listed, part by part. -/
def Listed (d : State K V T) (tag : V → T) (key : K) (vs : List V) : Prop :=
  ∃ u listing, (u, key, listing) ∈ d.completions ∧ Parts d tag u listing vs

/-- Every part a listing names was sent under its upload, with the tag listed. -/
def Sent (d : State K V T) (tag : V → T) (upload : Nat) (listing : List (Nat × T)) : Prop :=
  ∀ p ∈ listing, ∃ v, (upload, p.1, v) ∈ d.sent ∧ tag v = p.2

def Sound (tag : V → T) (d : State K V T) : Prop :=
  (∀ key vs, (key, vs) ∈ d.read → Listed d tag key vs)
    ∧ ∀ u listing, (u, listing) ∈ d.completed → Sent d tag u listing

omit [DecidableEq K] in
theorem matches_parts {d : State K V T} {tag : V → T} {u : Nat} :
    ∀ {listing : List (Nat × T)} {vs : List V}, d.matches tag u listing vs = true →
      Parts d tag u listing vs
  | [], [], _ => ⟨rfl, by simp⟩
  | (n, t) :: listing, v :: vs, h => by
    simp only [State.matches, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨hlen, hall⟩ := matches_parts h.2
    refine ⟨by simp [hlen], fun q hq => ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨h.1.1, h.1.2⟩
    · exact hall q hq
  | [], _ :: _, h | _ :: _, [], h => by simp [State.matches] at h

omit [DecidableEq K] [DecidableEq V] in
theorem held_sent {d : State K V T} {tag : V → T} {u : Nat} {listing : List (Nat × T)}
    (h : d.held tag u listing = true) : Sent d tag u listing := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  obtain ⟨⟨u', m, v⟩, hmem, hv⟩ := List.any_eq_true.mp this
  simp only [Bool.and_eq_true, beq_iff_eq] at hv
  obtain ⟨⟨rfl, rfl⟩, ht⟩ := hv
  exact ⟨v, hmem, ht⟩

/-- `d'` keeps every part and Complete `d` sent. -/
def Grows (d d' : State K V T) : Prop :=
  (∀ x ∈ d.sent, x ∈ d'.sent) ∧ ∀ x ∈ d.completions, x ∈ d'.completions

omit [DecidableEq K] [DecidableEq V] [DecidableEq T] in
theorem listed_grows {d d' : State K V T} {tag : V → T} (hg : Grows d d') {key : K} {vs : List V}
    (h : Listed d tag key vs) : Listed d' tag key vs := by
  obtain ⟨u, listing, hc, hf⟩ := h
  exact ⟨u, listing, hg.2 _ hc, hf.1, fun q hq => ⟨hg.1 _ (hf.2 q hq).1, (hf.2 q hq).2⟩⟩

omit [DecidableEq K] [DecidableEq V] [DecidableEq T] in
theorem sent_grows {d d' : State K V T} {tag : V → T} (hg : Grows d d') {u : Nat}
    {listing : List (Nat × T)} (h : Sent d tag u listing) : Sent d' tag u listing :=
  fun p hp => let ⟨v, hv, ht⟩ := h p hp; ⟨v, hg.1 _ hv, ht⟩

theorem sound_receive (tag : V → T) (d : State K V T) (call : Rpc.Call (Request K V T))
    (hd : Sound tag d) : Sound tag ((server tag).receive d call) := by
  have hg : Grows d ((server tag).receive d call) := by
    simp only [server]
    split <;> exact ⟨fun x h => by simp [h], fun x h => by simp [h]⟩
  have hread : ((server tag).receive d call).read = d.read := by simp only [server]; split <;> rfl
  have hcomp : ((server tag).receive d call).completed = d.completed := by
    simp only [server]; split <;> rfl
  refine ⟨fun key vs h => listed_grows hg (hd.1 key vs (hread ▸ h)),
    fun u listing h => sent_grows hg (hd.2 u listing (hcomp ▸ h))⟩

theorem sound_answer (tag : V → T) (d : State K V T) (call : Nat) (a : Answer V T)
    (d' : State K V T) (hd : Sound tag d) (h : (server tag).answer d call a = some d') :
    Sound tag d' := by
  obtain ⟨hread, hcomp⟩ := hd
  let drop : State K V T := { d with open_ := d.open_.filter (·.1 != call) }
  have hdrop : Sound tag drop := ⟨hread, hcomp⟩
  simp only [server, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨_, request⟩, -, h⟩ := h
  split at h
  · split at h
    · cases h
    · cases h; exact ⟨hread, hcomp⟩
  · split at h
    · cases h; exact hdrop
    · cases h
  · next key u listing =>
    split at h
    · next hv =>
      cases h
      refine ⟨hread, fun u' l hmem => ?_⟩
      rcases List.mem_cons.mp hmem with heq | hmem
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        simp only [State.valid, Bool.and_eq_true] at hv
        exact held_sent hv.1.2
      · exact hcomp u' l hmem
    · cases h
  · split at h
    · cases h; exact ⟨hread, hcomp⟩
    · cases h
  · next key vs =>
    split at h
    · next hr =>
      cases h
      refine ⟨fun k ws hmem => ?_, hcomp⟩
      rcases List.mem_cons.mp hmem with heq | hmem
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        obtain ⟨⟨u, k', listing⟩, hc, hm⟩ := List.any_eq_true.mp hr
        simp only [Bool.and_eq_true, beq_iff_eq] at hm
        obtain ⟨⟨rfl, -⟩, hm⟩ := hm
        exact ⟨u, listing, hc, matches_parts (d := d) hm⟩
      · exact hread k ws hmem
    · cases h
  · split at h
    · cases h
    · cases h; exact hdrop
  · cases h; exact hdrop
  · cases h

theorem sound_after {σ : Signature} (port : Rpc.Port σ (Request K V T) (Answer V T) Empty)
    (tag : V → T) {events : List (Event σ)} {d : Rpc.State (State K V T)}
    (h : (Rpc.outside port (server tag)).after events = some d) : Sound tag d.server :=
  Rpc.server_invariant port (server tag) (fun _ => True) (Sound tag)
    ⟨by simp [server], by simp [server]⟩ (fun s c hs _ => sound_receive tag s c hs)
    (sound_answer tag) (fun _ e => e.elim) (fun _ _ _ _ => trivial) h

/-- An object a read is answered with consists exactly of the parts some Complete of its key
listed, in order: each the part sent under that number of that upload, with the tag listed. In
every run the model allows, whatever was lost, retried, sent out of order or completed twice. -/
theorem read_listed {σ : Signature} (port : Rpc.Port σ (Request K V T) (Answer V T) Empty)
    (tag : V → T) {events : List (Event σ)} {d : Rpc.State (State K V T)}
    (h : (Rpc.outside port (server tag)).after events = some d) :
    ∀ key vs, (key, vs) ∈ d.server.read → Listed d.server tag key vs :=
  (sound_after port tag h).1

/-- A Complete is answered `completed` only for a listing whose every part was sent under its
upload with the tag listed. -/
theorem completed_sent {σ : Signature} (port : Rpc.Port σ (Request K V T) (Answer V T) Empty)
    (tag : V → T) {events : List (Event σ)} {d : Rpc.State (State K V T)}
    (h : (Rpc.outside port (server tag)).after events = some d) :
    ∀ u listing, (u, listing) ∈ d.server.completed → Sent d.server tag u listing :=
  (sound_after port tag h).2

end Lanes.Multipart
