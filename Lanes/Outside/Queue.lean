/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Events

/-!
# A message queue

A queue as SQS gives one: a consumer receives a message with a receipt, and the message is
invisible to others until its visibility timeout passes; then it is received again, unless it
was deleted with its latest receipt first. So a message is received at least once and maybe
more often, in no order (a standard queue), or in the order sent within its group (a FIFO
queue). After `maxReceives` receives of one copy it goes to the dead-letter queue (SQS's
`maxReceiveCount`, rule 2.6), which is also what keeps the checker finite.

The model has no time, so a visibility timeout may pass at any moment: a message received and
not yet deleted may be received again at once. A delete with a receipt that is not the latest
does nothing (SQS says it may or may not delete). A standard queue keeps a copy for each send of
an id it holds; a FIFO queue drops a resend of an id it holds, as its deduplication does, but
the model has no five-minute window.

Proved: each message is received at most `maxReceives` times for each copy the queue holds
(`Queue.received_le`), so at most `maxReceives` times in a FIFO queue (`Queue.fifo_received_le`);
a message deleted with its latest receipt is not received again unless it is sent again
(`Queue.deleted_not_received`).
-/

@[expose] public section

namespace Lanes.Queue

lanes_data structure Message (B : Type) where
  id : Nat
  /-- The message group of a FIFO queue. -/
  group : Nat := 0
  body : B
  deriving DecidableEq, Repr, Hashable, Codable

/-- Which outputs send and delete, and which inputs are receives, with their receipts. -/
structure Port (σ : Signature) (B : Type) where
  sent : σ.Out → Option (Message B) := fun _ => none
  deleted : σ.Out → Option Nat
  received : σ.In → Option (Nat × Message B)

structure Config where
  /-- Receives of one copy before it goes to the dead-letter queue. -/
  maxReceives : Nat
  /-- In order within a group, and a resend of an id held is dropped. -/
  fifo : Bool := false

structure State (B : Type) where
  /-- Every message held, in the order first sent. -/
  messages : List (Message B)
  /-- Copies of each id, as `Events.count` reads them. -/
  copies : List (Nat × Nat)
  /-- Receives of each id. -/
  received : List (Nat × Nat)
  /-- The latest receipt of each id received. -/
  latest : List (Nat × Nat)
  /-- Ids deleted with their latest receipt, and not sent again since. -/
  deleted : List Nat
  /-- Every receipt given, so that each is new. -/
  receipts : List Nat
  deriving DecidableEq, Repr, Hashable

variable {σ : Signature} {B : Type} [DecidableEq B]

open Events (count bump)

/-- In a FIFO queue, every earlier message of `m`'s group has been received. -/
def inOrder (d : State B) (m : Message B) : Bool :=
  (d.messages.takeWhile (· != m)).all fun e => e.group != m.group || 0 < count d.received e.id

/-- Whether `m` may be received now. -/
def ready (config : Config) (d : State B) (m : Message B) : Bool :=
  m ∈ d.messages && m.id ∉ d.deleted
    && count d.received m.id < config.maxReceives * count d.copies m.id
    && (!config.fifo || inOrder d m)

def receive (d : State B) (receipt : Nat) (m : Message B) : State B :=
  { d with received := bump d.received m.id
           latest := (m.id, receipt) :: d.latest.filter (·.1 != m.id)
           receipts := receipt :: d.receipts }

def delete (d : State B) (receipt : Nat) : State B :=
  match d.latest.find? (·.2 == receipt) with
  | some (id, _) => { d with deleted := id :: d.deleted }
  | none => d

def send (config : Config) (d : State B) (m : Message B) : State B :=
  if d.messages.any (·.id == m.id) then
    if config.fifo then d
    else { d with copies := bump d.copies m.id, deleted := d.deleted.filter (· != m.id) }
  else { d with messages := d.messages ++ [m], copies := bump d.copies m.id }

/-- What the queue may do, holding `initial` at the start. -/
def outside (port : Port σ B) (config : Config) (initial : List (Message B)) : Outside σ (State B) where
  init := initial.foldl (send config) ⟨[], [], [], [], [], []⟩
  allow d x :=
    match port.received x with
    | some (receipt, m) =>
      if receipt ∉ d.receipts && ready config d m then some (receive d receipt m) else none
    | none => none
  observe d out :=
    let d := match port.deleted out with
      | some receipt => delete d receipt
      | none => d
    match port.sent out with
    | some m => send config d m
    | none => d

/-- How often `events` receive a message with id `id`. -/
def receives (port : Port σ B) (id : Nat) (events : List (Event σ)) : Nat :=
  events.countP fun
    | .input x => (port.received x).any (·.2.id == id)
    | _ => false

omit [DecidableEq B] in
theorem count_copies_send (config : Config) (d : State B) (m : Message B) (id : Nat) :
    count d.copies id ≤ count (send config d m).copies id := by
  unfold send
  split
  · split
    · exact Nat.le_refl _
    · by_cases h : m.id = id
      · subst h; simp
      · simp [Events.count_bump_of_ne _ (Ne.symm h)]
  · by_cases h : m.id = id
    · subst h; simp
    · simp [Events.count_bump_of_ne _ (Ne.symm h)]

omit [DecidableEq B] in
theorem received_delete (d : State B) (receipt : Nat) : (delete d receipt).received = d.received := by
  unfold delete; split <;> rfl

omit [DecidableEq B] in
theorem copies_delete (d : State B) (receipt : Nat) : (delete d receipt).copies = d.copies := by
  unfold delete; split <;> rfl

omit [DecidableEq B] in
theorem received_send (config : Config) (d : State B) (m : Message B) :
    (send config d m).received = d.received := by
  unfold send; split
  · split <;> rfl
  · rfl

/-- Each message is received at most `maxReceives` times for each copy the queue holds, in every
run the model allows. -/
theorem received_le (port : Port σ B) (config : Config) (initial : List (Message B))
    {events : List (Event σ)} {d : State B} (h : (outside port config initial).after events = some d)
    (id : Nat) :
    receives port id events ≤ config.maxReceives * count d.copies id := by
  suffices hc : receives port id events + count (outside port config initial).init.received id
      = count d.received id ∧ count d.received id ≤ config.maxReceives * count d.copies id by
    omega
  have hinit : ∀ (l : List (Message B)) (d₀ : State B),
      count (l.foldl (send config) d₀).received id = count d₀.received id ∧
        (count d₀.received id ≤ config.maxReceives * count d₀.copies id →
          count (l.foldl (send config) d₀).received id
            ≤ config.maxReceives * count (l.foldl (send config) d₀).copies id) := by
    intro l
    induction l with
    | nil => intro d₀; exact ⟨rfl, fun h => h⟩
    | cons m rest ih =>
      intro d₀
      obtain ⟨h₁, h₂⟩ := ih (send config d₀ m)
      simp only [List.foldl_cons]
      refine ⟨by rw [h₁, received_send], fun hle => h₂ ?_⟩
      rw [received_send]
      exact Nat.le_trans hle (Nat.mul_le_mul_left _ (count_copies_send config d₀ m id))
  refine (outside port config initial).after_induction
    (P := fun events d => receives port id events
      + count (outside port config initial).init.received id = count d.received id
      ∧ count d.received id ≤ config.maxReceives * count d.copies id)
    ⟨by simp [receives], (hinit initial _).2 (by simp [count])⟩ ?_ h
  intro events d event d' ⟨ih, hle⟩ hsee
  cases event with
  | input x =>
    simp only [Outside.see, outside] at hsee
    split at hsee
    · next receipt m hx =>
      split at hsee
      · next hok =>
        obtain rfl := Option.some.inj hsee
        simp only [Bool.and_eq_true, decide_eq_true_eq, ready] at hok
        obtain ⟨-, ⟨⟨-, -⟩, hlt⟩, -⟩ := hok
        simp only [receives, List.countP_append] at ih ⊢
        by_cases hid : m.id = id
        · subst hid
          simp [hx, receive] at ih ⊢
          omega
        · simp [hx, hid, receive, Events.count_bump_of_ne _ (Ne.symm hid)] at ih ⊢
          exact ⟨ih, hle⟩
      · simp at hsee
    · simp at hsee
  | output out =>
    simp only [Outside.see, outside, Option.some.injEq] at hsee
    subst hsee
    simp only [receives, List.countP_append] at ih ⊢
    have hdel : ∀ d₀ : State B, (match port.deleted out with
        | some receipt => delete d₀ receipt | none => d₀).received = d₀.received ∧
        (match port.deleted out with
        | some receipt => delete d₀ receipt | none => d₀).copies = d₀.copies := by
      intro d₀; split
      · exact ⟨received_delete _ _, copies_delete _ _⟩
      · exact ⟨rfl, rfl⟩
    obtain ⟨hr, hc⟩ := hdel d
    split
    · next m _ =>
      refine ⟨by simp [ih, received_send, hr], ?_⟩
      rw [received_send, hr]
      refine Nat.le_trans hle (Nat.mul_le_mul_left _ ?_)
      have := count_copies_send config (match port.deleted out with
        | some receipt => delete d receipt | none => d) m id
      rwa [hc] at this
    · exact ⟨by simp [ih, hr], by rw [hr, hc]; exact hle⟩
  | _ =>
    simp only [Outside.see, Option.some.injEq] at hsee
    subst hsee
    simpa [receives, List.countP_append] using And.intro ih hle

/-- A FIFO queue holds one copy of each id: every id held has one, and none other has any. -/
def OneCopy (d : State B) : Prop :=
  ∀ id, count d.copies id ≤ 1 ∧ (0 < count d.copies id → d.messages.any (·.id == id))

omit [DecidableEq B] in
theorem oneCopy_send {config : Config} (hfifo : config.fifo = true) {d : State B}
    (h : OneCopy d) (m : Message B) : OneCopy (send config d m) := by
  intro id
  unfold send
  split
  · exact h id
  · next hnew =>
    by_cases hid : m.id = id
    · subst hid
      have h0 : count d.copies m.id = 0 := by
        rcases Nat.eq_zero_or_pos (count d.copies m.id) with h0 | hpos
        · exact h0
        · exact absurd ((h m.id).2 hpos) hnew
      simp [h0]
    · simp only [Events.count_bump_of_ne _ (Ne.symm hid)]
      refine ⟨(h id).1, fun hpos => ?_⟩
      simp only [List.any_append, (h id).2 hpos, Bool.true_or]

/-- In a FIFO queue each message is received at most `maxReceives` times. -/
theorem fifo_received_le (port : Port σ B) (config : Config) (hfifo : config.fifo = true)
    (initial : List (Message B)) {events : List (Event σ)} {d : State B}
    (h : (outside port config initial).after events = some d) (id : Nat) :
    receives port id events ≤ config.maxReceives := by
  have hone : OneCopy d := by
    refine (outside port config initial).after_invariant (fun _ => True) OneCopy ?_ ?_ ?_
      (fun _ _ => trivial) h
    · have : ∀ (l : List (Message B)) (d₀ : State B), OneCopy d₀ →
          OneCopy (l.foldl (send config) d₀) := by
        intro l; induction l with
        | nil => exact fun _ h => h
        | cons m rest ih => exact fun d₀ h => ih _ (oneCopy_send hfifo h m)
      exact this initial _ (fun id => by simp [count])
    · intro d x d' hd hallow
      simp only [outside] at hallow
      split at hallow
      · split at hallow
        · obtain rfl := Option.some.inj hallow
          intro id
          simpa [receive] using hd id
        · simp at hallow
      · simp at hallow
    · intro d out hd _
      have hd' : OneCopy (match port.deleted out with
          | some receipt => delete d receipt | none => d) := by
        split
        · intro id
          have hm : ∀ r, (delete d r).messages = d.messages := by
            intro r; unfold delete; split <;> rfl
          rw [copies_delete, hm]; exact hd id
        · exact hd
      simp only [outside]
      split
      · exact oneCopy_send hfifo hd' _
      · exact hd'
  exact Nat.le_trans (received_le port config initial h id)
    (by simpa using Nat.mul_le_mul_left config.maxReceives (hone id).1)

/-- A message deleted with its latest receipt is not received again, unless it is sent again. -/
theorem deleted_not_received (port : Port σ B) (config : Config) (initial : List (Message B))
    {d : State B} {x : σ.In} {receipt : Nat} {m : Message B}
    (hx : port.received x = some (receipt, m)) (hdel : m.id ∈ d.deleted) :
    (outside port config initial).allow d x = none := by
  simp [outside, hx, ready, hdel]

end Lanes.Queue
