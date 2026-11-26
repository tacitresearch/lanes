/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Behaviours.Server

/-!
# Acting once on a request that arrives twice

A client retries, and a link that retries hands a message over twice. The client names each
request by its own identity and a sequence number; `Once.actor` remembers, per client, the last
request it acted on and the effects of acting. That request again gets the same effects again,
without acting; an older one gets nothing. One entry per client is the bound (rule 2.6), as in
Raft's client sessions: a client sends its next request once the last one is answered (rule 1.5:
duplicate suppression is the endpoint's).

`Lanes.Semantics.Once` has the spec this implements, `Service.once`, and the proof for a
`Server` behind it.
-/

@[expose] public section

namespace Lanes.Once

structure Memo (C E : Type) where
  entries : List (C × Nat × List E) := []
  deriving Repr, BEq, Hashable

variable {C E : Type} [DecidableEq C]

namespace Memo

def find? (memo : Memo C E) (c : C) : Option (Nat × List E) :=
  (memo.entries.find? fun entry => decide (entry.1 = c)).map (·.2)

def record (memo : Memo C E) (c : C) (n : Nat) (effs : List E) : Memo C E :=
  ⟨(c, n, effs) :: memo.entries.filter fun entry => decide (entry.1 ≠ c)⟩

@[simp] theorem find?_empty (c : C) : ({} : Memo C E).find? c = none := rfl

@[simp] theorem find?_record_self (memo : Memo C E) (c : C) (n : Nat) (effs : List E) :
    (memo.record c n effs).find? c = some (n, effs) := by
  simp [find?, record]

theorem find?_record_of_ne (memo : Memo C E) {c c' : C} (n : Nat) (effs : List E)
    (h : c' ≠ c) : (memo.record c n effs).find? c' = memo.find? c' := by
  have hc : decide (c = c') = false := decide_eq_false (Ne.symm h)
  simp only [find?, record, List.find?_cons, hc, List.find?_filter]
  congr 2
  funext entry
  by_cases he : entry.1 = c' <;> simp [he, h]

end Memo

inductive Seen (E : Type) where
  | fresh
  | again (effs : List E)
  | stale

def Memo.seen (memo : Memo C E) (c : C) (n : Nat) : Seen E :=
  match memo.find? c with
  | some (last, effs) => if n = last then .again effs else if n < last then .stale else .fresh
  | none => .fresh

/-- `a`, acting once on each request `key` names. A message `key` reads as `none` is not a
request and is handled as `a` handles it. The memo is durable: a restart that forgot it would
act on a repeat. -/
def actor {S Msg : Type} (a : Actor S Msg E) (key : Msg → Option (C × Nat)) :
    Actor (S × Memo C E) Msg E where
  init := (a.init, {})
  step
    | (s, memo), m =>
      match key m with
      | none => let (s', effs) := a.step s m; ((s', memo), effs)
      | some (c, n) =>
        match memo.seen c n with
        | .fresh => let (s', effs) := a.step s m; ((s', memo.record c n effs), effs)
        | .again effs => ((s, memo), effs)
        | .stale => ((s, memo), [])
  recover
    | (s, memo) => let (s', effs) := a.recover s; ((s', memo), effs)

section Step

variable {S Msg : Type} (a : Actor S Msg E) (key : Msg → Option (C × Nat)) (s : S)
  (memo : Memo C E) (m : Msg)

theorem step_of_none (hk : key m = none) :
    (actor a key).step (s, memo) m = (((a.step s m).1, memo), (a.step s m).2) := by
  simp [actor, hk]

theorem step_of_fresh {c : C} {n : Nat} (hk : key m = some (c, n)) (hs : memo.seen c n = .fresh) :
    (actor a key).step (s, memo) m =
      (((a.step s m).1, memo.record c n (a.step s m).2), (a.step s m).2) := by
  simp [actor, hk, hs]

theorem step_of_again {c : C} {n : Nat} {effs : List E} (hk : key m = some (c, n))
    (hs : memo.seen c n = .again effs) : (actor a key).step (s, memo) m = ((s, memo), effs) := by
  simp [actor, hk, hs]

theorem step_of_stale {c : C} {n : Nat} (hk : key m = some (c, n)) (hs : memo.seen c n = .stale) :
    (actor a key).step (s, memo) m = ((s, memo), []) := by
  simp [actor, hk, hs]

theorem recover_eq (p : S × Memo C E) :
    (actor a key).recover p = (((a.recover p.1).1, p.2), (a.recover p.1).2) :=
  rfl

end Step

variable {In Out S : Type} [DecidableEq In] [DecidableEq Out]

/-- A `Server` that acts once on each request `key` names. -/
abbrev server (svc : Service (Server.sig In Out) S) (key : In → C × Nat) :
    System (Server.sig In Out) where
  State _ := S × Memo C (Effect (Server.sig In Out) ())
  actor _ := actor (Server.actor svc) fun x => some (key x)
  accept x := ⟨(), x⟩

end Lanes.Once
