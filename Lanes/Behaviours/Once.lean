/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Actor

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

end Lanes.Once
