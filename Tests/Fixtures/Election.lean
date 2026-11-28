/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
# Reference app: leader election

A fixture of the checker's tests (`Tests/Election.lean`, `Tests/Fair.lean`,
`Tests/SystemSound.lean`).

The election half of Raft. A node whose election timer fires starts a new term, votes for
itself and asks the others for their vote. A node grants at most one vote per term. A candidate
that collects votes from a majority becomes leader of that term.

Safety: at most one leader per term (`atMostOneLeaderPerTerm`). It rests on two facts: a node
votes once per term, and two majorities share a node.

The `votesOncePerTerm` switch exists to seed a bug. With it off, a node grants every request,
and the model checker finds two leaders in one term (`Tests/Election.lean`).

Following Ongaro's Raft (the election rules of `raft.tla`), without logs.
-/

namespace Tests.Fixtures.Election

open Lanes

/-- Whether more than half of `nodes` are in `votes`. Repeated votes count once. -/
def isMajority {α : Type} [DecidableEq α] (nodes votes : List α) : Bool :=
  2 * nodes.countP (· ∈ votes) > nodes.length

/-- A candidate carries the votes it has collected (rule 2.1). -/
inductive Role (N : Type) where
  | follower
  | candidate (votes : List N)
  | leader
  deriving DecidableEq, Repr, Hashable

/-- Term and vote are durable; the role is not. -/
structure Node (N : Type) where
  term : Nat
  /-- The node this node voted for in `term`, if any. -/
  votedFor : Option N
  role : Role N
  deriving DecidableEq, Repr, Hashable

inductive Msg (N : Type) where
  | electionTimeout
  | requestVote (term : Nat) (candidate : N)
  | vote (term : Nat) (voter : N)
  deriving DecidableEq, Repr, Hashable

abbrev sig (N : Type) [DecidableEq N] : Signature where
  Id := N
  Msg _ := Msg N

structure Config where
  /-- Real deployments randomise it per node. -/
  electionTimeout_ms : Nat := 150
  /-- Whether a node refuses a second vote in a term. Turn off only to seed a bug. -/
  votesOncePerTerm : Bool := true

variable {N : Type} [DecidableEq N]

def node (config : Config) (nodes : List N) (self : N) :
    (sig N).Actor self (Node N) where
  init := { term := 0, votedFor := none, role := .follower }
  step s
    | .electionTimeout =>
      match s.role with
      | .leader => (s, [])
      | _ =>
        let term := s.term + 1
        ({ term, votedFor := some self, role := .candidate [self] },
          (nodes.filter (· ≠ self)).map (fun p => .send p (.requestVote term self))
            ++ [.after config.electionTimeout_ms .electionTimeout])
    | .requestVote term candidate =>
      if term > s.term then
        ({ term, votedFor := some candidate, role := .follower },
          [.send candidate (.vote term self), .after config.electionTimeout_ms .electionTimeout])
      else if term == s.term && (s.votedFor.isNone || !config.votesOncePerTerm) then
        ({ s with votedFor := some candidate }, [.send candidate (.vote term self)])
      else (s, [])
    | .vote term voter =>
      match s.role with
      | .candidate votes =>
        if term == s.term then
          let votes := voter :: votes
          if isMajority nodes votes then ({ s with role := .leader }, [.cancel .electionTimeout])
          else ({ s with role := .candidate votes }, [])
        else (s, [])
      | _ => (s, [])
  recover s := ({ s with role := .follower }, [.after config.electionTimeout_ms .electionTimeout])

abbrev cluster (N : Type) [DecidableEq N] [Enum N] (config : Config) : System (sig N) where
  State _ := Node N
  actor self := node config Enum.all self
  accept x := nomatch x
  boot := Enum.all

/-- At most one leader per term. -/
def atMostOneLeaderPerTerm [Enum N] {config : Config} (c : SysState (cluster N config)) : Bool :=
  (Enum.all (α := N)).all fun a => (Enum.all (α := N)).all fun b =>
    a == b || !((c.state a).role == .leader && (c.state b).role == .leader
      && (c.state a).term == (c.state b).term)

def hasLeader [Enum N] {config : Config} (c : SysState (cluster N config)) : Bool :=
  (Enum.all (α := N)).any fun a => (c.state a).role == .leader

end Tests.Fixtures.Election
