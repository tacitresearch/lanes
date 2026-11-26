/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKV.Protocol

/-!
What a Raft cluster keeps true, as functions the model checker evaluates in every state. They
are the invariants of Ongaro's safety argument. The property clients care about, that the
cluster is the machine, is not here: it is refinement to `spec`, checked by a monitor.
-/

namespace RaftKV

open Lanes

variable {N C R M : Type} [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N]
variable {config : Config} {machine : Machine C R M}

abbrev Cluster (N : Type) {C R M : Type} [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N]
    (config : Config) (machine : Machine C R M) :=
  SysState (cluster N config machine)

def isLeader (s : Node N C M) : Bool :=
  s.role matches .leader _

def pairs (p : N → N → Bool) : Bool :=
  (Enum.all (α := N)).all fun a => (Enum.all (α := N)).all fun b => p a b

def electionSafety (c : Cluster N config machine) : Bool :=
  pairs fun a b => a == b
    || !(isLeader (c.state a) && isLeader (c.state b) && (c.state a).term == (c.state b).term)

/-- Two logs that agree on the term of an entry agree on everything up to it. -/
def logMatching (c : Cluster N config machine) : Bool :=
  pairs fun a b =>
    let la := (c.state a).log
    let lb := (c.state b).log
    (List.range (min la.length lb.length)).all fun i =>
      termAt la (i + 1) != termAt lb (i + 1) || la.take (i + 1) == lb.take (i + 1)

/-- What two nodes have both committed is the same: so they apply the same commands in the same
order. -/
def committedAgree (c : Cluster N config machine) : Bool :=
  pairs fun a b =>
    let n := min (c.state a).commit (c.state b).commit
    (c.state a).log.take n == (c.state b).log.take n

/-- A leader has every entry that a node no further on in terms knows to be committed. Raft's
leader completeness speaks of the term an entry was committed in, which no state records. A
node learns of a commitment in that term or a later one, so its own term bounds it: this is
what of leader completeness can be read off a state. -/
def leaderComplete (c : Cluster N config machine) : Bool :=
  pairs fun l a =>
    !isLeader (c.state l) || (c.state a).term > (c.state l).term
      || (c.state l).log.take (c.state a).commit == (c.state a).log.take (c.state a).commit

def appliedWithinCommit (c : Cluster N config machine) : Bool :=
  (Enum.all (α := N)).all fun a => (c.state a).applied ≤ (c.state a).commit

/-- Holds only because a leader never replaces a committed entry: it is leader completeness seen
from a follower. -/
def commitWithinLog (c : Cluster N config machine) : Bool :=
  (Enum.all (α := N)).all fun a => (c.state a).commit ≤ (c.state a).log.length

def entryTermsWithinTerm (c : Cluster N config machine) : Bool :=
  (Enum.all (α := N)).all fun a => (c.state a).log.all (·.term ≤ (c.state a).term)

end RaftKV
