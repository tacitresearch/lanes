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

/-! What the proof of commitment uses on the way, as far as a state without its history shows
it. The proof's own invariants speak of every state a node has been in; these are what they say
of the present one. -/

def termsSorted (c : Cluster N config machine) : Bool :=
  (Enum.all (α := N)).all fun a =>
    ((c.state a).log.zip ((c.state a).log.drop 1)).all fun (e, next) => e.term ≤ next.term

/-- A candidate holds no entry of the term it stands in. -/
def candidatesBehind (c : Cluster N config machine) : Bool :=
  (Enum.all (α := N)).all fun a =>
    match (c.state a).role with
    | .candidate _ => (c.state a).log.all (·.term < (c.state a).term)
    | _ => true

/-- A request for a vote tells the truth about the log of a node still standing. -/
def requestsCurrent (c : Cluster N config machine) : Bool :=
  c.net.all fun e =>
    match e.msg with
    | .requestVote term candidate lastIndex last =>
      let s := c.state candidate
      !(s.term == term && s.role matches .candidate _)
        || (lastIndex == s.log.length && last == lastTerm s.log)
    | _ => true

/-- Nobody has voted for a node in a term that node has not reached. -/
def votesKnown (c : Cluster N config machine) : Bool :=
  (Enum.all (α := N)).all fun a =>
    match (c.state a).votedFor with
    | some candidate => (c.state a).term ≤ (c.state candidate).term
    | none => true

/-- What a leader believes of a follower in its term is so. -/
def matchedHeld (c : Cluster N config machine) : Bool :=
  pairs fun l f =>
    match (c.state l).role with
    | .leader matched =>
      matched.all fun (p, m) =>
        p != f || (c.state f).term != (c.state l).term
          || (m ≤ (c.state f).log.length && m ≤ (c.state l).log.length
            && (c.state f).log.take m == (c.state l).log.take m)
    | _ => true

/-- An acknowledgement in flight is true of a follower still in the leader's term. -/
def acksHeld (c : Cluster N config machine) : Bool :=
  c.net.all fun e =>
    match e.msg with
    | .appended term f m =>
      (Enum.all (α := N)).all fun l =>
        !(isLeader (c.state l) && (c.state l).term == term && (c.state f).term == term)
          || (m ≤ (c.state f).log.length && m ≤ (c.state l).log.length
            && (c.state f).log.take m == (c.state l).log.take m)
    | _ => true

/-- An `append` in flight was cut from its leader's log and claims no more committed than the
leader has. -/
def appendsCut (c : Cluster N config machine) : Bool :=
  c.net.all fun e =>
    match e.msg with
    | .append term l prev prevTerm entries commit =>
      let s := c.state l
      !(isLeader s && s.term == term)
        || (prev ≤ s.log.length && prevTerm == termAt s.log prev
          && entries.isPrefixOf (s.log.drop prev) && commit ≤ s.commit)
    | _ => true

/-! What the proof that the cluster is the machine uses of a state. -/

omit [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N] in
/-- The machine after `entries`. -/
def Machine.run (machine : Machine C R M) (m : M) (entries : List (Entry N C)) : M :=
  entries.foldl (fun m entry => (machine.apply m entry.cmd).1) m

def appliedAllCommitted (c : Cluster N config machine) : Bool :=
  (Enum.all (α := N)).all fun a => (c.state a).applied == (c.state a).commit

/-- Each node's machine is the replicated one run over the entries the node has applied. -/
def machinesRun [BEq M] (c : Cluster N config machine) : Bool :=
  (Enum.all (α := N)).all fun a =>
    (c.state a).machine == machine.run machine.init ((c.state a).log.take (c.state a).applied)

/-- No node sends a request: those in flight came from clients. -/
def requestsFromClients (c : Cluster N config machine) : Bool :=
  c.net.all fun e =>
    match e.msg with
    | .propose _ _ => e.src.isNone
    | _ => true

end RaftKV
