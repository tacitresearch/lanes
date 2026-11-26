/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
# Raft

A cluster of nodes that replicate a log of commands and apply it, in order, to a state machine.
To its clients the cluster is that one machine (`spec`): this is what is checked, as refinement.

One node is one actor, and its step function is all of the protocol: elections, replication,
commitment and applying. It follows Ongaro's Raft with these choices:

- A leader keeps one number per follower, how much of the follower's log is known to match its
  own, and sends what follows that, at most `maxAppend` entries in one message. A follower
  acknowledges where what it was sent ends, and an acknowledgement that tells the leader
  something new brings the next batch. Nothing is ever refused and retried.
- A new leader knows of no follower's log. It sends each the end of its own, which a follower
  that was up to date takes at once. One that is not ignores it, and is sent the log from its
  start, batch by batch, from the first heartbeat on.
- A new entry goes at once to the followers that hold all before it. One that is behind gets it
  in its turn.
- Only grants and acknowledgements are sent. A node learns of a later term from the requests of
  that term.
- The node that took a command from its client answers it, when it applies the entry.
- No change of membership and no compaction of the log.

`Config` has two switches that seed the two classic bugs, for the model checker to find.
-/

namespace RaftKV

open Lanes

abbrev ReqId := Nat

/-- What the cluster replicates: commands `C`, results `R`, state `M`. -/
structure Machine (C R M : Type) where
  init : M
  apply : M → C → M × R

structure Entry (N C : Type) where
  term : Nat
  /-- The node that took the command from its client, and answers it. -/
  origin : N
  req : ReqId
  cmd : C
  deriving DecidableEq, Repr, Hashable

inductive Role (N : Type) where
  | follower
  | candidate (votes : List N)
  /-- For each follower heard from, how much of its log is known to match this leader's. -/
  | leader (matched : List (N × Nat))
  deriving DecidableEq, Repr, Hashable

/-- Everything but the role is durable. Entries are numbered from 1: entry `i` is `log[i - 1]`,
and `commit` and `applied` count entries. -/
structure Node (N C M : Type) where
  term : Nat
  votedFor : Option N
  log : List (Entry N C)
  commit : Nat
  applied : Nat
  machine : M
  role : Role N
  deriving Repr, Hashable

instance {N C M : Type} [DecidableEq N] [DecidableEq C] [BEq M] : BEq (Node N C M) where
  beq a b := a.term == b.term && a.votedFor == b.votedFor && a.log == b.log
    && a.commit == b.commit && a.applied == b.applied && a.machine == b.machine && a.role == b.role

instance {N C M : Type} [DecidableEq N] [DecidableEq C] [BEq M] [LawfulBEq M] :
    LawfulBEq (Node N C M) where
  rfl {a} := by
    change (a.term == a.term && a.votedFor == a.votedFor && a.log == a.log && a.commit == a.commit
      && a.applied == a.applied && a.machine == a.machine && a.role == a.role) = true
    simp
  eq_of_beq {a b} h := by
    change (a.term == b.term && a.votedFor == b.votedFor && a.log == b.log && a.commit == b.commit
      && a.applied == b.applied && a.machine == b.machine && a.role == b.role) = true at h
    cases a
    cases b
    simpa [and_assoc] using h

inductive Msg (N C : Type) where
  | electionTimeout
  | heartbeat
  | requestVote (term : Nat) (candidate : N) (lastIndex lastTerm : Nat)
  | vote (term : Nat) (voter : N)
  | append (term : Nat) (leader : N) (prevIndex prevTerm : Nat) (entries : List (Entry N C))
      (commit : Nat)
  | appended (term : Nat) (follower : N) (matched : Nat)
  | propose (req : ReqId) (cmd : C)
  deriving DecidableEq, Repr, Hashable

structure Request (N C : Type) where
  req : ReqId
  /-- The node the client sends to. A node that is not the leader drops the request. -/
  via : N
  cmd : C
  deriving DecidableEq, Repr, Hashable

structure Response (R : Type) where
  req : ReqId
  res : R
  deriving DecidableEq, Repr, Hashable

abbrev sig (N C R : Type) [DecidableEq N] [DecidableEq C] [DecidableEq R] : Signature where
  Id := N
  Msg _ := Msg N C
  In := Request N C
  Out := Response R

structure Config where
  /-- Real deployments randomise it per node. -/
  electionTimeout_ms : Nat := 150
  heartbeat_ms : Nat := 50
  /-- Whether a node refuses its vote to a candidate whose log is behind its own. Turn off only
  to seed a bug: a leader may then lack a committed entry. -/
  votesForUpToDateOnly : Bool := true
  /-- Whether a leader commits by counting only entries of its own term. Turn off only to seed a
  bug: an entry of an earlier term on a majority can still be overwritten. -/
  commitsOwnTermOnly : Bool := true
  /-- The most entries one `append` carries; zero counts as one. Entries are not measured, so
  this many of the largest must fit in one message of the transport. -/
  maxAppend : Nat := 8

/-- To its clients, the cluster is the machine. -/
def spec {N C R M : Type} [DecidableEq N] [DecidableEq C] [DecidableEq R]
    (machine : Machine C R M) : Service (sig N C R) M where
  init := machine.init
  step m r := ((machine.apply m r.cmd).1, [⟨r.req, (machine.apply m r.cmd).2⟩])

section Log

variable {N C : Type}

/-- The term of entry `index`, and 0 for the empty log before entry 1. -/
def termAt (log : List (Entry N C)) (index : Nat) : Nat :=
  if index = 0 then 0 else (log[index - 1]?.map (·.term)).getD 0

def lastTerm (log : List (Entry N C)) : Nat :=
  termAt log log.length

/-- A follower's entries after some point, given the leader's entries after the same point.
The follower keeps what agrees, replaces what conflicts and everything after it, and keeps what
it has beyond the leader's, since an older and shorter message may arrive late. -/
def merge : (own sent : List (Entry N C)) → List (Entry N C)
  | e :: own, n :: sent => if e.term = n.term then e :: merge own sent else n :: sent
  | [], sent => sent
  | own, [] => own

variable [DecidableEq N]

def matchedOf (matched : List (N × Nat)) (p : N) : Nat :=
  (matched.lookup p).getD 0

/-- Acknowledgements may arrive out of order, so the larger is kept. -/
def raise (matched : List (N × Nat)) (p : N) (index : Nat) : List (N × Nat) :=
  (p, max index (matchedOf matched p)) :: matched.filter (·.1 ≠ p)

end Log

section Node

variable {N C R M : Type} [DecidableEq N] [DecidableEq C] [DecidableEq R]
variable (config : Config) (nodes : List N) (machine : Machine C R M) (self : N)

abbrev Eff := Effect (sig N C R) self

def armElection : Eff self (N := N) (C := C) (R := R) :=
  .after config.electionTimeout_ms .electionTimeout

/-- Apply the entries that are committed and not yet applied, answering those this node took
from a client. -/
def applyCommitted (s : Node N C M) : Node N C M × List (Eff self (N := N) (C := C) (R := R)) :=
  ((s.log.take s.commit).drop s.applied).foldl (init := (s, [])) fun (s, effs) entry =>
    let result := machine.apply s.machine entry.cmd
    ({ s with machine := result.1, applied := s.applied + 1 },
      if entry.origin = self then effs ++ [.emit ⟨entry.req, result.2⟩] else effs)

/-- One batch: the entries after `prev`, as many as an `append` carries. -/
def appendFrom (s : Node N C M) (prev : Nat) (p : N) : Eff self (N := N) (C := C) (R := R) :=
  .send p (.append s.term self prev (termAt s.log prev)
    ((s.log.drop prev).take (max 1 config.maxAppend)) s.commit)

def appendTo (s : Node N C M) (matched : List (N × Nat)) (p : N) :
    Eff self (N := N) (C := C) (R := R) :=
  appendFrom config self s (min (matchedOf matched p) s.log.length) p

def broadcast (s : Node N C M) (matched : List (N × Nat)) :
    List (Eff self (N := N) (C := C) (R := R)) :=
  (nodes.filter (· ≠ self)).map (appendTo config self s matched)

/-- The followers known to hold all of the leader's log. Sending a batch on every proposal to
one that is behind as well would make each write cost a batch for every node that is down. -/
def abreast (s : Node N C M) (matched : List (N × Nat)) : List N :=
  (nodes.filter (· ≠ self)).filter (s.log.length ≤ matchedOf matched ·)

/-- The nodes whose logs are known to hold entry `index` of the leader's log: itself and the
followers that acknowledged it. -/
def holders (matched : List (N × Nat)) (index : Nat) : List N :=
  self :: (matched.filter (index ≤ ·.2)).map (·.1)

/-- The largest index a majority holds, among those the leader may commit by counting. -/
def advanceCommit (s : Node N C M) (matched : List (N × Nat)) : Node N C M :=
  let committable := fun index =>
    Quorum.isMajority nodes (holders self matched index)
      && (termAt s.log index == s.term || !config.commitsOwnTermOnly)
  match ((List.range' (s.commit + 1) (s.log.length - s.commit)).reverse.find? committable) with
  | some index => { s with commit := index }
  | none => s

/-- A node that hears of a later term is a follower in it and has not voted. A leader that
steps down has no election timer, so it gets one. -/
def enterTerm (s : Node N C M) (term : Nat) :
    Node N C M × List (Eff self (N := N) (C := C) (R := R)) :=
  if term > s.term then
    ({ s with term, votedFor := none, role := .follower },
      match s.role with
      | .leader _ => [.cancel .heartbeat, armElection config self]
      | _ => [])
  else (s, [])

def lead (s : Node N C M) : Node N C M × List (Eff self (N := N) (C := C) (R := R)) :=
  let s := advanceCommit config nodes self { s with role := .leader [] } []
  let (s, answers) := applyCommitted machine self s
  let tail := s.log.length - max 1 config.maxAppend
  (s, answers ++ [.cancel .electionTimeout]
    ++ (nodes.filter (· ≠ self)).map (appendFrom config self s tail)
    ++ [.after config.heartbeat_ms .heartbeat])

def onElectionTimeout (s : Node N C M) :
    Node N C M × List (Eff self (N := N) (C := C) (R := R)) :=
  match s.role with
  | .leader _ => (s, [])
  | _ =>
    let s := { s with term := s.term + 1, votedFor := some self, role := .candidate [self] }
    if Quorum.isMajority nodes [self] then lead config nodes machine self s
    else
      (s, (nodes.filter (· ≠ self)).map (fun p =>
          .send p (.requestVote s.term self s.log.length (lastTerm s.log)))
        ++ [armElection config self])

def onRequestVote (s : Node N C M) (term : Nat) (candidate : N) (lastIndex last : Nat) :
    Node N C M × List (Eff self (N := N) (C := C) (R := R)) :=
  let (s, effs) := enterTerm config self s term
  let free := s.votedFor.isNone || s.votedFor == some candidate
  let upToDate := last > lastTerm s.log || (last == lastTerm s.log && lastIndex ≥ s.log.length)
  if term == s.term && free && (upToDate || !config.votesForUpToDateOnly) then
    ({ s with votedFor := some candidate },
      effs ++ [.send candidate (.vote term self), armElection config self])
  else (s, effs)

def onVote (s : Node N C M) (term : Nat) (voter : N) :
    Node N C M × List (Eff self (N := N) (C := C) (R := R)) :=
  match s.role with
  | .candidate votes =>
    if term == s.term then
      if Quorum.isMajority nodes (voter :: votes) then lead config nodes machine self s
      else ({ s with role := .candidate (voter :: votes) }, [])
    else (s, [])
  | _ => (s, [])

def onAppend (s : Node N C M) (term : Nat) (leader : N) (prevIndex prevTerm : Nat)
    (entries : List (Entry N C)) (leaderCommit : Nat) :
    Node N C M × List (Eff self (N := N) (C := C) (R := R)) :=
  let (s, effs) := enterTerm config self s term
  if term < s.term then (s, effs)
  else
    match s.role with
    | .leader _ => (s, effs)
    | _ =>
      let s := { s with role := .follower }
      if prevIndex ≤ s.log.length && termAt s.log prevIndex == prevTerm then
        let last := prevIndex + entries.length
        let s := { s with
          log := s.log.take prevIndex ++ merge (s.log.drop prevIndex) entries
          commit := max s.commit (min leaderCommit last) }
        let (s, answers) := applyCommitted machine self s
        (s, effs ++ answers ++ [.send leader (.appended term self last), armElection config self])
      else (s, effs ++ [armElection config self])

def onAppended (s : Node N C M) (term : Nat) (follower : N) (index : Nat) :
    Node N C M × List (Eff self (N := N) (C := C) (R := R)) :=
  match s.role with
  | .leader matched =>
    if term == s.term then
      let news := matchedOf matched follower < index
      let matched := raise matched follower index
      let s := advanceCommit config nodes self { s with role := .leader matched } matched
      let (s, answers) := applyCommitted machine self s
      (s, if news && index < s.log.length then
        answers ++ [appendTo config self s matched follower] else answers)
    else (s, [])
  | _ => (s, [])

def onPropose (s : Node N C M) (req : ReqId) (cmd : C) :
    Node N C M × List (Eff self (N := N) (C := C) (R := R)) :=
  match s.role with
  | .leader matched =>
    let abreast := abreast nodes self s matched
    let s := { s with log := s.log ++ [{ term := s.term, origin := self, req, cmd }] }
    let s := advanceCommit config nodes self s matched
    let (s, answers) := applyCommitted machine self s
    (s, answers ++ abreast.map (appendTo config self s matched))
  | _ => (s, [])

def node : (sig N C R).Actor self (Node N C M) where
  init := { term := 0, votedFor := none, log := [], commit := 0, applied := 0
            machine := machine.init, role := .follower }
  step s
    | .electionTimeout => onElectionTimeout config nodes machine self s
    | .heartbeat =>
      match s.role with
      | .leader matched =>
        (s, broadcast config nodes self s matched ++ [.after config.heartbeat_ms .heartbeat])
      | _ => (s, [])
    | .requestVote term candidate lastIndex last =>
      onRequestVote config self s term candidate lastIndex last
    | .vote term voter => onVote config nodes machine self s term voter
    | .append term leader prevIndex prevTerm entries commit =>
      onAppend config machine self s term leader prevIndex prevTerm entries commit
    | .appended term follower index => onAppended config nodes machine self s term follower index
    | .propose req cmd => onPropose config nodes machine self s req cmd
  recover s := ({ s with role := .follower }, [armElection config self])

end Node

abbrev cluster (N : Type) {C R M : Type} [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N]
    (config : Config) (machine : Machine C R M) : System (sig N C R) where
  State _ := Node N C M
  actor self := node config Enum.all machine self
  accept r := ⟨r.via, .propose r.req r.cmd⟩
  boot := Enum.all

end RaftKV
