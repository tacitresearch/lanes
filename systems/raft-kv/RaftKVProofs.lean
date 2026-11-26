/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKVProofs.Refines

/-!
# The top theorem

What `Check.lean` checks with a monitor on three nodes, proved for every cluster: to its clients
the cluster is the machine it replicates, each command taking effect at one instant between its
arrival and its answer. The proof is `RaftKVProofs/Refines.lean`, on the invariants of
`RaftKV/Proofs`.

This library needs `Lanes.Semantics`, and so Mathlib. Nothing executable imports it.
-/

namespace RaftKV

open Lanes

/--
The cluster implements the machine, whatever the links between nodes lose, repeat or reorder and
whichever nodes crash and restart. The one assumption on the environment is that a client's
request is not handed to a node twice: a node cannot tell a request repeated by the link from
one the client made twice, and appends both. `Check.lean` has the run that shows it is needed.
-/
def ImplementsMachine (N : Type) {C R M : Type} [DecidableEq N] [DecidableEq C] [DecidableEq R]
    [Enum N] (config : Config) (machine : Machine C R M) : Prop :=
  ∀ env : EnvModel (sig N C R), (∀ node, (env.link none node).duplicating = false) →
    (cluster N config machine).Implements env (spec machine)

/-- With both switches on, every cluster implements its machine. -/
theorem implementsMachine (N : Type) {C R M : Type} [DecidableEq N] [DecidableEq C]
    [DecidableEq R] [Enum N] (config : Config) (machine : Machine C R M)
    (hup : config.votesForUpToDateOnly = true) (hown : config.commitsOwnTermOnly = true) :
    ImplementsMachine N config machine :=
  fun env henv => cluster_implements hup hown env henv

/-- info: 'RaftKV.implementsMachine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.implementsMachine

/-- info: 'RaftKV.cluster_implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.cluster_implements

/-- info: 'RaftKV.recording_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.recording_refines

end RaftKV
