/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKVProofs.Refines
import RaftKVProofs.Once
import RaftKVProofs.Checked

/-!
# The top theorem

What `Check.lean` checks with a monitor on three nodes, proved for every cluster: to its clients
the cluster is the machine it replicates, each command taking effect at one instant between its
arrival and its answer. The proof is `RaftKVProofs/Refines.lean`, on the invariants of
`RaftKV/Proofs`.

The same with the machine behind its memo, once per command and with no assumption on the
environment, is `RaftKVProofs/Once.lean`. What a PASS of `Check.lean` means is
`RaftKVProofs/Checked.lean`.

This library needs `Lanes.Semantics`, the proof layer. Nothing executable imports it.
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

/--
The cluster implements the machine once per command, whatever every link loses, repeats or
reorders, those from clients included, and whichever nodes crash and restart. The machine is
behind its memo (`Machine.once`): a command names its client and the client's number for it,
and is answered with its name. A command sent again, or handed to a node twice, takes effect
at most once and may be answered again; an answer the memo no longer keeps is not handed over
(`onceCluster`).
-/
def ImplementsMachineOnce (N Cl : Type) {C R M : Type} [DecidableEq N] [DecidableEq Cl]
    [DecidableEq C] [DecidableEq R] [Enum N] (config : Config) (machine : Machine C R M) : Prop :=
  ∀ env, (onceCluster N Cl config machine).ImplementsOnce env (named N Cl machine) Request.key

/-- With both switches on, every cluster implements its machine once per command, in every
environment. -/
theorem implementsMachine_once (N Cl : Type) {C R M : Type} [DecidableEq N] [DecidableEq Cl]
    [DecidableEq C] [DecidableEq R] [Enum N] (config : Config) (machine : Machine C R M)
    (hup : config.votesForUpToDateOnly = true) (hown : config.commitsOwnTermOnly = true) :
    ImplementsMachineOnce N Cl config machine :=
  fun env => onceCluster_implements hup hown env

/-- info: 'RaftKV.implementsMachine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.implementsMachine

/-- info: 'RaftKV.cluster_implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.cluster_implements

/-- info: 'RaftKV.recording_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.recording_refines

/-- info: 'RaftKV.implementsMachine_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.implementsMachine_once

/-- info: 'RaftKV.onceCluster_implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.onceCluster_implements

/-- info: 'RaftKV.recording_refines_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.recording_refines_once

/-- info: 'RaftKV.always_of_pass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.always_of_pass

/-- info: 'RaftKV.monitor_of_pass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.monitor_of_pass

/-- info: 'RaftKV.traces_of_pass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.traces_of_pass

end RaftKV
