/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import RaftKV.Protocol

/-!
# The top theorem, stated

What `Check.lean` checks with a monitor on three nodes, as a proposition for every cluster: to
its clients the cluster is the machine it replicates, each command taking effect at one instant
between its arrival and its answer. It is not proved. `RaftKV/Proofs/Commit.lean` has what the
proof starts from: what a majority has held in a term (`Chosen`) is never lost and every node's
commit index is within it, so the commands that have taken effect are one growing list.

This file needs `Lanes.Semantics`, and so Mathlib. It is a library of its own that nothing
executable imports.
-/

namespace RaftKV

open Lanes

/--
The cluster implements the machine, whatever the links between nodes lose, repeat or reorder and
whichever nodes crash and restart. The one assumption on the environment is that a client's
request is not handed to a node twice: a node cannot tell a request repeated by the link from
one the client made twice, and appends both. Expected to hold when both switches of `config` are
on.
-/
def ImplementsMachine (N : Type) {C R M : Type} [DecidableEq N] [DecidableEq C] [DecidableEq R]
    [Enum N] (config : Config) (machine : Machine C R M) : Prop :=
  ∀ env : EnvModel (sig N C R), (∀ node, (env.link none node).duplicating = false) →
    (cluster N config machine).Implements env (spec machine)

end RaftKV
