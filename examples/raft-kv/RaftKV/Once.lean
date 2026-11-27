/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKV.Protocol

/-!
# A machine whose clients name their commands

A client retries, and a node cannot tell a retry from a new request: it appends both. So the
memo of `Lanes.Once` goes in the machine, not in a node: a command names its client and the
client's number for it, and `Machine.once` remembers, per client, the last number it acted on
and its answer. That number again is answered as before, without acting; an older one is
answered `none`, since its answer is no longer kept. The memo is part of the state the cluster
replicates, so an entry appended twice takes effect once and is answered twice, and the
protocol does not change.

`onceCluster` is the cluster with that machine as its clients see it: an answer is the named
answer the machine gave, and an empty one is not handed over.
-/

namespace RaftKV

open Lanes

lanes_data structure Named (Cl C : Type) where
  client : Cl
  seq : Nat
  cmd : C
  deriving DecidableEq, Repr, Hashable, Codable

variable {N Cl C R M : Type} [DecidableEq N] [DecidableEq Cl] [DecidableEq C] [DecidableEq R]

def Request.key (x : Request N (Named Cl C)) : Cl × Nat :=
  (x.cmd.client, x.cmd.seq)

def Machine.once (machine : Machine C R M) (Cl : Type) [DecidableEq Cl] :
    Machine (Named Cl C) (Option (Named Cl R)) (M × Once.Memo Cl (Named Cl R)) where
  init := (machine.init, {})
  apply
    | (m, memo), ⟨c, n, cmd⟩ =>
      match memo.seen c n with
      | .fresh => (((machine.apply m cmd).1, memo.record c n [⟨c, n, (machine.apply m cmd).2⟩]),
          some ⟨c, n, (machine.apply m cmd).2⟩)
      | .again answers => ((m, memo), answers.head?)
      | .stale => ((m, memo), none)

/-- To clients that name their commands, the cluster is the machine, each answer named as its
command. -/
def named (N Cl : Type) [DecidableEq N] [DecidableEq Cl] (machine : Machine C R M) :
    Service (Request N (Named Cl C)) (Named Cl R) M where
  init := machine.init
  step m x := ((machine.apply m x.cmd.cmd).1,
    [⟨x.cmd.client, x.cmd.seq, (machine.apply m x.cmd.cmd).2⟩])

abbrev onceCluster (N Cl : Type) [DecidableEq N] [DecidableEq Cl] [Enum N] (config : Config)
    (machine : Machine C R M) :=
  (cluster N config (machine.once Cl)).filterMapIO (In := Request N (Named Cl C)) id
    Response.res

end RaftKV
