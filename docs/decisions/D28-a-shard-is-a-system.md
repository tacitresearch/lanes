# D28. A shard is a system, and a cluster is runtimes with a router

Status: Partly superseded by D37 (the router between shards in one process)

`Lanes/Runtime/Shard.lean`; the in-process router of this section is gone (D37). `System.shard sys hosts` is `sys` as a
shard that hosts some of its actors sees it: a message to an actor hosted elsewhere leaves as
an output (a parcel), a parcel arriving is an input, and an actor not hosted only forwards. A
cluster starts one ordinary runtime per shard and routes parcels between them, on a lane that is
never full so that two shards cannot block each other.

Why not a kernel that knows about shards: the kernel and its proofs stay as they are, each
shard keeps the journal it already has, and the same `System.shard` with a router over a socket
is a system spread over machines. The work moves to one theorem, that shards and parcels in
flight together stand for a state of the one system, which is about composition and not about
any kernel.

Consequences:

- Outputs of different shards are not ordered among themselves.
- A cluster has no journal yet. Each shard would journal the parcels it receives, so messages
  need a codec, and a restarted shard must be sent again what its journal does not have.
- Back-pressure is at each shard's outside inbox. Between shards nothing is refused, so a
  shard that falls behind is noticed only by its queue.

The theorem (`Lanes/Runtime/ShardSound.lean`, `Lanes/Proof/Lossy.lean`). `System.split sys
hosts` is two shards joined, each parcel one emits an input of the other; a wired emit is a
direct send in a join, so a message between shards is one message in flight, as in `sys`.
`System.SplitReachable.merged`: in a run where every input from outside goes to the shard that
hosts its receiver and no parcel comes from outside, every state of the split, read as one
state, is a state `sys` reaches alone, up to `SysState.Equiv`. The proof is a forward
simulation, one event to one event of the same kind, carried by the invariant that nothing is
in flight to or from a copy that only forwards. Why it is not simpler:

- *Booting.* A join boots its left system first, and real shards boot independently, so the
  split's first state is `sys` booted in another order. Without stops that order is invisible
  up to `SysState.Equiv`. A boot actor that stops as it starts loses the messages already in
  flight to it, and which those are depends on the order: `fragile` in `Tests/Split.lean`
  reaches, split, a state it never reaches alone. The theorem assumes `System.SteadyBoot`
  (no boot actor stops as it starts, or the links to it are lossy). This is a property of
  booting shards one by one, not of `System.shard`, and the fix, if one is wanted, is in what
  a boot is.
- *State invariants need no assumption.* `System.Reachable.lossy`: whatever a system reaches,
  it reaches when every link may also lose messages, the same events with drops after each
  crash and stop. Where every link is lossy a stop loses nothing, so `SteadyBoot` holds, and an
  invariant of actor states proved for every environment transfers (`Invariant.split_state`).
- *Outputs.* Two equal outputs from different shards are two values in the split's outbox and
  one in `sys`, so the split may hand over the newer first. The correspondence is exact up to
  the order of the outputs waiting (`merged_exact`), which `SysState.Equiv` already ignores.
- *The copies that only forward.* `EnvModel.split` lets them neither crash nor restart by
  themselves; they are never started, because nothing is ever in flight to them. A statement
  for an arbitrary environment of the split would treat their starts and crashes as steps that
  change nothing.

Any number of shards (`Lanes/Runtime/ShardsSound.lean`). `System.shards sys hosts`, with
`hosts : σ.Id → Fin n`, is `System.joinAll` of the `n` shards `sys.shard (hosts · == k)`, a
family join whose wiring sends each parcel to the shard `hosts` names for its receiver; the
copies are named `(shard, actor)`. This is what `Peers` runs, with `home i` the address of
process `hosts i`. It is stated directly and not as nested splits, because the two-shard
theorem does not compose: the split of a split has shards of a join rather than of `sys`, and
its theorem concludes `Reachable`, which admits parcels from outside and inputs at the wrong
shard, where the inner split needs a well-routed run; a join with a split on one side is not a
split, and the theorem is about `split` only, not a congruence for `join`. Composing would need
the theorem restated to keep routing, and would still not give the system `Peers` runs. The
proof is the two-shard one over a product instead of a sum, so it has no case on the side and
is about 740 lines with the family join, against 1,040; it reuses that proof's boot lemmas, and a
boot shard by shard is `sys`'s boot regrouped, the same up to `SysState.Equiv` under
`SteadyBoot` (`SysState.boot_grouped`). The checks found nothing new: on three shards the bank
and a relay of three boot actors reach exactly the states of the system alone, and `fragile` is
again the only failure, gone where its link is lossy.
