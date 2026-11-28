# D66. A migration carries the old kernel across a deploy, once, with a proof

Status: Superseded by new-volatile-actors.md

*Supersedes the part of D24 and D36 that has a changed system refuse its old files.*

A real application changes its state and message types between deploys. Until now the files of
a shard carried a name (`system := "ledger 4"`), bumped by hand when a type changed, and the
binary with the new types refused the old files: the deploy started empty. A migration lets the
new version read the old files and go on, and says what the proofs of the new version still say
afterwards.

## What is migrated: the kernel, at a start, after the old code has replayed the journal

The binary of version 2 keeps version 1's system: its types, codecs and step functions, frozen
in a module of their own. A start that finds files of version 1 loads them as version 1 did,
snapshot and journal through version 1's step functions, so the kernel is exactly the one the
old shard had (`Disk.Torn.load`, unchanged). It then migrates that kernel: every actor's state,
every message queued or waiting on a timer, every output not yet handed over. It saves the
result as a snapshot under the new name and replaces the journal by one that begins at that
mark. From then on nothing of version 1 is read again. The pure part is `Journal.Upgrade.start`
and `Disk.begin`, in `Lanes/Durable/Upgrade.lean`; the maps and the proof are a `Migration`, in
`Lanes/Durable/Migration.lean`.

The alternatives:

- *Migrate the journalled inputs and replay them through the new step functions*, the usual
  event-sourcing upgrade. Rejected: it changes history. The outputs the old shard handed over,
  answers a client has, were computed by the old functions, and a replay through the new ones
  rebuilds a state that may disagree with them: a transfer refused then is accepted now, a Raft
  node votes otherwise (D36 met this with timeouts). It also does not remove the need to migrate
  states, since a snapshot holds states and the journal before its mark is gone.
- *Migrate only the snapshot, and refuse a journal with entries after its mark.* Rejected:
  there is no clean shutdown that leaves an empty tail (rule 3.3), so almost every real start
  would be refused. The old step functions are needed for the tail.
- *A version tag on each persisted value* (a versioned codec that reads any older version by
  decoding with the old codec and migrating). Rejected as the on-disk mechanism. A record is an
  opaque byte string, so a tag cannot be told apart from an old untagged value, and existing
  files have none: a file-level marker is needed anyway. And a file never mixes versions,
  because a migration rewrites the whole state at once. The idea survives at the type level:
  `lanes_data … from Old := f` declares how a value of the previous version becomes one of this
  (`T.migrate`, an instance of `Migrate`), and a `Migration` takes states and messages through
  those functions.

The cost is that the old version's code stays in the binary as long as files of that version
may exist. Only its step functions and codecs are needed, not those of versions in between: a
binary of version 3 that must read files of version 1 keeps version 1's system and a migration
from 1 to 3.

## What the proofs say across a migration

Lanes' theorems are about runs of one system from its boot. After a migration the new shard's
run starts from the migrated kernel, which boot never gives. So:

- *What carries over* is a property of each new actor that the actor's own steps and restarts
  keep and that holds at its initial state (`Actor.Inductive`), provided the migration lands in
  it. Every kernel theorem is about runs from the kernel's state whatever it is
  (`Kernel.exec_sound`), so such a property holds of every actor in every state the new shard
  reaches (`Kernel.exec_inductive`, `Migration.inv_exec`).
- *What does not* is an invariant proved only over states reachable from boot
  (`System.Invariant`, `Actor.Invariant` without induction), and refinement to the spec: the
  migrated state need not be reachable from boot. An application that wants one of those after
  a migration proves it inductive, or proves the migrated state reachable.
- *The obligation is a type.* `Migration old new` carries the maps of identities (injective:
  two actors never become one), states, messages and outputs, an invariant `inv` of each new
  actor with `keeps : ∀ j, (new.actor j).Inductive (inv j)`, and
  `lands : ∀ i s, (old.actor i).Reachable s → inv (id i) (state i s)`. It cannot be built
  without the proof. `lands` quantifies over the states an old actor reaches on its own, which
  every actor of a kernel the old shard can have is in (`Kernel.exec_cell_reachable`), so the
  application proves it from the old version's own invariants.
- *The new run starts from the old state, migrated*: `Migration.cell_kernel` says the migrated
  kernel holds each old actor's cell migrated, when an actor never written to migrates to one
  never written to.

## The files, crashes and compatibility

- *The header.* A store has a `system` name and a `version`, and its files carry
  `Journal.label system version`: the name alone for version 0, the name and `version n` on a
  second line otherwise. Version 0 is exactly the header every journal has today, so existing
  journals are version 0 of their name and replay as before (`Journal.label_zero`). A ledger
  that wants versions keeps its name, `"ledger 4"`, and starts counting from version 1.
- *Which upgrade reads a file.* `Store.upgrades` lists the older versions a store reads, each
  with its label, system, codecs and migration. A journal whose header is another label is
  refused as before unless an upgrade reads it (`Disk.begin`).
- *Dying during a migration.* The two writes are the snapshot under the new name, then the
  journal that begins at its mark. An old journal beside a snapshot under the new name is a
  migration whose journal was not yet replaced, and the start finishes it.
  `Upgrade.begin_crash`: wherever the process dies, the next start gives the same migrated
  kernel and never a refusal.
- *After a migration.* `Disk.Holds` and `Disk.Torn` now take the kernel a history starts from
  (boot by default). Once the two writes are done the files hold a history that starts from the
  migrated kernel (`Upgrade.holds`), so every theorem about appends, saves, mends and deaths goes
  on from there, and at every later start the files load as a kernel whose every actor satisfies
  `inv` (`Upgrade.inv_load`).
- *Request ids.* The new journal's first mark carries the length of the old history, so the
  number of entries in the shard's history never goes down and no request id is given twice
  (D29).
- *Outputs.* Those the old shard had not marked as handed over are migrated (`Migration.output`)
  and handed over before the first write; dying before it hands them over again. Delivery stays
  at least once.

## Not done, for the owner to decide

- `Http.serve` takes no upgrades: its system is the application's behind the gate, and a
  migration would have to be lifted through the gate's join. The ledger and the rookery need
  that before they can use migrations.
- A shard that was itself started by a migration is in states its `inv` covers, not
  necessarily states its actors reach from their initial state. A second migration's `lands`
  covers only the latter, so `Upgrade.inv_load` is stated for an old shard that started at boot.
  Covering a chain needs `lands` over a precondition that both cases satisfy.
- A migration that maps a refinement between the old spec and the new one is not stated.
