# D73. The shard chooses from its own timing whether a batch's steps are worked out in parallel

Status: Accepted

D64 let a shard's actors step in parallel within a wave, behind `Runtime.Config.workers`, off by
default. On the warm machine it gained 40–56% where each step does real work (`lanes-heavy-par`)
and cost about 10% where steps are trivial (`lanes-many-par`); the kernel alone cost about a
microsecond more a message on trivial steps. No fixed setting is right for both, and an
application does not know ahead which it is. This decision lets the shard choose, a batch at a
time, from how long its recent batches took, and makes that choice the default.

## What changes

- `Runtime.Config.parallel : off | on | auto`, `auto` by default. `off` is the shard as it was
  before D64: each input a turn of its own, every step on the shard's thread. `on` is D64's
  `workers` above one: every wave with mail for two actors or more is worked out on the pool.
  `auto` asks `Pace` (`Lanes/Runtime/Pace.lean`) before each batch.
- `Runtime.Config.workers` is now the most threads a wave is worked out on, `0` by default, which
  is the machine's hardware threads (`System.Platform.Internal.getHardwareConcurrency`). One
  worker is `off`.
- A wave's spread is a value, `Kernel.Spread`: the threads, and the fewest actors in a piece
  (`minPiece`). A wave whose actors fit in one piece is not planned; with `minPiece` one this is
  D64's rule that a wave with one actor's mail is not.
- Inputs that arrive together are grouped as before whenever the mode is not `off`, but at most
  `min batch snapshotEvery` inputs to a group (`Batch.group`). A group of 1,024 trivial inputs
  cost 1.3–1.4 µs a message against 0.55 for the same inputs one turn each, measured with
  `Batch.run` alone; at 64 it costs 0.565 against 0.61. And a turn's entries are written
  together, so a group larger than `snapshotEvery` put a save off by the whole group.

Whether inputs are grouped depends on the configuration only, never on the pace: the pace
chooses how a batch runs and not which batch runs.

## The pace

The shell reports, for each batch that did work, its units of work (messages delivered, timers
fired, actors started: `Pace.work`), how long `Batch.run` took, and how long since the end of the
batch before: the batch's cycle, which holds the handing over of outputs, the look at the inbox
and any wait for input. The pace keeps four rates, each batch weighing an eighth less than the
one after it, weighted by its work so that a batch of one unit counts for little; an eighth is a
half-life of about five batches, which follows a change within a few and smooths most of the
noise of one. They are the cost of a unit on the shard's thread (`cost`, from the batches run
there), the cycle a unit while each way is in use (`inline`, `pool`), and the cycle a unit
whatever the way (`arrived`).

1. **Cheap work stays.** While a unit of work costs less than `cheap_ns` (2 µs) on the shard's
   thread, the pool is not tried. D64 put the cost of handing a message to another thread at
   about a microsecond; on four workers a step of under about 1.3 µs cannot gain even with
   perfect sharing, and the pace's own probes would cost more than they could find. Trivial
   actors, which most applications have, never pay for the pool.
2. **Only a shard that would be behind alone.** The pool is taken only while the work arriving
   would keep the shard's thread busy `busyOn` (75) percent of the time or more, at its cost a
   unit (`arrived` units times `cost`, over `arrived` time), and left under `busyOff` (50). A shard
   that keeps up alone gains only a shorter batch, and the pool's threads take cores the rest of
   the process may need. The gap between the two is the hysteresis: on the pool the shard is
   busy less of the time, which must not take it off the pool.
3. **The shorter cycle is kept.** The pool is tried at once when it is worth it, and from then
   the way with the shorter cycle a unit is used, the other taken when it is shorter by an
   eighth. Switching costs nothing, so the margin is only against flapping on noise.
4. **The way not in use is measured again for one batch** in two cases. When the cycle of the way
   in use has halved or doubled since the other was last run, the work has changed and the old
   comparison says nothing. Otherwise after `probeFirst` (8) batches, then twice that each time
   the other is found the slower, up to `probeEvery` (64) batches times how much slower it was
   and at most `probeAtMost` (1,024). A batch's time is noisy: a way left on one bad batch is
   tried again after eight. A batch run the slower way, `r` times slower, costs `r − 1` batches,
   so once the interval has grown the cost of looking is about one batch in 64. A probe's batch
   replaces the old rates of its way rather than joining them.
5. **The pool cannot shorten a cycle more than `workers` times**, so the cycle on the shard's
   thread is read as at most `workers` times the pool's. This keeps a stale rate from a time of
   heavy steps from holding a batch of trivial ones on the pool.
6. **A piece holds at least `piece_ns` (20 µs) of work** at the shard's cost a unit: `minPiece`
   is `piece_ns` over `cost`. A task costs a wake-up of a pool thread; a narrow wave of cheap
   steps stays on the shard's thread even in a batch that goes to the pool.

*Why time both ways and not only threshold the cost of a step.* Whether the pool pays depends on
whether there are cores free for it, which the step's cost does not say. D64 measured
`lanes-heavy-par` slower than `lanes-heavy` on a server of two CPUs, where the cores were full;
in this shared four-core container, under a load of eight, `benchWaves` gave 33 µs a message on
one worker and 31 on four, where D64 measured 31 and 9 on a quieter day. A threshold on the step
would take the pool where it loses.

*Why cycles and not batches.* D64 measured `lanes-heavy-par` slower than `lanes-heavy` on two
server CPUs. There the pool's threads take the cores of the threads that read the requests: the
shard's batches may be shorter, but it waits longer for the next. A batch's time does not show
that; its cycle does. A first version of the pace compared batch times, took the pool there, and
served fewer requests than `off` in one run in this container; that run was disturbed by other
jobs, so it is a direction and not a number.

*What it cannot do.* A batch is decided before it runs, from the batches before it. The first
batch of a burst of heavy inputs that follows a long run of trivial ones runs on the shard's
thread, and the first trivial batch after heavy ones on the pool; a burst that is one batch, as a
few hundred inputs arriving at once are, is never run the better way. And it sees only its own
shard: two shards in one process each time their own cycles.

## Why it changes nothing the system does

The spread enters pure code only through `Batch.Config.spread`. `Kernel.runWaves_eq` holds for
every spread (`k.runWaves spread fuel = k.runBatch fuel`), so `Journal.turnAll_spread`: a turn is
the same whatever its spread; and `Batch.run_spread`: `Batch.run { c with spread }` is
`Batch.run c`, kernel, acts and answers. So whatever the pace chooses, from whatever timing,
every theorem about a batch holds as it did (`Batch.run_kernel`, `run_sound`, `run_peek`,
`run_resolved`, which hold for every configuration), and auto computes exactly what one worker
computes from the same commands. Their statements now name a `Kernel.Spread` where they named a
number of workers; their proofs are unchanged.

What the pace decides is proved irrelevant; that it decides well is measured. The shell's
timing, the pace it keeps and the counts of batches it reports (`Runtime.batches`) are trusted
only for speed, in the shell's row of `TRUSTED.md`.

## Measured

`bench/README.md`, "Choosing from the shard's timing", in the shared four-core container:
`benchAuto`, the shard without IO on seven workloads (trivial and heavy steps, one or two actors
and 64, mixed steps, phases of each), three sessions of seven runs. Differences under about a
third were noise. Within it auto was as fast as the faster of `off` and `on` on every workload
in every session, at worst 24% slower in a row whose spread was 38%; `on` was up to 2.8 times
slower than auto on trivial steps and `off` up to 1.5 times on heavy ones. Whether the pool paid
for heavy steps changed between sessions with the other agents' load (35, 22 and 36 µs a message
on the pool against 35–37 on one thread), and auto followed it. Over HTTP on two server CPUs,
where no mode gains (D64), auto was within the noise of `off` and used its CPU a request.

**The default.** `auto` is the default because on these numbers it is never meaningfully worse
than the better fixed setting, it is `off` but for the grouping of inputs where steps are cheap,
and the grouping costs nothing measurable once groups are bounded. The warm machine's run is to
come (`lanes-many-auto`, `lanes-heavy-auto` and `benchAuto`); it should show `lanes-heavy-auto`
near `lanes-heavy-par` and `lanes-many-auto` near `lanes-many`, and if it does not, the
thresholds move, not the default.

## Risks

- **Grouping is now the default.** A journal written with `auto` has one turn for inputs that
  arrived together, as D64's `workers` did: it replays the same, but differs from one written
  with `off`, and the outputs of inputs that arrive together may come in another order, which the
  semantics allows. `Tests/Release.lean` saved fewer images, its journal being shorter, and now
  saves more often.
- **D64's risk of shared states** stays: an actor stepped on the pool never has its state updated
  in place again. With `auto` that happens only to applications whose steps cost more than
  `cheap_ns`.
- **`workers` 0 counts the machine's hardware threads**, not those the process may run on: under
  `taskset` it is too many, which costs a task a piece the pool cannot run at once.
- **The thresholds are this container's.** `cheap_ns` and `piece_ns` come from D64's numbers and
  this decision's; the warm machine may move them.
