# D?. Waves are the default as the kernel's waves under `auto`, and free-running is not built

Status: Accepted

`Lanes/Runtime/IO/Shell.lean`, `Lanes/Runtime/PeekSound.lean`, `Lanes/Runtime/WavePlan.lean`,
`bench/Mixed.lean`, `bench/mixed.sh`, `examples/videos/Videos/Waves.lean`,
`examples/videos/Waves.lean`. Issue #106, "waves as the default, then a benchmark with mixed
step costs at p99, to decide on free-running". Issue #93 sets the order: the default runtime
applies a batch in parallel in waves, proved equal to running the journal in order, and actors
run free of waves only if a benchmark with mixed step costs shows a gain at p99. D64 made the
kernel's waves, D73 let the shard choose them a batch at a time (`parallel := .auto`), D88 made
them update states in place, D107 measured how wide waves of whole journal entries would be on
the video site, and D109 split the site so that they are 11 to 35 entries wide.

## What the default is

Three readings of "waves as the default" were weighed:

1. `parallel := .auto` with as many workers as the machine has hardware threads: the kernel's
   waves of messages (`Kernel.waves`, `Kernel.mail`), each batch on the pool or on the shard's
   thread as `Pace` chooses.
2. Waves of whole journal entries (`WavePlan.split`) on top of the kernel's.
3. Both.

The default is the first, and it is what `Runtime.Config` already gives (`parallel := .auto`,
`workers := 0`, D73); a test pins it (`Tests/Runtime.lean`). Every server, node and example that
passes `{}` or sets other fields runs it. Waves of entries are not added, for three reasons.

- **They are narrower than the kernel's.** `lake exe videosWaves kernel` cuts the same workload
  into the kernel's waves, a batch at a time, the answers to one batch's calls coming in a later
  one. With a thread for each receiver and steps of equal cost, a wave takes as long as its
  busiest receiver's messages, so the work over the sum of those is the speedup the waves allow.
  The same for waves of entries is entries over waves (D109's column):

  | Views | Batch | Entries per wave of entries (`WavePlan`) | Messages per kernel wave | Receivers per kernel wave | Kernel waves' messages over their longest receivers' |
  | --- | --- | --- | --- | --- | --- |
  | By popularity | 64 | 11.38 | 34.34 | 29.80 | 13.61 |
  | By popularity | 256 | 15.43 | 138.37 | 112.05 | 23.27 |
  | Uniform | 64 | 12.72 | 34.34 | 31.53 | 17.95 |
  | Uniform | 256 | 35.08 | 138.37 | 121.74 | 57.40 |

  The kernel takes each message on its own, so two entries that touch one actor share a wave and
  only that actor's steps are in order; waves of entries put them in different waves. A batch is
  about four kernel waves, the hops of its longest entry.
- **They need each entry's actors before it runs.** An entry touches the actors its messages
  reach, which only running it tells: a visit goes on to the owner of the video, a job's word to
  the scheduler that holds the job. An application would have to declare them, as Calvin's
  transactions declare their read and write sets, and the declaration would be trusted or proved.
- **They would weaken the theorem.** Entries applied whole in parallel queue their sends, number
  their timers and put out their outputs in another order than `runBatch`, so the batch would be
  equal to the journal's order only up to `SysState.Equiv` and a renaming of timer tokens (D64
  shows the stronger statement false for the kernel). The kernel's waves are `runBatch` value for
  value.

`WavePlan` stays what D107 made it, the measure of a journal's width.

## What is proved of the default

Whatever `auto` chooses, the shard computes what one thread computes:

- `Kernel.runWaves_eq`: a batch in waves, however spread, is `runBatch`, kernel, events and
  outputs in the same order.
- `Batch.run_spread`: a batch of the shell is the same whatever its spread.
- `Batch.chain_spread` (new, `Lanes/Runtime/PeekSound.lean`): the shard's whole history, each
  batch given any spread (the `n`th `spread n`), is the history one thread gives, act for act:
  the same journal entries, outputs, saves and answers. `Pace`'s choices over a run, which depend
  on its timing, are such a sequence, so `Batch.chain_sound` and `Batch.chain_peek_after` hold of
  the history `auto` runs. Its proof is `run_spread` by induction over the batches; gate
  `Tests/Axioms/Runtime.lean`.
- `Journal.turnAll_eq_exec`: the inputs `auto` groups into one turn are what replaying the
  turn's entries does.

Nothing is weakened: no statement changed.

## The benchmark

Two programs, each run in three sessions minutes apart on the shared four-core container, other
agents' work giving a load of 0.5 to 2.

**Mixed step costs** (`bench/Mixed.lean`, `bench/mixed.sh`; `bench/README.md`, "Mixed step
costs"): 64 clients each keep one request outstanding to one of 64 counters, closed loop, and
each step costs what the workload draws. Five ways: the shell serial (`.off`), in waves (`.on`)
and `.auto`, four workers each; and two prototypes of free-running actors with no kernel, no
journal and no order between actors, each answer handed over as soon as its step is done: one
run queue of actors with mail under one lock, taken by four threads a message at a time; and four
threads that each own the counters whose number is theirs modulo four and take their queue all at
once. Five runs a session of 64,000 requests, the first tenth of each client's not counted;
below, the range of the sessions' medians. The calibration of a microsecond of hashing varied
between sessions by a fifth (438 to 529 rounds), so a workload's costs are nominal within that.

| Steps | Way | p50 µs | p99 µs | p99 of the cheap steps µs | Answers a second |
| --- | --- | ---: | ---: | ---: | ---: |
| All 2 µs | serial | 213–230 | 316–363 | | 267,000–280,000 |
| | waves | 309–313 | 396–511 | | 195,000–202,000 |
| | auto | 193–216 | 409–445 | | 283,000–316,000 |
| | free, one run queue | 669–681 | 2,413–2,493 | | 73,000–74,000 |
| | free, a queue a thread | 80–86 | 432–464 | | 538,000–548,000 |
| 1 in 50 at 500 µs, else 2 µs | serial | 635–742 | 1,910–2,372 | 1,902–2,367 | 72,000–84,000 |
| | waves | 757–895 | 1,636–1,916 | 1,617–1,915 | 73,000–85,000 |
| | auto | 732–841 | 1,934–2,264 | 1,933–2,263 | 74,000–82,000 |
| | free, one run queue | 664–683 | 2,460–2,519 | 2,440–2,503 | 72,000–75,000 |
| | free, a queue a thread | 151–163 | 1,703–1,846 | 1,684–1,827 | 163,000–183,000 |
| 1 in 5 at 50 µs, else 1 µs | serial | 692–808 | 1,052–1,281 | 1,034–1,266 | 78,000–92,000 |
| | waves | 504–538 | 775–944 | 758–940 | 114,000–124,000 |
| | auto | 503–559 | 841–984 | 835–983 | 106,000–122,000 |
| | free, one run queue | 612–691 | 2,210–2,440 | 2,204–2,426 | 75,000–82,000 |
| | free, a queue a thread | 168–189 | 788–978 | 781–963 | 251,000–278,000 |
| All 50 µs | serial | 2,782–3,346 | 3,282–4,265 | | 18,900–22,800 |
| | waves | 1,045–1,196 | 1,780–1,919 | | 51,700–54,400 |
| | auto | 1,060–1,219 | 2,795–3,339 | | 48,000–54,500 |
| | free, one run queue | 718–806 | 2,521–2,997 | | 61,900–70,200 |
| | free, a queue a thread | 498–576 | 2,754–3,314 | | 71,900–87,500 |

Within a session the spread of a cell over its five runs, (highest − lowest) / median, was up to
46% for answers a second and up to 155% for a p99, so differences under about a third are noise.

**The video site** (`lake exe videosWaves time 4 5`): D109's workload, taken a batch at a time as
above, each batch accepted and run to quiet by the kernel alone, on one thread (`runBatch`), in
waves on four workers (`runWaves`), and as `auto` chooses with `Pace` fed the batches' times.
Every entry of a batch waits for the whole batch, so each counts the batch's time; five runs a
session, the range of the sessions' medians, views by popularity (uniform views gave the same
within the noise):

| Batch | Way | p50 µs | p99 µs | Entries a second | Batches on the pool |
| --- | --- | ---: | ---: | ---: | ---: |
| 1 | serial | 3 | 13–14 | 238,000–246,000 | |
| | waves | 6 | 162–196 | 75,000–87,000 | all |
| | auto | 3 | 14–16 | 227,000–245,000 | 0–1% |
| 64 | serial | 239–242 | 340–350 | 259,000–264,000 | |
| | waves | 1,766–1,941 | 2,412–2,839 | 31,700–35,800 | all |
| | auto | 241–271 | 340–650 | 220,000–259,000 | none |
| 256 | serial | 966–987 | 1,173–1,815 | 253,000–257,000 | |
| | waves | 5,404–5,976 | 6,175–8,148 | 41,700–47,000 | all |
| | auto | 964–980 | 1,114–1,475 | 252,000–259,000 | none |

## What the numbers say

- **Videos' steps are cheap.** An entry costs about 4 µs on the shard's thread, and a unit of
  work (a message delivered, a timer fired, an actor started) about 1.6 µs, under `Pace`'s
  `cheap_ns` of 2 µs, so `auto` ran every batch, or nearly, on the shard's thread and was as fast
  as serial. On the pool a batch took six to eight times as long: a wave of about 34 messages
  cost about 400 µs more there. `perf` puts it in the task manager and in Lean's freeing of
  objects other threads made, D64's cost of a hand-off, here for states with maps in a table of
  a thousand members' actors keyed by strings; it was not profiled further. So the site is as
  wide as D109 measured and gains nothing from it: waves as the default change nothing
  measurable for it, and nothing it does (the theorems above).
- **Waves gain where every step costs.** At 50 µs a step, waves on four workers answered 2.4 to
  2.7 times what serial did and halved its p99. With one step in five at 50 µs they gained about
  40% in throughput and a quarter at p99. With one in fifty at 500 µs they gained nothing: a batch
  of 64 holds a costly step three times in four, and every step of the batch waits for it.
- **Free-running shows no gain at p99.** In both mixed workloads the better prototype's p99, and
  its p99 of the cheap steps alone, is within the noise of the waves' (1,703–1,846 µs against
  1,636–1,916; 788–978 against 775–944), and with every step costly it is worse (2,754–3,314
  against 1,780–1,919). A cheap step owned by a thread that is in a costly one waits as it waits
  for a wave. The prototype that avoids that, one run queue, pays its lock more than it saves.
- **It shows a gain at p50 and in throughput:** a p50 three to five times lower and about 2.2
  times the answers on mixed costs, twice the answers on cheap steps. That is an upper bound. The
  prototype has no kernel, no journal and no order between actors, and its counters never message
  each other, the case that needs no order. A work-stealing runtime might also lower p99; it was
  not prototyped.
- **`auto` follows the better fixed way in throughput**, as D73 found, but at 50 µs a step its p99
  is near serial's. Its probes of the shard's thread, one batch after eight on the pool and then
  after twice as many each time, are under one batch in a hundred of a run this short, and each
  is a batch three times as long, which its 64 requests and those queued behind them wait for.

## Free-running is not built

Issue #93 asks for a gain at p99, and there is none here. What it does gain, p50 and throughput,
is measured on a prototype that leaves out what makes the default runtime's result the journal's
order. Keeping that order while actors run free needs, at each actor, its messages in an order
fixed by the journal and not by timing: for messages from other actors, each entry's actors known
before it runs, the declaration waves of entries would need, or the order of every delivery
written to the journal, a write per message. Either changes the step's contract or the journal, and
the theorems would hold up to `SysState.Equiv` at best.

So free-running is not built, and `bench/Mixed.lean` keeps the prototypes so that the question can
be asked again. It is asked again when the warm runner, with cores to spare, shows the better
prototype's p99 below the waves' by more than its spread in a mixed workload (`gh workflow run
bench.yml -f servers=none -f mixed=true`), or when an application's measured p50 matters more than
its p99. This machine's four shared cores are not the warm runner's 32; the numbers above are a
direction until it confirms them.

## Not measured

- The kernel's waves and free-running over HTTP: the shell's numbers leave out the gate, the
  connections and the journal's syncs.
- The video site free-running: its actors message each other (a visit, a job), which the
  prototypes cannot order.
- Pieces of a wave finer than one a worker. A wave is cut into as many pieces as workers
  (`Kernel.plan`); finer pieces would balance costly steps between threads, and are proved the
  same by `Kernel.runWaves_eq`, which holds for every spread.
