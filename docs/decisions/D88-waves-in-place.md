# D88. Steps worked out on the pool update their states in place

Status: Accepted

`Lanes/Runtime/Wave.lean`, `Lanes/Runtime/Pace.lean`, `Lanes/Proof/HashMap.lean`,
`Tests/Scale.lean`, `Tests/Pace.lean`. D84 made a step on the shard's thread update its actor's
state in place and left the steps worked out on the pool copying it. With two busy actors of a
million numbers a write took about 2.4 ms with `parallel := .on`, where it takes about a
microsecond with `.off`, and `.auto` took the pool for such steps.

- *Why it copied.* A plan (`Kernel.Ahead`) held every state the steps passed through: each step's
  state was both in the plan and the next step's input, so the next step copied it. The kernel
  also kept the state the plan started from, and the plan's result handed every state back to the
  shard's thread.
- *What changed in the plan.* A plan keeps of each actor the effects of each step, whether the
  state it leaves is one starting gives (`Actor.fresh`, which `rest` needs), and the last state
  only. A task then holds the only reference to the state after its first step. A plan ends at
  the first step that stops the actor.
- *What changed in the kernel.* The kernel leaves the state the wave began with in the actor's
  cell, settles each planned step with that state, and writes the last state at the last step.
  Where an actor's steps stop being taken before its last, the kernel works out the state the
  steps taken leave, from the state in its cell, and writes it (`Plan.fixAt`): when a timer of
  the actor goes off, when a message other than the plan's next comes, when the wave ends first
  (timers took some of its units), and, for every actor at once, before a start that writes a
  cell that is not in the table (`Plan.real`). That costs the steps again and a copy. The first
  three need a timer or a stop in the wave; the last, an actor released at rest and woken in the
  same wave.
- *Why the state stays in the cell, and is not taken out as `takeState` does.* The kernel needs
  it to work out the state where the steps stop early. And it costs no copy: see below.
- *Why all states are written before a new cell.* A cell that is not in the table may grow it,
  and growing it moves every entry. Writes to cells already there move nothing, so they can be
  made in either order; that is what the proof needs.
- *What is proved.* `Kernel.runWaves_eq` keeps its statement, and so does every theorem above
  it. The kernel during a wave is no longer `runBatch`'s value for value: it holds the start
  state in planned cells. So `Kernel.runBatchAhead_eq` now says that the batch with the plan's
  states written (`Plan.real`) is `runBatch` from the plan's kernel with them written, for every
  good plan; `Kernel.good_plan` adds that a new plan has no step taken, so writing it changes
  nothing; and `Kernel.wave_eq` puts the two together for `waves_eq`, the only caller of either.
  What makes it hold: writes to two keys already in a `Std.DHashMap`, or a write to one and the
  removal of another, commute value for value (`DHashMap.insert_comm_of_contains`,
  `erase_insert_comm_of_contains`, `erase_insert_of_contains`, over Std's model of the map, as
  D84's `insert_insert_of_contains`); handling a message for one actor commutes with writing
  another's state (`Kernel.handle_setState`, `Plan.fixAll_local`); and settling a step and then
  writing a state is settling the step with that state (`Kernel.setState_settle`). Nothing is
  trusted.
- *What it still costs.* Lean never updates in place an object another thread has seen. A state
  handed to a task, or handed back by one, is marked shared, and its first write copies it. So
  each actor the pool steps has its state copied once a wave, by its first step in the task,
  and once more by its first step on the shard's thread after a wave on the pool. A wave holds
  at most `min batch snapshotEvery` inputs, 64 by default, so with `.on` a write still pays a
  share of a copy, which grows with the state. Only actors whose states never leave their thread
  would avoid it, and the kernel's cells hold the states.
- *The pace.* Two changes keep `.auto` off the pool for cheap steps on large states. The first
  batch on the shard's thread after the pool counts as the pool's, since it pays for the pool's
  copies; counted as the shard's, it made the shard's steps look costly and the pool no slower,
  and `Pace` stayed on the pool. And the pool is tried only after the shard has done
  `Pace.Config.firstUnits` (64) units on its own thread, until then each batch's cost replacing
  the last: an actor's first write copies an initial state the system holds, and one such batch
  made the first steps look costly. A probe of the shard's thread from the pool now takes two
  batches, so looking costs about two batches in 64 instead of one.

## Measured

On the shared four-core container, a write to one of two or eight busy actors, each a state of
`n` numbers, on a shard with four workers: the fastest of three runs of 1,000 writes, two
sessions, before and after, alternating.

| actors, n | `.off` | `.on` before | `.on` after | `.auto` before | `.auto` after |
| --- | --- | --- | --- | --- | --- |
| 2, 10^4 | 1.0–1.5 µs | 15–21 µs | 3.1–3.4 µs | 1.4–1.6 µs | 1.0–1.5 µs |
| 2, 10^6 | 1.4–1.6 µs | 2.4 ms | 131–151 µs | 22–24 µs | 1.1–1.5 µs |
| 8, 10^4 | 1.0–1.8 µs | 27–29 µs | 4.9–10 µs | 1.6–1.8 µs | 1.0–1.4 µs |
| 8, 10^6 | 1.2–1.8 µs | 2.4–2.5 ms | 506–544 µs | 41–58 µs | 1.3–1.6 µs |

A copy of a million numbers took 0.6–0.9 ms there. With `.on`, eight actors pay four times what
two do: a wave of 64 writes copies each actor's state, whatever its share of the writes.

Nothing measured on small states moved. `Tests/Scale.lean`'s other cases were within their
noise: 20,000 messages in 12–18 ms with 1,000 or 100,000 actors, 1.4–1.7 million inputs a second
from one sender, 1.6–2.2 million turns a second of the kernel alone, a write to one actor's state
0.3–0.4 µs in the kernel and 0.9–1.5 µs on a shard, before and after. The bench's servers, built
both ways and run alternately, three runs of 5 s at 16 connections, the server on two CPUs and
the load generator on the other two, under a load of 6 to 10 from other jobs, medians in
requests a second, before and after: `lanes` 26,600 and 26,900; `lanes-par` (two workers, one
actor) 23,800 and 22,400; `lanes-many-auto` 23,100 and 22,100; `lanes-heavy-auto` 14,100 and
16,400; `lanes-heavy-par` 13,300 and 16,700. Runs of one server differed by up to 40%.
