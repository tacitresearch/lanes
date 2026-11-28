# D23. Time is data, and a shard is a thread

Status: Accepted

*Refines D18, after a second independent review.*

The kernel now owns the clock's meaning. The shell reports what the clock says
(`Kernel.advance`); the kernel keeps an agenda of pending timers, says which are due
(`Kernel.step`), how long nothing will be (`Kernel.wait`) and whether the shard is idle
(`Kernel.quiet`), and does a bounded batch of work in one pure call (`Kernel.runBatch`). There
are no timer commands, no tokens handed to the shell and no sleeping task per timer. The shell
sleeps once, until the next deadline or the next input.

The shard's loop runs on a thread of its own, not as an `Async` task, and keeps the kernel in a
reference that each operation empties and refills.

Why:

- The review found that cancelled timers kept sleeping and then flooded the bounded inbox, and
  that waiting for "no timers" waited for cancelled ones. With the agenda in the kernel,
  cancelling is a pure update and there is nothing to leak.
- It found that no theorem said what the kernel tells the shell to do. With timers inside, the
  only thing left to tell is the outputs, and `Kernel.exec_outputs` proves they are exactly the
  outputs of the run.
- It found that a message cost time linear in the number of actors. The cause is in Lean's
  runtime, not in any logic: an object another thread may see is never updated in place, and
  state held across an `await` is handed to the task system. So an `Async` loop copies its
  state on every update. A plain loop on its own thread does not. `Tests/Scale.lean` measures
  it: the same cost per message at 1,000 and at 100,000 actors.

Consequences:

- A program whose `main` returns without stopping its runtimes does not exit, as with any
  thread that is not a daemon. `Http.Server.stop` stops the runtime.
- `stop` means stop now: the shard finishes the commands already handed over and one batch,
  then ends, even if actors still have messages for each other. Draining could never end.
- Every kernel operation is total and consumes the kernel: there is no "nothing to do" result
  that would force the caller to keep a second reference.
- The agenda holds exactly the pending timers, whatever the shell does
  (`Kernel.exec_wellFormed`, in `Lanes/Runtime/KernelTimers.lean`). Soundness does not depend on
  it (`fire_sound` holds for any timer the shell could name); promptness does. From it: a timer
  that is due is fired and not slept through, a kernel that says there is work does some, the
  shell sleeps until exactly the earliest deadline, and idle means nothing queued and nothing
  pending (`Kernel.WellFormed.wait_of_due`, `step_of_due`, `step_events_ne_nil`, `wait_for_ms`,
  `quiet_iff`).
- A timer that is due and a message that is queued take turns (`Kernel.timerTurn`,
  `Kernel.timerNext`). The first version always fired the due timer, and a later review showed
  what that costs: an actor that arms `after 0` again in its timer's handler, or enough periodic
  timers that one is always due, kept every message waiting for ever. Always taking the message
  would starve timers the same way. With turns, each waits for at most one step of the other
  kind (`Kernel.WellFormed.step_of_queued`, `step_of_due`). One bit of state is enough and the
  bound is the smallest there is; counters or priorities would need a policy nobody has asked
  for.
- The batch of work the shell asks for is a kernel operation like the others (`Kernel.Op.batch`),
  so `Kernel.exec_reachable`, `exec_outputs` and `exec_wellFormed` are about the calls the shell
  makes, not about single steps it never makes.
- Proving it found a defect. `Kernel.fire` erased the agenda entry at the `due` it was given
  before looking whether the timer it was given was pending. A shell that fired a real `due` at
  another actor or for another message made the kernel forget the timer that `due` belonged to:
  it stayed pending, never fired, and the shard counted as idle. `fire` now leaves the agenda as
  it is unless the timer is pending (`Tests/Kernel.lean`). The shell in `Runtime.lean` reaches
  `fire` only through `step`, which names the agenda's own entry, so it could not do this.
