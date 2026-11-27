# D84. The kernel takes an actor's state out of its cell before the step

`Lanes/Runtime/Kernel.lean`, `Lanes/Runtime/KernelSound.lean`, `Lanes/Proof/HashMap.lean`,
`Tests/Scale.lean`. A write to an actor whose state held a million numbers took about a
millisecond, ten thousand numbers about seven microseconds: every step copied the whole state.

- *Why it copied.* `Kernel.handle` gave the step `(k.cell i).state`. `cell` reads the cell with
  `get?`, which leaves it in the hash map of actors, so the state had two references when the
  step ran: the map's and the step's. `Array.set` and `HashMap.insert` copy an object that is
  shared. The IR shows it: `inc` of the state, the step, and the map still holding the cell. No
  functional test could see it.
- *What changed.* `Kernel.takeState` writes the cell back with `init` in place of the state and
  returns the state. The map then holds no reference to it, and the step updates it in place.
  `settle` writes the cell again with the new state, as it did before. When `i` has no cell,
  the state is `init`, as before. Only `handle` takes the state out; the rest of the kernel is
  unchanged.
- *Why a placeholder and not `erase`.* `settle` reads the cell's `up` and its timers from the
  map. A placeholder keeps them there, so `settle` did not change. An erased cell and a cell
  inserted again would also be a different hash map value, laid out differently.
- *What is proved.* The kernel computes the same values, not only the same map: the theorems say
  "the same kernel" (`Kernel.runWaves_eq`, `Journal.turn_eq_exec`). A key written twice in a
  `Std.DHashMap` is the map in which it is written once, when the key was there
  (`DHashMap.insert_insert_of_contains`, over Std's model of the map). So `settle` after
  `takeState` is `settle` on the cell as it was (`Kernel.settle_setCell`), and `Kernel.handle_eq`
  keeps its statement; it was `rfl` and is now that proof. No other proof changed. Nothing is
  trusted: no `implemented_by`.
- *What it costs.* A write takes about half a microsecond in the kernel and one on a shard, at
  ten thousand numbers and at a million. With a journal it takes what the journal takes, 5 to
  10 µs on the machine measured, at both sizes. `init` is read once more a step, which is free
  when it is a constant.
- *Checked by time.* `Tests/Scale.lean` writes a thousand times to a state of 10^4 numbers and to
  one of 10^6, in the kernel and on a shard, the fastest of three runs. It fails when the larger
  takes more than ten times the smaller and 50 ms. Before this change the larger took about a
  second.
- *Not fixed: steps worked out on the pool.* A wave's plan (`Kernel.ahead`) keeps every state it
  passes through, and the kernel keeps the state the plan starts from, so a step worked out on
  the pool copies the state. With `parallel := .on` and two actors of a million numbers, a step
  takes about 4 ms. `auto` can choose the pool for such steps, because a copy makes a step look
  costly. A plan that does not keep its states would change `Kernel.Plan.Good` and its proofs;
  until then a system with large states and several busy actors runs with `parallel := .off`.
- *Not fixed: starts.* `startActor` gives `recover` the state that the cell still holds. A start
  is not a step and is rare.
