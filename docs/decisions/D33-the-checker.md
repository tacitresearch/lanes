# D33. The checker: measure, then normalise once per state

`Lanes/Check/{Search,SearchSound,System,SystemSound,EquivDecide}.lean`,
`Lanes/Actors/{Inspect,Scheduler}.lean`. The checker explored about 15,000 states per second.
The work was to find out why before changing anything, and to keep every theorem about the
search that runs.

*What was measured.* The election check with no crash (24,345 states, 125,943 transitions)
under callgrind, and the one with one crash (164,847 states) by sampling stacks and by wall
time, each version against the others in the same minute, because the machine is shared.

- 68% of the instructions walked chains of closures. `Enum.tabulate` was meant to cut them: it
  was compiled to a lookup that still called the function it was given, so `compact` added a
  layer to the chain instead of replacing it. A definition that returns a function is compiled
  as one that also takes the argument; only data is computed where it is written.
- `SysState.netEquiv` took 45,000 instructions a call and ran on four transitions out of five:
  it filtered both lists once for every message in either.
- A state was hashed 1.4 times per transition (lookup, insertion, and again whenever the table
  grew), and every hash and comparison looked each actor up three times on either side.
- After those, the time is memory: allocating and freeing a successor's objects, and reading
  stored states that are no longer in the cache.

*What was changed*, with the time of the 164,847-state check on one core (before: 10.8 to
11.2 s):

- A state's actors are one list of slots, `Slots`, which is data. `Check.Node.of` builds it
  once per state, reads the world's functions from it (`SysState.compactWith`, equal to the
  state by `compactWith_of`) and hashes and compares along it (`Node.beq_iff` is unchanged:
  equality of nodes is `World.Equiv`). `World.next` no longer compacts; it is the semantics,
  and whoever keeps a state compacts it.
- `netEquiv` matches each message of one list against the other and removes it, in one pass
  (`netEquiv_iff` is unchanged).
- The search keeps a state with its hash (`Hashed`) and compares hashes before states. Equal
  keys then have equal hashes by definition, so `search_sound` and what follows from it no
  longer assume the hash agrees with `==`; a hash that does not costs duplicates, not
  soundness.
- Together: 3.0 to 3.7 s, about 50,000 states per second, 3.5 times faster. Counts, depths,
  coverage, traces and witnesses of every check are the same as before, compared as text.

*Tasks.* `Search.runBatches` takes the waiting states a batch at a time, computes their
successors in tasks and stores them in order. In Lean's logic a task is its value, so it is
`Search.run` (`Search.runBatches_eq`, by induction on the fuel), and `Search.explore_eq` says
the search of `Check.search` is `Search.run` whichever is chosen. The theorems of
`SearchSound` are stated of that search. It is off by default (`Options.tasks`) because it
loses: 6.3 to 7.4 s of wall time and 10 to 16 s of processor time for the check above, on four
cores shared with other work, and 8.6 to 9.8 s of processor time with a single worker, where
the search without tasks takes 3. The samples
show the time in counting references and in freeing on one thread what another allocated. The
runtime explains both. An object that crosses to another thread has its references counted
atomically from then on, and the workers and the storing thread all touch the same closures,
tables and parent states. And such an object is never updated in place (`lean_is_exclusive`),
so the table of stored states has to stay on one thread: finding duplicates is sequential, and
it is two fifths of the work. What four idle cores would give was not measured; the storing
thread alone bounds it near the time without tasks.

*Tried and rejected.*

- Batches without tasks. Computing the successors of 4,096 states and then storing them took
  5.1 to 5.5 s where storing each state's successors at once took 3.2 to 4.0 s: by the time a
  successor was compared it had left the cache. So with tasks off the search is `Search.run`
  itself.
- Smaller batches and tasks (256 states, 16 per task): 17 to 22 s of processor time against
  10 to 16 s.

*Considered and not tried.*

- Sorting the messages in flight so that equal traffic compares in one pass: every state would
  pay for the sort and only the duplicates gain.
- Handing the duplicates of a batch back to a worker to free, which takes the freeing off the
  storing thread. It needs a use of the garbage that the compiler will not remove, and the
  counting stays.
- Fingerprints in place of states: the exact search is the one that is proved.

*What the next factor costs.* A state here is a tree of small objects. About sixty were freed
per transition before the slot list, which by count removes some twenty, and a stored state is
read through a chain of pointers, each a likely cache miss. The remedy is a state that is one flat value (an encoding of the
actors, timers and traffic, with the messages in flight in a canonical order), compared by
content and hashed incrementally. That removes most of the allocation, makes a comparison one
pass over memory, and gives workers something they can exchange without counting references.
It needs an encoding for every state and message type, which `Codec` already asks of durable
systems, and a proof that the encoding is injective up to `World.Equiv`.
