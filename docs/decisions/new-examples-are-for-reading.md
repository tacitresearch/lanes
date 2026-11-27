# D?. Examples are for reading, fixtures are for the tests

There were two places for applications: `Examples/`, a library of the root package with small
reference apps, and `systems/`, three Lake packages that depend on Lanes by path. Ten test files
imported `Examples.*`, the axiom gate gated their theorems, and the inventory counted them as
evidence, so an example could not be made clearer for its reader without touching the tests.

Now there is one `examples/` directory with one Lake package per project, each depending on
Lanes by path as an application of a user depends on it by git: `counter`, `bank`, `bank-web`,
`kv-cache`, `election`, `watchdog`, `raft-kv`, `ledger`, `rookery`. `examples/README.md` says in
what order to read them and which shows what. The small ones each have their proofs, their axiom
gate (`<Name>/Proofs/Axioms.lean`, as the large ones) and model checks that `lake test` runs.
Package names are Lean names (`bankWeb`, `kvCache`), since a manifest's must be; the directories
keep the hyphens.

What the tests need is in the root package, in `Tests/Fixtures/`, under `Tests.Fixtures.*`: the
bank, its web front, the key-value store, election and the watchdog, and their proofs, which the
axiom gate and the inventory cite (`Link.reliable` is proved only through the watchdog's
theorems). They are the files that were in `Examples/`, moved; the examples are copies of them
written for reading, with their own namespaces (`Bank`, `KV`). The two may now differ, and a
change for the reader is not a change to the tests. The cost is that the small proofs are
compiled twice in CI.

`examples/counter` is exactly what `lake exe lanes new counter --lanes-path ../..` writes, its
manifest apart. The template is not generated from it: the template's names are filled in
(`{{Name}}`), and `Counter` would be both the application's name and its module's. Instead
`Tests/New.lean`, in `lake test`, compares every file the template writes with the example's,
so the two cannot drift apart unnoticed.

CI builds and checks the small examples in one job, and keeps a job each for the three large
ones. The runner machine's warm copy of `raft-kv`'s build keeps its old place on the machine
(`$LANES_SHARED/…/systems/raft-kv`), which only the runner script and the Lean action read.
