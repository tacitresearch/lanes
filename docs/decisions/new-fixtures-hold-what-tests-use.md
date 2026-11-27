# D?. The fixtures hold what the tests use, the examples the proofs

D60 put copies of the small applications in `Tests/Fixtures/`, their proofs included, so that
the axiom gate and the inventory could cite them. That kept about 900 lines of proofs twice, each
copy compiled, and the copies in the fixtures were read by nothing but the gate.

The fixtures now hold the systems and what a test of the framework calls: the bank's
`balance_nonneg`, which `Tests/Split.lean` carries to the bank on shards, and its
`money_conserved` (`Tests/Fixtures/BankProofs.lean`), which `Tests/SplitProofs.lean` carries to
two shards. The proofs of election, the key-value store and the watchdog are only in their
examples, under the examples' own axiom gates.

The inventory read no evidence from those proofs that it does not find elsewhere, with one
exception: `Event.visible` was stated only by the key-value store's proof that a read cache
breaks refinement. `Tests/SystemSound.lean` states it as well, in what a PASS of the store's
refinement check means for its traces, which was an `example` and is now the theorem
`Tests.SystemSound.kv_traces`. `Link.reliable`, which D60 says was proved only through the
watchdog's theorems, is proved through `EnvModel.lossy` by the theorems that state an
environment, and `System.withGhost`, which only the election's proof applied in a definition,
is now a spec, used only in statements, as a ghost is.
