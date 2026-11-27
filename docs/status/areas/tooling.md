| Tooling | `lanes new` (its types declared with `lanes_data`), `lanes lint` (text-level, the sizes of trusted files, that every repository path a doc cites exists, and the files `--fix` writes: their line counts, the index of decisions and the numbers of new ones, the status page, the inventory), `lanes check`, `lanes inventory` (`docs/INVENTORY.md`: every public definition with its status and evidence, read from the built modules; lint fails on one of `Lanes/` without evidence that is not on `docs/inventory-none.md`); `instance_by_cases` for instances defined by cases on an identity (`Inspect` of a system whose actors differ); CI on every push to the pull request (build with warnings as errors, then lint, tests and a generated app, model checks, `examples/raft-kv` and `examples/ledger` as parallel jobs); the mutation gate in parallel shards, nightly, by hand and on pull requests labelled `mutants`, on GitHub's runners or a warm EC2 machine the workflow starts and stops (`docs/RUNNERS.md`); `scripts/lean-goals` for a file's errors and goals from a language server kept open; axiom gate | `LanesCli/`, `Lanes/Core/ByCases.lean`, `.github/`, `infra/`, `scripts/`, `Tests/Axioms.lean` |

- `lanes lint` is text-level, but for the inventory. `no-io-in-step`, `bounded`, `field-leak`
  and `fn-length` need the elaborator and are not implemented.
- The inventory's "proved" is only as strong as the gates: a gated theorem covers every
  definition its statement names and what those run in their own module, whether or not it
  says all they are for. A test or a check covers what it names in the same way, which makes the
  checker's own plumbing (`Check.Report.ok`, `Inspect`) "checked" because checks use it.
  `lanes_data`, `macro_rules` and `elab_rules` are invisible to it: a test uses the syntax, not
  a constant. `LanesCli/` is listed but not held to the list of definitions without evidence.
- The warm runner machine, its CloudFormation stack and the start and stop jobs have been checked
  with linters and stubs only, not yet run against AWS.
