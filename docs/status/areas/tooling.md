| Tooling | `lanes new` (its types declared with `lanes_data`), `lanes lint` (text-level, and the size of trusted files), `lanes check`; `instance_by_cases` for instances defined by cases on an identity (`Inspect` of a system whose actors differ); CI on every push to the pull request (build with warnings as errors, lint, tests, model checks, a generated app); axiom gate | `LanesCli/`, `Lanes/Actors/ByCases.lean`, `.github/workflows/ci.yml`, `Tests/Axioms.lean` |

- `lanes lint` is text-level. `no-io-in-step`, `bounded`, `field-leak` and `fn-length` need the
  elaborator and are not implemented.
