### Changed

- `docs/ARCHITECTURE.md` holds, area by area and application by application, what each part does, its claims with their evidence, and the limits of the design; fixable limits are issues labelled `known-limit` (`docs/decisions/D100-each-doc-has-one-job.md`).
- Each decision has a status line under its title, and the generated index lists the current decisions first; `lanes lint` fails on a decision without one.
- `lanes inventory` prints the inventory instead of writing a file.
- The runners' page is `infra/README.md`.

### Removed

- The claims table (CLAIMS.md), the status page (STATUS.md) and its fragments with the lint rule `status`, the committed inventory (INVENTORY.md), the standard library's triage (STDLIB.md) and the history folder of `docs/`; the roadmap is a pointer to the issues.
