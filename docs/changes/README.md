# Unreleased changes

One file per change, `<slug>.md`, named after the change: the changelog's fragments. Two pull
requests then never edit the same file, as they did when each added a line to `CHANGELOG.md`.
A fragment has one or more sections, each a heading followed by its entries:

```markdown
### Added

- `Lanes.Thing`: what a user can now do, in one line.
```

The sections are those of Keep a Changelog: Added, Changed, Deprecated, Removed, Fixed and
Security. An entry is one line that starts with `- `; a line that starts with two spaces
continues it. `lake exe lanes lint` checks each fragment (lint `changelog`).

`lake exe lanes changelog` prints the Unreleased section: each section's entries from every
fragment, the fragments in the order of their names. At a release, `lake exe lanes changelog
--release X.Y.Z YYYY-MM-DD` writes it into `CHANGELOG.md` and removes the fragments
(`docs/RELEASING.md`).
