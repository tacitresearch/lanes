### Added

- `lanes changelog`: the Unreleased section, gathered from the fragments in `docs/changes/`, one file per change; `--release X.Y.Z DATE` writes it into `CHANGELOG.md` and removes them. Lint `changelog` checks each fragment.
- `lanes stats`: the totals no committed file holds, trusted lines, decisions, changelog fragments and the inventory's statuses by area (`lanesInventory --summary`).

### Changed

- The generated docs are line-local, so that two pull requests that change different items do not conflict: the inventory has no summary and its evidence no counts; the decisions' index is sorted by slug; the README has no total of trusted lines (`docs/decisions/new-generated-lines-are-local.md`).
- A change a user would notice adds a fragment to `docs/changes/` instead of a line to `CHANGELOG.md`, and the CI job `changelog` asks for one (`CONTRIBUTING.md`).
