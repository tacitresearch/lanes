### Added

- `docs/decisions/new-layered-packages.md`: a proposal to split Lanes into layered packages in one
  repository with one version and a `lanes` umbrella, to remove Mathlib and CSLib, and to fetch
  prebuilt builds by commit. `scripts/layers.py` computes the import graph it cites.
