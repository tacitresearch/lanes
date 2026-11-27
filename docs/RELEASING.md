# Releasing

How Lanes is versioned and released. `CHANGELOG.md` holds what each release changed.

## Versions

Lanes follows [Semantic Versioning](https://semver.org/). While it is 0.x, a minor release
(0.1.0 to 0.2.0) may break the API, and a patch release (0.1.0 to 0.1.1) only fixes: no
declaration is removed, renamed or given another type. From 1.0.0 on, only a major release
breaks.

A release is a tag `vX.Y.Z` on `main`, at a commit whose `version` in `lakefile.lean` is
`X.Y.Z`. Reservoir, Lean's package index, reads the tags and the version from the repository.
`lake exe lanes new` makes an app that requires `main` unless it is given `--rev vX.Y.Z`.

## Toolchain

Each release names, in its `CHANGELOG.md` section, the Lean toolchain it targets (the contents
of `lean-toolchain`) and the CSLib commit it pins; Mathlib is the one CSLib pins. A toolchain
bump is a pull request of its own, after CSLib has made the same bump (`AGENTS.md`, "Build and
checks"), with nothing else in it but what the bump needs.

## Deprecation

A public declaration of a stable module that is renamed or removed is kept for one minor release
with `@[deprecated new_name (since := "X.Y.Z")]`, or `@[deprecated (since := "X.Y.Z")]` when
nothing replaces it, and removed in the minor release after. A patch release deprecates nothing.

## Stability

A module is stable or experimental.

- Stable: changes follow the deprecation rule above.
- Experimental: may change or go in any minor release, without deprecation.

A module is experimental when its `/-! -/` header has the line `Stability: experimental`; a
module without that line is stable. `lanes lint` does not check this yet.

## Checklist

1. In `CHANGELOG.md`, give the Unreleased entries their version and the date
   (`## [X.Y.Z] - YYYY-MM-DD`), with the toolchain line, open an empty Unreleased above it, and
   update the compare links at the bottom.
2. Set `version` in `lakefile.lean` to `X.Y.Z`, in the same pull request.
3. Run the benchmark on the runner machine (`.github/workflows/bench.yml`, `bench/README.md`) and
   compare it with the last release; say a regression in the CHANGELOG section.
4. Merge the pull request through the merge queue. Tag the merge commit on `main`, signed
   (`git tag -s vX.Y.Z -m "Lanes X.Y.Z"`) or annotated (`git tag -a`), and push the tag.
5. Make a GitHub Release from the tag whose notes are the CHANGELOG section:
   `gh release create vX.Y.Z --verify-tag --title "Lanes X.Y.Z" --notes-file <section>`.
6. Within a day, check that Reservoir lists `X.Y.Z` and that its build of it passed; if not,
   find out why before announcing the release.
