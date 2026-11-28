# Releasing

How Lanes is versioned and released. `CHANGELOG.md` holds what each release changed. Until a
release, each change is a fragment of its own in `docs/changes/` (`CONTRIBUTING.md`), and `lake
exe lanes changelog` prints them as the Unreleased section.

## Versions

Lanes follows [Semantic Versioning](https://semver.org/). While it is 0.x, a minor release
(0.1.0 to 0.2.0) may break the API, and a patch release (0.1.0 to 0.1.1) only fixes: no
declaration is removed, renamed or given another type. From 1.0.0 on, only a major release
breaks.

A release is a tag `vX.Y.Z` on `main`, at a commit whose `version` in `lakefile.lean` is
`X.Y.Z`. Reservoir, Lean's package index, reads the tags and the version from the repository.
`lake exe lanes new` makes an app that requires the release tag of the checkout it runs from,
or that checkout's commit when no tag is at it, unless it is given `--rev`. Until the first
release, every new app is pinned to a commit, and its lakefile says so.

## Toolchain

Each release names, in its `CHANGELOG.md` section, the Lean toolchain it targets (the contents
of `lean-toolchain`). Lanes requires no other package. A toolchain bump is a pull request of its
own (`AGENTS.md`, "Build and checks"), with nothing else in it but what the bump needs.

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

1. Run `lake exe lanes changelog --release X.Y.Z YYYY-MM-DD`. It gathers the fragments of
   `docs/changes/` into a section `## [X.Y.Z] - YYYY-MM-DD` of `CHANGELOG.md`, below the
   Unreleased heading, each section's entries in the order of the fragments' names, and removes
   the fragments. Read the section and edit it as one text: put the entries in an order a user
   reads, and add the toolchain line. Then update the compare links at the bottom.
2. Set `version` in `lakefile.lean` to `X.Y.Z`, in the same pull request.
3. Run the benchmark on the runner machine (`.github/workflows/bench.yml`, `bench/README.md`) and
   compare it with the last release; say a regression in the CHANGELOG section.
4. Merge the pull request through the merge queue. Tag the merge commit on `main`, signed
   (`git tag -s vX.Y.Z -m "Lanes X.Y.Z"`) or annotated (`git tag -a`), and push the tag.
5. Make a GitHub Release from the tag whose notes are the CHANGELOG section:
   `gh release create vX.Y.Z --verify-tag --title "Lanes X.Y.Z" --notes-file <section>`.
6. Within a day, check that Reservoir lists `X.Y.Z` and that its build of it passed; if not,
   find out why before announcing the release.
