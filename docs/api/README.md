# API docs

The reference of `import Lanes`, every module and declaration with its docstring and a link to
its source, built with [doc-gen4](https://github.com/leanprover/doc-gen4). This directory is a
Lake package of its own, so the library and its manifest do not depend on doc-gen4. It requires
Lanes from this clone and doc-gen4 at the tag of the toolchain in `lean-toolchain`.

From the clone, once Lanes builds (`lake exe cache get`, then `lake build`):

```bash
docs/api/link-packages.sh && (cd docs/api && lake build +Lanes:docs)
```

The pages are in `docs/api/.lake/build/doc`; open `index.html` through a local server
(`python3 -m http.server -d docs/api/.lake/build/doc`), since the search reads files that a
browser does not load from `file://`. CI builds them on every push to main and every pull request
that changes `Lanes/` (`.github/workflows/docs.yml`), as the artifact `api-docs`.

`link-packages.sh` makes `docs/api/.lake/packages` a directory of links to the root's
`.lake/packages`, one for each package of the root's `lake-manifest.json`, so Mathlib and the
rest are neither fetched nor built again; Lake fetches doc-gen4, its dependencies and `Cli`,
which doc-gen4 builds, into real directories beside them. It checks that
`docs/api/lake-manifest.json` pins those packages at the root's revisions, which it must: Lake
would otherwise check another revision out in the root's copy. Never link the whole directory,
and never run `lake update` here; after the root's manifest changes, write this one again with
its entries for the root's packages copied from the root's, and doc-gen4 at the new tag.

`+Lanes:docs` documents the module `Lanes` and what it imports: the Lanes API, and Lean's
`Init`, `Std`, `Lean` and `Lake`, which doc-gen4 always documents. `+Lanes.Proofs:docs` adds the
soundness theorems, which import only `Std` too. Neither documents Mathlib; `Lanes:docs`, the
whole library, would, since it includes `Lanes.Semantics`. The first build takes about ten
minutes, most of it Lean's own modules; after it, only the modules that changed and the pages.

How much of the API has docstrings: `lake exe lanes docstrings`, and `--list` for the
declarations without one.
