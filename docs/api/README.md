# API docs

The reference of `import Lanes` and of the soundness theorems, `import Lanes.Proofs`: every
module and declaration with its docstring and a link to its source, built with
[doc-gen4](https://github.com/leanprover/doc-gen4). This directory is a Lake package of its
own, so the library and its manifest do not depend on doc-gen4. It requires Lanes from this
clone and doc-gen4 at the tag of the toolchain in `lean-toolchain`.

From the clone, once Lanes builds (`lake build`):

```bash
docs/api/link-packages.sh && (cd docs/api && lake build +Lanes.Proofs:docs)
```

The pages are in `docs/api/.lake/build/doc`. Serve them to read them
(`python3 -m http.server -d docs/api/.lake/build/doc`): the search reads files that a browser
does not load from `file://`. CI builds them on every push to main and every pull request that
changes `Lanes/` (`.github/workflows/docs.yml`), as the artifact `api-docs`.

`+Lanes.Proofs:docs` documents that module and what it imports: the API, the soundness theorems,
and Lean's `Init`, `Std`, `Lean` and `Lake`, which doc-gen4 always documents. `+Lanes:docs` is
the API alone. Neither reaches the proof layer, which only `Lanes.Semantics` imports;
`Lanes:docs`, the whole library, documents it too. The first build takes about ten minutes,
most of it Lean's own modules; after it, about a minute: the modules that changed and the pages.

`link-packages.sh` makes `docs/api/.lake/packages` a directory of links to the root's
`.lake/packages`, one for each package of the root's `lake-manifest.json` (it has none now), so
they are neither fetched nor built again. Lake fetches doc-gen4 and its dependencies, `Cli`
among them, into real directories beside them: a build here writes nothing into the root's
packages. The script checks that
`docs/api/lake-manifest.json` pins the root's packages at the root's revisions, which it must:
Lake would otherwise check another revision out in the root's copy. Never link the whole
directory, and never run `lake update` here. When the root's manifest or the toolchain changes,
write this manifest again: the root's entries, marked `inherited`, after `lanes` and doc-gen4 at
the new tag, then doc-gen4's own dependencies from its manifest at that tag.

How much of the API has docstrings: `lake exe lanes docstrings`, and `--list` for the
declarations without one.
