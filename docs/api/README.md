# API docs

The reference of `import Lanes` and of the soundness theorems, `import Lanes.Proofs`: every
module and declaration with its docstring and a link to its source, built with
[doc-gen4](https://github.com/leanprover/doc-gen4). This directory is a Lake package of its
own, so the library and its manifest do not depend on doc-gen4. It requires Lanes from this
clone and doc-gen4 at the tag of the toolchain in `lean-toolchain`.

From the clone, once Lanes builds (`lake build`):

```bash
cd docs/api && lake build +Lanes.Proofs:docs
```

The pages are in `docs/api/.lake/build/doc`. Serve them to read them
(`python3 -m http.server -d docs/api/.lake/build/doc`): the search reads files that a browser
does not load from `file://`. CI builds them on every push to main and every pull request that
changes `Lanes/` (`.github/workflows/docs.yml`), as the artifact `api-docs`.

`+Lanes.Proofs:docs` documents that module and what it imports: the API, the soundness theorems,
and Lean's `Init`, `Std`, `Lean` and `Lake`, which doc-gen4 always documents. `+Lanes:docs` is
the API alone. The first build takes about ten minutes, most of it Lean's own modules; after it,
about a minute: the modules that changed and the pages.

Lanes requires no package, so Lake fetches only doc-gen4 and its dependencies, into
`docs/api/.lake/packages`. Never run `lake update` here. When the toolchain changes, write
`docs/api/lake-manifest.json` again: `lanes`, doc-gen4 at the new tag, then doc-gen4's own
dependencies from its manifest at that tag.
