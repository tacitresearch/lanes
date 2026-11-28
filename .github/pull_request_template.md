Fixes #n
<!-- First line: "Fixes #n" or "Part of #n" (CONTRIBUTING.md). GitHub closes the issue when a PR that says "Fixes" merges. -->

## What and why

<!-- One paragraph. Cite the rules of AGENTS.md that shaped a choice ("rule 2.6"). -->

## Checklist

- [ ] The spec came first and is model-checked (rules 1.2, 5.1), or no spec changed.
- [ ] Every new definition is proved, or tested, or listed in `TRUSTED.md` (rule 5.8); lint passes.
- [ ] A decision file in `docs/decisions/` if a design changed.
- [ ] The claims and limits of the area in `docs/ARCHITECTURE.md`, or a `known-limit` issue, if what works changed.
- [ ] The rules that shaped a choice are cited above.
- [ ] `lake build --wfail`, `lake test`, `lake exe lanesCheck` and `lake exe lanes lint` pass after merging `main`.
