# Contributing to Lanes

Lanes is a framework for verified software in Lean 4: actors with pure step functions, one
semantics, a proved runtime kernel, a model checker, proofs, and adapters.

## Build and check

`AGENTS.md` is the rules file, for people and agents alike: how to build, the checks to run
before a change is done, the design rules, the code and proof conventions, and the layout of
the repository. Read it first; this file does not repeat it. Lanes links libsodium, so a clone
needs a C compiler, `libsodium-dev` and `pkg-config` (`README.md`).

## How a change is made

- Work is trunk-based: `main` is the only long-lived branch. Make one branch per change, from
  `main`, and open a pull request from it.
- A pull request merges through the merge queue once the `build` check passes. `build` passes
  only when every CI job before it passed: the build with warnings as errors, lint, the tests,
  the model checks, the differential tests against Go, and the applications' jobs.
- Before asking for review, merge `main` into the branch and run the checks again (`AGENTS.md`,
  "Parallel branches").
- A design that is settled or changed gets a decision file in `docs/decisions/`, written as
  `AGENTS.md` says (a new file, numbered on `main`). A decision is never rewritten: a new one
  supersedes it.
- Cite the rules that shaped a choice in the pull request description, by number ("rule 2.6").

## What is reviewed by a person

A theorem says that code meets its spec, not that the spec says what was meant. So a person
reviews what proofs cannot: specs, trusted code (`TRUSTED.md`), the C, CI and infrastructure,
and decisions. `.github/CODEOWNERS` names who. The rest is evidenced by proofs, model checks and
tests, which CI runs; a reviewer reads those for what they claim, not line by line.

## The changelog

A pull request that changes the library, the C, the `lanes` command or the app template adds a
line under `Unreleased` in `CHANGELOG.md`, in one of Added, Changed, Fixed or Security. A CI job
(`changelog`) checks this. A change with nothing to tell a user (a proof refactored, a comment
fixed) gets the label `no-changelog` instead; push again after adding the label, since the job
reads the labels the pull request had when it ran.

## Agents

Contributions written by agents are welcome under the same rules and the same checks; most of
Lanes was written that way. The person who opens the pull request, or on whose behalf an agent
opens it, answers for it, and its specs and trusted code are reviewed by a person like any
other.

## Reporting

Bugs and proposals: the issue forms. Vulnerabilities, and theorems whose statement does not
mean what their docs say: privately, as `SECURITY.md` says. Conduct: `CODE_OF_CONDUCT.md`.
