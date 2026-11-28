# Contributing to Lanes

Lanes is a framework for verified software in Lean 4: actors with pure step functions, one
semantics, a proved runtime kernel, a model checker, proofs, and adapters.

## Build and check

`AGENTS.md` is the rules file, for people and agents alike: how to build, the checks to run
before a change is done, the design rules, the code and proof conventions, and the layout of
the repository. Read it first; this file does not repeat it. A clone needs elan and a C compiler
(`README.md`).

## How a change is made

- Work is trunk-based: `main` is the only long-lived branch. Make one branch per change, from
  `main`, and open a pull request from it.
- Every pull request belongs to an issue, and its description's first line names it: `Fixes #n`
  when the pull request finishes the issue, `Part of #n` when it is one step of it. GitHub closes
  the issue when a pull request that says `Fixes` merges, and lists the others on it. A change
  with no issue gets one first.
- A pull request merges through the merge queue once the `build` check passes. `build` passes
  only when every CI job before it passed: the build with warnings as errors, lint, the tests,
  the model checks, the differential tests against Go, and the applications' jobs.
- Before asking for review, merge `main` into the branch and run the checks again (`AGENTS.md`,
  "Parallel branches").
- A design that is settled or changed gets a decision file in `docs/decisions/`, written as
  `AGENTS.md` says (a new file, numbered on `main`, with a status line under its title). A
  decision is never rewritten: a new one supersedes it and changes the old one's status line.
- What works and what is claimed of it is in `docs/ARCHITECTURE.md`, with the evidence; a limit
  that can be fixed is an issue labelled `known-limit`. A change updates either in the same pull
  request.
- A change to a type that a journal or a snapshot holds is checked against what was written
  before (`AGENTS.md`, rule 2.8): after one that old files read, run `lake exe lanes lint --fix`,
  which pins the new schema, and commit the pinned file. Files of the corpus
  (`Tests/Journals/`) are added at a release (`docs/RELEASING.md`) and never rewritten.
- Cite the rules that shaped a choice in the pull request description, by number ("rule 2.6").

## What is reviewed by a person

A theorem says that code meets its spec, not that the spec says what was meant. So a person
reviews what proofs cannot: specs, trusted code (`TRUSTED.md`), the C, CI and infrastructure,
and decisions. `.github/CODEOWNERS` names who. The rest is evidenced by proofs, model checks and
tests, which CI runs; a reviewer reads those for what they claim, not line by line.

## The changelog

No pull request writes a changelog entry. `CHANGELOG.md` says what changed between two releases,
for someone who uses Lanes: the net change, a short list, not the history (git and
`docs/decisions/` hold that). It is written when a release is cut (`docs/RELEASING.md`), from the
git log since the last tag and the decisions accepted since. The files left in `docs/changes/`
are raw material for the first release's notes.

## Agents

Contributions written by agents are welcome under the same rules and the same checks; most of
Lanes was written that way. The person who opens the pull request, or on whose behalf an agent
opens it, answers for it, and its specs and trusted code are reviewed by a person like any
other.

## Reporting

Bugs and proposals: the issue forms. Vulnerabilities, and theorems whose statement does not
mean what their docs say: privately, as `SECURITY.md` says. Conduct: `CODE_OF_CONDUCT.md`.
