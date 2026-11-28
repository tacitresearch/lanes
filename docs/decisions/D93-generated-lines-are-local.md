# D93. Each generated line is about one item, and unreleased changes are fragments

Status: Partly superseded by D100-each-doc-has-one-job.md (the status fragments) and by D110-volatile-actors.md (the changelog fragments)

The first recommendation of the structure proposal (pull request #83). Pull requests were taken
off the merge queue for conflicts almost every time another one landed: 19 dequeues in 20 pull
requests, and 48 of 135 commits only wrote the generated files again. GitHub's merge ignores
the merge driver of `.gitattributes`, so the conflicts it saw were real to it. Most were in a
few lines:

- the last row of the inventory's summary, `| All | … |`, which every new definition changed;
- the counts in the inventory's evidence ("and 22 more"), which every new test of a definition
  changed;
- the rows of `docs/STATUS.md` (removed), consecutive lines of one table, and the known limits of all
  areas, one run of lines: git calls changes to neighbouring lines a conflict;
- the end of the decisions' index, where every new decision was appended;
- the README's total of trusted lines;
- the top of `CHANGELOG.md`'s Unreleased section, where every pull request added its line.

## The rule

A generated file stays committed and checked by `lanes lint`, so the docs on the main branch are
current. What it holds changes: each line is about one item, and no committed line depends on
the whole repository. Two pull requests then conflict only when they change the same item, or
two items whose lines are neighbours.

- `docs/INVENTORY.md` (removed) has no summary. An evidence cell names at most three items, in order, and
  then "and others", with no count.
- `docs/STATUS.md` (removed) has one section per area and per app, each from its fragment in
  `docs/status/` (removed), with a heading between neighbours. A fragment has one item per line, in sorted
  lists, which `lanes lint --fix` sorts; a new item lands at its own place, not at the end.
- The decisions' index is sorted by slug, not by number.
- The README names no total. `lake exe lanes stats` prints the totals, and CI writes them to the
  job's summary.
- `TRUSTED.md` keeps each file's count. A change to trusted code should show there, and a
  conflict there means two pull requests changed trusted files whose rows are neighbours.

## Changelog fragments

An unreleased change is a file of its own, `docs/changes/<slug>.md`, as Go keeps `doc/next/`: a
section heading of Keep a Changelog and the change's entries. `CHANGELOG.md` keeps the released
history. `lake exe lanes changelog` prints the Unreleased section from the fragments, and at a
release `--release X.Y.Z DATE` writes it into `CHANGELOG.md` and removes them. The CI job
`changelog` asks for a fragment where it asked for a line, and the label `no-changelog` still
excuses a change. The entries written before there were fragments are one fragment,
`docs/changes/before-fragments.md`, in the order and sections they had, so that the history
reads as it did.

## Not done

- A merge driver: GitHub's merge does not run one.
- A bot that merges the main branch, runs `lint --fix` and pushes after each dequeue: it treats
  the symptom, at a full build per dequeue.
- One small file for every count: every pull request would change it.
- Generated files left out of the repository: the pages would leave the main branch, and an
  agent would have to build the library to read the inventory.
