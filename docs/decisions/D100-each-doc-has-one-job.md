# D100. Each doc has one job, and is generated or tested where it can be

Status: Partly superseded by new-volatile-actors.md (the inventory computed by `lanesInventory`)

Issue #110. Agents do what the docs say, so a fact written in two places, or a list kept by
hand, goes stale and misleads them. The docs had grown such overlaps: the status page, the
claims table, the architecture, the roadmap and the standard library's triage each said what
exists and what is missing, and the inventory was a committed file that every change to a
definition rewrote.

- Each fact lives in one place. `docs/ARCHITECTURE.md` has a section per area and per
  application: what it does, its claims with their evidence, premises and status, and the limits
  the design accepts. `docs/CLAIMS.md` and the status page (`docs/STATUS.md`, generated from
  `docs/status/`) are merged into it, and the generator of the status page and its lint rule are
  gone.
- Work and status are GitHub issues, not docs. A limit that can be fixed is an issue labelled
  `known-limit`; the roadmap points to issue #93 and the issues; the fixable limits of the status
  page and the open items of the roadmap and of the standard library's triage (`docs/STDLIB.md`)
  are listed one a line in `docs/known-limits-to-file.md` until they are filed. `docs/history/` is
  gone: git keeps it. This supersedes the part of
  `docs/decisions/D93-generated-lines-are-local.md` that keeps the status in fragments.
- A doc states rules and reasons, or it is generated or tested. The inventory is computed by
  `lanesInventory`, which `lanes lint` runs for the checks `inventory` and `inventory-none` and
  `lanes inventory` prints; no committed file holds it. This supersedes the part of
  `docs/decisions/D47-the-inventory-is-computed.md` that writes `docs/INVENTORY.md`.
- Each decision has a status line under its title, which the decision that supersedes it
  changes; the generated index lists the current decisions first, and `lanes lint` fails on a
  decision without one.

Why: a fact in one place cannot disagree with itself, and a generated or tested doc cannot drift
from what it describes. The cost is that the architecture is long; it is one page an agent
reads by area, not six pages that overlap.
