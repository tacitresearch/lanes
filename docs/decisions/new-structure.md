# D?. A cleaner repository structure (proposal)

The owner asked for a pass over the repository's structure. This is a proposal for the owner to
accept or edit, part by part. Nothing moves in this change: five pull requests are open, and
moves would conflict with each of them. The numbers are measured on `origin/main` at `c1d9d9d`
(pull request #75).

Section 1 can be done first and alone: it is the generated docs, which cost the most tonight.
Sections 2 to 6 are the structure: the test kit, a rule for vendors, the split of `Lanes/Web/`,
the sign-in example, and the rest. Section 7 orders the work, and section 8 lists what the owner
must decide.

## 1. Generated docs that do not conflict (do this first)

### What it costs

Every pull request is dequeued from GitHub's merge queue for `MERGE_CONFLICT` whenever another
one lands, and the conflict is almost always in a generated file. Each costs a merge of main, a
rebuild, `lake exe lanes lint --fix` and a push.

Measured over the last 20 merged pull requests (#56 to #75, 09:32 to 14:42):

- 39 entries into the queue for 20 merges: 19 dequeues, and 10 of the 20 dequeued at least once
  (#68 four times). 18 of the 19 dequeues happened within a minute of another pull request
  landing.
- 135 commits that are not merges, of which 48 say they regenerate the generated files after a
  merge of main; and 53 merges of main into the branches.
- 10 of the 19 dequeues re-run without a custom merge driver, as GitHub merges (the branch's head
  when it was queued, against the main that had just landed): `docs/INVENTORY.md` conflicts in
  all 10, `docs/STATUS.md` in 6, `docs/decisions/README.md` in 5, `TRUSTED.md` in 1. In 5 of the
  10 the generated files were the only conflict (#68 twice, #62 once, #72 twice).

Which generated regions each merge changed:

| PR | Dequeued | `INVENTORY.md` summary | `INVENTORY.md` module sections | `STATUS.md` hunks | `README.md` total | `TRUSTED.md` | Decisions index |
| --- | ---: | --- | ---: | ---: | --- | --- | --- |
| #56 | 0 | | | 2 | | | |
| #57 | 0 | yes | 1 | 4 | yes | rows | yes |
| #55 | 2 | yes | 7 | 1 | yes | rows | yes |
| #59 | 0 | yes | 1 | | | counts | |
| #60 | 1 | yes | 29 | 3 | yes | rows | yes |
| #61 | 1 | yes | 15 | 5 | | rows | yes |
| #64 | 0 | yes | 12 | 4 | | rows | yes |
| #63 | 2 | yes | 12 | 5 | | rows | |
| #65 | 1 | yes | 16 | 3 | | rows | yes |
| #66 | 2 | yes | 17 | 3 | | rows, counts | yes |
| #69 | 0 | | | | | | |
| #70 | 0 | yes | 1 | 2 | | | yes |
| #73 | 0 | | | | | | |
| #62 | 2 | yes | 18 | 5 | | rows | yes |
| #74 | 0 | | | | | | |
| #72 | 2 | yes | 11 | 2 | | | yes |
| #68 | 4 | yes | 26 | 2 | yes | rows | yes |
| #67 | 2 | yes | 10 | 3 | | | |
| #76 | 0 | | 16 | 3 | | rows | |
| #75 | 0 | yes | 4 | 1 | yes | rows | yes |
| **Of 20** | | **15** | **16** | **16** | **5** | **13** | **12** |

The lines that make two unrelated pull requests conflict:

- **The inventory's summary.** Its last row, `| All | 2407 | 1262 | … |`, changed in 15 of 20.
  Any two of those conflict. It was the conflict in all 10 re-runs.
- **Counts inside the inventory's evidence.** `Check.Report.ok`'s cell reads "`Tests/Bank.lean`,
  … and 22 more"; every new test that uses it changes the count (4 of the 10 re-runs).
- **The decisions index.** A new decision is appended after the last line. Two pull requests
  that each add one insert at the same place, so they always conflict (12 of 20 add one).
- **Adjacent rows of `STATUS.md`.** The areas' rows are consecutive lines of one table, and git
  calls changes to neighbouring lines a conflict: one pull request changed "Proof layer", the
  other "Runtime" (#72 against #70). The known limits of all areas are also one run of lines,
  with no area between them. The fragments in `docs/status/` never conflict there; the page does.
- **The README's total**, "About 3,550 lines of trusted code", changed in 5 of 20.

### Why the obvious fixes do not work

- **A merge driver.** `.gitattributes` names a driver (`merge=generated`). GitHub's server-side
  merge ignores custom drivers, so the queue never uses it.
- **A merge-queue job that runs `lanes lint --fix` and pushes a fix.** The queue builds a merge
  group only when the branch merges cleanly; a conflicting branch is dequeued before any job
  runs. The group's branch (`gh-readonly-queue/…`) cannot be pushed to, and a group whose head
  changed is not merged. A bot on the `dequeued` event of `pull_request` could merge main with
  the driver, run `lake build lanesInventory && lake exe lanes lint --fix`, push and requeue. It
  works, but it costs a full build per dequeue and a token that can push and start CI, and it
  treats the symptom. It is the fallback if the fix below is refused.
- **Moving every count into one small generated file.** Every pull request that changes a count
  would then change that one file, so any two would conflict. Counts have to leave the committed
  files, not gather in one.
- **Not committing the generated files**, generating them in CI or in the docs build, with lint
  checking the sources only. It ends the conflicts. But the pages leave main: `docs/STATUS.md`,
  `docs/INVENTORY.md` and the index are no longer in a checkout or on GitHub, the README's links
  break, and an agent has to build the library to read the inventory. "Docs on main are always
  current" would hold only by calling the sources the docs.

### What to do: each pull request touches only its own lines, and no total is committed

Keep every generated file committed and checked by `lanes lint`, so main stays current. Change
what is generated, so that two pull requests conflict only when they change the same item, and
so that nothing in a committed file adds up over all items. Git does not call two changes a
conflict when an unchanged line separates them.

| File | Change | Where in the code |
| --- | --- | --- |
| `docs/INVENTORY.md` | Drop the summary table. `lake exe lanes inventory --summary` prints it, and CI writes it to the job's summary. An evidence cell names at most three items, chosen in a stable order, and then "and others", with no count | `summary` and `render` in `LanesCli/Inventory.lean`; "and N more" at line 386 |
| `docs/STATUS.md` | One section per area and per app (`### Web`, then what exists, where, and that area's known limits), instead of rows of one table and one run of limits. Neighbouring fragments are then separated by a heading | `statusPlan` in `LanesCli/Generated.lean`; `docs/status/page.md` |
| `docs/status/*/*.md` | A fragment may hold several lines: one item per line, sorted, instead of one row of about 1,500 characters. The "Adapters" fragment was edited by both sides in 5 of the 10 re-runs | `splitFragment` |
| `docs/decisions/README.md` | The index is sorted by slug, not by number, one line per decision with its number first. A new decision lands at its own place in the list instead of after the last line, so two new ones conflict only when their slugs are neighbours | `indexText` |
| `README.md` | No number: "the trusted code is listed with its sizes in `TRUSTED.md`". `lanes lint` prints the total | `rewriteTotal`, `trustedPlan` |
| `TRUSTED.md` | Keep each file's count. A change to trusted code should show in `TRUSTED.md`, and a conflict there means two pull requests changed trusted files whose rows are neighbours, which a reviewer should see | none |

Two things found on the way go in the same pull request, or one before it:

- `TRUSTED.md`'s row for `Lanes/Web/IO/Server.lean` lost its count and a column separator in a
  merge resolution (the merge of #60 left `` `Lanes/Web/IO/Server.lean`,   | ``; #63 then dropped
  the `|`). `trusted-size` reads only `` `path`, N lines `` entries, so a row without a count
  passes, and the file's 642 lines are missing from the total: the README says about 3,550, and
  the listed counts with it come to about 4,200. Fix the row, and make `trusted-listed` require a
  counted entry for each file it finds, not only a mention.
- `docs/decisions/README.md` says decisions follow `DESIGN.md`, which is gone, and that main
  numbers them after a merge; `AGENTS.md` says whoever opens the pull request does. Rewrite its
  preamble.

Cost: one pull request of about 150 lines in `LanesCli/`, `Tests/Lint.lean`, `AGENTS.md`
("Parallel branches") and the regenerated files. It changes every generated file once, so each
open pull request merges main once more, as today. After it, the 5 re-run dequeues whose only
conflicts were generated would most likely not have happened, and the "Adapters" fragment split
would have avoided a sixth.

Hand-edited lists that conflict the same way are in section 6.

## 2. The test kit: `Lanes/Testing/` and `Tests/`

### Now

- `Lanes/Testing/`: 4 modules, 970 lines, 82 definitions (81 tested, 1 checked). `Http.lean`
  (a server of a handler on a local port, readers of a response), `Browser.lean`, `S3.lean` (a
  fake S3 that checks signatures and policies), `OAuth.lean` (a fake identity provider).
- It is the fourth root of the `Lanes` library, outside `import Lanes`
  (`docs/decisions/D77-a-test-kit.md`), so no serving binary links it.
- Imported by `Tests/S3.lean`, `Tests/OAuth.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean`
  (and its names used by `Tests/Oracle/Service/S3Post.lean`), by `examples/videos` (its
  `Videos/EndToEnd.lean`, a root of the library that `Main.lean` does not import, and
  `Live.lean`), and by `Tests/TutorialWeb/EndToEnd.lean` in pull request #78.
- Vendor fakes are already outside it: the metadata service and SES are faked in
  `integrations/aws/Checks/Fake.lean`.

### Options

1. Keep it a root of the `Lanes` library (D77).
2. A Lake package of its own, `testing/`, requiring `lanes`. D77 weighed it: cleaner to depend
   on, and not needed, since an application already requires `lanes` and the kit imports
   nothing more.
3. Move it into `Tests/`. Not possible: an application cannot import `Tests`, which is every
   project's own name.

### Recommendation

Keep it where it is, and write down what belongs where:

- **In the kit**: a fake of a protocol that `Lanes/` speaks (HTTP, S3, OAuth 2.0 and OpenID
  Connect), a driver (the browser), and a reader of pages, when more than one test or an
  application uses it.
- **In an integration**: a fake of one vendor's service, beside its client.
- **In `Tests/`**: the cases, the vectors, the model checks, the fixtures, and a helper only one
  test file uses (`Tests/HttpClient.lean`'s `holding`, `Tests/Tls.lean`'s `openssl` server).
- **`Http.Loopback` stays in `import Lanes`.** It is pure, and `examples/bank-web/Check.lean`
  and `examples/upload/Check.lean` drive it with `import Lanes` alone. Moving it into the kit is
  possible, and would make those checks import `Lanes.Testing`; it is not worth the change.

How examples import it: a test root (`Check.lean`, `EndToEnd.lean`, `Test.lean`) imports
`Lanes.Testing`; `Main.lean` and what it imports never do. A `testing` check in `lanes lint`
can hold that: in `Lanes/`, only `Lanes/Testing/` imports `Lanes.Testing`; in a package, no
module that a `Main.lean` reaches imports it. It is text-level, as `layering` is.

Moves: none. Additions, each small: the form reader another agent is adding (it replaces the two
copies of `uploadOf`, section 6), and `examples/ledger/Live.lean` and
`examples/rookery/Live.lean` rewritten on `Testing.Browser`. D77 was written because three
applications each wrote a scripted browser; videos moved to the kit, the ledger and rookery did
not.

## 3. Protocols in `Lanes/`, vendors in `integrations/`

### Now

D61 keeps vendors out of `Lanes/`. D71 took S3 and Signature Version 4 in all the same, as a
protocol many stores speak. D74 put a role's credentials and SES in `integrations/aws`, and D82
CloudFront's signed URLs, as one vendor's formats. Vendor names in `Lanes/` today:

| Where | What | Verdict |
| --- | --- | --- |
| `Lanes/Web/S3/` (5 files), `Lanes/Web/Http/SigV4.lean`, `Lanes/Web/Http/SigV4Sound.lean`, `Lanes/Web/IO/S3.lean` | The S3 API and Signature Version 4 | Protocol (D71): stays, moves to `Lanes/S3/` (section 4) |
| `S3.Endpoint.aws` (`Lanes/Web/S3/Basic.lean:45`) | AWS's host form, `s3.<region>.amazonaws.com` | Vendor. Moves to `integrations/aws` as `Aws.S3.endpoint`, beside `Aws.Ses.Endpoint.aws` and `Aws.Sqs.Endpoint.aws` |
| `S3.credentialsFromEnv` (`Lanes/Web/IO/S3.lean:40`) | Reads `AWS_ACCESS_KEY_ID`, `AWS_SECRET_ACCESS_KEY`, `AWS_SESSION_TOKEN` | Vendor convention. Moves to `integrations/aws` beside the role's credentials, and its trusted lines with it |
| The namespace in `CompleteMultipartUpload` (`Lanes/Web/S3/Basic.lean:90`) | `http://s3.amazonaws.com/doc/2006-03-01/` | Protocol: every S3 server reads it. Stays |
| `Lanes/Outside/Queue.lean` (SQS), `Lanes/Outside/Idempotent.lean` and `Lanes/Outside/Effects/Payments.lean` (Stripe) | A class's model, saying whose documentation it follows | Stays |
| `Lanes/Lib/Postgres/IO/Client.lean` (RDS) | A docstring | Stays |
| `Lanes/Testing/OAuth.lean` (GitHub) | A fake of OAuth 2.0 without OpenID Connect whose user API is shaped as GitHub's | Stays: it fakes the class the GitHub preset is one of |
| `Lanes/Web/IO/Tls.lean` (GitHub) | A comment about CI's macOS runners | Stays |

No SES, SQS, Stripe, Google, CloudFront or RDS code is in `Lanes/`.

### The rule

A new rule in the design group, as rule 1.8:

> 1.8 **Protocols in `Lanes/`, vendors in `integrations/`.** `Lanes/` holds a protocol that
> more than one independent implementation speaks (HTTP, TLS, OAuth 2.0 and OpenID Connect, the
> S3 API and Signature Version 4, PostgreSQL's protocol) and the model of a class of outside
> system (D61). What only one vendor serves is a Lake package under `integrations/`: its APIs
> and formats (SES, SQS, CloudFront's signed URLs), its endpoints, regions and environment
> variables, its credentials, its presets (sign-in with Google or GitHub), and its fakes. A
> vendor's name appears in `Lanes/` only in prose that says whose documentation a model or a
> protocol follows. *Why:* what a vendor changes should not change `Lanes/`, and an integration
> can be released or dropped on its own.

What moves: the two definitions above, and `examples/videos` then requires `integrations/aws`
(as D82 already expects). About 40 lines in 9 files: `Lanes/Web/S3/Basic.lean`,
`Lanes/Web/IO/S3.lean`, `integrations/aws`, `examples/videos` (`Main.lean`, `Live.lean`,
`Videos/EndToEnd.lean`, `lakefile.toml`), `Tests/S3.lean:112`, and `docs/DEPLOY.md:314-323`. A
`vendors` check in `lanes lint` could refuse the names in code lines of `Lanes/`; it is optional.

## 4. `Lanes/Web` split into `Http`, `Auth` and `Net`

### Now

| Directory | Files | Lines | What |
| --- | ---: | ---: | --- |
| `Lanes/Web/Http/` | 26 | 10,710 | HTTP as data, its grammar, the wire format, the reader, connections, the gate, the front, routes, cookies, SSE, streams, waiting requests, the loopback, operators' endpoints, the shared cache's model, Signature Version 4 |
| `Lanes/Web/Html/` | 5 | 995 | HTML values, templates, htmx |
| `Lanes/Web/Auth/` | 6 | 1,677 | Tokens, password digests, failed attempts, sessions, JOSE, ID tokens, OAuth |
| `Lanes/Web/S3/` | 5 | 1,260 | The S3 client's calls and answers, multipart, POST policies, XML |
| `Lanes/Web/IO/` | 6 | 1,366 | The server, the client, operators' IO, the S3 client's IO, the sign-in's IO, TLS |
| `Lanes/Lib/Net/` | 3 | 2,025 | IP addresses, URLs |
| `Lanes/Net/` | 4 | 2,791 | The courier (namespace `Lanes.Peers`), the transport, a node with an HTTP front |

Edges that run against the layers: `Lanes/Lib/Net/Url.lean` imports `Lanes/Web/Http/Basic.lean`
for percent-encoding (D62 left it); `Lanes/Lib/Mime/MediaType.lean` imports
`Lanes/Web/Http/Grammar.lean`; `Lanes/Lib/Postgres/IO/Client.lean` imports
`Lanes/Web/IO/Tls.lean`; and the pure `Lanes/Web/S3/Basic.lean` imports the IO module
`Lanes/Web/IO/Client.lean`, where the client's data (`Client.Call`, `Scheme`, `Port`, `Config`)
lives.

Who imports these paths: only `Lanes/` itself (about 130 import lines in about 50 files, with
`Lanes.lean` and `Lanes/Proofs.lean`). No example, integration, template, benchmark or
`docs/api` names one: they import `Lanes`, `Lanes.Proofs`, `Lanes.Semantics` or `Lanes.Testing`
(and three JSON proof modules). The namespaces do not follow paths (D62), so no public name changes.

### Proposal

Four areas replace `Lanes/Web/`, and `Lanes/Net/` takes in what is below HTTP. The layers run
`Lanes/Lib/` → `Lanes/Net/` → `Lanes/Http/` → `Lanes/Html/`, `Lanes/Auth/`, `Lanes/S3/`, but
for the node (`Lanes/Net/IO/Node.lean`), an IO file that runs the server, as today.

| Path | Contents | Namespaces (unchanged) |
| --- | --- | --- |
| `Lanes/Net/` | IP addresses, URLs and percent-encoding, TLS (`IO/Tls.lean`); and, as now, the courier, the transport and a node | `Lanes.Ip`, `Lanes.Url`, `Lanes.Tls`, `Lanes.Peers` |
| `Lanes/Http/` | HTTP as data, grammar, media types, wire format, reader, connections, gate, front, routes, cookies, SSE, streams, waiting, loopback, operators' endpoints, the shared cache's model; the server, the client and operators' IO in `IO/` | `Lanes.Http` |
| `Lanes/Html/` | HTML values, templates, htmx | `Lanes.Html`, `Lanes.Hx` |
| `Lanes/Auth/` | Tokens, password digests, failed attempts, sessions, JOSE, ID tokens, OAuth; the sign-in's IO in `IO/` | `Lanes.Auth`, `Lanes.Jose`, `Lanes.OAuth` |
| `Lanes/S3/` | Signature Version 4, the S3 client's calls and answers, multipart, POST policies, XML; the client's IO in `IO/` | `Lanes.SigV4`, `Lanes.S3` |

Choices made, each open to the owner:

- **One `Lanes/Net/`, not two.** Today `Lanes/Net/` is the courier and `Lanes/Lib/Net/` is
  addresses. Putting addresses, URLs and TLS beside the courier gives one directory for the
  network, and moves 4 files. Renaming the courier's directory to `Lanes/Peers/`, after its
  namespace, would keep the two concerns apart, and moves 4 more.
- **Signature Version 4 goes with S3**, its one user in `Lanes/`; `integrations/aws` signs SES
  and SQS with it from there.
- **The shared cache's model stays in `Lanes/Http/`.** The layout table says models live in
  `Lanes/Outside/`, but this one is stated over requests: moving it would make
  `Lanes/Outside/` import `Lanes/Http/` while `Lanes/Http/Front.lean` imports
  `Lanes/Outside/Basic.lean`. The table should say so instead.
- **Media types move into `Lanes/Http/`**: they are RFC 9110's, and it removes the edge from
  `Lanes/Lib/` into HTTP.
- **Percent-encoding moves from `Lanes/Web/Http/Basic.lean` into `Lanes/Net/Percent.lean`** with
  its names kept (`Http.percentDecode`, `Http.percentEncodeByte`, `Http.hexValue?`), which removes
  the edge from URLs into HTTP. It is a move of definitions, so it is a pull request of its own.
- **The client's data moves out of its IO file** into `Lanes/Http/Client.lean`, so the S3 client
  stops importing IO. Also a move of definitions, later.

### The moves

`Lanes/Net/` (4 files):

| Old path | New path |
| --- | --- |
| `Lanes/Lib/Net/Ip.lean` | `Lanes/Net/Ip.lean` |
| `Lanes/Lib/Net/Url.lean` | `Lanes/Net/Url.lean` |
| `Lanes/Lib/Net/UrlSound.lean` | `Lanes/Net/UrlSound.lean` |
| `Lanes/Web/IO/Tls.lean` | `Lanes/Net/IO/Tls.lean` |

`Lanes/Html/` (5 files): `Lanes/Web/Html/X.lean` → `Lanes/Html/X.lean` for `Basic`,
`BasicSound`, `Htmx`, `HtmxSound`, `Syntax`.

`Lanes/Auth/` (7 files): `Lanes/Web/Auth/X.lean` → `Lanes/Auth/X.lean` for `IdToken`, `Jose`,
`Login`, `OAuth`, `Token`, `TokenSound`; and:

| Old path | New path |
| --- | --- |
| `Lanes/Web/IO/SignIn.lean` | `Lanes/Auth/IO/SignIn.lean` |

`Lanes/S3/` (8 files): `Lanes/Web/S3/X.lean` → `Lanes/S3/X.lean` for `Basic`, `Multipart`,
`Post`, `PostSound`, `Xml`; and:

| Old path | New path |
| --- | --- |
| `Lanes/Web/Http/SigV4.lean` | `Lanes/S3/SigV4.lean` |
| `Lanes/Web/Http/SigV4Sound.lean` | `Lanes/S3/SigV4Sound.lean` |
| `Lanes/Web/IO/S3.lean` | `Lanes/S3/IO/Client.lean` |

`Lanes/Http/` (29 files): `Lanes/Web/Http/X.lean` → `Lanes/Http/X.lean` for the 24 files
other than `SigV4` and `SigV4Sound` (above): `Basic`, `Conn`, `ConnSound`, `Cookie`,
`CookieSound`, `Front`, `FrontSound`, `Gate`, `Grammar`, `Loopback`, `Ops`, `OpsSound`,
`ReadRequest`, `ReadRequestSound`, `Route`, `RouteSound`, `SharedCache`, `Sse`, `SseSound`,
`Stream`, `Waiting`, `Wire`, `WireSound`, `WireSpec`; and:

| Old path | New path |
| --- | --- |
| `Lanes/Web/IO/Server.lean` | `Lanes/Http/IO/Server.lean` |
| `Lanes/Web/IO/Client.lean` | `Lanes/Http/IO/Client.lean` |
| `Lanes/Web/IO/Ops.lean` | `Lanes/Http/IO/Ops.lean` |
| `Lanes/Lib/Mime/MediaType.lean` | `Lanes/Http/MediaType.lean` |
| `Lanes/Lib/Mime/MediaTypeSound.lean` | `Lanes/Http/MediaTypeSound.lean` |

`Lanes/Web/`, `Lanes/Lib/Net/` and `Lanes/Lib/Mime/` are then empty.

What else each move rewrites: `Lanes.lean` and `Lanes/Proofs.lean`; the import lines of the
moved files and their importers; `Tests/Axioms/Web.lean`, split into `Tests/Axioms/Http.lean`,
`Html.lean`, `Auth.lean` and `S3.lean`, and the URL, IP and media types parts of
`Tests/Axioms/Lib.lean`, into `Tests/Axioms/Net.lean` and `Tests/Axioms/Http.lean`; the
protocol directories `["Lanes/Lib", "Lanes/Web"]` of the `oracles` check
(`LanesCli/Lint.lean:320`) and `oracles/README.md`; `scripts/mutants.py`; `TRUSTED.md`;
`AGENTS.md`'s layout table and rule 5.9; `docs/ARCHITECTURE.md`, `docs/STDLIB.md`,
`docs/CLAIMS.md` and the status fragments. `docs/decisions/` and `docs/history/` keep the old
paths: they record the past.

Churn: 53 files moved and about 400 references in 77 files (224 for HTTP, 66 for Auth, 53 for
S3, 29 for Net, 21 for Html), all mechanical: `git mv` and one substitution table, no definition
changed, as D62 did. Pull requests that edit a moved file still merge (git follows renames);
those that add a file under `Lanes/Web/` have to move it: #71 (`Lanes/Web/IO/CLoop.lean`) and
#58 (`Lanes/Web/Http/Read.lean`), both drafts.

### Compatibility: no re-exporting modules

Do not keep modules at the old paths that re-export the new ones:

- Nothing is released yet: `CHANGELOG.md`'s 0.1.0 is "unreleased", and there is no tag.
- Nothing outside `Lanes/` and `Tests/` imports a moved path (measured above), and no name
  changes, so code on `import Lanes` compiles unchanged.
- 53 shims would each need a place in the inventory, the `layering` and `oracles` checks, and
  the docs would name two paths for one module (rule 1.7).

The `CHANGELOG.md` entry under "Changed" gives the table of old and new paths.

Optional, and the same in kind: `Lanes/Lib/Postgres/` (10 files, 75 references in 26 files) to
`Lanes/Postgres/`, so that the two clients of outside systems, S3 and PostgreSQL, are both
top-level areas and `Lanes/Lib/` is the standard library alone.

## 5. Sign-in, folded into videos

`examples/sign-in` (290 lines in 4 Lean files, its gate included) is a standalone sign-in:
"the start of a video site", whose members sign in with Google or GitHub and get a session.
`examples/videos` does all of it (sign-in with both, sessions, signing out with a form token)
and more. Its package's library is also called `Videos`, with the namespace `Videos`, as the
video site's is. Its one theorem of its own, that the same identity signing in again is the same
member (`Videos.register_again`, `Videos.register_lookup`), has no counterpart in videos.

`docs/TUTORIAL-WEB.md` (pull request #78) teaches the smallest sign-in, in its step 2, with a
session cookie, and its code is kept true by `Tests/TutorialWeb/`.

Recommendation: delete `examples/sign-in`. State its theorem of videos' `Site.signIn` (the same
issuer and subject signing in again gets the same member), and point `examples/README.md`'s
reader to the tutorial for the smallest sign-in. Edits: `examples/README.md` (item 10 and the
feature table), `docs/status/apps/sign-in.md` (deleted), `docs/CLAIMS.md`'s row,
`docs/ARCHITECTURE.md:579`, `docs/DEPLOY.md:308`, `.github/workflows/ci.yml:147`, `CHANGELOG.md`.
About 290 lines out and 30 in. After #77, which rewrites videos' spec and proofs, and #78.

## 6. Other findings

### Hand-edited lists that conflict like generated ones

| File | Touched by, of 20 | Conflicts in the 10 re-runs | Proposal |
| --- | ---: | ---: | --- |
| `CHANGELOG.md` | 17 | 1 | Seven pull requests inserted at the top of "Added", at its first or second line. One file per change under `docs/changes/`, gathered into `CHANGELOG.md` at release (`docs/RELEASING.md`); the CI check asks for a file there instead |
| `Tests/Main.lean` | 10 | 3 | The imports and the lists of tests are appended in no order. Sort them, one per line |
| `docs/status/areas/adapters.md` | 9 | 5 | One row of 1,500 characters: one item per line, sorted (section 1) |
| `Lanes.lean`, `Lanes/Proofs.lean` | 8, 3 | 0 | Already sorted, one per line |
| `docs/ARCHITECTURE.md`, `docs/CLAIMS.md` | 15, 13 | 2, 2 | Prose; these conflicts are mostly real |

### Duplicated helpers

| Helper | Copies | Proposal |
| --- | --- | --- |
| The session cookie: its name (`hostCookie`), the cookie, `prepare` (drop the client's cookie and any header under the verified name, put the verified value there), reading it back | `examples/videos/Videos/Web.lean:78-106`, `examples/sign-in/Videos.lean`, `Tests/TutorialWeb/Web.lean:55-70` (#78); rookery's and the ledger's `verified?` and `signedIn` add the form token | `Lanes/Auth/Session.lean`, pure, with the theorem that a header a client sent under the verified name never reaches the system |
| `main`'s configuration: a number from the environment (`ms`), `LANES_HOST`, `LANES_IDLE_MS`, `LANES_DRAIN_MS` | `examples/counter/Main.lean` (and the template), `examples/videos/Main.lean`, `examples/reminders/Main.lean`, `Tests/TutorialWeb/Main.lean` (#78) | `Http.ServerConfig.fromEnv`, read once at start (rule 2.5), in `Lanes/Http/IO/Server.lean` |
| `loadKey`: 32 random bytes in a file only its user reads, made at the first start | `examples/videos/Main.lean:36`, `Tests/TutorialWeb/Main.lean` (#78) | `Auth.Key.load` in `Lanes/Auth/IO/`, with its row in `TRUSTED.md` |
| An OAuth client from `<NAME>_CLIENT_ID` and `<NAME>_CLIENT_SECRET` | `examples/videos/Main.lean:48`, `examples/sign-in/Main.lean:20`, #78 | `OAuth.Client.fromEnv` beside the sign-in's IO |
| `uploadOf`: a page's form, its action and hidden fields | `examples/videos/Videos/EndToEnd.lean:50`, `Tests/TutorialWeb/EndToEnd.lean:23` (#78), the same code | The kit's form reader that another agent is adding; both switch to it |
| A scripted client: `send`, `sessionOf`, `header?`, `body`, `contains` | `examples/ledger/Live.lean`, `examples/rookery/Live.lean` | `Testing.Browser` and its readers |

### Modules in the wrong area, by `AGENTS.md`'s layout table

- `Lanes/Lib/Net/Url.lean` and `Lanes/Lib/Mime/MediaType.lean` import HTTP from the standard
  library; `Lanes/Web/IO/Tls.lean` is TLS under "Web", imported by PostgreSQL's client;
  `Lanes/Web/Http/SigV4.lean` is S3's signing under HTTP. Section 4 moves them.
- `Lanes/Web/S3/Basic.lean`, which is pure, imports `Lanes/Web/IO/Client.lean`. Section 4.
- `Lanes/Web/Http/SharedCache.lean` is a model of an outside system outside `Lanes/Outside/`.
  It stays (section 4); the table should say so.
- The table's row for `Lanes/Web/` does not name `Loopback`, `Waiting`, `Ops`, `SharedCache`,
  `Sse` or `Stream`; the new rows of section 4 do.

### Dead modules

None. Every module of `Lanes/` is imported by a root, and every file of `Tests/` is a driver,
imported by one, or built as a check (`Tests/Inventory.lean`, `Tests/Liveness.lean`,
`Tests/SplitProofs.lean`). The one superseded package is `examples/sign-in` (section 5).

### Naming

- The courier's directory is `Lanes/Net/`, its namespace `Lanes.Peers`, its module `Courier`;
  addresses are in a second `Net`, `Lanes/Lib/Net/`. Section 4 leaves one.
- `Lanes/Web/IO/S3.lean` opens `Lanes.SigV4` and `Lanes.S3`; it becomes
  `Lanes/S3/IO/Client.lean`.
- Two example packages have a library named `Videos` (section 5).
- The apps' status fragments are not named after their examples:
  `docs/status/apps/key-value-store.md` (`kv-cache`), `leader-election.md` (`election`),
  `todo-list.md` (`todo-db`), `raft-key-value-store.md` (`raft-kv`). Rename each to its
  directory's name: 4 renames.
- Proofs are `XSound.lean` beside `X.lean` in most areas, but `Sound.lean` inside a feature's
  directory in `Lanes/Behaviours/Jobs/`, `Lanes/Behaviours/Schedule/` and `Lanes/Outside/Store/`.
  Not worth moving; `AGENTS.md` can name `XSound.lean` as the form for new files.

### `docs/` sprawl

| File | State | Proposal |
| --- | --- | --- |
| `docs/PLAN.md` | 50 lines, last changed by #57 this morning. Item 7's "next" (the store, the queue, a recorded run of a real service) was done since, by #65, #66 and #76 | Fold what is current into a short "Now" section of `docs/ROADMAP.md` and delete it. With many agents at once, the open pull requests are the work in progress |
| `docs/ROADMAP.md` | 87 lines | Keeps the direction, gains "Now" |
| `docs/STATUS.md`, `docs/CLAIMS.md`, `docs/INVENTORY.md`, `docs/ARCHITECTURE.md` | Four views of what exists | Keep all four. A hand-written `docs/README.md` of about 20 lines says which to read for what, and which docs are for users (the tutorials, `docs/DEPLOY.md`, `docs/STDLIB.md`, the API reference) and which for maintainers (`docs/RELEASING.md`, `docs/RUNNERS.md`) |
| `docs/history/` | 2 files, 767 lines | Keep |
| `docs/RUNNERS.md` | About the machine whose stack is in `infra/` | Optional: `infra/README.md` |
| `docs/status/` | Not checked by `links`, and `docs/STATUS.md` is exempt: `docs/status/areas/data.md` cites `oracle/`, which does not exist | Check the fragments, and fix the path |

References to `docs/PLAN.md`: `AGENTS.md`, `docs/ROADMAP.md`, `docs/status/page.md`.

## 7. The plan: what first, and how to stage it

Each step is one pull request, small and of one kind. A move pull request moves files and
rewrites references only, and is opened when no open pull request edits the files it moves.
Step 1 comes first because every later step, moves included, is cheaper once two pull requests
no longer conflict over a total.

| Step | Pull request | Size | Waits for |
| ---: | --- | --- | --- |
| 1 | `TRUSTED.md`'s row for the server, and `trusted-listed` requires a counted entry | about 20 lines | nothing |
| 2 | Generated docs (section 1): no summary or totals, evidence without counts, `STATUS.md` in sections, fragments one item per line, the index by slug, the decisions preamble | about 150 lines and the regenerated files | nothing; land it when the queue is short, since every open branch merges main once more |
| 3 | `Tests/Main.lean` sorted; changelog fragments under `docs/changes/` | about 150 lines | step 2 |
| 4 | Rule 1.8 in `AGENTS.md`; `S3.Endpoint.aws` and `S3.credentialsFromEnv` to `integrations/aws` | about 40 lines, 9 files | #77 (it edits `examples/videos`) |
| 5 | Move `Lanes/Net/` (4 files) | moves | step 2 |
| 6 | Percent-encoding from `Lanes/Web/Http/Basic.lean` to `Lanes/Net/Percent.lean`, names kept | 1 new file, 3 edited | step 5 |
| 7 | Move `Lanes/Html/` (5 files) | moves | step 2 |
| 8 | Move `Lanes/Auth/` (7 files) | moves | step 2 |
| 9 | Move `Lanes/S3/` (8 files) | moves | step 4 |
| 10 | Move `Lanes/Http/` (29 files); `AGENTS.md`'s table; `Tests/Axioms/Web.lean` split | moves | steps 5 to 9; #71 and #58 closed, merged or told to move their new files |
| 11 | Fold `examples/sign-in` into videos | about 290 lines out, 30 in | #77, #78 |
| 12 | Kit: switch both `uploadOf` to the form reader; the ledger and rookery on `Testing.Browser` | about 200 lines | the form reader, #78 |
| 13 | Shared helpers: session cookie, `ServerConfig.fromEnv`, `Auth.Key.load`, `OAuth.Client.fromEnv` | new API, with proofs and a `TRUSTED.md` row | step 10 |
| 14 | Docs: `docs/PLAN.md` into `docs/ROADMAP.md`, `docs/README.md`, the apps' fragments renamed, `links` over `docs/status/` | docs | step 2 |
| 15 | Optional: `Lanes/Lib/Postgres/` to `Lanes/Postgres/`; `Lanes/Net/`'s courier to `Lanes/Peers/`; the client's data out of its IO file | moves | step 10 |

Steps 5, 7, 8 and 9 can be written in parallel: they touch disjoint files except `Lanes.lean`,
`Lanes/Proofs.lean`, `AGENTS.md` and the docs, where each changes its own sorted lines. Queue
them one after another all the same, so that each is built on the last. Until step 10, the
layout table has a row for each new area and a shrinking row for `Lanes/Web/`.

## 8. Questions for the owner

1. Generated docs: accept "each pull request touches only its own lines, and no total is
   committed" (section 1), or prefer not committing the generated files, or the bot that
   resolves dequeued branches?
2. Is a decisions index sorted by slug acceptable, in place of one sorted by number?
3. May the README lose its trusted total, and the inventory its summary, from the committed
   files?
4. Rule 1.8 as worded, and do `S3.Endpoint.aws` and `S3.credentialsFromEnv` move to
   `integrations/aws`?
5. One `Lanes/Net/` holding addresses, URLs, TLS and the courier, or the courier renamed to
   `Lanes/Peers/`?
6. Signature Version 4 under `Lanes/S3/`, or kept with HTTP?
7. No re-exporting modules at the old paths?
8. `Lanes/Lib/Postgres/` to `Lanes/Postgres/`, or left in the standard library?
9. Delete `examples/sign-in`, its theorem moving to videos?
10. `docs/PLAN.md` folded into `docs/ROADMAP.md`?
11. Changelog fragments, in place of one file every pull request edits?
