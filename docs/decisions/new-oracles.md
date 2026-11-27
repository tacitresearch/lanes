# D?. Every parser has an oracle and every model a recorded run, in one place, and lint keeps the list

D50 compared the standard library's parsers with Go's, and the other comparisons grew one at a
time: Signature Version 4 against botocore on five examples, JWS by hand, PostgreSQL's messages
against psql's recorded sessions, TLS against `openssl s_server`, and the models of outside
services against runs written by hand. Three were owed: the S3 XML reader against Go's
`encoding/xml` (D71), the metrics page against Prometheus's `expfmt` (D69), SES's address check
against `net/mail` (D74). This makes the comparisons one strategy, with one place, two kinds, a
policy and a check that the policy is kept.

## One place: `oracles/`

`oracles/` holds one folder per reference implementation: `oracles/go` (a Go module: the
standard library, `golang.org/x/time`, Prometheus's `expfmt`; Go and each module pinned in
`go.mod` and `go.sum`), `oracles/botocore`, `oracles/jwcrypto`, `oracles/moto` (each a
`requirements.txt` with every package pinned) and `oracles/postgres`. A folder holds what is not
Lean: the reference's program, its pin, and what was recorded from it (`answers.jsonl` for a pure
oracle, `<model>.jsonl` for a service). `oracles/README.md` is the manifest: each folder's
reference, version, pin and what it is the reference for, and each protocol module and model
against its oracle, or the reason it has none. `oracle/` moved to `oracles/go/` with `git mv`,
and `Tests/Oracle/vectors/<package>.jsonl` to `oracles/go/<package>/answers.jsonl`.

The Lean halves stay in `Tests/Oracle/` (`<Package>.lean` for a pure oracle, `Service/` for a
service), not in `oracles/`. A Lean module must sit under its library's root, `lake test`
replays the records from the `Tests` library, and the application packages
(`integrations/aws`) import the driver from it. The other way, `Tests/Oracle` grown up with Go
modules and virtual environments inside it, would put toolchains that are not Lean's in the test
tree that Lake globs, and make the references' pins harder to find. So the references are in
one place and the Lean in another, and the manifest ties them: rule 1.1 applied to directories,
a reference beside its pin, the code that uses it beside the code it tests.

## Two kinds

**Pure oracles** are D50's pattern, made language-neutral. A `Package` (`Tests/Oracle/Basic.lean`)
names its `Reference`, `.go dir` or `.python dir`; the driver (`Tests/Oracle/Run.lean`) builds
the Go program, or makes a virtual environment from the folder's `requirements.txt` when it is
not the one the environment was made from, in `LANES_ORACLE_CACHE` or `.lake/oracles`, writes the
cases and compares the answers. The protocol is D50's: a case per line, inputs in hex, only
acceptance and the structured result compared. A package whose case is a document of parts that
must agree (a page and the families it was rendered from, a request as JSON) does not shrink a
difference by deleting bytes (`shrinks := false`), and one whose cases are large records fewer
answers (`recorded`). `lake exe lanesOracle` runs Lanes's; `lake exe oracle` in
`integrations/aws` runs the integration's with the same driver.

**Service oracles** run our client, through its handler, against a real or reference
implementation of a service, record the run, and check it against our model of the service with
`Outside.allows` (`Store.State.run` for the store). The record is the events the model sees,
a call and its answer per line, kept in `oracles/<reference>/<model>.jsonl`; `lake test` reads it
back and checks it against the model again, so a model made stricter than the service it
describes fails without the service. An oracle runs only when the variable that names its
service (`LANES_MOTO`, `LANES_POSTGRES`) is set, and says it is skipped otherwise;
`oracles/moto/run.sh` and `oracles/postgres/run.sh` start the service on a free port, run the
oracles, and stop it by its process id or with `pg_ctl`.

## The policy

- Every parser or encoder in `Lanes/Lib/`, and the protocol code of `Lanes/Web/` (the wire
  format, Signature Version 4, XML, JOSE), has a pure oracle, or `oracles/README.md` says why
  not: it is not a format (a hash checked against its standard's vectors, a state machine), it
  is ours alone (a signed token only Lanes reads), or the oracle is owed and named.
- Every model of an outside service in `Lanes/Outside/` has at least one run recorded from a
  real or reference implementation, or the manifest says why not.

This is rule 5.9 of `AGENTS.md`. Lint `oracles` keeps the manifest true: every folder of
`oracles/` has a row of references; every module of `Lanes/Lib/` and `Lanes/Web/` and every
model of `Lanes/Outside/` that is not a proof (`…Sound.lean`) or IO has a row; a row names an
oracle or gives a reason; and every module and path a row names exists. A new module fails lint
until it has a row, and a module that goes away fails until its row does. The scope is by
directory, not by guessing which modules parse: a reason is one line, and a module that is not a
format says so once.

## CI

The pure oracles run on every pull request, in `ci.yml`'s job `oracle`: 20,000 cases a package at
seed 0 and at the run's id, about a minute for all of them at each seed, and the integration's. The service oracles start
services and wait on them, so they run in a workflow of their own, `services.yml`, nightly and by
hand: it installs PostgreSQL 16 and Python's `venv`, runs both scripts with `--record`, and keeps
the records as its artifact, to be copied over the committed ones when the owner wants them.

## Results

On 100,000 cases at seed 0 (and, for XML, seeds 7, 11 and 12):

- **XML** (`oracles/go/xml`, `Tests/Oracle/Xml.lean`): 86,704 agree, 13,296 known, none other;
  51,836 documents accepted by Go. Go's Decoder reads tokens and leaves the document to its
  caller, so the program also asks for one root with only blanks, comments, processing
  instructions and directives around it, as XML 1.0's `document` production does.
- **Metrics** (`oracles/go/expfmt`, `Tests/Oracle/Metrics.lean`): `expfmt`'s parser reads the
  page ours renders, and what it reads is compared with what the families say a reader should
  see: 87,442 agree, 12,558 known, none other.
- **Signature Version 4** (`oracles/botocore`, `Tests/Oracle/SigV4.lean`): botocore 1.44.12
  signs the same request, its URL written as botocore's serializers write one, with
  `S3SigV4Auth` for S3 (signed or `UNSIGNED-PAYLOAD`) and `SigV4Auth` for SES and STS: 84,966
  agree, 15,034 known, none other.
- **JWS** (`oracles/jwcrypto`, `Tests/Oracle/Jose.lean`): tokens signed in the test, by RSASSA-
  PKCS1-v1_5 on `Rsa.powMod` and ECDSA on P-256 in Jacobian coordinates written for it, under
  keys made with Python's `cryptography`, two fifths of them tampered with: 93,730 agree, 6,270
  known, none other; 28,480 accepted by jwcrypto. That the test's signer is right is checked by
  `Rsa.verifyReference` and by the keys' public points.
- **Mail addresses** (`oracles/go/mail`, `integrations/aws/Checks/Mail.lean`): 62,181 agree,
  37,819 known, none other. Every address ours takes Go reads as itself with no display name.
- **S3 on moto 5.2.6** (`oracles/moto/s3.jsonl`): gets, puts, deletes, two puts in flight at
  once and a put with a deadline of 1 ms, which came back `unknown` and whose object the next get
  read: the model's uncertain write, seen. Allowed.
- **SES on moto** (`oracles/moto/ses.jsonl`): a send from a sender not verified, rejected with
  `MessageRejected`; the sender verified with `CreateEmailIdentity`; sends to one and to three
  recipients; one timed out. Allowed.
- **PostgreSQL 16.15** (`oracles/postgres/store.jsonl`): write skew and a lost `COMMIT` at both
  levels, and 50 runs of up to three transactions interleaved at random. Allowed, once the bug
  below was fixed.

## What the oracles found

- **The store model refused what PostgreSQL does at serializable.** A scan was recorded as the
  rows without the keys its transaction had written, and compared with all of the store's rows,
  so after a transaction scanned what it had written, no state held its reads, and every later
  read was refused: 3 of the first 12 random runs at serializable. `Read.all` now carries the keys the
  transaction had written, which the comparison leaves out (`Lanes/Outside/Store/Basic.lean`,
  tested in `Tests/Store.lean`). The model was stricter than the service, so a system checked
  against it was checked in fewer runs than PostgreSQL makes; the theorems of
  `Lanes/Outside/Store/Sound.lean` do not read scans and are unchanged.
- **The XML reader misread XML 1.0** in small ways, now fixed (`Lanes/Web/S3/Xml.lean`): it kept a
  carriage return that §2.11 reads as a line feed; it took characters and references outside
  §2.2's `Char` (`&#1;`, `&#xFFFE;`, a raw `\x01`); names starting with a digit, `-` or `.`;
  `]]>` in text; `--` in a comment and a comment ending in `-`; and a processing instruction
  with no target. It refused a character reference with leading zeros, which XML allows.
- **The metrics renderer writes what it is given.** Two families whose names are one once made
  valid, labels whose names are one once made valid, `__name__`, `le` on a histogram's series, and
  two series of a histogram with one set of labels make a page `expfmt` refuses or reads as one
  series. These are known differences, not fixed: ours never makes such families itself, and
  refusing them is a change to `Metrics.render`'s type (below).
- Nothing else: every other difference is a decision below.

## Where ours departs, and why

Each is a `known` predicate in the package's file; those that say "the reference reads X" check
that ours, given the input with X written our way, answers as the reference did.

- *XML.* Go reads a document type and CDATA; ours refuses both, so nothing is expanded and a text
  is read one way (with CDATA written as text and declarations removed, ours answers as Go).
  Ours skips attributes without reading them, which S3 writes only as namespaces; Go refuses a
  malformed one. Ours refuses nesting deeper than 16. Go reads names in any script and checks
  the declaration's version and encoding; ours reads ASCII names and skips the declaration. Go
  reads a name as a QName, with one colon at most; ours as XML 1.0's names, whole. Go reads a
  reference to a surrogate as U+FFFD, which XML forbids; ours refuses it.
- *Metrics.* Go reads values as float64, so a number of more than 15 significant digits reads
  back as another; ours writes it exactly. The four cases of what the renderer writes as given.
- *Signature Version 4.* Services other than S3 escape the path twice and remove dot segments
  and empty ones; ours signs a path as S3 does, which is the same for a path that needs neither,
  as SES's does not. botocore does not sign `User-Agent`, `Expect` or `X-Amzn-Trace-Id`; ours
  signs every header it writes, and either signature is valid. Ours does not write, so does not
  sign, a header its writer refuses. botocore squeezes any Unicode whitespace in a value (Python's
  `str.split`); ours squeezes spaces and tabs, HTTP's blanks.
- *JWS.* Ours refuses an RSA key under 2048 bits (RFC 7518 §3.3), uses a key only for the
  algorithm its set names for it (RFC 7517 §4.4, RFC 8725 §3.1), and understands no `crit`
  extension, where jwcrypto reads RFC 7797's `b64`. Ours does not check a signature under a key
  its set marks for encryption.
- *Mail.* Ours takes a bare addr-spec of ASCII with a domain of two LDH labels or more, within
  RFC 5321's lengths; Go also reads display names, angle brackets, comments, quotes, UTF-8, a
  domain of one label or a literal (D74).

## Not done

- **Payments, idempotency keys and webhooks** have no recorded run: Stripe's test mode needs a
  key and stripe-mock keeps no state. The manifest says so; their runs are written by hand.
- **moto does not check signatures**, so the signing of a call that moto answers is botocore's
  test, not moto's. A run against AWS, or against MinIO, which checks them, is not made.
- Owed, and named in the manifest: Go's `http.ParseCookie` for the cookie parser, an HTML parser
  (html5lib, or a browser) for the renderer, the W3C XML conformance suite.
- The service records change with each run (moto's ids and dates), so the nightly workflow keeps
  them as an artifact instead of committing them.

## For the owner

- Whether `Metrics.render` should refuse, or merge, families and series that collide, which
  would make every page it writes one `expfmt` reads as given; today the page's maker decides.
- Whether the nightly service run should open a pull request when a record changes in kind (a
  new answer, a refusal), rather than leaving the artifact to be copied by hand.
- Whether the PostgreSQL oracle should run transactions on threads of their own, so that a
  request may wait on another's lock as the handler's do; today two transactions open at once
  never write one key.
