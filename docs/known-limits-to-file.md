# Known limits to file (temporary)

**Temporary.** This file exists only to be turned into GitHub issues labelled `known-limit`, one
issue per line, and then deleted (issue #110). Do not add to it, and do not cite it: a new
fixable limit is an issue. Limits that are inherent to the design are in the "Limits" of their
area in `docs/ARCHITECTURE.md`.

Each line is `[Area or application, kind] text`, the text as the status page had it.

## Known limits

- [Adapters, limit] CloudFront's signed URLs and cookies (`Aws.CloudFront`) have not run against CloudFront: they are compared with botocore's `CloudFrontSigner`, and what CloudFront takes is read from AWS's SDKs, not its documentation. The cookies have no `Domain`, so they reach CloudFront only when it serves the site's own host. Keys are RSA of 2048 bits or P-256, in a PEM that is not encrypted; a policy's addresses are IPv4.
- [Adapters, limit] No WebSockets, and no TLS server: TLS is terminated in front, by the load balancer or a reverse proxy. The HTTP client speaks HTTP/1.1, plain or over TLS, over IPv4, a connection per call, with no proxy (`CONNECT`); a name resolves to its first IPv4 address.
- [Adapters, limit] The AWS integration has not run against AWS: the metadata service, a container's endpoint and SES are fakes written from AWS's documentation as remembered. Credentials come from IMDSv2 or a container's endpoint only (no profiles, SSO or STS), over IPv4, and are kept in memory, fetched again at each start. SES sends simple messages (no attachments, templates or raw MIME), to bare addresses, with no webhooks; it takes no idempotency key, so a send whose answer was lost may be sent twice if it is sent again.
- [Adapters, limit] The PostgreSQL client resolves a name to its first IPv4 address at each connect, and takes IPv6 addresses but no IPv6 address of a name; it has no Unix sockets, no `PGSERVICE` or `~/.postgresql/root.crt`, and does not check a password file's permissions. It has no client certificates, no CRL or OCSP check, and its direct TLS is tested against `openssl s_server` only. It has no `COPY`, `LISTEN`/`NOTIFY`, binary formats, named statements or cancellation; the pool does not watch idle connections, and `Store.handler` does not use it. A message is decoded through a list of bytes, so `message_max` (1 MiB by default) also bounds the memory a reply takes. Its live tests run only when `LANES_POSTGRES` or `LANES_POSTGRES_TLS` names a server; CI runs none.
- [Adapters, limit] The S3 client sends and receives whole bodies, in memory, within the HTTP client's `maxResponseBytes`, a multipart upload's whole body too (`S3.upload` sends it a part at a time, one part after another); videos go between the browser and S3 through a `POST` form and presigned links. Credentials come from the environment, are given, or are read at each call from a source (`SigV4.Source`), such as the AWS integration's. It has not been run against AWS, MinIO or LocalStack, nor over TLS in a test; the XML reader, scoped to S3's answers, is not yet tested against Go's. No conditional write. That S3 refuses a presigned part whose `Content-Length` is not the one signed is believed, not checked against AWS; moto reads no `POST` policy, so what S3 refuses under one is checked against AWS's example and botocore only.
- [Adapters, limit] The cache, wall-clock, shared-cache and throttling models have no adapter and no recorded run of a real system. The queue's calls (`Aws.Sqs`) have no handler and have run against moto only, which deletes a message with any receipt it was given. The queue takes a delete as done when it is handed over and has no five-minute window for FIFO deduplication; the cache's leases are memcached's, which Redis gives only through a script; the wall clock's skew is not measured; the throttling model has one caller.
- [Adapters, limit] The client's TLS context, with its trust store, is made for each call (about 3 ms with Ubuntu's). Revocation is not checked. OpenSSL fixes reach Lanes with Lean's toolchain. The trust store is `SSL_CERT_FILE` when it is set. The C declares the functions of the OpenSSL the toolchain links, 4.1.0, and `scripts/tls-declarations.py` checks them against the system's headers, 3.0 on Ubuntu 24.04: 4.1's headers are generated from templates by its own build.
- [Adapters, limit] The models of external services are not tested against a real service: the adapters for them, the S3 client and the AWS integration's SES, run against fakes, and the other recorded runs are written by hand from the documentation. Idempotency keys do not expire in the model; a real payment service forgets them after 24 hours. Requests other than one that makes a thing (retrieve, list, cancel, refund) are not modelled.
- [Behaviours, limit] Beside a system, that the answer reaches the requester, and at most once, is not yet carried through the join: it is proved of the jobs actor alone.
- [Data, limit] Base64 recurses once per four characters, so a very long input (megabytes) uses stack in proportion.
- [Data, limit] What `Lanes.Base64`, `Lanes.Ip` and `Lanes.TimeFormat` refuse is stated by theorems only for Base64 (`decode` accepts exactly the canonical text); for addresses and dates, that they refuse what Go refuses is tested, not proved, on the oracle's generated cases.
- [Data, limit] What `Lanes.Url` and `Lanes.MediaType` refuse is tested against Go, not proved. A URL's IP literal is kept as an address and printed as RFC 5952 writes it, so `print (parse s)` is `s` only up to that; IPvFuture literals are refused. Rate limits have no table of buckets per key yet.
- [Model checker, limit] A refinement check (`Check.refines`) takes 15 to 30 times as long as a plain check of the same system: the monitor keeps a candidate for each order in which the inputs in flight may have taken effect (92 for the five requests of the tutorial's shelf), and closing them is quadratic in their number. `lake exe lanesCheck` prints the shelf's times (`Tests/MonitorSpeed.lean`).
- [Model checker, limit] Exact checks of the videos example spend half their time confirming duplicates: four transitions in five reach a stored state, and Lean's derived equality walks both values. A compact encoding compared as bytes, or a smaller stored node, is the next factor; neither is done (`docs/decisions/D92-checker-scale.md`). Symmetry over interchangeable actor ids has the theorem it needs at the level of models, but not the one that `SysState.step` commutes with renaming actors; there is no partial-order reduction.
- [Model checker, limit] The checker runs about 50,000 states per second on one core (the election model: 164,847 states in 3.0 to 3.7 s, against 10.8 to 11.2 s before the work of D33), and its tasks do not help: Lean counts references to shared objects atomically and never updates them in place, so four workers cost two to three times the processor time for no gain in wall time. At this rate ten million states take over three minutes and, stored exactly, about 7 GB (0.75 kB a state on the election model). The next factor needs states that are flat data (D33).
- [Runtime, limit] A journal's name has to cover everything its replay reads: the version of the step functions and every setting they use, timeouts among them, since a timer is due at the clock's reading plus the configured delay. Nothing checks that a name does. `raft-kv` puts its whole `Config` in the name, so a timeout of a node that has run cannot be changed.
- [Runtime, limit] A migration needs the old version's system, its step functions and codecs, in the new binary for as long as files of that version may exist. `Http.serve` takes no upgrades yet: its system is the application's behind the gate, and a migration would have to be lifted through the gate. What carries over a migration is what each new actor keeps by its own steps; an invariant proved only from boot, or refinement, does not, and a shard migrated twice is covered by `Journal.Upgrade.inv_load` only for the first migration.
- [Runtime, limit] A save writes the whole kernel, and the shard does nothing else meanwhile. `raft-kv` never compacts its log, so a node's snapshot grows with every command it has ever taken.
- [Runtime, limit] A step that emits very many outputs is quadratic in their number (`Kernel.performAll` appends one at a time): 20,000 outputs from one step take most of a second.
- [Runtime, limit] Cutting off a write that did not finish, and cutting a journal at a save, replace the journal file by a new one, which gets default permissions; `.tmp` files left by a process killed in between are not cleaned up.
- [Runtime, limit] The kernel's message queue has no bound of its own (see `TRUSTED.md`).
- [Runtime, limit] The runtime releases only an actor whose state is one a start gives it (`Actor.fresh`, which an actor declares; the default declares none). An actor that is idle in any other state keeps its cell for good, so a session-per-user system still grows with its users. Releasing it means its state must live somewhere else, so this waits for the persistence adapter.
- [Test kit, limit] The browser runs no script and follows no redirect, and ignores a cookie's domain, expiry and `Secure`.
- [Tooling, limit] The warm runner machine, its CloudFormation stack and the start and stop jobs have been checked with linters and stubs only, not yet run against AWS.
- [Tooling, limit] `lanes lint` is text-level, but for the inventory. `no-io-in-step`, `bounded`, `field-leak` and `fn-length` need the elaborator and are not implemented.
- [Web, limit] A response streams to an HTTP/1.0 client in chunks, which it does not read. A body that streams is no longer handed on once the client ends its side. That the pieces of a whole run make up the body, and the bytes of a whole stream the parts given, is model-checked, not proved. A request that streams, its pieces and its pulls pass by `ServerConfig.ops` and `arrive`.
- [Web, limit] Behind `Http.serveShard` a response must be put out by an actor of the process that took the request. Request ids are each process's own, so a response put out on another shard reaches that shard's gate, which may be waiting on the same id for another client. Nothing prevents this; `Tests/Fronted.lean` shows the mild case, a `504` at the front that took the request.
- [Web, limit] Sign-in: the key of the tickets and the states used live in memory, so a restart refuses the callbacks of sign-ins begun before it; a full set of states used (`maxUsed`) refuses sign-ins begun before the states it dropped; no refresh tokens, no UserInfo endpoint, no `.well-known` fetched at run time, no RFC 9207 `iss` on the callback; ID tokens of RS256 and ES256 only; `iat`, `auth_time`, `acr` and `at_hash` are not checked. With `arrive`, requests of one connection may enter the system out of order.
- [Web, limit] The connection's own refusals (`400`, `408`, `413`, `431`, `501`) are neither counted in the metrics nor logged. The metrics page and the health checks are on the application's port; the page is answered only to a loopback peer by default, and the health checks to every peer.
- [Web, limit] The gate keeps waiting requests in a list, so each request costs time linear in `maxPending`.
- [Web, limit] The head of a request, and a chunked body, is read again from its start each time bytes of it arrive, so one sent a byte at a time costs time quadratic in its length, within its limit and its deadline.
- [Web, limit] The server writes no `Date` header, and answers an unknown method `501`.
- [Ledger, not proved yet] Liveness.
- [Ledger, not proved yet] The gate in front as a refinement.
- [Payments, limit] No adapter: the shop runs only in the checker and the proof.
- [Raft key-value store, not proved yet] Liveness.
- [Reminders, limit] No form token: anyone who can reach the server can schedule and cancel.
- [rookery, not proved yet] An API post's `posted` as a statement about runs (a repeated `seq` is answered from the memo).
- [rookery, not proved yet] Liveness.
- [rookery, not proved yet] The bridge (tested).
- [rookery, not proved yet] The gate in front as a refinement.
- [Sign-in, limit] Sessions are signed with a key made at start, so they end with the process, and the members are not journalled; neither the example nor its presets has been run against Google or GitHub.
- [To-do list, limit] The actor's state is volatile: a crash forgets the to-dos waiting.
- [Videos, not proved yet] That a deleted video's object is deleted or reported, and that the worker reports, so that a confirmed upload ends ready or failed (checked, with no crash).
- [Videos, not proved yet] The bridge (tested).
- [Videos, not proved yet] The proved properties of the spec's functions as statements about the system's traces.
- [Videos, limit] Not run against AWS or a real provider; `videosLive` runs the flow against a bucket the environment names. Links handed out before a delete last until they expire. Every page view is journalled. No search or mail (its README). No worker that speaks the transcode format but the test kit's, and a round under way has no deadline. A journal of before the pipeline (`videos 2`) is refused, not upgraded.

## Roadmap items

The open items of the roadmap. The direction is issue #93 and `docs/ROADMAP.md`.

- [Proofs, roadmap] A relation library from what the key-value store's proof repeated, a cheaper invariant rule and a counterexample-to-induction finder, so that proving an application is cheap enough to be routine; the ledger's refinement is the measure.
- [Proofs, roadmap] Evidence for every definition of `Lanes/`: take entries off `docs/inventory-none.md` by proving, testing or listing them in `TRUSTED.md`.
- [Proofs, roadmap] Take the premise that a client's link does not duplicate a request off the gate and off Raft, as D48 took it off the key-value store.
- [Runtime, roadmap] Save idle actors that are not at their start when they rest, and read them back when mail comes; this waits for a place to keep their state.
- [Behaviours, roadmap] Slow work that is not one request's, as the ledger's friction log asks (`examples/ledger/README.md`): carry a job's answer to its requester through the join, at most once there, as the gate's is; end sessions in bulk; statements in the ledger.
- [Specs, roadmap] Each system's spec and its premises in one place, which a person reads before any public claim.
- [Models of external services, roadmap] Runs recorded from the real services, not only from references (moto, the fakes).
- [Deploy, roadmap] Run the deploy path of `docs/DEPLOY.md` on AWS once and record the run.
- [Deploy, roadmap] Sign forms and links with the instance role's credentials, which the bridge, being pure, cannot fetch, so that the tutorial and `examples/videos` need no long-lived key.
- [Checker, roadmap] Checker v2: states as flat data, symmetry, a parallel search that pays, a lasso search for liveness.
- [Several shards, roadmap] A proof that the running processes implement `System.shards`.
- [Raft key-value store, roadmap] Run on three machines; membership change; log compaction; liveness.
- [Batteries, roadmap] A TLS server; observability beyond the server's own pages; the ledger on a database.
- [Developer experience, roadmap] `lanes prove`; a counterexample-to-induction finder; a trace viewer.
- [Launch, roadmap] The launch work: the flagship application deployed, and the write-up.

## Stdlib items

What the triage of Go's standard library (the deleted STDLIB.md) left to build or bind,
with its priority for web applications: P0 is needed by the flagship application, P1 is common,
P2 rare. Pure code is built in Lean, proved, and compared with Go on generated inputs; what
touches the operating system or cryptography is bound to OpenSSL (D46).

- [Stdlib, P0] Rate limits: a table of buckets per key (an address, a user) in a `Std.TreeMap`, with full buckets dropped so the table stays bounded; the bucket is `Lanes/Lib/RateLimit.lean`.
- [Stdlib, P1] `encoding/base32` (TOTP secrets): RFC 4648 §6, laws as base64; oracle Go `base32.StdEncoding`.
- [Stdlib, P1] `encoding/csv` (exports and imports): RFC 4180, `parse (print rows) = some rows`; oracle Go `encoding/csv` with its lenient options off.
- [Stdlib, P1] `mime/multipart` (uploads, attachments): RFC 7578, RFC 2046 §5.1, a boundary never occurs in a part; oracle Go `multipart.Reader`, `multipart.Writer`.
- [Stdlib, P1] `mime`: the table of file extensions.
- [Stdlib, P1] `net/mail` (addresses at sign-up): RFC 5322 §3.4 and RFC 6532; oracle Go `mail.ParseAddress`. SES's check of a bare addr-spec is done (`integrations/aws/Aws/Ses.lean`).
- [Stdlib, P1] `net/http` `DetectContentType` (an upload is the type it claims): the WHATWG MIME Sniffing Standard; oracle Go.
- [Stdlib, P1] `path` (a request's path, static files): RFC 3986 §5.2.4, `clean (clean p) = clean p`; oracle Go `path.Clean`, `path.Match`.
- [Stdlib, P1] `log/slog` (structured logs): one JSON object per line as slog's `JSONHandler` writes; there is no general logger, only the server's access log.
- [Stdlib, P1] `unicode` (names and text by category): tables generated from the Unicode Character Database, with a theorem per table.
- [Stdlib, P1] `unicode/utf16` (count text as a browser's `maxlength` does): `decode (encode s) = s`; oracle Go.
- [Stdlib, P1] `x/text/unicode/norm` (NFC): UAX #15; oracle `NormalizationTest.txt`.
- [Stdlib, P1] `x/text/cases` (case folding): Unicode §3.13; oracle `CaseFolding.txt`, Go x/text.
- [Stdlib, P1] `x/text/secure/precis` (user names and passwords prepared): RFC 8264, RFC 8265; needs norm and cases.
- [Stdlib, P1] `x/net/idna` (host names in links): UTS #46, RFC 5891, Punycode; oracle `IdnaTestV2.txt`.
- [Stdlib, P1] `x/oauth2`: refresh tokens and calling APIs on a user's behalf (sign-in is built); compare the requests with Go x/oauth2 against a scripted provider.
- [Stdlib, P1] `regexp`: RE2 syntax, a matcher proved to agree with the language of an expression and to run in linear time; oracle Go `regexp` and RE2's suites.
- [Stdlib, P1] Markdown for posts: a port of `Lean.Data.Markdown`, which an application binary cannot link.
- [Stdlib, P1] Bind OpenSSL's AES-256-GCM or ChaCha20-Poly1305 (encrypted cookies, data at rest), Ed25519 (webhook signatures), SHA-1 (TOTP, the WebSocket handshake), HKDF, and X25519.
- [Stdlib, P2] `compress/flate`, `gzip`, `zlib` with CRC-32: `inflate (deflate x) = some x`; oracle Go both ways.
- [Stdlib, P2] `encoding/binary` (varints), `encoding/pem` (RFC 7468), `mime/quotedprintable` (RFC 2045 §6.7): round trips against Go.
- [Stdlib, P2] `encoding/asn1`: reading DER (only the two shapes the signature check writes exist, `Lanes/Lib/Crypto/PublicKey.lean`).
- [Stdlib, P2] `encoding/xml` beyond S3's answers: XML 1.0, against the W3C conformance suite; writing Atom and RSS feeds.
- [Stdlib, P2] `net/smtp`: an RFC 5321 client as an actor, compared with Go's against a scripted server.
- [Stdlib, P2] `html` unescaping (WHATWG named character references) and `x/net/html` (sanitizing HTML from elsewhere, against html5lib-tests).
- [Stdlib, P2] `strconv` floats: shortest round trip against Lean's `Float.Model`; oracle Go `strconv.FormatFloat`, `ParseFloat`.
- [Stdlib, P2] `x/net/publicsuffix` (cookie domains): the Public Suffix List's algorithm.
- [Stdlib, P2] `x/net/websocket`: RFC 6455 framing as a pure reader and writer, against the Autobahn TestSuite.
- [Stdlib, P2] `crypto/ecdh`: X25519 and P-256 from OpenSSL's libcrypto.
- [Stdlib, oracle] Compare the cookie parser with Go's `http.ParseCookie` and `http.ParseSetCookie`.
- [Stdlib, oracle] Compare the TLS client's refusals with a Go program that serves certificates it makes with `crypto/x509` (expired, wrong host, self-signed, unknown root, good), beside `openssl s_server`.
