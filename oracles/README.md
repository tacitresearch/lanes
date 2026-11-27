# Oracles

What Lanes is compared with, and what it is not compared with and why
(`docs/decisions/D80-oracles.md`). There are two kinds, kept apart:

- **Pure oracles** give one input to ours and to a reference implementation and compare the
  outputs, on generated inputs: `lake exe lanesOracle [--cases N] [--seed S] [package…]`, and
  `lake exe oracle` in `integrations/aws`. Each package is `Tests/Oracle/<Package>.lean` (or
  `integrations/aws/Checks/Mail.lean` and `integrations/aws/Checks/CloudFront.lean`), the
  reference's program is in its folder here, and its answers to the first cases are kept in the
  folder's `answers.jsonl` (or another file, when two packages share a reference), which `lake test` replays
  and `--record` rewrites. Every difference is a `known` predicate with its reason, or a failure.
- **Service oracles** run our client against a real or reference implementation of a service and
  check the run against our model of it with `Outside.allows`: `oracles/moto/run.sh` and
  `oracles/postgres/run.sh` start the service, run `lake exe lanesServiceOracle` (and
  `lake exe serviceOracle` in `integrations/aws`) and stop it; `--record` rewrites the record in
  the folder, which `lake test` checks against the model again. Each is skipped, with a message,
  when its service is not there.

Programs are built, and Python environments made, in `LANES_ORACLE_CACHE`, or `.lake/oracles`.
CI runs the pure oracles on every pull request (`.github/workflows/ci.yml`, job `oracle`) and the
service oracles nightly and by hand (`.github/workflows/services.yml`).

`lanes lint` checks this file (rule `oracles`): every folder here has a row in the first table;
every module of `Lanes/Lib/` and `Lanes/Web/`, but proofs and IO, has a row in the second, and
every model of `Lanes/Outside/` one in the third, naming an oracle or saying why there is none;
every module a row names exists, and so does every path it cites.

## References

| Folder | Reference | Version | Pinned in | The reference for |
| --- | --- | --- | --- | --- |
| `oracles/go` | Go's standard library, `golang.org/x/time` and Prometheus's `expfmt` | Go 1.24.7, x/time 0.11.0, prometheus/common 0.67.5 | `oracles/go/go.mod`, `oracles/go/go.sum` | Base64, IP addresses, times, JSON, media types, rate limits, URLs, XML, mail addresses, the metrics page; and, with Node and h11 (`oracles/go/requests/requests.py`, by hand), the request reader |
| `oracles/botocore` | botocore, and `cryptography` for the signatures it is given | 1.44.12, cryptography 50.0.2 | `oracles/botocore/requirements.txt` | Signature Version 4; CloudFront's signed URLs (`oracles/botocore/cloudfront.jsonl`), signed with the published test keys of `oracles/botocore/keys/` |
| `oracles/jwcrypto` | jwcrypto | 1.6.2 | `oracles/jwcrypto/requirements.txt` | JWS in compact form and JWK Sets |
| `oracles/moto` | moto's server, S3, SES API v2 and SQS | 5.2.6 | `oracles/moto/requirements.txt` | the recorded runs of the object store, multipart, email and queue models, and of `POST` forms |
| `oracles/postgres` | PostgreSQL | 16 (16.15 recorded) | the CI job's `postgresql-16` | the store model's recorded runs |

## Protocol modules

| Module | Oracle | Or why not |
| --- | --- | --- |
| `Lanes/Lib/Crypto/Certificate.lean` | `Tests/PostgresTls.lean` | The hash for channel binding of certificates `openssl` made, against `openssl dgst`, and accepted by PostgreSQL 16 |
| `Lanes/Lib/Crypto/Hmac.lean` | | Not a format: RFC 4231's vectors, and libsodium on thousands of inputs (`Tests/Crypto.lean`) |
| `Lanes/Lib/Crypto/Md5.lean` | | Not a format: RFC 1321's examples, and the digests psql sent in the recorded sessions (`Tests/Postgres.lean`) |
| `Lanes/Lib/Crypto/Pbkdf2.lean` | | Not a format: through SCRAM, against RFC 7677 and libpq's recorded session (`Tests/Postgres.lean`) |
| `Lanes/Lib/Crypto/PublicKey.lean` | `Tests/Signature.lean`, `Tests/Sign.lean` | The DER of keys and signatures against what the `openssl` command writes, and read back from OpenSSL's; a public key's PEM against `openssl pkey -pubout` |
| `Lanes/Lib/Crypto/Sign.lean` | `Tests/Sign.lean`, `oracles/botocore` | A binding: RFC 6979's signatures, `openssl dgst -sign`, and `cryptography`'s signatures in the CloudFront oracle |
| `Lanes/Lib/Crypto/Sha256.lean` | | Not a format: FIPS 180-4's examples, and libsodium on thousands of inputs (`Tests/Crypto.lean`) |
| `Lanes/Lib/Crypto/Sha512.lean` | | Not a format: FIPS 180-4's examples, as `openssl dgst` computes them (`Tests/Crypto.lean`) |
| `Lanes/Lib/Crypto/Sodium.lean` | | A binding: libsodium against the Lean references (`Tests/Crypto.lean`) |
| `Lanes/Lib/Crypto/Verify.lean` | `Tests/Signature.lean` | A binding: OpenSSL's check against `Rsa.verifyReference` and keys `openssl` made |
| `Lanes/Lib/Encoding/Base64.lean` | `oracles/go/base64` | |
| `Lanes/Lib/Encoding/Digits.lean` | | Numbers in a base, read back as written (`Lanes/Lib/Encoding/Digits.lean`'s theorems); compared through every format that uses them |
| `Lanes/Lib/Encoding/Json.lean` | | Imports the modules below |
| `Lanes/Lib/Encoding/Json/Basic.lean` | | Values, not a format |
| `Lanes/Lib/Encoding/Json/Classes.lean` | | Typed values to and from `Json`, not text |
| `Lanes/Lib/Encoding/Json/Grammar.lean` | | RFC 8259's grammar, the spec the parser and printers are proved against; JSONTestSuite (`Tests/Json.lean`) |
| `Lanes/Lib/Encoding/Json/Parser.lean` | `oracles/go/json` | |
| `Lanes/Lib/Encoding/Json/Printer.lean` | `oracles/go/json` | Go parses what the printer writes in the parser's cases; proved to read back (`Json.parse_compress`) |
| `Lanes/Lib/Metrics.lean` | `oracles/go/expfmt` | |
| `Lanes/Lib/Mime/MediaType.lean` | `oracles/go/mime` | |
| `Lanes/Lib/Net/Ip.lean` | `oracles/go/netip` | |
| `Lanes/Lib/Net/Url.lean` | `oracles/go/url` | |
| `Lanes/Lib/Postgres/Bytes.lean` | `Tests/Postgres.lean`, `oracles/postgres` | The fields of the messages, in the sessions recorded from PostgreSQL 16 and psql 16 (`Tests/Postgres/`) |
| `Lanes/Lib/Postgres/Conn.lean` | `Tests/Postgres.lean`, `oracles/postgres` | A state machine, not a format: the recorded sessions, and the live runs |
| `Lanes/Lib/Postgres/Message.lean` | `Tests/Postgres.lean`, `oracles/postgres` | The messages, in the recorded sessions; written and read again against a live server |
| `Lanes/Lib/Postgres/Pool.lean` | | Decisions, not a format: proved (`Pool.run_size`, `Pool.never_again`) and model-checked (`Tests/PostgresPool.lean`) |
| `Lanes/Lib/Postgres/Scram.lean` | `Tests/Postgres.lean`, `Tests/PostgresTls.lean` | RFC 7677's example and libpq's recorded session; with channel binding, Python's `hashlib` and PostgreSQL 16 with TLS |
| `Lanes/Lib/Postgres/Settings.lean` | `Tests/PostgresLive.lean` | libpq's variables and password file: `psql` connects with the same, against PostgreSQL 16 |
| `Lanes/Lib/Postgres/Table.lean` | `oracles/postgres` | The SQL of the store's operations, against PostgreSQL itself |
| `Lanes/Lib/RateLimit.lean` | `oracles/go/rate` | |
| `Lanes/Lib/Time/Civil.lean` | `oracles/go/time` | Through the formats, whose dates it computes |
| `Lanes/Lib/Time/Format.lean` | `oracles/go/time` | |
| `Lanes/Web/Auth/IdToken.lean` | | The claims of an ID token, decided and proved (`OAuth.IdToken.verify_accepted`); its JWS is `Jose`'s |
| `Lanes/Web/Auth/Jose.lean` | `oracles/jwcrypto` | |
| `Lanes/Web/Auth/Login.lean` | | Not a format: failed attempts and their bounds |
| `Lanes/Web/Auth/OAuth.lean` | | A flow, model-checked against an attacker's browser (`Tests/OAuth.lean`); the providers' documents are recorded (`integrations/google/recorded`) |
| `Lanes/Web/Auth/Token.lean` | | Tokens only Lanes writes and reads; proved to accept exactly what it signs (`Auth.verify_sign`) |
| `Lanes/Web/Html/Basic.lean` | | Proved against a model of the HTML tokenizer (`Html.lex_render`); not yet compared with html5lib or a browser |
| `Lanes/Web/Html/Htmx.lean` | | Attributes from routes, not a format of its own |
| `Lanes/Web/Html/Syntax.lean` | | The template syntax, elaborated to `Html.Basic`'s values |
| `Lanes/Web/Http/Basic.lean` | | HTTP as data, not text |
| `Lanes/Web/Http/Conn.lean` | | A connection's decisions, proved (`Lanes/Web/Http/ConnSound.lean`); its bytes are `Wire`'s and `ReadRequest`'s |
| `Lanes/Web/Http/Cookie.lean` | | Proved to read back what it writes (`Lanes/Web/Http/CookieSound.lean`); Go's `http.ParseCookie` is owed (`docs/STDLIB.md`) |
| `Lanes/Web/Http/Front.lean` | | Decisions, not a format |
| `Lanes/Web/Http/Gate.lean` | | Decisions, not a format |
| `Lanes/Web/Http/Grammar.lean` | | RFC 9110's tokens and field values, used by the reader and the writer |
| `Lanes/Web/Http/JournalName.lean` | | A journal's name, read back only as it is written, and a migration across gates; tested (`Tests/Web.lean`) |
| `Lanes/Web/Http/Loopback.lean` | | A front end with no socket for tests, not a format: its bytes are `Conn`'s and `Wire`'s |
| `Lanes/Web/Http/Ops.lean` | | Routes and access for the operators' endpoints; their page is `Metrics`' |
| `Lanes/Web/Http/ReadRequest.lean` | `oracles/go/requests` | Go's, Node's and h11's servers on `Tests/ReadRequest.corpus`, by hand |
| `Lanes/Web/Http/Route.lean` | | Routes as values, proved (`Lanes/Web/Http/RouteSound.lean`) |
| `Lanes/Web/Http/SigV4.lean` | `oracles/botocore` | |
| `Lanes/Web/Http/SharedCache.lean` | | RFC 9111's rules for a shared cache, as decisions on a response, not a format; checked against a seeded bug in `Tests/SharedCache.lean`. A run through a real CDN or Varnish is owed |
| `Lanes/Web/Http/Sse.lean` | | Proved to read what it writes against a model of the WHATWG reader (`Lanes/Web/Http/SseSound.lean`); a comparison with another reader, a browser's, is owed |
| `Lanes/Web/Http/Stream.lean` | | Pieces and parts of a streamed body through the gate, not a format: the bytes are `Conn`'s and `Wire`'s |
| `Lanes/Web/Http/Waiting.lean` | | Request ids, not a format |
| `Lanes/Web/Http/Wire.lean` | `oracles/go/requests` | The writer proved against the reader (`Lanes/Web/Http/WireSound.lean`); the responses it reads against `openssl s_server` (`Tests/Tls.lean`) and moto (`oracles/moto`) |
| `Lanes/Web/Http/WireSpec.lean` | | The spec the wire format is proved against |
| `Lanes/Web/S3/Basic.lean` | `oracles/moto`, `oracles/botocore` | Its calls signed as botocore signs, and run against moto |
| `Lanes/Web/S3/Multipart.lean` | `oracles/moto/s3-multipart.jsonl`, `Tests/S3Upload.lean` | The flow and the calls by hand against moto (`Tests/Oracle/Service/S3Multipart.lean`); botocore 1.44's presigned `UploadPart` recorded as a vector; the flow model-checked against `Lanes/Outside/Multipart.lean`. Known: moto 5.2.6 answers `500`, not `404 NoSuchUpload`, to a part sent after an abort |
| `Lanes/Web/S3/Post.lean` | `oracles/moto/s3-post.jsonl`, `Tests/S3Upload.lean` | Forms posted to moto (`Tests/Oracle/Service/S3Post.lean`): moto reads the form and stores the file at its key, with its type. Known: moto 5.2.6 reads no policy, so it admits a file over the range, another key and an expired policy, which `Post.check` refuses as S3 documents; that check is AWS's documented example and botocore 1.44's `generate_presigned_post`, recorded as vectors, and the policy is proved to read back (`S3.Post.form_policy`) |
| `Lanes/Web/S3/Xml.lean` | `oracles/go/xml` | |
| `Lanes/Web/Transcode.lean` | | A format Lanes and its workers write, no vendor's: JSON through `Json`'s parser and printer, which have their oracle, and an HMAC tag through `Auth.tag`; read back as written and checked against the test kit's worker (`Tests/Testing.lean`). There is no reference worker to compare with |
| `Lanes/Testing/Transcode.lean` | | A fake for tests, not a format: it speaks `Lanes/Web/Transcode.lean`'s, and is tested against a site of `listen` (`Tests/Testing.lean`) |
| `integrations/aws/Aws/CloudFront.lean` | `oracles/botocore` | The policy and the whole link, signature included, against botocore's `CloudFrontSigner` |
| `integrations/aws/Aws/Ses.lean` | `oracles/go/mail`, `oracles/moto` | The address check against `net/mail`; the calls against moto |
| `integrations/aws/Aws/Sqs.lean` | `oracles/moto/sqs.jsonl` | The calls against moto (`integrations/aws/Checks/SqsMoto.lean`) |

## Outside models

| Model | Recorded run | Or why not |
| --- | --- | --- |
| `Lanes/Outside/Basic.lean` | | What an outside may do, `Outside`, and no service |
| `Lanes/Outside/Cache.lean` | | Owed: a recorded run against Redis needs a service in the nightly job; checked against a seeded bug in `Tests/Cache.lean` |
| `Lanes/Outside/Clock.lean` | | A clock is not a service to record: its jumps and skew are what NTP and the kernel document; checked against a seeded bug in `Tests/WallClock.lean` |
| `Lanes/Outside/Effects/Basic.lean` | | The class of services with a lifecycle; its instances are below |
| `Lanes/Outside/Effects/Email.lean` | `oracles/moto/ses.jsonl` | |
| `Lanes/Outside/Effects/Payments.lean` | | Owed: Stripe's test mode needs a key, and stripe-mock keeps no state; runs written by hand (`Tests/Outside.lean`) |
| `Lanes/Outside/Events.lean` | | Owed, with Payments: webhooks need a service that sends them; runs written by hand (`Tests/Outside.lean`) |
| `Lanes/Outside/Idempotent.lean` | | Owed, with Payments: SES and S3 take no idempotency key; runs written by hand (`Tests/Outside.lean`) |
| `Lanes/Outside/Multipart.lean` | `oracles/moto/s3-multipart.jsonl` | Parts by their size and digests, not their bytes |
| `Lanes/Outside/ObjectStore.lean` | `oracles/moto/s3.jsonl`, `oracles/moto/s3-post.jsonl` | `POST` uploads as writes granted to a browser |
| `Lanes/Outside/Queue.lean` | `oracles/moto/sqs.jsonl` | A standard queue with a dead-letter queue, and a FIFO queue, through `Aws.Sqs`. Known: moto 5.2.6 deletes a message with any receipt it was given, where SQS may keep it after a delete with a stale one; the model allows both |
| `Lanes/Outside/Rpc.lean` | `oracles/moto/s3.jsonl`, `oracles/moto/ses.jsonl` | The calls the object store's and the email model are made of |
| `Lanes/Outside/Store/Basic.lean` | `oracles/postgres/store.jsonl` | |
| `Lanes/Outside/Throttle.lean` | | Owed: no service in CI answers 429 as a real one does; checked against a seeded bug in `Tests/Throttle.lean` |
| `Lanes/Outside/Transcode.lean` | | Owed: no reference worker, and a vendor's (MediaConvert, Mux) does not speak the wire format; runs written by hand (`Tests/Outside.lean`), and the test kit's worker in `examples/videos`, not recorded |
