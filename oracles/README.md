# Oracles

What Lanes is compared with, and what it is not compared with and why
(`docs/decisions/D80-oracles.md`). There are two kinds, kept apart:

- **Pure oracles** give one input to ours and to a reference implementation and compare the
  outputs, on generated inputs: `lake exe lanesOracle [--cases N] [--seed S] [package…]`. Each
  package is `Tests/Oracle/<Package>.lean` (or, for a service, beside its tests, as
  `Tests/Aws/Mail.lean` and `Tests/Aws/CloudFront.lean` are), the
  reference's program is in its folder here, and its answers to the first cases are kept in the
  folder's `answers.jsonl` (or another file, when two packages share a reference), which `lake test` replays
  and `--record` rewrites. Every difference is a `known` predicate with its reason, or a failure.
- **Service oracles** run our client against a real or reference implementation of a service and
  check the run against our model of it with `Outside.allows`: `oracles/moto/run.sh` and
  `oracles/postgres/run.sh` start the service, run `lake exe lanesServiceOracle` and stop it;
  `--record` rewrites the record in
  the folder, which `lake test` checks against the model again. Each is skipped, with a message,
  when its service is not there.

Programs are built, and Python environments made, in `LANES_ORACLE_CACHE`, or `.lake/oracles`.
CI runs the pure oracles on every pull request (`.github/workflows/ci.yml`, job `oracle`) and the
service oracles nightly and by hand (`.github/workflows/services.yml`).

`lanes lint` checks this file (rule `oracles`): every folder here has a row in the first table;
every module of `Lanes/Lib/` and `Lanes/Web/`, but proofs and IO, has a row in the second,
every model of `Lanes/Outside/` one in the third, and every module of `Lanes/Services/` one in
the fourth, naming an oracle or saying why there is none;
every module a row names exists, and so does every path it cites.

## References

| Folder | Reference | Version | Pinned in | The reference for |
| --- | --- | --- | --- | --- |
| `oracles/go` | Go's standard library, `golang.org/x/time` and Prometheus's `expfmt` | Go 1.24.7, x/time 0.11.0, prometheus/common 0.67.5 | `oracles/go/go.mod`, `oracles/go/go.sum` | Base64, IP addresses, times, JSON, media types, rate limits, URLs, XML, mail addresses, the metrics page, multipart bodies, DEFLATE, gzip and zlib; and, with Node and h11 (`oracles/go/requests/requests.py`, by hand), the request reader |
| `oracles/cbor2` | cbor2 | 6.3.0 | `oracles/cbor2/requirements.txt` | CBOR: what the decoder reads, and the deterministic encoding against cbor2's canonical one |
| `oracles/botocore` | botocore, and `cryptography` for the signatures it is given | 1.44.12, cryptography 50.0.2 | `oracles/botocore/requirements.txt` | Signature Version 4; CloudFront's signed URLs (`oracles/botocore/cloudfront.jsonl`), signed with the published test keys of `oracles/botocore/keys/` |
| `oracles/jwcrypto` | jwcrypto | 1.6.2 | `oracles/jwcrypto/requirements.txt` | JWS in compact form and JWK Sets |
| `oracles/moto` | moto's server, S3, SES API v2 and SQS | 5.2.6 | `oracles/moto/requirements.txt` | the recorded runs of the object store, multipart, email and queue models, and of `POST` forms |
| `oracles/google` | Google's OpenID Connect provider: its discovery document and JWK Set | Fetched on 2026-11-27 | the files themselves | Google's sign-in preset (`Tests/Oidc/Google.lean`) |
| `oracles/libpq` | libpq, the copy psycopg-binary's wheel ships, loaded with ctypes; the program refuses another major | 18, in psycopg-binary 3.3.9 | `oracles/libpq/requirements.txt` | PostgreSQL's connection strings, URIs and service file |
| `oracles/postgres` | PostgreSQL | 16 (16.15 recorded) | the CI job's `postgresql-16` | the recorded runs of the key-value and the typed store models, and the typed store's answers against their meaning |

## Protocol modules

| Module | Oracle | Or why not |
| --- | --- | --- |
| `Lanes/Lib/Compress/Checksum.lean` | `oracles/go/flate` | Through gzip's and zlib's checks; CRC-32 also against its bitwise definition and the published check values (`Tests/Compress.lean`) |
| `Lanes/Lib/Compress/Deflate.lean` | `oracles/go/flate` | What it writes, read by Go in the oracle's cases |
| `Lanes/Lib/Compress/Gzip.lean` | `oracles/go/flate` | Known: a header with a reserved flag, which RFC 1952 has a decoder refuse and Go reads |
| `Lanes/Lib/Compress/Inflate.lean` | `oracles/go/flate` | |
| `Lanes/Lib/Crypto/Certificate.lean` | `Tests/PostgresTls.lean` | The hash for channel binding of certificates `openssl` made, against `openssl dgst`, and accepted by PostgreSQL 16 |
| `Lanes/Lib/Crypto/Hmac.lean` | | Not a format: RFC 4231's vectors, and OpenSSL on thousands of inputs (`Tests/Crypto.lean`) |
| `Lanes/Lib/Crypto/Md5.lean` | | Not a format: RFC 1321's examples, and the digests psql sent in the recorded sessions (`Tests/Postgres.lean`) |
| `Lanes/Lib/Crypto/Native.lean` | | A binding: OpenSSL against the Lean references, and Argon2id against RFC 9106 and the hashes and strings libsodium made (`Tests/Crypto.lean`) |
| `Lanes/Lib/Crypto/Pbkdf2.lean` | | Not a format: through SCRAM, against RFC 7677 and libpq's recorded session (`Tests/Postgres.lean`) |
| `Lanes/Lib/Crypto/PublicKey.lean` | `Tests/Signature.lean`, `Tests/Sign.lean` | The DER of keys and signatures against what the `openssl` command writes, and read back from OpenSSL's; a public key's PEM against `openssl pkey -pubout` |
| `Lanes/Lib/Crypto/Sign.lean` | `Tests/Sign.lean`, `oracles/botocore` | A binding: RFC 6979's signatures, `openssl dgst -sign`, and `cryptography`'s signatures in the CloudFront oracle |
| `Lanes/Lib/Crypto/Sha256.lean` | | Not a format: FIPS 180-4's examples, and OpenSSL on thousands of inputs (`Tests/Crypto.lean`) |
| `Lanes/Lib/Crypto/Sha512.lean` | | Not a format: FIPS 180-4's examples, as `openssl dgst` computes them (`Tests/Crypto.lean`) |
| `Lanes/Lib/Crypto/Verify.lean` | `Tests/Signature.lean` | A binding: OpenSSL's check against `Rsa.verifyReference` and keys `openssl` made |
| `Lanes/Lib/Encoding/Base64.lean` | `oracles/go/base64` | |
| `Lanes/Lib/Encoding/Cbor.lean` | | Imports the modules below |
| `Lanes/Lib/Encoding/Cbor/Basic.lean` | | Values, not a format; a float's widths, checked against the machine's own conversion (`Tests/Cbor.lean`) |
| `Lanes/Lib/Encoding/Cbor/Classes.lean` | | Typed values to and from `Cbor`, not bytes; each reads back (`Cbor.nat?_ofNat`, `Cbor.int?_ofInt`, the `LawfulCbor` instances) |
| `Lanes/Lib/Encoding/Cbor/Decode.lean` | `oracles/cbor2` | Also RFC 8949's examples of Appendix A and its malformed inputs of Appendix F (`Tests/Cbor.lean`); proved to read back what the encoder writes (`Cbor.decode_encode`). Known: cbor2 refuses a map with two keys Python counts equal, such as `true` and `1`, where Lanes reads both; cbor2 reads a NaN's payload only in part |
| `Lanes/Lib/Encoding/Cbor/Derive.lean` | | Typed values to and from `Cbor`, not bytes; each reads back (`Cbor.Fields.readObject_object`, `Cbor.Codec.ofAlts`), and `Tests/Cbor.lean` pins the shapes against the JSON's |
| `Lanes/Lib/Encoding/Cbor/Encode.lean` | `oracles/cbor2` | Also Appendix A (`Tests/Cbor.lean`). Known: cbor2's canonical order puts shorter keys first (RFC 7049), where RFC 8949 §4.2.1 sorts them bytewise; cbor2 writes every NaN as `f97e00` |
| `Lanes/Lib/Encoding/Digits.lean` | | Numbers in a base, read back as written (`Lanes/Lib/Encoding/Digits.lean`'s theorems); compared through every format that uses them |
| `Lanes/Lib/File.lean` | | Not a format: a file replaced whole by the proved plan (`Tests/FileSystem.lean`, `Tests/Crypto.lean`) |
| `Lanes/Lib/Encoding/Fields.lean` | | Fields and constructors for any format of values, not a format; their laws are proved (`Lanes.Fields.pair`, `Lanes.Alts.sum`) |
| `Lanes/Lib/Encoding/Json.lean` | | Imports the modules below |
| `Lanes/Lib/Encoding/Json/Basic.lean` | | Values, not a format |
| `Lanes/Lib/Encoding/Json/Classes.lean` | | Typed values to and from `Json`, not text |
| `Lanes/Lib/Encoding/Json/Derive.lean` | | Typed values to and from `Json`, not text; each reads back (`Json.Fields.readObject_object`, `Json.Codec.ofAlts`), and `Tests/Derive.lean` pins the shapes |
| `Lanes/Lib/Encoding/Json/Grammar.lean` | | RFC 8259's grammar, the spec the parser and printers are proved against; JSONTestSuite (`Tests/Json.lean`) |
| `Lanes/Lib/Encoding/Json/Parser.lean` | `oracles/go/json` | |
| `Lanes/Lib/Encoding/Json/Printer.lean` | `oracles/go/json` | Go parses what the printer writes in the parser's cases; proved to read back (`Json.parse_compress`) |
| `Lanes/Lib/Log.lean` | | Proved one line of JSON text that the parser reads back as the record (`Log.render_oneLine`, `Log.parse_render`); its fields in `slog`'s order checked by hand (`Tests/Log.lean`) |
| `Lanes/Lib/Metrics.lean` | `oracles/go/expfmt` | |
| `Lanes/Lib/Mime/MediaType.lean` | `oracles/go/mime` | |
| `Lanes/Lib/Mime/Multipart.lean` | `oracles/go/multipart` | Go's `Reader` is laxer, each a `known` difference in `Tests/Oracle/Multipart.lean`: it reads a body with no delimiter as no parts, takes a bare line feed for CR LF, a delimiter not on a line of its own as text, header names that are no tokens, folded header lines, headers that are not UTF-8, and a body that ends after a delimiter with no last delimiter; ours refuses them. Proved to read back what it writes (`Multipart.parse_write`) |
| `Lanes/Lib/Net/Ip.lean` | `oracles/go/netip` | |
| `Lanes/Lib/Net/Percent.lean` | `oracles/go/url` | Through the URL's cases, which decode and encode with it (`Tests/Oracle/Url.lean`) |
| `Lanes/Lib/Net/Url.lean` | `oracles/go/url` | |
| `Lanes/Lib/RateLimit.lean` | `oracles/go/rate` | |
| `Lanes/Lib/Time/Civil.lean` | `oracles/go/time` | Through the formats, whose dates it computes |
| `Lanes/Lib/Time/Format.lean` | `oracles/go/time` | |
| `Lanes/Web/Auth/IdToken.lean` | | The claims of an ID token, decided and proved (`OAuth.IdToken.verify_accepted`); its JWS is `Jose`'s |
| `Lanes/Web/Auth/Jose.lean` | `oracles/jwcrypto` | |
| `Lanes/Web/Auth/Login.lean` | | Not a format: failed attempts and sessions, and their bounds |
| `Lanes/Web/Auth/OAuth.lean` | | A flow, model-checked against an attacker's browser (`Tests/OAuth.lean`); the providers' documents are recorded (`oracles/google`) |
| `Lanes/Web/Auth/Password.lean` | | PHC strings of Argon2id: read and written back as libsodium's `crypto_pwhash_str` wrote four (`Tests/Crypto.lean`), and proved to read back as written (`Auth.Phc.parse?_encode`); no reference is run on generated strings, since none is linked in CI's toolchain |
| `Lanes/Web/Auth/Rows.lean` | | Not a format: rows of the typed store, whose SQL is the driver's (`Tests/Oracle/Service/Db.lean`) |
| `Lanes/Web/Auth/Token.lean` | | Tokens only Lanes writes and reads; proved to accept exactly what it signs, before it expires (`Auth.verify_eq_some`) |
| `Lanes/Web/Html/Basic.lean` | | Proved against a model of the HTML tokenizer (`Html.lex_render`); not yet compared with html5lib or a browser |
| `Lanes/Web/Html/Htmx.lean` | | Attributes from routes, not a format of its own |
| `Lanes/Web/Html/Syntax.lean` | | The template syntax, elaborated to `Html.Basic`'s values |
| `Lanes/Web/Http/Basic.lean` | | HTTP as data, not text |
| `Lanes/Web/Http/Compress.lean` | | Decisions on a response and its codings, not a format: tested in `Tests/Compress.lean`; its bytes are `Gzip`'s |
| `Lanes/Web/Http/Conn.lean` | | A connection's decisions, proved (`Lanes/Web/Http/ConnSound.lean`); its bytes are `Wire`'s and `ReadRequest`'s |
| `Lanes/Web/Http/Cookie.lean` | | Proved to read back what it writes (`Lanes/Web/Http/CookieSound.lean`); Go's `http.ParseCookie` is owed |
| `Lanes/Web/Http/Front.lean` | | Decisions, not a format |
| `Lanes/Web/Http/Gate.lean` | | Decisions, not a format |
| `Lanes/Web/Http/Grammar.lean` | | RFC 9110's tokens and field values, used by the reader and the writer |
| `Lanes/Web/Http/Admit.lean` | | Decisions and a system, not a format |
| `Lanes/Web/Http/Loopback.lean` | | A front end with no socket for tests, not a format: its bytes are `Conn`'s and `Wire`'s |
| `Lanes/Web/Http/Ops.lean` | | Routes and access for the operators' endpoints; their page is `Metrics`' |
| `Lanes/Web/Http/ReadRequest.lean` | `oracles/go/requests` | Go's, Node's and h11's servers on `Tests/ReadRequest.corpus`, by hand |
| `Lanes/Web/Http/Route.lean` | | Routes as values, proved (`Lanes/Web/Http/RouteSound.lean`) |
| `Lanes/Web/Http/SigV4.lean` | `oracles/botocore` | |
| `Lanes/Web/Http/SharedCache.lean` | | RFC 9111's rules for a shared cache, as decisions on a response, not a format; checked against a seeded bug in `Tests/SharedCache.lean`. A run through a real CDN or Varnish is owed |
| `Lanes/Web/Http/Sse.lean` | | Proved to read what it writes against a model of the WHATWG reader (`Lanes/Web/Http/SseSound.lean`); a comparison with another reader, a browser's, is owed |
| `Lanes/Web/Http/Stream.lean` | | Pieces and parts of a streamed body through the gate, not a format: the bytes are `Conn`'s and `Wire`'s |
| `Lanes/Web/Http/View.lean` | | Reads answered from the state, not a format |
| `Lanes/Web/Http/Waiting.lean` | | Request ids, not a format |
| `Lanes/Web/Http/Wire.lean` | `oracles/go/requests` | The writer proved against the reader (`Lanes/Web/Http/WireSound.lean`); the responses it reads against `openssl s_server` (`Tests/Tls.lean`) and moto (`oracles/moto`) |
| `Lanes/Web/Http/WireSpec.lean` | | The spec the wire format is proved against |

## Outside models

| Model | Recorded run | Or why not |
| --- | --- | --- |
| `Lanes/Outside/Basic.lean` | | What an outside may do, `Outside`, and no service |
| `Lanes/Outside/Cache.lean` | | Owed: a recorded run against Redis needs a service in the nightly job; checked against a seeded bug in `Tests/Cache.lean` |
| `Lanes/Outside/Clock.lean` | | A clock is not a service to record: its jumps and skew are what NTP and the kernel document; checked against a seeded bug in `Tests/WallClock.lean` |
| `Lanes/Outside/Effects/Basic.lean` | | The class of services with a lifecycle; its instances are below |
| `Lanes/Outside/Effects/Email.lean` | `oracles/moto/ses.jsonl` | |
| `Lanes/Outside/Events.lean` | | Owed, with Payments: webhooks need a service that sends them; runs written by hand (`Tests/Outside.lean`) |
| `Lanes/Outside/FileSystem.lean` | `Tests/FileSystem.lean` | The model below as an outside; runs written by hand, with `io` errors and a power loss |
| `Lanes/Outside/FileSystem/Basic.lean` | `Tests/FileSystem.lean` | Run live, not recorded: every `lake test` makes a script of calls in a temporary directory and checks each answer, errors included, against the model's. A loss of power cannot be run: what it leaves is the model's assumption, trusted (`TRUSTED.md`) |
| `Lanes/Outside/FileSystem/Log.lean` | | A pattern proved on the model, not a service; checked at every crash point in `Tests/FileSystem.lean` |
| `Lanes/Outside/FileSystem/Replace.lean` | | A pattern proved on the model, not a service; checked at every crash point in `Tests/FileSystem.lean`, and run by `File.replace` |
| `Lanes/Outside/Idempotent.lean` | | Owed, with Payments: SES and S3 take no idempotency key; runs written by hand (`Tests/Outside.lean`) |
| `Lanes/Outside/ObjectStore.lean` | `oracles/moto/s3.jsonl`, `oracles/moto/s3-post.jsonl` | `POST` uploads as writes granted to a browser |
| `Lanes/Outside/Queue.lean` | `oracles/moto/sqs.jsonl` | A standard queue with a dead-letter queue, and a FIFO queue, through `Aws.Sqs`. Known: moto 5.2.6 deletes a message with any receipt it was given, where SQS may keep it after a delete with a stale one; the model allows both |
| `Lanes/Outside/Rpc.lean` | `oracles/moto/s3.jsonl`, `oracles/moto/ses.jsonl` | The calls the object store's and the email model are made of |
| `Lanes/Outside/Store/Basic.lean` | `oracles/postgres/store.jsonl` | |
| `Lanes/Db/Model.lean` | `oracles/postgres/db.jsonl` | Generated transactions one at a time and three at once, through `Lanes/Services/Postgres/IO/Db.lean`. Not recorded: a lost `COMMIT`, which the key-value store's runs record at the protocol |
| `Lanes/Outside/Throttle.lean` | | Owed: no service in CI answers 429 as a real one does; checked against a seeded bug in `Tests/Throttle.lean` |

## Services

Each service's protocol modules and models (`Lanes/Services/README.md`).

| Module | Oracle or recorded run | Or why not |
| --- | --- | --- |
| `Lanes/Services/Aws.lean` | | Imports the modules below |
| `Lanes/Services/Aws/CloudFront.lean` | `oracles/botocore` | The policy and the whole link, signature included, against botocore's `CloudFrontSigner` |
| `Lanes/Services/Aws/Imds.lean` | | Client only (`docs/decisions/D113-service-models.md`): tested against fakes of the metadata service (IMDSv2) and of a container's endpoint, written from AWS's documentation, run in `Tests/Aws/Imds.lean`; no emulator of either runs in CI |
| `Lanes/Services/Aws/Refresh.lean` | | A policy, not a format: proved (`Aws.Refresh.current_fresh`, `Aws.Refresh.refresh_in_time`) and model-checked against a model of the metadata service (`Tests/Aws/Refresh.lean`) |
| `Lanes/Services/Aws/Ses.lean` | `oracles/go/mail`, `oracles/moto` | The address check against `net/mail`; the calls against moto |
| `Lanes/Services/Aws/Sqs.lean` | `oracles/moto/sqs.jsonl` | The calls against moto (`Tests/Aws/SqsMoto.lean`) |
| `Lanes/Services/Oidc.lean` | | Imports the modules below |
| `Lanes/Services/Oidc/GitHub.lean` | | Client only (`docs/decisions/D113-service-models.md`): GitHub's answers in the shapes its REST documentation gives, written by hand (`Tests/Oidc/GitHub.lean`); none is recorded from GitHub |
| `Lanes/Services/Oidc/Google.lean` | `oracles/google` | The preset's endpoints, issuers and algorithms against Google's discovery document and JWK Set as recorded (`Tests/Oidc/Google.lean`) |
| `Lanes/Services/Postgres.lean` | | Imports the modules below |
| `Lanes/Services/Postgres/Bytes.lean` | `Tests/Postgres.lean`, `oracles/postgres` | The fields of the messages, in the sessions recorded from PostgreSQL 16 and psql 16 (`Tests/Postgres/`) |
| `Lanes/Services/Postgres/ConnInfo.lean` | `oracles/libpq` | Connection strings and URIs against `PQconninfoParse`, and service files against what `PQconnectStartParams` takes from them (`Tests/Oracle/Libpq.lean`). Known: libpq keeps percent-decoded bytes that are not UTF-8, which a Lean string cannot hold |
| `Lanes/Services/Postgres/Conn.lean` | `Tests/Postgres.lean`, `oracles/postgres` | A state machine, not a format: the recorded sessions, and the live runs |
| `Lanes/Services/Postgres/Message.lean` | `Tests/Postgres.lean`, `oracles/postgres` | The messages, in the recorded sessions; written and read again against a live server |
| `Lanes/Services/Postgres/Pool.lean` | | Decisions, not a format: proved (`Pool.run_size`, `Pool.never_again`) and model-checked (`Tests/PostgresPool.lean`) |
| `Lanes/Services/Postgres/Scram.lean` | `Tests/Postgres.lean`, `Tests/PostgresTls.lean` | RFC 7677's example and libpq's recorded session; with channel binding, Python's `hashlib` and PostgreSQL 16 with TLS |
| `Lanes/Services/Postgres/Settings.lean` | `Tests/PostgresLive.lean`, `oracles/libpq` | libpq's variables and password file: `psql` connects with the same, against PostgreSQL 16; its strings and service files through `ConnInfo.lean`'s oracle; which source wins, by hand from libpq's documentation (`Tests/PostgresSettings.lean`) |
| `Lanes/Services/Postgres/Sql.lean` | `oracles/postgres/db.jsonl` | The SQL of the typed store's operations against PostgreSQL itself: every answer of generated transactions compared with its meaning (`Tests/Oracle/Service/Db.lean`); a value reads back from its parameter (`Postgres.Sql.decode_param`) |
| `Lanes/Services/Postgres/Table.lean` | `oracles/postgres` | The SQL of the store's operations, against PostgreSQL itself |
| `Lanes/Services/S3.lean` | | Imports the modules below |
| `Lanes/Services/S3/Basic.lean` | `oracles/moto`, `oracles/botocore` | Its calls signed as botocore signs, and run against moto |
| `Lanes/Services/S3/Multipart.lean` | `oracles/moto/s3-multipart.jsonl`, `Tests/S3Upload.lean` | The flow and the calls by hand against moto (`Tests/Oracle/Service/S3Multipart.lean`); botocore 1.44's presigned `UploadPart` recorded as a vector; the flow model-checked against `Lanes/Services/S3/MultipartModel.lean`. Known: moto 5.2.6 answers `500`, not `404 NoSuchUpload`, to a part sent after an abort |
| `Lanes/Services/S3/MultipartModel.lean` | `oracles/moto/s3-multipart.jsonl` | Parts by their size and digests, not their bytes |
| `Lanes/Services/S3/Post.lean` | `oracles/moto/s3-post.jsonl`, `Tests/S3Upload.lean` | Forms posted to moto (`Tests/Oracle/Service/S3Post.lean`): moto reads the form and stores the file at its key, with its type. Known: moto 5.2.6 reads no policy, so it admits a file over the range, another key and an expired policy, which `Post.check` refuses as S3 documents; that check is AWS's documented example and botocore 1.44's `generate_presigned_post`, recorded as vectors, and the policy is proved to read back (`S3.Post.form_policy`) |
| `Lanes/Services/S3/Testing.lean` | | A fake for tests, not a client: it checks signatures with the client's own `SigV4`, so the client is compared with moto and botocore, not with it |
| `Lanes/Services/S3/Xml.lean` | `oracles/go/xml` | |
| `Lanes/Services/Stripe.lean` | | Imports the modules below |
| `Lanes/Services/Stripe/Payments.lean` | | Owed: Stripe's test mode needs a key, and stripe-mock keeps no state; runs written by hand (`Tests/Outside.lean`) |
