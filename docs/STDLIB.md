# The standard library, triaged from Go's

Go's standard library covers what an application needs without third-party packages. Lanes
wants the same coverage, with everything proved (`docs/decisions/D45-everything-is-proved.md`).
This page goes through every public package of Go 1.24
(`go list std`, 172 packages without `internal` and `vendor`), plus the `golang.org/x` packages
most web applications take, and says for each where Lanes gets it.

The rule applied is: write in Lean, and prove, what decides (protocols, parsers, formats, data
structures); bind what depends on what Lean cannot express or check (timing side channels,
assembly, the operating system); and test what we write against a reference implementation on
generated inputs. A proof says the code meets its spec, not that the spec says what the standard
means. Go's implementation has had years of scrutiny, so disagreeing with it on generated inputs
is how a misread standard shows up.

## Classes

| Class | Meaning | Packages |
| --- | --- | --- |
| a | Lean core, `Std` or Batteries has it (module named) | 37 |
| b | Pure and needed by applications: build in Lean and prove | 26 |
| c | Touches the operating system or cryptography: bind (library named) | 11 |
| d | Not needed for Lanes applications (reason given) | 79 |
| e | Already in Lanes (module named) | 19 |

Of the 19 `golang.org/x` packages listed at the end, 8 are (b), 3 are (c), 7 are (d) and 1 is (e).

A package gets the class of what applications use it for. Three have a part in another class,
listed on their own line: the formats of `time` (b, P0), `File.Sync` in `os` (c, P0) and content
sniffing and event streams in `net/http` (b, P1).

Three qualifications apply to (a):

- **Not linkable.** Runtime modules import `Std` only (design decision 5): `import Lean` takes a
  binary from about 5 MB to about 137 MB (D15), and Batteries comes in only through Mathlib.
  Something that exists only in `Lean.*` (`Lean.Data.Json`, `Lean.Data.Markdown`,
  `Lean.Data.Html`) or in Batteries is available to proofs and tests, and has to be ported, as
  JSON was, before an application can run it. Such rows say so.
- **Unproved.** Some `Std` code decides things and has no theorems: `Std.Http.Data.URI.Parser`
  and `Std.Time.Format.*` have none (counted on this toolchain, `v4.37.0-rc1`). Where an
  application's correctness rests on such code, the row is (b) and the `Std` module is what is
  used until ours exists.
- **Bound.** Some `Std` functions are C behind `@[extern]`: `Std.Net.IPv4Addr.ofString` is
  libuv's `inet_pton`, `IO.getRandomBytes` reads `/dev/urandom`. That is (a) for what touches
  the OS, but parsing an address is a decision, so `net/netip` is (b).

Sizes, counting proofs: small is under 500 lines, medium 500 to 2,000, large over 2,000.
Priorities are for web applications. P0 is needed by the flagship application: deployed,
public, multi-user, with sessions, posts, timelines, rate limits and outbound HTTP calls to an
API. P1 is common, P2 rare.

## Text, numbers and data structures

| Go package | Class | Where, or why not |
| --- | --- | --- |
| `bufio`, `io`, `io/ioutil` | a | `IO.FS.Handle` (`getLine`, `read`, `write`), `IO.FS.Stream`, `Std.Async.IO`, `Std.Data.ByteSlice` |
| `bytes`, `strings` | a | `ByteArray`, `String`, `String.Slice` and string patterns in `Init.Data.String`; byte and UTF-8 lemmas in `Lanes/Proof/ByteArray.lean`, `Lanes/Proof/Utf8.lean` |
| `strconv` | a | `String.toNat?`, `String.toInt?` (`Std.Data.String.ToNat`, `ToInt`), `Nat.repr`, `Float.ofScientific`. No float parser and no shortest float printer: JSON numbers in `Lanes.Json` are exact decimals, so none is needed yet (b, P2 below) |
| `fmt` | a | `ToString`, `s!` interpolation, `Repr`, `Std.Format` |
| `errors` | a | `Except`, `IO.Error`; an unexpected state in a step is `stop`, not an error value |
| `cmp`, `sort`, `slices`, `maps`, `iter` | a | `Ord`, `compare`; `Array.qsort`, `List.mergeSort` (with its lemmas), `Array.binSearch`; `Std.HashMap`, `Std.TreeMap`, `Std.ExtTreeMap` with their lemmas; `Std.Data.Iterators`, `ForIn` |
| `container/heap` | a | `Batteries.Data.BinaryHeap`, `BinomialHeap`, `PairingHeap` (not linkable: port when an application needs a heap; timers already have the kernel's own) |
| `container/list` | a | `List`; a queue is `Lanes.Fifo` (`Lanes/Data/Fifo.lean`) |
| `container/ring` | d | `Lanes.Fifo` covers bounded queues |
| `hash`, `hash/maphash` | a | `Hashable`, `LawfulHashable`, `hash64` |
| `hash/fnv` | e | FNV-1a in `Lanes/Durable/Frame.lean`, the journal's checksum |
| `hash/crc32`, `hash/adler32` | b | the checksums of gzip and zlib; built with `compress/*` (P2) |
| `hash/crc64` | d | no format an application reads uses it |
| `math` | a | `Float` (C doubles and libm), with the logical model `Float.Model` (IEEE binary64, `Init.Data.Float.Model`) to state what an operation does |
| `math/big` | a | `Nat` and `Int` are arbitrary precision (GMP); `Rat` in `Init.Data.Rat` |
| `math/bits` | a | `UInt8` to `UInt64`, `BitVec` and its lemmas, `Nat.log2` |
| `math/cmplx` | d | no application use |
| `math/rand`, `math/rand/v2` | a | `StdGen` (`Init.Data.Random`), Batteries' Mersenne Twister (not linkable). In a step, randomness is an input, never a call |
| `unicode` | b | Lean's `Char.isAlpha`, `Char.toUpper` and the rest are ASCII only. Unicode categories exist only as CommonMark's punctuation and whitespace classes in `Lean.Data.Markdown.Unicode` (not linkable) |
| `unicode/utf8` | a | `String` is valid UTF-8 by construction; `String.fromUTF8?`, `String.validateUTF8`, `String.utf8EncodeChar` |
| `unicode/utf16` | b | only `Lean.Data.Lsp.Utf16` (not linkable); needed to count text as a browser's `maxlength` does |
| `regexp`, `regexp/syntax` | b | Lean has no regular expressions |
| `text/template`, `text/template/parse` | d | views are Lean (`Lanes.Html` templates), plain text is `s!` |
| `text/scanner`, `text/tabwriter` | d | tools, not applications |
| `index/suffixarray` | d | full-text search is not in scope; P2 at most |
| `unique`, `weak`, `structs`, `unsafe` | d | runtime and memory-layout tools without a use in a pure step |

## Encodings, compression and formats

| Go package | Class | Where, or why not |
| --- | --- | --- |
| `encoding` | e | the interfaces; Lanes' equivalent is `Codec` with its round-trip law (`Lanes/Data/Codec.lean`, `lanes_data`) |
| `encoding/json` | e | `Lanes.Json` (`Lanes/Lib/Encoding/Json/`, D15): total, bounded, strict. Its print-then-parse round trip is not proved yet; JSONTestSuite and Go are its oracles |
| `encoding/hex` | e | `Bytes.hex`, `Bytes.unhex?` (`Lanes/Lib/Crypto/Hmac.lean`, `Bytes.unhex?_hex` proved) |
| `encoding/base64` | b | P0, built: `Lanes/Lib/Encoding/Base64.lean` |
| `encoding/base32` | b | P1 |
| `encoding/binary` | b | P2; fixed-width big-endian is in `Lanes.Frame` already |
| `encoding/csv` | b | P1 |
| `encoding/pem` | b | P2 |
| `encoding/asn1` | b | P2 |
| `encoding/xml` | b | P2; a reader of the part S3's answers use, in `Lanes/Web/S3/Xml.lean`, tested against Go's (`oracles/go/xml`) |
| `encoding/gob` | d | Go's own format; Lanes has `Codec` |
| `encoding/ascii85` | d | PostScript and PDF only |
| `compress/flate`, `compress/gzip`, `compress/zlib` | b | P2: the reverse proxy compresses responses, and a client can ask for none |
| `compress/bzip2`, `compress/lzw` | d | legacy formats |
| `archive/tar`, `archive/zip` | d | an export is JSON or CSV |
| `mime` | b | P0 for media types, built: `Lanes/Lib/Mime/MediaType.lean`; P1 for the extension table |
| `mime/multipart` | b | P1 |
| `mime/quotedprintable` | b | P2 |
| `html` | e | escaping in `Lanes.Html` (`Lanes/Web/Html/Basic.lean`, proved safe). Unescaping (`html.UnescapeString`) is P2, and the table of character references exists in `Lean.Data.Html.CharRef` (not linkable) |
| `html/template` | e | `Lanes.Html`, the template macro and `Lanes.Hx` (`Lanes/Web/Html/`): text escaped by type, URL attributes checked at render |
| `image`, `image/color`, `image/color/palette`, `image/draw`, `image/gif`, `image/jpeg`, `image/png` | d | an upload is stored as bytes. Decoding hostile images to resize them would be (b, large); for now that is a separate service |

## Network and HTTP

| Go package | Class | Where, or why not |
| --- | --- | --- |
| `net` | a | `Std.Async.TCP`, `Std.Async.UDP`, `Std.Async.DNS` (libuv's `getaddrinfo`), `Std.Net.Addr`. Lanes uses TCP (`Lanes.Peers`, the HTTP client) and DNS (the HTTP client) |
| `net/netip` | b | P0, built: `Lanes/Lib/Net/Ip.lean` (`Std.Net.Addr` parses and prints with libuv's `inet_pton` and `inet_ntop`, and has no prefixes) |
| `net/url` | b | P0, built: `Lanes/Lib/Net/Url.lean` (references, resolution, normalization, queries) with `Lanes/Lib/Net/UrlSound.lean`; forms in `Lanes/Web/Http/Basic.lean`. `Std.Http.Data.URI` parses RFC 3986 with no theorems |
| `net/http` (server) | e | `Lanes.Web.IO.Server` on `Std.Net`, reading requests with `Lanes/Web/Http/ReadRequest.lean` (proved), with the gate (`Lanes/Web/Http/Gate.lean`) deciding; routes `Lanes/Web/Http/Route.lean`; cookies `Lanes/Web/Http/Cookie.lean`; sessions and log-in `Lanes/Web/Auth/` |
| `net/http` (client) | e | `Lanes.Web.IO.Client` and `Lanes.Web.Http.Wire` (the reader proved). `Std.Http` has no client, only a pure redirect planner (`Std.Http.Protocol.H1.Redirect`). TLS from the OpenSSL Lean's toolchain links (c, P0, built: `Lanes/Web/IO/Tls.lean`, D67) and names (DNS, P0, built: a name resolves to its first IPv4 address) |
| `net/http` (`DetectContentType`) | b | P1, to check an upload is what it claims |
| `net/http` (streamed responses) | b | P1: server-sent events for live timelines; the server adapter answers once per request today |
| `net/http/httptest` | e | handlers are pure functions tested directly; adapters are tested against recorded runs (`Lanes.Outside`, `Tests/HttpClient.lean`) |
| `net/textproto` | e | header lines are read in `Lanes/Web/Http/ReadRequest.lean` and written and read in `Lanes.Web.Http.Wire` |
| `net/http/cookiejar` | d | the application is the server; a client that logs in elsewhere is rare |
| `net/http/httputil` | d | reverse proxying and dumps; the proxy in front is not Lean |
| `net/http/pprof`, `net/http/httptrace` | d | Go runtime introspection |
| `net/http/cgi`, `net/http/fcgi` | d | deployment models Lanes does not use |
| `net/mail` | b | P1; SES's check of a bare addr-spec, `integrations/aws/Aws/Ses.lean`, tested against Go's (`oracles/go/mail`) |
| `net/smtp` | b | P2: mail goes through a provider's HTTP API |
| `net/rpc`, `net/rpc/jsonrpc` | d | shards talk through `Lanes.Peers`; other services through HTTP |

## Cryptography

| Go package | Class | Where, or why not |
| --- | --- | --- |
| `crypto/sha256` | e | libsodium's, bound in `Lanes/Lib/Crypto/Sodium.lean`, with `Lanes.Sha256` (pure Lean, NIST vectors) as its reference (D46) |
| `crypto/hmac` | e | libsodium's, bound in `Lanes/Lib/Crypto/Sodium.lean`, with `Lanes.Hmac` (pure Lean, RFC 4231 vectors) as its reference (D46) |
| `crypto/pbkdf2` | e | `Lanes/Lib/Crypto/Pbkdf2.lean`, over libsodium's HMAC, for SCRAM-SHA-256 only (RFC 7914 vectors); passwords are digested with Argon2id (D46) |
| `crypto/rand` | a | `IO.getRandomBytes` (reads `/dev/urandom`); Lanes binds libsodium's `randombytes_buf`, which uses `getrandom(2)` and also works where `/dev` is not mounted (D46) |
| `crypto/subtle` | c | libsodium `sodium_memcmp`, bound (D46): compiled Lean promises nothing about timing, so the Lean comparison is only the reference |
| `crypto/tls` | e | the client, from the OpenSSL Lean's toolchain ships, bound in `native/tls.c` and `Lanes/Web/IO/Tls.lean`; inbound TLS stays at the load balancer or reverse proxy |
| `crypto/x509`, `crypto/x509/pkix` | e | OpenSSL's, inside the TLS client: the chain verified against the system's roots or a file given, the name or address checked (`Lanes/Web/IO/Tls.lean`); of a certificate, Lean reads only the signature algorithm, for channel binding (`Lanes/Lib/Crypto/Certificate.lean`) |
| `crypto/aes`, `crypto/cipher` | c | libsodium `crypto_aead_xchacha20poly1305_ietf` (or `crypto_aead_aes256gcm`), for encrypted cookies and data at rest (P1) |
| `crypto/ed25519` | c | libsodium `crypto_sign` (P1: webhook signatures) |
| `crypto/ecdh` | c | libsodium `crypto_scalarmult` for X25519; P-256 from OpenSSL's `libcrypto` (P2) |
| `crypto/ecdsa` | e | verifying only: P-256 with SHA-256 from the OpenSSL Lean's toolchain ships, bound in `native/verify.c` and `Lanes/Lib/Crypto/Verify.lean`, the key's and the signature's DER written in Lean (`Lanes/Lib/Crypto/PublicKey.lean`); for ES256 tokens; signing with a P-256 key and RFC 6979's nonce, from the same OpenSSL (`native/sign.c`, `Lanes/Lib/Crypto/Sign.lean`), over SHA-1 or SHA-256, for CloudFront's signed URLs |
| `crypto/rsa` | e | verifying only: PKCS #1 v1.5 with SHA-256, bound from the same OpenSSL (`native/verify.c`), with a Lean reference (`Rsa.verifyReference`); for RS256 tokens. Signing with PKCS #1 v1.5 over SHA-1 or SHA-256 (`native/sign.c`, `Lanes/Lib/Crypto/Sign.lean`); no PSS or encryption |
| `crypto/sha1` | c | `libcrypto` (P1: TOTP is HMAC-SHA-1; also the WebSocket handshake) |
| `crypto/sha512` | e | `Lanes/Lib/Crypto/Sha512.lean`, SHA-512 and SHA-384 in pure Lean (NIST vectors, `openssl dgst`), for the hash of a certificate that channel binding sends; libsodium has SHA-512 and not SHA-384 |
| `crypto/hkdf` | c | libsodium `crypto_kdf_hkdf_sha256` (P1: deriving keys from one secret) |
| `crypto` | d | a registry of hash functions; Lean calls functions by name |
| `crypto/md5` | e | `Lanes/Lib/Crypto/Md5.lean`, pure Lean, for PostgreSQL's `md5` authentication only (RFC 1321 vectors); broken as a hash |
| `crypto/des`, `crypto/rc4`, `crypto/dsa`, `crypto/elliptic` | d | broken, legacy or deprecated |
| `crypto/sha3`, `crypto/mlkem` | d | no application use yet; ML-KEM matters inside TLS, which is bound |
| `crypto/fips140` | d | Go's FIPS mode |

libsodium is the default because its interfaces are hard to misuse and it is small. OpenSSL is
there because TLS needs it, and then provides what libsodium lacks (P-256, RSA, SHA-1), so
there are two libraries and not three. Bindings are tested against Project Wycheproof's vectors
and the RFCs' own.

## Operating system, time and runtime

| Go package | Class | Where, or why not |
| --- | --- | --- |
| `os` | a | `IO.FS` (files, directories, `rename`, `Handle.lock`, `createTempFile`), `IO.getEnv`, `IO.Process.exit`, `IO.appPath` |
| `os` (`File.Sync`) | c | `fsync(2)` and `fdatasync(2)`, also on the directory after a rename. Lean's `IO` has none. Done: bound in `native/lanes.c` and used by `Lanes/Durable/IO/Journal.lean` (D46) |
| `os/exec` | a | `IO.Process.spawn`, `IO.Process.output`, `Std.Async.Process` |
| `os/signal` | a | `Std.Async.Signal`; `Http.Server.stopOnSignal` drains at `SIGTERM` |
| `os/user` | d | an application does not look up OS users |
| `io/fs`, `path/filepath` | a | `IO.FS` (`readDir`, `metadata`, `walkDir`), `System.FilePath` |
| `path` | b | P1 |
| `embed` | a | `include_str` (`Init.Notation`), used for templates. There is no `include_bytes`; binary assets would need a small macro |
| `time` | a | `Std.Time` (civil dates and times, `Duration`, `Timestamp.now`), `IO.monoNanosNow`; `Lanes.Clock` (`Lanes/Outside/IO/Clock.lean`) is the adapter that makes time an input (D23) |
| `time` (formats) | b | P0, built: `Lanes/Lib/Time/Format.lean`. `Std.Time.Formats` has `iso8601` (whole seconds only) and `httpDate`, with no theorems, and `rfc850` is written `dd-MM-uuuu` under a docstring that says `dd-MMM-YY` |
| `time/tzdata` | a | `Std.Time.Zoned.Database` reads TZif files from the system's `zoneinfo`; an embedded copy is not needed on a server |
| `context` | e | deadlines are `Effect.after` and `Effect.cancel` (`Lanes/Core/System.lean`, D3); a request's deadline is the gate's |
| `sync`, `sync/atomic` | a | `Std.Sync` (`Mutex`, `Channel`, `Semaphore`, `Barrier`, `Notify`, `Broadcast`), `IO.Ref`. Lanes actors share nothing, so applications do not use them |
| `log` | a | `IO.println`, `IO.eprintln` |
| `log/slog` | b | P1. The HTTP server's access log is JSON lines (`Lanes/Web/Http/Ops.lean`); there is no general logger |
| `log/syslog` | d | logs go to standard error and the service manager collects them |
| `expvar` | b | P1, built as a metrics page in the Prometheus text format rather than expvar's JSON: `Lanes/Lib/Metrics.lean`, served by the HTTP server (`ServerConfig.ops`) |
| `flag` | d | an application takes a few arguments and the environment; the `Cli` package is in the manifest (through Mathlib) if a tool needs more |
| `testing` | e | `lake test`, the model checker (`Lanes.Check`), seeded random runs (`Lanes/Check/Fuzz.lean`), mutants (`scripts/mutants.py`) |
| `testing/quick` | a | Plausible, pinned in `lake-manifest.json` through Mathlib |
| `testing/fstest`, `testing/iotest`, `testing/slogtest` | d | fakes for Go interfaces |
| `database/sql`, `database/sql/driver` | e | state is actor state with a journal by default; PostgreSQL's protocol is `Lanes/Lib/Postgres/` (a client, not a generic driver interface), and a transactional store is the model `Lanes/Outside/Store/Basic.lean` |
| `syscall` | d | specific calls are bound one by one (`fsync`), not as a package |
| `plugin`, `reflect` | d | Lean has no run-time reflection; codecs are derived by `lanes_data` |
| `runtime`, `runtime/cgo`, `runtime/coverage`, `runtime/debug`, `runtime/metrics`, `runtime/pprof`, `runtime/race`, `runtime/trace` | d | Go runtime internals |
| `debug/buildinfo`, `debug/dwarf`, `debug/elf`, `debug/gosym`, `debug/macho`, `debug/pe`, `debug/plan9obj` | d | object files and debuggers |
| `go/ast`, `go/build`, `go/build/constraint`, `go/constant`, `go/doc`, `go/doc/comment`, `go/format`, `go/importer`, `go/parser`, `go/printer`, `go/scanner`, `go/token`, `go/types`, `go/version` | d | Go tooling |

## From `golang.org/x`

| Package | Class | Where, or why not |
| --- | --- | --- |
| `x/crypto/argon2` | c | libsodium `crypto_pwhash` (Argon2id). Done (D46): computed off the shard, by a bridge's `prepare` |
| `x/crypto/bcrypt` | d | Argon2id instead; bcrypt only to import users from elsewhere |
| `x/crypto/chacha20poly1305`, `x/crypto/nacl/secretbox`, `x/crypto/nacl/box` | c | libsodium (P1) |
| `x/crypto/acme/autocert`, `x/crypto/ssh` | d | certificates belong to the reverse proxy; no SSH |
| `x/net/html` | b | P2: an application takes text and Markdown, not HTML |
| `x/net/idna` | b | P1 |
| `x/net/publicsuffix` | b | P2 |
| `x/net/websocket` | b | P2: server-sent events cover live timelines |
| `x/net/http2` | d | the reverse proxy speaks HTTP/2 to browsers |
| `x/text/unicode/norm` | b | P1 |
| `x/text/cases` | b | P1 |
| `x/text/secure/precis` | b | P1 |
| `x/text/language`, `x/text/encoding` | d | one language and UTF-8 only, for now |
| `x/time/rate` | b | P0, built: `Lanes/Lib/RateLimit.lean` (the bucket; not yet the table of buckets per key) |
| `x/sync` (`errgroup`, `semaphore`, `singleflight`) | d | concurrency is actors |
| `x/oauth2` | e | sign-in only: the authorization code flow with PKCE and OpenID Connect (`Lanes/Web/Auth/OAuth.lean`, `Lanes/Web/IO/SignIn.lean`); no refresh tokens or token sources for calling APIs |

## What to build (b)

| Package | An application uses it for | Spec | Oracle | Size | P |
| --- | --- | --- | --- | --- | --- |
| `encoding/base64` | opaque pagination cursors, `Authorization: Basic`, JWT segments, `data:` URLs | RFC 4648 §4, §5; `decode (encode b) = some b`, and `decode` accepts only canonical text (strict padding, zero trailing bits) | Go `base64.StdEncoding.Strict()`, `RawURLEncoding`; RFC 4648 §10 vectors | small | P0, built |
| `net/netip` | the client's address from the proxy's `X-Forwarded-For`, as a rate-limit key; `/64` prefixes for IPv6; host literals in URLs | RFC 4291 §2.2 (text forms), RFC 5952 (canonical output), RFC 4632 (prefixes), RFC 6874 (zones in URLs); `parse (print a) = some a`, masking idempotent, `contains` agrees with masking | Go `netip.ParseAddr`, `ParsePrefix`, `Addr.String`, `Prefix.Masked` | small | P0, built |
| `net/url` | URLs of outbound API calls and their query strings, `Location` of redirects, links in posts | RFC 3986 §3 grammar, §5.2 resolution (§5.4's examples as theorems), §6.2.2 normalization; `parse (print u) = some u` | Go `url.Parse`, `ResolveReference`, `Values.Encode`; WHATWG `urltestdata.json` for the `http(s)` cases where WHATWG and RFC 3986 agree (they differ on purpose elsewhere) | medium | P0, built |
| `time` (formats) | timestamps of posts in JSON and `<time datetime>`, `Date`, `Expires`, `Last-Modified`, `Retry-After` and cookie `Expires` | RFC 3339 §5.6; RFC 9110 §5.6.7 (IMF-fixdate to write; the two obsolete forms read only); days from a civil date and back as inverse functions (Hinnant's algorithm) | Go `time.Parse(time.RFC3339Nano, …)`, `Format`, `http.ParseTime`, `http.TimeFormat` | small | P0, built |
| `mime` (media types) | checking the `Content-Type` of forms and of API responses, and its `charset` | RFC 9110 §8.3.1 (with the `token` and `quoted-string` of §5.6, shared with `Lanes.Web.Http.Cookie`), RFC 2231 parameters; `parse (format m) = some m` | Go `mime.ParseMediaType`, `FormatMediaType` | small | P0, built |
| `x/time/rate` | limits per user and per address on posts and log-ins; keeping under an API's quota | the token bucket of x/time/rate: `tokens t = min burst (tokens t₀ + rate·(t − t₀))`, allowed iff `n ≤ tokens`; theorem: in any window of length `w` at most `burst + rate·w` events are allowed | x/time/rate `AllowN(t, n)` and `ReserveN`, which take the time as an argument and so replay exactly | small | P0, built |
| `encoding/base32` | TOTP secrets | RFC 4648 §6; laws as base64 | Go `base32.StdEncoding` | small | P1 |
| `encoding/csv` | exports and imports | RFC 4180 grammar; `parse (print rows) = some rows` | Go `encoding/csv` (it reads `\r\n` as `\n` and is lenient with options; compare with those off) | small | P1 |
| `mime/multipart` | uploads (avatars, attachments) | RFC 7578, RFC 2046 §5.1; `parse (write parts) = some parts`, a boundary never occurs in a part | Go `multipart.Reader`, `multipart.Writer` | medium | P1 |
| `net/mail` | e-mail addresses at sign-up | RFC 5322 §3.4 address grammar, RFC 6532 for UTF-8 | Go `mail.ParseAddress`, `ParseAddressList` | medium | P1 |
| `net/http` (`DetectContentType`) | checking an upload is the type it claims | WHATWG MIME Sniffing Standard | Go `http.DetectContentType` | small | P1 |
| `net/http` (event streams) | live timelines | WHATWG HTML §9.2 (`text/event-stream`); `parse (write events) = events` | the specification's examples; Go has no parser | small | P1 |
| `path` | cleaning a request's path, static files | RFC 3986 §5.2.4 `remove_dot_segments`; `clean (clean p) = clean p` | Go `path.Clean`, `path.Match` | small | P1 |
| `log/slog` | structured logs | one JSON object per line, as slog's `JSONHandler` writes (RFC 3339 times, keys in order) | Go `slog.NewJSONHandler` on the same records | small | P1 |
| `expvar` | a metrics page | Prometheus text exposition format 0.0.4 | `github.com/prometheus/common/expfmt` parsing our output | small | P1, built; `oracles/go/expfmt` |
| `unicode` | validating names and text by category | the Unicode Character Database (`UnicodeData.txt`, `DerivedCoreProperties.txt`), tables generated from it with a theorem per table that lookup agrees with the list | the UCD files directly; Go 1.24 is at Unicode 15.0.0, so it disagrees on newer characters | medium | P1 |
| `unicode/utf16` | counting text as `maxlength` in a browser does | Unicode §3.9 D91; `decode (encode s) = s` on scalar values | Go `utf16.Encode`, `Decode` | small | P1 |
| `x/text/unicode/norm` | user names and search keys compared after NFC | UAX #15; NFC idempotent, `nfc ∘ nfd = nfc` | `NormalizationTest.txt`; Go x/text | medium | P1 |
| `x/text/cases` | case-insensitive names | Unicode §3.13 default case folding | `CaseFolding.txt`, `SpecialCasing.txt`; Go x/text | medium | P1 |
| `x/text/secure/precis` | user names and passwords prepared before comparison | RFC 8264, RFC 8265 (`UsernameCaseMapped`, `OpaqueString`); needs norm and cases | Go x/text/secure/precis | small | P1 |
| `x/net/idna` | host names in links in posts | UTS #46, RFC 5891, RFC 3492 (Punycode, `decode (encode s) = s`) | `IdnaTestV2.txt`; Go x/net/idna | medium | P1 |
| `x/oauth2` | "log in with" another service; calling APIs on a user's behalf | RFC 6749 §4.1 with PKCE (RFC 7636): built for signing in, as pure decisions done where a request arrives, not as an actor (`docs/decisions/D72-sign-in-with-oauth.md`); calling APIs later (refresh tokens) is not | Go x/oauth2 against a scripted provider, comparing the requests each sends: not done; tested against a provider run in the test | medium | P1, sign-in built |
| `regexp`, `regexp/syntax` | validation, search, rewriting links | RE2 syntax; the language of an expression and leftmost-first matching as the spec; the matcher (Pike VM or derivatives) proved to agree and to run in linear time | Go `regexp`; RE2's suites in Go's tree (`regexp/testdata/re2-search.txt`, `re2-exhaustive.txt.bz2`) and the AT&T POSIX tests there (`basic.dat`, `nullsubexpr.dat`, `repetition.dat`) | large | P1 |
| `compress/flate`, `gzip`, `zlib`, `hash/crc32`, `hash/adler32` | reading compressed API responses and uploads | RFC 1950, 1951, 1952; `inflate (deflate x) = some x`; CRC-32 as polynomial division | Go `compress/*` both ways (Go inflates ours, we inflate Go's at every level), Go `crc32.ChecksumIEEE` | large | P2 |
| `encoding/binary` | varints and fixed-width fields of other services' formats | protobuf varint and zigzag; round trips | Go `binary.AppendUvarint`, `Uvarint`, `BigEndian` | small | P2 |
| `encoding/pem` | reading keys for the bound libraries | RFC 7468; round trip | Go `encoding/pem` | small | P2 |
| `encoding/asn1` | DER-encoded ECDSA signatures (JWT ES256 wants `r ‖ s`); written, not read, for the two shapes the signature check needs in `Lanes/Lib/Crypto/PublicKey.lean` | ITU-T X.690 DER; round trip and canonicity | Go `encoding/asn1`, x/crypto/cryptobyte | large | P2 |
| `encoding/xml` | Atom and RSS feeds (written, like `Html`); reading XML is rarer | XML 1.0 (fifth edition) | W3C XML Conformance Test Suite; Go `encoding/xml` is lenient, so second | large | P2 |
| `mime/quotedprintable` | mail bodies | RFC 2045 §6.7; round trip | Go `mime/quotedprintable` | small | P2 |
| `net/smtp` | sending mail without a provider's API | RFC 5321 client as an actor; needs TLS (c) | Go `net/smtp` against a scripted server, comparing the bytes each client sends | medium | P2 |
| `html` (unescaping) | reading text out of HTML from elsewhere | WHATWG named character references (`entities.json`) | Go `html.UnescapeString` | small | P2 |
| `strconv` (floats) | printing and reading binary64 values | shortest round trip (`parse (print x) = x`, no shorter string does), against Lean's `Float.Model` | Go `strconv.FormatFloat(x, 'g', -1, 64)`, `ParseFloat` | medium | P2 |
| `x/net/html` | sanitizing HTML from elsewhere | WHATWG HTML §13.2 (tokenizer, tree construction) | html5lib-tests; Go x/net/html | large | P2 |
| `x/net/publicsuffix` | cookie domains; showing a link's registrable domain | the Public Suffix List's algorithm | the list's `test_psl.txt`; Go x/net/publicsuffix | small | P2 |
| `x/net/websocket` | two-way live features | RFC 6455 framing as a pure reader and writer; needs SHA-1 (c) and base64 | Autobahn TestSuite; Go x/net/websocket | medium | P2 |

## Plan

### P0, in build order

Each step depends only on steps above it and on what Lanes has.

1. **Base64**: done, `Lanes/Lib/Encoding/Base64.lean`.
2. **IP addresses**: done, `Lanes/Lib/Net/Ip.lean`. Replaces `Std.Net.IPv4Addr.ofString` where a
   decision rests on it.
3. **URLs**: done, `Lanes/Lib/Net/Url.lean`, with host literals from 2 and percent decoding from
   `Lanes/Web/Http/Basic.lean`.
4. **Media types**: done, `Lanes/Lib/Mime/MediaType.lean`. Its RFC 9110 `token` and
   `quoted-string` grammar is its own; `Lanes.Web.Http.Cookie` and `Lanes.Web.Http.Wire` should share it.
5. **Time formats**: done, `Lanes/Lib/Time/Format.lean`, on `Lanes/Lib/Time/Civil.lean`.
6. **Rate limits**: the bucket is done, `Lanes/Lib/RateLimit.lean`. Still to build: a table
   of buckets per key (an address from 2, a user) in a `Std.TreeMap`, with buckets that are full
   dropped so the table stays bounded.
7. **`fsync`**: done (D46), in `native/lanes.c`, used by `Lanes/Durable/IO/Journal.lean`.
8. **libsodium**: done (D46): Argon2id for `Password.digest`, `sodium_memcmp` for `Bytes.same`,
   `randombytes_buf`, SHA-256 and HMAC-SHA-256.
9. **TLS and names in the HTTP client**: done (D67), with the OpenSSL that Lean's toolchain
   links, verifying against the system's roots with the host name checked, and `Std.Async.DNS`
   for names (`Lanes/Web/IO/Client.lean`, `Lanes/Web/IO/Tls.lean`).

What is left of 6 can go on a branch of its own. The (e) rows that decide and are not
yet proved come after: `Lanes.Json`'s round trip (oracles JSONTestSuite and Go `encoding/json`) and the cookie parser (Go
`http.ParseCookie`, `http.ParseSetCookie`).

### Differential tests against Go

- **Where.** A Go module in `oracles/go/` (`oracles/go/go.mod`, Go pinned like the Lean
  toolchain, `golang.org/x/time` and `github.com/prometheus/common` pinned in
  `oracles/go/go.sum`), with one small program per package, `oracles/go/<package>/main.go`, among
  the other references of `oracles/README.md`. The Lean side is `Tests/Oracle/<Package>.lean`,
  run by `lanesOracle` (`Tests/OracleMain.lean`; D50).
- **Protocol.** Lean generates cases from a seed and writes them as JSON lines,
  `{"id": 7, "op": "parse", "in": "<hex>"}`; inputs are hex so that invalid UTF-8 survives. The
  Go program reads every line from standard input and answers one line per case:
  `{"id": 7, "ok": true, "out": {…}}`, or `"ok": false` when it rejects the input. Only
  acceptance and the structured result are compared, never error messages. Lean runs its own
  function on the same cases, renders the result in the same shape with `Lanes.Json`, and
  compares.
- **Inputs.** Three sources: random strings over the alphabet the grammar cares about (for URLs,
  `:/?#[]@!$&'()*+,;=%`, letters, digits and some non-ASCII); values generated from the spec's
  grammar, then mutated by one edit; and the public suites (urltestdata, the RFCs' vectors,
  cases taken from Go's own `_test.go` tables), mutated. A disagreement prints the seed, the
  input and both answers, and is shrunk by deleting bytes while Go and Lean still disagree.
- **Known differences.** Where our spec departs from Go on purpose (Go's `url.Parse` accepts
  some inputs RFC 3986 rejects), the difference is a `known` predicate of the package's
  `Tests/Oracle/<Package>.lean` with a reason, and the comparison skips only the cases it
  matches. The rate limiter's cases use rates and times at which Go's float64 token count is
  exact (`Tests/Oracle/RateLimit.lean`), because ours is exact.
- **Without Go.** The first answers of each reference are recorded in
  `oracles/<reference>/answers.jsonl` and replayed by `lake test`, which never needs Go; static
  vectors (RFC test vectors, JSONTestSuite) are committed beside the tests that read them, with
  their source and licence.
- **In CI.** The job `oracle` of `.github/workflows/ci.yml` runs `lake exe lanesOracle --cases
  20000` at seed 0 and at the run's id as seed, which builds each program into `.lake/oracles/`.
  It fails on any difference no `known` predicate decides, printing the command that reproduces
  it.
- **Bindings.** For (c), the oracle is test vectors (Wycheproof, RFC 9106 for Argon2id) and, for
  TLS, a Go program that serves certificates it makes with `crypto/x509` (expired, wrong host,
  self-signed, unknown root, good) on local ports: the Lean client must refuse all but the good
  one.

## What Lean has and lacks, on this toolchain

- `Std` has an HTTP/1.1 **server** (`Std.Http`, sans-IO, with a pure redirect planner) but no
  client; TCP, UDP, DNS, timers, processes and signals (`Std.Async`); time with zones, a TZif
  reader and formats including `httpDate` (`Std.Time`); hash and tree maps with lemmas; and
  synchronisation (`Std.Sync`). It has no TLS, no regular expressions, no base64, no hash
  function beyond `hash64`, no compression, no Unicode tables beyond ASCII, and no `fsync`.
- What decides in `Std.Http` and `Std.Time` is unproved: the URI parser and the format modules
  have no theorems, and `Std.Time.Formats.rfc850` does not match its docstring. Proved code with
  a Go oracle would have caught that.
- `Lean.*` has a CommonMark parser (`Lean.Data.Markdown`, CommonMark 0.31.2, with Unicode
  punctuation and whitespace classes and case folding for ASCII, Latin-1 and Greek), HTML values
  with the table of character references (`Lean.Data.Html`), JSON and UTF-16 positions. None can
  be linked into an application binary without `Lean` (137 MB against about 5 MB, D15), so each
  is a port, as JSON was. Markdown for posts would
  be the next such port (P1).
- Core has a logical model of IEEE floats (`Float.Model`, binary32 and binary64), so float
  printing and parsing can be stated and proved against it.
- Address parsing in `Std.Net` and `IO.getRandomBytes` are C behind `@[extern]` (libuv's
  `inet_pton`, `/dev/urandom`).
