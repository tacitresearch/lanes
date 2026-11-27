### Data

Where: `Lanes/Data/`, `Lanes/Lib/`, `native/`, `oracles/`.

- All total and `Std`-only.
- Base64 (RFC 4648, each byte string with exactly one spelling: `Base64.decode_eq_some_iff`), compared with Go's standard library on generated cases (`lake exe lanesOracle`).
- Civil dates with day numbers and POSIX seconds (`Civil.ofDays_toDays`, `Civil.toDays_ofDays`).
- IP addresses and CIDR prefixes (RFC 4291 text forms, RFC 5952 output, `Ip.parse_print`, `Ip.Prefix.parse_print`, `Ip.Prefix.contains_iff`), compared with Go's standard library on generated cases.
- JSON (parser, printers, `ToJson`/`FromJson`; the parser accepts exactly RFC 8259's grammar within its limits, `Json.parse_iff`, and reads back what the printers write, `Json.parse_compress`; JSONTestSuite passes).
- Majority quorums (`Quorum.majority_inter`).
- Media types (RFC 9110 §8.3.1, `MediaType.parse_format`, case-insensitive by `MediaType.parse_format_eq`), compared with Go's standard library on generated cases.
- Metrics in the Prometheus text format, whose histograms' buckets count the observations at or below their bounds (`Metrics.Histogram.observeAll_eq`) and whose label values and help text a reader reads back as written (`Metrics.readLabelValue_escapeLabel`, `Metrics.readHelp_escapeHelp`), tested against text checked by hand and against Prometheus's `expfmt`, which parses what it writes.
- RFC 3339 and HTTP dates (`TimeFormat.parseRfc3339_print`, `TimeFormat.parseHttpDate_print`), compared with Go's standard library on generated cases.
- SHA-256, HMAC-SHA-256, the comparison of byte strings, and Argon2id from OpenSSL's libcrypto (`Native`, bound from `native/lanes.c`), secure random bytes from Lean's runtime, with SHA-256, HMAC-SHA-256 and the comparison also in pure Lean as references, both tested against the NIST and RFC 4231 vectors and compared on thousands of random inputs (`Bytes.same_iff`, `Bytes.unhex?_hex` proved).
- The token bucket of x/time/rate with exact arithmetic (`RateLimit.allowed_le`: at most `burst + rate · w` in a window of `w`; `RateLimit.allow_after_reserve`), compared with Go's on generated cases.
- URI references (RFC 3986: `Url.parse_print`, resolution as §5.2 with §5.4's examples evaluated and no dot segment left, `Url.dotFree_resolve`, idempotent normalization, `Url.normalize_normalize`), compared with Go's standard library on generated cases.
- `Codec` (records with a round-trip law, kept by pairs, sums, lists and maps; `Codec.struct%` and `Codec.sum%` write one for a structure or an inductive type in a line; `Codable` instances for the built-in types).
- `Enum`.
- `Frame` (length and checksum framing with the torn-write theorem).
- `lanes_data` (a structure or an inductive type declared once, deriving `Codable`, `Enum` and a field-by-field `LawfulBEq` from the declaration's text, without linking `Lean`).

Known limits:

- Base64 recurses once per four characters, so a very long input (megabytes) uses stack in proportion.
- IPv6 zones (`fe80::1%eth0`) are refused, also in URLs, and a leap second (`23:59:60`) is not a time.
- What `Lanes.Base64`, `Lanes.Ip` and `Lanes.TimeFormat` refuse is stated by theorems only for Base64 (`decode` accepts exactly the canonical text); for addresses and dates, that they refuse what Go refuses is tested, not proved, on the oracle's generated cases.
- What `Lanes.Url` and `Lanes.MediaType` refuse is tested against Go, not proved. A URL's IP literal is kept as an address and printed as RFC 5952 writes it, so `print (parse s)` is `s` only up to that; IPvFuture literals are refused. Rate limits have no table of buckets per key yet.
