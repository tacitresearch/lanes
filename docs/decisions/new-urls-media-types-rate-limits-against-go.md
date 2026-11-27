# D?. URLs, media types and rate limits against Go, and where they depart from it

D50's pattern, applied to three more packages of `docs/STDLIB.md`'s P0: `Lanes.Url`
(`Lanes/Http/Url.lean`, RFC 3986) against `net/url`, `Lanes.MediaType`
(`Lanes/Http/MediaType.lean`, RFC 9110 §8.3.1) against `mime.ParseMediaType`, and
`Lanes.RateLimit` (`Lanes/Data/RateLimit.lean`) against `golang.org/x/time/rate`, pinned in
`oracle/go.mod`. Each departure is a `known` predicate in `Tests/Oracle/Url.lean`,
`Tests/Oracle/MediaType.lean` or `Tests/Oracle/RateLimit.lean`; most check that ours, given the
input written our way, answers as Go did.

**Results on 100,000 cases each (seed 0).** URLs: 75,905 agree, 24,095 known, none other. Media
types: 63,132 agree, 36,868 known, none other. Rate limits: 100,000 agree. About a quarter of
the URL cases and a third of the media type cases are mutated or random text, which is where
the two standards and Go part.

**URLs.** A URL keeps each component as written, percent-encoded, and the host as an
`Ip.Addr` or a registered name, so that a decision about a host never reads text twice.

- *Go accepts more.* Go's `url.Parse` takes characters RFC 3986 does not allow where they stand
  (spaces, non-ASCII, `[`, `]`, `"`, `{` in a path, a query or a fragment; `@` in a userinfo; `:`
  in a registered name), a `%` that starts no escape in a query, brackets around anything, and
  zones. Ours refuses them, as RFC 3986 §2 and §3 do; it reads RFC 6874 zones no more than
  `Lanes.Ip` does, and no IPvFuture literal, which no browser reads either.
- *Go refuses more.* Go refuses `%41` in a host ("only non-ASCII may be escaped"); §3.2.2 allows
  any escape in a registered name, and so does the WHATWG standard.
- *What Go's `URL` cannot hold.* An empty fragment (`a#`), an empty authority before an empty
  path (`http://`), `///` without a scheme (Go reads a path). Ours keeps the first two; the
  comparison drops them before comparing.
- *Resolution.* Ours is §5.2.2, strict, against an absolute base (§5.1). Go also resolves
  against a relative base; keeps the base's fragment for an empty reference (§5.2.2 takes the
  reference's); drops the base's empty query; removes the base's dot segments for an empty
  reference (§5.2.2 keeps the base's path as it is, so `Url.dotFree_resolve` assumes a base
  without them); reads a base with no authority and a rootless path as "opaque" and resolves
  against it as if its path were `/`, writing an empty authority; and writes a result whose path
  starts with `//` with one `/`. Ours writes such a path after no authority as `/.//`, as the
  WHATWG standard does, so that it does not read back as an authority.
- *Printing.* Go writes an IP literal as it was written, a userinfo and a host re-encoded from
  their bytes, and a path that decodes to `*` as `*`; ours writes an address as RFC 5952 does
  and the rest as it was read.

**Media types.** The type, subtype and names are kept in lowercase, a name occurs once (RFC 6838
§4.3), and a field value has no whitespace at its ends (RFC 9110 §5.5).

- Go reads a type without a subtype (a `Content-Disposition` value), whitespace around `=` and
  at the ends, `\n`, `\r`, `\v` and `\f` as whitespace, controls in a quoted string, `{` and `}`
  in tokens, a name repeated with the same value, and RFC 2231 names (`title*=...`, which RFC
  9110 media types do not have). It keeps a backslash before a character that is not one of its
  "tspecials", as MSIE wrote paths; §5.6.4 drops it. Ours follows RFC 9110 in each.
- RFC 9110 §5.6.6 allows empty parameters (`a/b;;c=d`); Go allows only one trailing `;`.
- Go's `FormatMediaType` writes a value that is not ASCII in RFC 2231 form; ours writes it in a
  quoted string, as `obs-text`.

**Rate limits.** The spec is exact: credit in units of `1 / period_ms` of a token, time in
milliseconds. Go's limiter counts tokens in a float64, so the cases use rates of 1/8 to 8 a
second, powers of two, and times that are multiples of 125 ms, at which every token count and
every delay Go computes is exact; at those, there is no difference.
