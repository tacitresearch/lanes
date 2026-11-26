# D?. The server reads requests by a strict profile, and every refusal closes the connection

The server is to read HTTP/1.1 itself, on `Std.Net`, so that what it accepts is decided by a
proved reader rather than by `Std.Http`. Request smuggling lives in the gap between two parsers
that frame the same bytes differently: a proxy that reads `Transfer-Encoding` and a backend that
reads `Content-Length` (CL.TE, TE.CL), one that recognises `Transfer-Encoding: xchunked` or a
folded line and one that does not (TE.TE), one that ends a line at a bare LF and one that does
not. A backend cannot know which proxy is in front of it, so its defence is to accept only bytes
that every reasonable parser frames the same way, and to refuse the rest. RFC 9112 leaves many
of these choices to the recipient ("MAY", "either reject or replace"); the reader takes the
rejecting branch each time. Stricter than RFC 9112 is allowed; looser is a bug.

`Request.read limits bytes pos` (`Lanes/Http/ReadRequest.lean`) looks at the bytes from `pos` and
answers one of three things: it needs more; here is a request and the index just after it; or
refuse with a status. A refusal is final: the server answers it and closes the connection,
since after bytes it cannot frame it cannot know where the next request starts. After a request,
the next one is read from the index it ended at, so pipelined requests in one buffer are read in
turn.

## Accepted

- A request line `method SP target SP version CRLF`, with exactly one space between the parts.
- Methods `GET`, `HEAD`, `POST`, `PUT`, `PATCH`, `DELETE`, in capitals (methods are case
  sensitive). `HEAD` is read as `GET` with a flag, as the server answers it today.
- A target in origin form: `/`, then the characters RFC 3986 allows in a path (unreserved,
  sub-delims, `:`, `@`, `/`, and `%` with two hex digits), then optionally `?` and a query of
  those characters and `?`. Path segments and query pairs are percent-decoded and must give
  UTF-8; `+` is a space in the query and a `+` in the path. `/` is the empty path; `a=1&b` gives
  `("a","1")` and `("b","")`; an empty query is no pairs.
- Versions `HTTP/1.1` and `HTTP/1.0`.
- Field lines `name ":" OWS value OWS CRLF`: the name a token, the value any characters but
  controls other than tab (so UTF-8 is allowed; the head must be UTF-8). Names are given in
  lowercase and values without the blanks around them, in the order received.
- One `Host` field, required in HTTP/1.1 (RFC 9112, 3.2), its value non-empty and made of the
  characters of an RFC 3986 host and port.
- Framing (RFC 9112, 6.3), decided from the head alone: one `Content-Length` of one to eighteen
  digits; or one `Transfer-Encoding` whose value is `chunked` (any case), in HTTP/1.1; or neither,
  which is a body of length zero.
- A chunked body of chunks `1*16HEXDIG CRLF data CRLF`, ended by a chunk of size zero and a
  CRLF. The body is the chunks put together.
- `Connection: close`, or HTTP/1.0, says the connection ends after the response. `Expect:
  100-continue` is reported with the head, so that the socket loop can answer `100 Continue`.

## Refused, and with what

| Bytes | Status | Why |
| --- | --- | --- |
| A request line longer than `line_max` (8192) bytes | 414 | RFC 9112, 3; decided as soon as `line_max + 2` bytes have no CRLF |
| A head longer than `head_max` (16384) bytes, or more than `fields_max` (100) fields | 431 | RFC 6585 |
| A `Content-Length` above `body_max` (1 MiB), a chunked body that grows above it, or more than `chunks_max` (4096) chunks | 413 | Decided from the length or the size line, before the data arrives |
| A method that is a token but not one of the six | 501 | RFC 9110, 9.1 |
| A version `HTTP/d.d` other than 1.0 and 1.1 | 505 | Stricter than RFC 9110, 2.5, which would read `HTTP/1.2` as 1.1 |
| A `Transfer-Encoding` that ends in `chunked` after another coding (`gzip, chunked`) | 501 | RFC 9112, 6.1: a coding not understood |
| Everything else below | 400 | |

Refused with 400:

- **CL.TE**: both `Content-Length` and `Transfer-Encoding` (RFC 9112, 6.1 allows either refusing
  or reading the coding; refusing removes the choice).
- **Two `Content-Length` fields**, alike or not, and a list `5, 5` (RFC 9110, 8.6 allows reading
  alike values as one); a length that is not one to eighteen digits (`+5`, `0x5`, `5 5`).
- **TE.TE**: any `Transfer-Encoding` other than one field `chunked`: `xchunked`, `chunked, x`,
  `chunked` twice or in two fields, an empty value, a coding whose last element is not chunked
  (RFC 9112, 6.1 says 400 for that one), and any `Transfer-Encoding` in HTTP/1.0 (RFC 9112, 6.1).
- **Obsolete line folding**: a field line that starts with a space or a tab, including the first
  one after the request line (RFC 9112, 2.2 and 5.2 allow replacing it with spaces instead).
- **Whitespace between a name and its colon** (RFC 9112, 5.1, a MUST), and any name that is not a
  token.
- **A bare LF** anywhere in the head, which some parsers take as the end of a line (RFC 9112, 2.2
  lets a recipient do so), and **a bare CR** (RFC 9112, 2.2 allows replacing it with a space). A
  NUL or another control character but tab in a value (RFC 9110, 5.5). A head that is not UTF-8.
- **A chunk size line that is not one to sixteen hex digits followed by CRLF**: blanks, a sign,
  `0x`, more than sixteen digits, a chunk extension (`5;a=b`), a bare LF. Chunk data not followed
  by CRLF. A trailer field after the last chunk.
- A request line with two spaces, a tab, or a part missing; a target in absolute form
  (`http://h/p`), authority form or `*`; a target with a character outside the set above
  (`"`, `<`, `>`, `\`, `^`, `` ` ``, `{`, `|`, `}`, `#`, a space, non-ASCII), a bad
  percent-escape, or escapes that do not decode to UTF-8.
- An empty line before the request line.
- No `Host` in HTTP/1.1, two `Host` fields, or a `Host` that is empty or has another character.

## Departures from RFC 9112, all toward refusing

- An empty line before the request line is refused; RFC 9112, 2.2 says a server SHOULD ignore
  at least one. Only HTTP/1.0 clients of the last century send one.
- Chunk extensions are refused; RFC 9112, 7.1.1 says a recipient MUST ignore unrecognised ones.
  Their grammar (quoted strings, blanks around `;` and `=`) is where parsers have been found to
  disagree (bare LF and quoted CRLF inside extensions), and no common client sends them.
- Trailer fields are refused; RFC 9112, 7.1.2 lets a recipient discard them. The same reason, and
  a chunked request with trailers is rare.
- The absolute form of a target is refused; RFC 9112, 3.2.2 says a server MUST accept it. A Lanes
  server is an origin server, which clients do not send that form to, and the form brings a
  second host (the target's) beside `Host`.
- `HTTP/1.2` and later minor versions are refused with 505 rather than read as 1.1.
- HTTP/1.0 connections always close after the response; `Connection: keep-alive` is not honoured.

## Limits

Every limit is a field of `Request.Limits` (rule 2.6), with the defaults above. Given a limit,
the reader never needs more than `head_max` bytes for the head, and the body it gives is at most
`body_max` bytes, framed in at most `chunks_max` chunks of at most sixteen hex digits each. The
reader asks for more only while fewer than that many bytes have arrived. A chunk count limit
exists because the framing of a chunked body is not bounded by its data: a body of one-byte
chunks takes six bytes on the wire for each byte of data.

## What is proved and what is tested

The reader is total (no `partial`), and these are proved (`Lanes/Http/ReadRequestSound.lean`):
what `Request.wire` writes is read back, at its last byte and not before, wherever it is in the
buffer and whatever follows it; an answer once given does not change as more bytes arrive; an
answer ends within the bytes given and within the limits; and each case of the smuggling list
above is refused, for every head of that shape. The differential test (`scripts/requests.py`)
compares the verdicts with Go's `net/http`, Python's `h11` and Node's `http` on a corpus, and is
tested, not proved.
