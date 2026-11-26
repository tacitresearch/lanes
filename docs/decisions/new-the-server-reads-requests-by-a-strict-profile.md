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
- **A tab in a `Content-Length` or `Transfer-Encoding` line**, `chunked\t` and `\tchunked`
  among them. RFC 9110, 5.5 lets a tab stand for a blank around a value; Node's parser refuses
  `chunked\t` and Go's reads it as `chunked`, so a proxy and a backend can disagree on it. Spaces
  around those values are read.
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

The reader is total (no `partial`), and these are proved (`Lanes/Http/ReadRequestSound.lean`,
every one on the standard axioms alone, `Tests/Axioms/Http.lean`):

- *Answers stay.* What the reader makes of the first `n` bytes is that it needs more, or what
  it makes of all of them (`Request.read_extract`); an answer given stays whatever arrives after
  it (`Request.read_append`).
- *Limits.* It asks for more only while fewer than `message_max` bytes have arrived from where
  it starts (`Request.read_more`); a request it gives ends after where it starts, within the
  bytes given and within `message_max` of where it starts, with a body of at most `body_max`
  bytes (`Request.read_done`). `message_max` is `max (line_max + 2) head_max + body_max + 20 *
  (chunks_max + 1)`.
- *Round trip.* What `Request.wire` writes of a request within the limits (`Request.fits`: the
  request line, the head, the fields and the body within theirs, a host of host characters, and
  a path other than `[""]`, which is written `/` like the empty path) is read back as that
  request, names in lowercase and blanks around values left out (`Request.sent`), wherever it
  starts in the buffer and whatever follows it (`Request.read_wire`), so pipelined requests are
  read in turn; every strict start of it needs more (`Request.read_wire_extract`), which is
  what reading it in any split amounts to.
- *Smuggling shapes*, for a head written as lines (`Request.headWire`), each line not empty and
  none with an LF, and whatever follows the head: a `Content-Length` beside a
  `Transfer-Encoding`, in either order, with any values and blanks around the names
  (`read_lengthAndCoding`); two `Content-Length` fields (`read_twoLengths`); a blank before the
  first colon of a field line (`read_blankInName`) and a field line that starts with a blank
  (`read_fold`); a CR in a line (`read_bareCR`); and, for lines none of which has a CR, an LF in a
  line (`read_bareLF`): each is refused, never read and never waited on. A chunk whose size line,
  up to its CR, is not one to sixteen hex digits is refused (`read_badChunkSize`), extensions and
  blanks among them. These rest on `Request.readHead_headWire`, that such a head is read as its
  lines, and `Request.parseHead_clean`, that a head the reader takes has neither CR nor LF in a
  line.

Tested, not proved (`Tests/ReadRequest.lean`, `Tests/ReadRequest.corpus`): which status each
refusal gets beyond 414 and 431 for a head over its limits; the refusals of the request line, the
target, `Host`, a tab in a framing field, a length that is not digits, a coding other than
`chunked`, chunk data without its CRLF and a trailer; what the reader makes of forms
`Request.wire` does not write (a chunked body, `HEAD`, HTTP/1.0, no blank after a colon, leading
zeros, `+` in a query); that every start of each case of the corpus reads as needing more or as
the whole; and each limit at its edge.

## Against other parsers

`scripts/requests.py` puts the corpus to Go 1.24's `net/http`, Node 22's `http` (llhttp, not
lenient) and h11 0.16. No disagreement is looser: where the reader reads a request, every other
parser reads the same one, with the same method and body length. It is stricter on 132 verdicts
out of 390, all decided above: the target's characters and escapes, the absolute and asterisk
forms, unknown methods (Go and h11 read `FOO` and lowercase `get`), HTTP/1.2 and 2.0, `Host`
(Node reads two hosts and hosts with blanks), obs-fold and bare LF (Go and h11 read both),
CL.TE and TE.CL (Go and h11 read the coding), two equal lengths, a tab around a framing value,
chunk extensions and trailers (all three read them), a chunk size with a trailing blank (Go and
h11 read it), seventeen digits (Node and h11), a coding in HTTP/1.0 (all three), and the limits.
The others refuse with another status 22 times: Go and h11 answer 501 to a coding that does
not end in `chunked`, where RFC 9112, 6.1 says 400; Node answers 400 where the reader answers
501, 505, 413 or 414. Five times the others refuse a request cut short when the connection ends,
where the reader waits; the socket loop closes such a connection. One disagreement comes from
how Node is driven (it drops its answer to a request when its parser fails on the next one in
the same packet) and is listed in the script.
