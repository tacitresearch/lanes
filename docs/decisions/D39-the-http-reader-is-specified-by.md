# D39. The HTTP reader is specified by writers, and its limit is on the response

`Response.read` was tested, not proved, and a statement of what it must do needed something to
say "a response a server sends". `Lanes/Http/WireSpec.lean` now has writers of responses
(`Response.wire`, `wireChunked`, `wireToEnd`, `wireAfter`), in the library rather than the
tests because they are the specification the theorems in `Lanes/Http/WireSound.lean` are stated
against, and in a file of their own because no adapter runs them, so they are not trusted: the reader reads back what they write, at the last byte and not before. They write one
form of each framing; the other forms a server may use (a reason phrase, leading zeros, chunk
extensions, trailers) stay tested only, in `TRUSTED.md`.

Stating the round trip "whatever follows the response" showed that it was false: the reader
refused everything once more than `limit` bytes had arrived, so a whole response followed by a
few bytes of the next one, or of garbage, was refused when together they passed the limit. The
limit now applies to the bytes the response takes up (`readFrom` reports where it ends). What
it bounds is unchanged: the reader asks for more only while at most `limit` bytes have arrived
(`Response.read_more`), and a response it gives, its body included, ends within `limit` bytes
(`Response.read_some`). The same statement for the head showed that the reader took a status
line with a bare CR in its reason, which RFC 9112, 2.2 forbids; such a line is now refused.

The reader was restructured for the proofs and not otherwise changed: the head is split into
lines and parsed over lists of characters, the end of a chunk's size line is its own function,
and the reader reports where a response ends. That a strict start of a whole response waits is
not proved for each writer: what the reader makes of the first `n` bytes is that it needs more,
or what it makes of all of them (`readFrom_extract`), and an answer from `n` bytes ends within
them.
