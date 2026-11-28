# D120. Compression in pure Lean, logs in the lowest package, forms read strictly

Status: Accepted

Three pieces of the standard library came together (issues #233 and #234): `multipart/form-data`,
structured logs and compression. Each needed a choice that shapes what comes after it.

## Compression is pure Lean, not a binding of zlib

DEFLATE, gzip and zlib's format are in `Lanes/Lib/Compress/`, in Lean, with nothing trusted.

Weighed by rule 1.8:

- **Reach.** Both choices give the same reach: gzip responses for clients that take them,
  responses in gzip or `deflate` read by the client, and a library apps call for files and
  caches.
- **Cost.** A binding of zlib would be about a hundred lines of C, a row in `TRUSTED.md`, zlib's
  headers on every machine that builds an application (CI, macOS, the generated apps), and a C
  library parsing the bytes an attacker sends. A pure inflate is about three hundred lines whose
  decisions are Lean's, total, with a theorem that bounds its output
  (`Inflate.size_le`). Rule 2.7 binds only what Lean cannot express; compression is not that.
- **Where the bugs are.** Decompression reads untrusted input; that is the part to have in Lean.
  It is compared with Go's `compress/flate`, `gzip` and `zlib` on streams our encoder writes, on
  dynamic blocks with codes made at random, and on those edited a byte at a time
  (`Tests/Oracle/Compress.lean`).
- **What is given up.** The encoder writes one block with the fixed Huffman code and greedy
  matches, so text comes out larger than zlib's fastest level writes it, still a small fraction
  of the text. An encoder with codes of its own per block is a later change inside
  `Lanes.Deflate`, which already writes a block with any code (`Deflate.canonical`,
  `Deflate.block`).

The server compresses only when `ServerConfig.compression` is set: a compressed page that holds
a secret and text an attacker chose leaks the secret through its size (BREACH), so it is turned
on knowingly. The client asks for gzip and decodes it by default, as Go's does, unless the
request names its own `Accept-Encoding`.

## Logs are in the lowest package

A record renders as one line of JSON in `slog`'s order (`Lanes/Lib/Log.lean`), and the runtime's
shell, which is below the standard library (D99), reports its own faults through the logger. So
the logger, and the JSON printer and the time format it renders with, are in the package of the
semantics and the checker (`LanesCli/Layers.lean`): `Lanes/Lib/Log.lean`,
`Lanes/Lib/Encoding/Json/{Basic,Printer}.lean`, `Lanes/Lib/Encoding/Digits.lean` and
`Lanes/Lib/Time/{Civil,Format}.lean`. They import only `Std` and each other; nothing moves on disk.
The alternative, a function the runtime is given to report with, would leave the runtime's lines
unlike every other log line. The IO that writes a line is `Lanes/Runtime/IO/Log.lean`.

The access log is now a log record: it gained `level` and `msg` before its fields, and keeps its
fields and their order.

## Forms are read as RFC 2046 and RFC 7578 say

`Multipart.parse` refuses what RFC 2046 forbids where Go's `mime/multipart` takes it: a body
with no delimiter (Go reads no parts), a delimiter not on a line of its own, a bare line feed
for CR LF, a header name that is no token, a folded header line, a header that is not UTF-8, and
a body that ends after a delimiter with no last delimiter (Go reads the parts before it). Each
is a decided difference of the oracle (`Tests/Oracle/Multipart.lean`). Browsers write none of
them. A parser that refuses is one whose theorem says what it reads (`Multipart.parse_write`);
one that guesses would need a spec of its guesses.
