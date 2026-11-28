# D122. CSV, paths, an HTML sanitizer and WebSockets in the standard library

Status: Accepted

Issues #233 and #234 list what people building software in Lean reach for and Lanes lacks. This
decision adds four of them (#194, #199, #216 and the codec of #219): CSV
(`Lanes/Lib/Encoding/Csv.lean`), paths and globs (`Lanes/Lib/Path.lean`, `Lanes/Lib/Glob.lean`),
character references and a sanitizer of HTML (`Lanes/Web/Html/Unescape.lean`,
`Lanes/Web/Html/Sanitize.lean`), and WebSockets (`Lanes/Web/Http/WebSocket.lean`). It records the
choices that are not in the code.

## Each is a root of its own

As CBOR is (`docs/decisions/D118-cbor.md`), each piece is a root of the library in
`lakefile.lean` and not in `import Lanes`: a program imports the one it uses, and one that uses
none builds and links none of them. So the cost to people who never use them is a line in the
lakefile and the time CI takes. A piece moves into `import Lanes` when the core needs it, as a
file server would need `Path.under`.

## What is proved, and where the proof stands

- CSV: `Csv.parse_write`, the round trip, for every table within the limits and every dialect.
  The reader is a state machine fed a character at a time, so a file can be read in pieces and its
  records taken as they come; the proof is about that machine, not a second reader.
- Paths: `Path.clean_clean` and `Path.under_names`. `under` refuses a request whose `..` would
  climb out of its root rather than clamping it as Go's `http.Dir` does: a request that tries is
  an attack or a bug, and answering it with another file hides both.
- The sanitizer: `Html.sanitize_safe` is proved of its last step, `Sanitize.prune`, which keeps
  only what the policy allows whatever tree it is given, and through the browser model of
  `Html.lex_render`. So the tokenizer and the tree builder before it, which are where
  sanitizers' bugs usually are, are outside the proof: they can lose text, never let markup in.
  Whatever the policy, elements whose content a browser runs or parses by other rules
  (`Sanitize.dropped`, SVG and MathML among them) and `on…`, `style` and `srcset` are never kept,
  so a policy cannot open the holes that mutation attacks use.
- WebSockets: `WebSocket.decode_encode`, the frame codec's round trip.

## Agreeing with a reference, and where we do not

Each is compared with a reference on generated inputs (`oracles/README.md` lists every known
difference). Three are choices:

- CSV keeps a CRLF inside a quoted field, where Go turns it into LF: RFC 4180 lets a field hold
  CRLF, and a reader that changes a field cannot read back what was written.
- A `**` that is a whole name of a glob matches across `/`, as `.gitignore` and build tools read
  it; Go's `path.Match` reads it as `*`. A pattern without such a name matches as Go's does.
- The WebSocket decoder checks what is wrong with a frame in the order websockets checks it, and
  reads a length not written in the fewest bytes, as browsers and websockets read it: the RFC
  binds the sender, and refusing would only make Lanes the one peer that fails.

## Not done

The server does not hand an upgraded connection to `WebSocket.Conn`: that is a change to
`Http.Conn` and the gate (how messages reach the system and leave it), which is a design of its
own. A WebSocket client is not here either. SMTP (#215) is not here.
