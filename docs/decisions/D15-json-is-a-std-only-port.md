# D15. JSON is a `Std`-only port of `Lean.Data.Json`

`Lanes.Json` (`Lanes/Data/Json/`) is the value type, parser, printers and `ToJson`/`FromJson`
classes of Lean core, ported so that nothing imports `Lean`. It differs from the original in
four ways:

- **Total.** No `partial`. The parser is written directly over the positions of the input
  (`s.Pos`) and not in `Std.Internal.Parsec`, whose results do not record that the position
  advanced; each function returns a proof of that, and recursion is on the bytes left to read.
- **Canonical values.** A `JsonNumber` carries a proof that it has no trailing fractional zero,
  and an object is an array of fields sorted by key (built by `Json.mkObj` or the parser), where
  the original uses `Std.TreeMap.Raw`. Structural equality is then equality of documents, so
  `Json` has `DecidableEq` and a `Hashable` that agrees with it, and printed key order is fixed.
- **Bounded.** `Json.parse` takes `maxDepth` (default 128) and `maxDigits` (default 1000, for
  both the digits of a number and its exponent) and rejects input beyond them.
- **Strict.** An unpaired `\u` surrogate is an error, not U+FFFD.

There is no `deriving` handler (it needs `Lean` meta code); instances for structures are written
by hand. `LawfulJson` states that an encoding loses nothing.

Why: any `import Lean` takes a compiled binary from about 5 MB to about 137 MB, and runtime
modules must stay small (design decision 5). Canonical values make `Json` usable in actor
messages and states, which the model checker compares and hashes (D8).

Measured again on 2026-11-27 for the module system's `meta import`: a library that does
`public meta import Lean`, imported by an application either way, still gives a 137 MB binary,
because Lake links it. So sugar for applications (a declaration that defines a type together
with its codec, or a system together with its signature and instances) has to be a macro, which
needs only `Init` and sees the declaration's syntax, not a deriving handler or an elaborator.
