# D?. CBOR is the standard binary encoding, derived by `lanes_data` as JSON is

Status: Accepted

`docs/decisions/D115-serialization.md` left a type two ways out of the process, JSON and rows,
and removed the binary codec `lanes_data` derived: it was a format of our own, for the journal.
Issue #234 asks for a standard binary encoding: one other languages read, compact, with no
schema, for messages between processes, cache values, files and logs (a Raft log, for one), and
for the formats built on it, COSE and WebAuthn among them. The owner chose CBOR (RFC 8949).

## What there is

`Lanes/Lib/Encoding/Cbor/`, laid out as the JSON library is:

- `Lanes.Cbor`, the data model of §2: `uint n` and `nint n` (`-1 - n`), each with a 64-bit
  argument; byte and text strings; arrays and maps as lists, a map keeping its order; tags; the
  simple values, with `false`, `true`, `null` and `undefined` named and the others a byte that is
  not 20 to 31; floats.
- `Cbor.encode`, the preferred serialization of §4.1, and `Cbor.encodeDeterministic`, the
  deterministic encoding of §4.2.1: the preferred serialization of `canonical v`, which is `v`
  with every map's entries sorted by their bytes.
- `Cbor.decode`, with a `Config` of limits (depth, the length of a string, an array or a map, the
  whole input), checked as it reads, and `accept`: any well-formed encoding, only the preferred
  one, or only the deterministic one. It refuses what Appendix F calls not well-formed, text that
  is not UTF-8, and bytes after the item.
- `ToCbor`, `FromCbor`, `LawfulCbor` and `NonNullCbor`, with instances for the basic types, and
  `deriving ToCbor, FromCbor` in `lanes_data`.

## Choices

**A float is its binary64 bits, and the encoder chooses the width.** The data model does not tell
a half from a double of the same value (§2), and the preferred serialization writes the shortest
width that holds the value exactly (§4.1). So a value holds no width: a half or a single read is
widened to the double it holds, and the encoder narrows it again only when narrowing loses
nothing. Narrowing is checked by widening back (`Cbor.toHalf?`), so the round trip needs no
proof about the arithmetic of floats; that the narrowing finds the shortest width is tested, every
half and many singles against the machine's own conversion, and the bytes against cbor2.

**The strict decoders compare with the encoder.** `accept := .preferred` reads as the lenient
decoder does, then writes what it read and takes the input only if it is those bytes; likewise
`.deterministic`. A check in each branch of the decoder would give a finer error but a second
definition of the preferred serialization to keep in step with the encoder; the comparison makes
each value's accepted encoding unique by construction (`Cbor.eq_of_decode_strict`), at the cost
of writing the value once more. A COSE signature or a hash over a value needs exactly that
property.

**The deterministic order sorts an entry's bytes, its key's then its value's.** An item's
encoding never starts another's, so this is the order of the keys that §4.2.1 asks for, and
entries with equal keys, which a valid map does not have, still get one order. The canonicity
theorem (`Cbor.encodeDeterministic_eq_of_equiv`) then needs no premise that keys are distinct.

**Duplicate keys are not refused.** §5.6 makes a map with a key twice invalid, not malformed, and
refusing it costs a comparison of keys per map. The decoder keeps both entries and a derived
reader takes a field's first. An application that needs them refused, as COSE's headers do,
checks its map; a check in the decoder is a later option.

**A derived type has its JSON's shape.** A structure is a map with a text key per field, named as
the field is and in the order of the fields, a field encoded as `null` left out; a constructor is
its name as text, or a map of one entry, its name, holding the map of its arguments. Integer keys
would be more compact, but names are what the code uses and what a reader in another language
sees, and the two formats agreeing means one description of a type serves both (`Tests/Cbor.lean`
checks it). `Nat` and `Int` past 64 bits are bignums (tags 2 and 3, §3.4.3).

**One derive for both formats.** The pieces that carry the laws, `Fields` and `Alts`
(`Lanes/Lib/Encoding/Fields.lean`), do not depend on the values they write, and the JSON derive
now uses them too; a format adds its field, its object and its tagging. In `lanes_data`,
`Declare.Format` names a format's classes and pieces, and the code that builds a codec from a
declaration is the same for JSON and CBOR. The only proof per type stays `decide` on distinct
names.

**What it costs.** Six modules, the proofs in one of them, all total and nothing trusted: no
`extern`, no `partial`, no IO (the byte comparisons the deterministic order uses are core Lean's). The module
is not in `import Lanes`; it is a root of the library of its own (`lakefile.lean`), so a program
that does not import `Lanes.Lib.Encoding.Cbor` neither builds nor links it. `lanes_data` only
names the CBOR pieces when asked to derive them. It forces nothing on the rest of the library:
reach (a format that most languages and devices read) against a cost paid by those who import it
(rule 1.8).

## Evidence

- Proved: `Cbor.decode_encode` (what is written reads back, for every value within the limits),
  `Cbor.decode_encodeDeterministic`, `Cbor.encodeDeterministic_eq_of_equiv`,
  `Cbor.eq_of_decode_strict`, `Cbor.fits_of_decode` and `Cbor.decode_tooLarge`
  (`Lanes/Lib/Encoding/Cbor/Sound.lean`), and the laws of the derived and the basic instances.
- Tested: RFC 8949's Appendix A, written and read, and Appendix F, refused; random values through
  every mode; `Tests/Cbor.lean`.
- Compared: Python's cbor2 on generated inputs (`oracles/cbor2`, `Tests/Oracle/Cbor.lean`). Its
  known differences: its canonical order is RFC 7049's, shorter keys first; it writes every NaN
  as `f97e00`; it refuses a map with keys Python counts equal, such as `true` and `1`.

## Limits

- A recursive type has no derived CBOR, as it has no derived JSON.
- A value cannot ask for a float's width: the encoder writes the shortest.
- Tags are kept, not read: a bignum is `tag 2` holding bytes until `FromCbor Nat` reads it, and
  the decoder does not check what a tag holds.
- No duplicate keys are refused, and the decoder reads one item, not a sequence (RFC 8742).
