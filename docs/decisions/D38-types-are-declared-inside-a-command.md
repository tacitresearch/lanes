# D38. Types are declared inside a command that derives what Lean's handlers cannot

Status: Accepted

Around Raft's one actor stood a codec for each of its eight types, written field by field
beside the declaration, and a `BEq` with its law written by hand for the node, whose machine
may be a function. Lean derives instances with handlers that run in the elaborator, and an
application that imports `Lean` to run one of its own links it, 137 MB even through
`meta import` (D15). A macro sees syntax only, so it cannot read the fields of a type declared
elsewhere. So the declaration is
written inside the command: `lanes_data structure …` and `lanes_data inductive …` expand to the
ordinary declaration, pass the classes Lean knows to `deriving instance`, and derive three
themselves from the text of the fields and constructors.

- `Codable`, a class beside the structure `Codec`. `Codec` stays a value that journals,
  snapshots and transports are given; the class lets a derived codec find each field's by its
  type, and has instances for the built-in types, `Fin n`, `Option`, `List`, pairs, sums,
  sigma types and `Std.ExtTreeMap`. `T.codec` takes a codec for each type parameter, so
  `Request.codec Codec.fin` still reads as it did, and the instance applies it to the
  parameters' instances. The codec is the one `Codec.struct%` or `Codec.sum%` builds, with the
  same field codecs a person wrote, so the law holds by construction and the records are the
  same: journals and snapshots of raft-kv and the bank read as before. Raft's node, messages and
  answers were compared with the hand-written codecs, and `Tests/Codec.lean` compares one on
  every run.
- `Enum`, through a nested sum of products of the constructors' arguments, listed and mapped
  back.
- `LawfulBEq`, for a structure: `==` field by field, and its law. Lean's own
  `deriving BEq, ReflBEq, LawfulBEq` asks `BEq` of every type parameter, and so of `Entry N C`
  inside the node's log, which then needs a derived `BEq` of its own beside the one
  `DecidableEq` gives. The command asks `BEq` (and `LawfulBEq`) only of a parameter that is a
  field's whole type and appears in no other, and `DecidableEq` of the rest, which is the
  context the node's hand-written instance had.

The command accepts fields `x : T` and `x : T := default` and arguments `(x y : T)`, with
docstrings; a type with `extends`, indices or recursion is declared as usual and given a codec
with the macros. Errors in what it derives are reported on the command, not on a field.

The ledger met four gaps, and each closed without `Lean`. A constructor is read with
`rawIdent`, as `inductive` reads one, so `| open` is accepted and `Op.open` is named. The
derived codecs and `Enum` bound each argument to its own name, so an argument named like its
constructor (`| ask (ask : Ask C)`) was read in the pattern as the constructor, which a macro
cannot see is a constant; they now bind names with a macro scope, which no constant has.
Default values pass through to the structure and change nothing derived, since a codec writes
every field. A value with a property is a subtype (`{s : String // valid s}`): `Codec.subtype`
writes the value and reads it back only if the property is decided true, and `Enum` filters;
`DecidableEq`, `Hashable` and `Repr` come from Lean's instances for `Subtype`. A field that is
a proof about an earlier field, as the ledger's `Name` had, is the one form left out: a macro
cannot tell whether a name in a type is an earlier field or a constant, and a field-by-field
codec has nothing to write for a proof. The command finds a field's name in a later field's
type by text and refuses it, with an error that names the field and says to use a subtype; it
refuses only when it derives one of its own classes, so `deriving DecidableEq` alone still
passes the structure to Lean. `lanesTest` grew by 37 KB, all of it the new tests; its other
code and `bankWeb` are 64 bytes smaller, and neither links `Lean`.

Instances defined by cases on an identity, for systems whose actors have different messages or
states, were a `match` with `inferInstanceAs` per class and per identity. The tactic
`instance_by_cases` introduces the identity, takes it apart where instance search fails, and
fills `Signature.Inspect` and `System.Inspect` the same way.

In the examples, tests, the template and raft-kv, 144 lines of codecs, `BEq`, `Enum` and
per-identity instances became 16. `raftNode` grew by 3 KB, `bankWeb` by 3 KB, and `lanes` is
unchanged. Not done: a system's `Inspect` still takes one line for its signature and one for
itself (a macro cannot name the signature of a system with parameters), and Raft's effects are
still annotated `(N := N) (C := C) (R := R)`, because `Eff` takes the node's identity only.
