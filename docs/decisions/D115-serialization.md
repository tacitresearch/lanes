# D115. `lanes_data` derives JSON and rows, each with its round trip; the binary codec goes

Status: Accepted

`docs/decisions/D110-volatile-actors.md` leaves a type two ways out of the process: JSON, for
HTTP, and rows, for the typed store of `docs/decisions/D111-typed-store.md`. The binary codec
`lanes_data` derived (`Codable`, D38) was for journal files and peers, which left main with the
journal. Nothing wrote a codec after that. This decision is issue #244: `lanes_data` derives
both mappings, each with its law, and the codec goes.

## JSON: `deriving ToJson, FromJson`

The two are derived together, with `LawfulJson` (`fromJson? (toJson a) = .ok a`) and
`NonNullJson` (`toJson a ≠ null`). A one-way encoder would be shorter, but the law is the point:
a client and a test can rely on reading back what the server writes.

**The shape** is that of Lean's own `deriving ToJson, FromJson`, so that it reads as people
who use Lean expect, and what Lean writes reads back here:

- a structure is an object with a field per Lean field, named as the field is (no renaming to
  `snake_case`: the name is the one the code uses, and a client in another language maps it);
- a constructor is externally tagged: its name, as a string, when it has no argument, else an
  object of one field, its name, holding the object of its arguments.

It differs from Lean's in one rule: a field whose value is encoded as `null` is left out, and a
missing field reads as `null`. Lean leaves out only a field whose name ends in `?`. The rule
makes `Option` fields optional on the wire, which is what HTTP clients send, and it makes the
law hold without a case per type: a key gives back what was written whether it was written or
left out. A constructor whose arguments are all left out is therefore written as its name, the
same as one with none. Externally tagged sums need no reserved field name, unlike a `"type"`
field inside the object, which would collide with an argument named `type`.

**The law, by construction.** A per-type proof by tactics would have to reason about the sorted,
deduplicated objects `Json.mkObj` builds, for every shape. Instead the command builds the
encoding from pieces that carry their laws, as the binary codec did
(`Lanes/Lib/Encoding/Json/Derive.lean`):

- `Json.Fields α`, an object's fields: `field`, `unit`, `pair`, `map`. Its law says that reading
  gives back the value when each key gives what was written; `Fields.readObject_object` proves
  that an object built by `mkObj`, with the `null` fields left out, does so when the keys are
  distinct.
- `Json.Alts α`, the constructors: `ctor`, `sum`, `map`. A sum reads by the tag, which needs
  the tags of its two sides apart.
- `Json.Codec.object` and `Json.Codec.ofAlts` make a `Json.Codec` (the two functions and the two
  laws), from which the four instances are made.

What is left per type is that its field names, and its constructor names, are distinct. The
command states that of a literal list of strings and proves it by `decide`, so no free variable
(a type parameter's instance) stops the decision. A type parameter is given `ToJson`,
`FromJson` and `LawfulJson`, and `NonNullJson` when a field's type mentions `Option`, since
`Option α` is lawful only when `α` is never `null`.

## Rows: a `table` line

`TableOf α` (D111) was written by hand: the table, `toRow`, `ofRow`, and the law. A structure
whose fields are column types now declares its table after `deriving`:

```lean
lanes_data structure Todo where
  id : Int64
  owner : Int64
  title : String
  done : Bool := false
  deriving DecidableEq, Repr
  table todos key id
    index byTitle on owner, title
```

This defines `todos : TableOf Todo` and `todos.byTitle : Db.Index`. A line, not an attribute or
a class: a table has a name the code uses (`todos.get`, `todos.scan`), a key, and indexes, which
a class instance found by type would hide, and a macro can read only the declaration it is
given (D38). The words `table`, `key`, `index`, `unique` and `on` are read as identifiers there
(`&"…"`), so no name elsewhere becomes a keyword.

- **Columns.** A field's type is a column through `Db.ColumnOf`: `Int64`, `ByteArray`, `String`
  and `Bool` (`Db.Scalar`), never `NULL`, and `Option` of one, nullable, `none` being `NULL`.
  `Int` and `Nat` have none: a column holds 64 bits, and a value that does not fit would not
  read back.
- **Order.** The primary key is a table's first columns (D111), so the columns are the key's
  fields, in the order the line gives, then the others in their order. Index positions are
  computed from that.
- **Names.** PostgreSQL's names are the Lean names in `snake_case` (`createdAt` is
  `created_at`), since D111 admits only lowercase identifiers. An index's name starts with its
  table's (`todos_by_title`), since PostgreSQL names indexes per schema. A string after a name
  gives another.
- **Laws.** `Db.Columns α` carries two: a value reads back from what it writes, followed by
  anything (`read_write`), and what reads back is what was written (`write_read`). The table
  `Columns.table` builds has the first as `TableOf.ofRow_toRow`, and the second as
  `Columns.toRow_of_ofRow`, which a proof about what a scan found needs: `examples/todo-db`'s
  `ofRow_eq` was a case analysis on the hand-written row, and is now that theorem. `TableOf`
  itself is unchanged, so a table written by hand still works.

Migrations stay hand-written SQL (D111). The derived schema is what `Postgres.Typed.checkSchema`
compares them with.

## The binary codec goes

`Codec`, `Codable`, `Codec.struct%` and `Codec.sum%` (`Lanes.Data.Codec`) are removed, and
`deriving Codable` is no longer accepted. Nothing in the library, the examples, the tests or the
integrations read or wrote a codec; the S3 code used only a lemma from that file, which is in
`Lanes/Proof/Utf8.lean`. `Enum` and `LawfulBEq` stay: the checker lists identities with `Enum`.

## Limits

- A recursive type has no derived JSON: the codec is a value, and the command cannot define one
  that refers to itself. A type with `extends` or indices is declared as usual and given
  instances with `Json.Codec` and `Db.Columns` by hand.
- A table's type has no parameters, and a field of another type has no column: the store's rows
  hold scalars only (D111).
- JSON field names are Lean's. An API whose names differ writes its instances by hand.
