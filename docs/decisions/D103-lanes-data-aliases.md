# D103. Former names and defaults in `lanes_data`: `(was old)` and `:= value`

Status: Superseded by D110-volatile-actors.md

The data-format decision ("A data format that outlives its version: one schema
per file, values read by name") left this syntax to its first implementation (its detail 3).
This is that proposal, and `lanes_data` takes it.

A reader matches the writer's fields and constructors to its own by name. Two facts must then be
in the declaration: the names a field or a constructor had before, so that a rename is not read
as a removal and an addition; and the value a field takes when old data does not have it. Both
go into the type's `Schema` (`Lanes/Data/Schema.lean`), which `deriving Codable` derives.

## The syntax

```lean
lanes_data structure Point where
  x : Int
  height (was y) : Int := 0
  deriving Codable

lanes_data inductive Shape where
  | dot
  | circle (centre : Point) (radius : Nat := 1)
  | path (was line) (points : List Point) (closed (was shut) : Bool)
  deriving Codable
```

- `(was a b)` comes right after the name it is about: a field, a constructor, or one argument
  of a constructor. It lists the former names; there may be several, as a field may be renamed
  twice.
- A default is written as Lean already writes it: `x : T := v` for a field, and the binder
  default `(x : T := v)` for a constructor's argument, which Lean's `inductive` takes too.
  The default is what the derived schema records, as a `Value`, and what a reader will take
  when the data has no such field. A field without one cannot be added to a type whose old
  data must still be read.
- The Lean declaration is the one written without the `(was …)` clauses. The former names live
  only in the schema.

## Why this form

- *Next to the name.* A rename is one edit on one line, and a reviewer sees the old name where
  the new one is. A clause elsewhere (after `deriving`, say `renamed y => height`) is easy to
  forget, and it names fields by text far from them.
- *It cannot be read as anything else.* An argument group always has a `:`, and `(was y)` has
  none, so the parser tells them apart; it is tried as one unit (`atomic`), so an argument
  named `was`, `(was : Nat)`, still parses. `was` is not a keyword: it is matched as a word only
  there, so a field or a function named `was` keeps working.
- *Not an attribute.* `@[was y] height : Int` looks like a Lean attribute that Lean would check,
  and inside a constructor's argument group it reads badly.
- *Not numbers.* Numbered fields were set aside by the data-format decision: a second name kept
  by hand beside every field.

## A default names no field

Lean lets a structure's default name another field (`y : Nat := x + 1`). A schema holds a
default as a value, not as a function of the other fields, so `deriving Codable` refuses such a
default with an error that names the field. Without the check, the default would be read in the
codec's scope, where the name might mean something else.

## Not yet

- Former names of a type itself. A reader reaches a value through its place in the schema (the
  type of a field), so a renamed type may need none; matching by name decides.
- What a reader does with the former names and the defaults. That is matching by name, step 4
  of the data-format decision; this decision only records them.
