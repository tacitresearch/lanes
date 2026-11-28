module

import Lanes
meta import Spike.Lanes

/-! The errors of the handlers of `Spike.Lanes`. Not in an executable: a failed instance
is compiled as an error that panics when the program starts. -/

open Lanes

namespace App.Errors

def valid (s : String) : Bool := 0 < s.length

/-! The errors are reported at the class's name in `deriving`, as Lean's own handlers report. -/

/--
error: deriving: the type of `ok` names another field. Put the property in that field's type, as
a subtype `{x : α // p x}`.
-/
#guard_msgs (whitespace := lax) in
structure Checked where
  text : String
  ok : valid text = true
  deriving ToJson, FromJson

/--
error: deriving: `rest` is of a type that refers to `App.Errors.Tree`: a derived codec is a value
and cannot refer to itself
-/
#guard_msgs (whitespace := lax) in
inductive Tree where
  | leaf
  | node (rest : List Tree)
  deriving ToJson

/--
error: failed to synthesize instance of type class
  ToJson (Nat → Nat)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
structure NoJson where
  f : Nat → Nat
  deriving ToJson

/-! Lean's `ToJson` is in scope too, through the handlers' `meta import`: with `open Lean`, the
name is ambiguous, and the full name chooses. -/

open Lean in
/-- error: ambiguous identifier ``ToJson`, possible interpretations: [Lanes.ToJson, Lean.ToJson] -/
#guard_msgs in
structure Both where
  n : Nat
  deriving ToJson

open Lean in
structure Chosen where
  n : Nat
  deriving Lanes.ToJson

end App.Errors
