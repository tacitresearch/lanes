/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Axioms.Actors
import Tests.Axioms.Auth
import Tests.Axioms.Behaviours
import Tests.Axioms.Check
import Tests.Axioms.Data
import Tests.Axioms.Examples
import Tests.Axioms.Html
import Tests.Axioms.Http
import Tests.Axioms.Semantics

/-!
The axiom gate (rule 5.5). Each headline theorem may depend only on Lean's three standard
axioms. If a `sorry` or a new axiom reaches one of them, its gate stops compiling. The gates are
built by `lake build`, not linked into the test executable.

A theorem's gate is in `Tests/Axioms/<Area>.lean`, for the directory of the module that states
it (`Lanes/Actors/` is `Actors.lean`; `Examples/` and `Tests/` are `Examples.lean`), after the
other gates of that module, under the line `-- <module>`.
-/
