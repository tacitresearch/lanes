/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Axioms.Behaviours
import Tests.Axioms.Check
import Tests.Axioms.Core
import Tests.Axioms.Data
import Tests.Axioms.Durable
import Tests.Axioms.Lib
import Tests.Axioms.Net
import Tests.Axioms.Proof
import Tests.Axioms.Runtime
import Tests.Axioms.Semantics
import Tests.Axioms.Tests
import Tests.Axioms.Web

/-!
The axiom gate (rule 5.5). Each headline theorem may depend only on Lean's three standard
axioms. If a `sorry` or a new axiom reaches one of them, its gate stops compiling. The gates are
built by `lake build`, not linked into the test executable.

A theorem's gate is in `Tests/Axioms/<Area>.lean`, for the directory under `Lanes/` of the
module that states it (`Lanes/Web/Http/Wire.lean` is `Web.lean`; `Tests/`, the fixtures included,
is `Tests.lean`), after the other gates of that module, under the line `-- <module>`.
-/
