/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
A value never to be printed or logged: a password, a key, a token. `Repr` and `ToString` show
only that it is one, so a configuration or a message that holds one may derive `Repr` and be
logged. `reveal` is the one way to the text.
-/

@[expose] public section

namespace Lanes

structure Secret where
  /-- Read only to use it: to sign with it, or to send it where it belongs. -/
  reveal : String
  deriving DecidableEq, Hashable, Inhabited

instance : Repr Secret := ⟨fun _ _ => "<secret>"⟩

instance : ToString Secret := ⟨fun _ => "<secret>"⟩

theorem Secret.toString_eq (s : Secret) : toString s = "<secret>" := rfl

end Lanes
