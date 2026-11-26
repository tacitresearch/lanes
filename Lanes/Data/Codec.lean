/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std
public import Std.Data.String.ToNat

/-!
A `Codec` writes values as bytes and reads them back, with the law that reading what was
written gives the value. The law is a field, so a codec without it cannot be built.
-/

@[expose] public section

namespace Lanes

structure Codec (α : Type) where
  encode : α → ByteArray
  decode : ByteArray → Option α
  sound : ∀ a, decode (encode a) = some a

namespace Codec

theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp [String.fromUTF8?, String.fromUTF8, s.isValidUTF8]

def string : Codec String where
  encode s := s.toUTF8
  decode := String.fromUTF8?
  sound := fromUTF8?_toUTF8

def nat : Codec Nat where
  encode n := (toString n).toUTF8
  decode bytes := (String.fromUTF8? bytes).bind String.toNat?
  sound n := by
    rw [fromUTF8?_toUTF8]
    simp

end Codec

end Lanes
