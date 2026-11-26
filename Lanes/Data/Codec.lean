/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std
public import Std.Data.String.ToNat

/-!
A `Codec` writes a value as a run of records and reads it back, with the law that reading what
was written gives the value and leaves what followed. The law is a field, so a codec without it
cannot be built, and codecs for pairs, sums, lists and mapped types keep it by construction.

Records are whole byte strings. Where one ends and the next begins is not a codec's concern:
`Lanes.Frame` settles that, with its own proofs.
-/

@[expose] public section

namespace Lanes

structure Codec (α : Type) where
  write : α → List ByteArray
  read : List ByteArray → Option (α × List ByteArray)
  sound : ∀ a rest, read (write a ++ rest) = some (a, rest)

namespace Codec

variable {α β : Type}

theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp [String.fromUTF8?, String.fromUTF8, s.isValidUTF8]

def bytes : Codec ByteArray where
  write b := [b]
  read
    | b :: rest => some (b, rest)
    | [] => none
  sound _ _ := rfl

def unit : Codec Unit where
  write _ := []
  read rest := some ((), rest)
  sound _ _ := rfl

def string : Codec String where
  write s := [s.toUTF8]
  read
    | b :: rest => (String.fromUTF8? b).map (·, rest)
    | [] => none
  sound s rest := by
    show (String.fromUTF8? s.toUTF8).map (·, rest) = _
    rw [fromUTF8?_toUTF8]
    rfl

def nat : Codec Nat where
  write n := [(toString n).toUTF8]
  read
    | b :: rest => ((String.fromUTF8? b).bind String.toNat?).map (·, rest)
    | [] => none
  sound n rest := by
    show ((String.fromUTF8? (toString n).toUTF8).bind String.toNat?).map (·, rest) = _
    rw [fromUTF8?_toUTF8]
    simp

/-- One after the other. -/
def pair (a : Codec α) (b : Codec β) : Codec (α × β) where
  write x := a.write x.1 ++ b.write x.2
  read records := do
    let (x, rest) ← a.read records
    let (y, rest) ← b.read rest
    return ((x, y), rest)
  sound x rest := by simp [List.append_assoc, a.sound, b.sound]

/-- A type written as another. `back` may refuse what `to` never produces. -/
def map (c : Codec β) (to : α → β) (back : β → Option α) (h : ∀ a, back (to a) = some a) :
    Codec α where
  write a := c.write (to a)
  read records := do
    let (b, rest) ← c.read records
    let a ← back b
    return (a, rest)
  sound a rest := by simp [c.sound, h]

def bool : Codec Bool :=
  nat.map (fun b => if b then 1 else 0) (fun n => if n = 0 then some false else some true)
    (by intro b; cases b <;> rfl)

def fin {n : Nat} : Codec (Fin n) :=
  nat.map (·.val) (fun k => if h : k < n then some ⟨k, h⟩ else none) (by intro a; simp)

def int : Codec Int :=
  (pair bool nat).map (fun i => (decide (i < 0), i.natAbs))
    (fun (negative, size) => some (if negative then -(size : Int) else size))
    (by intro i; by_cases h : i < 0 <;> simp [h] <;> omega)

/-- A tag, then the value. -/
def sum (a : Codec α) (b : Codec β) : Codec (α ⊕ β) where
  write
    | .inl x => nat.write 0 ++ a.write x
    | .inr y => nat.write 1 ++ b.write y
  read records := do
    let (tag, rest) ← nat.read records
    match tag with
    | 0 => (a.read rest).map fun (x, rest) => (.inl x, rest)
    | 1 => (b.read rest).map fun (y, rest) => (.inr y, rest)
    | _ => none
  sound x rest := by
    cases x <;> simp [List.append_assoc, nat.sound, a.sound, b.sound]

def option (c : Codec α) : Codec (Option α) :=
  (sum unit c).map (fun | none => .inl () | some a => .inr a)
    (fun | .inl () => some none | .inr a => some (some a)) (by intro a; cases a <;> rfl)

def readMany (c : Codec α) : Nat → List ByteArray → Option (List α × List ByteArray)
  | 0, records => some ([], records)
  | n + 1, records => do
    let (a, rest) ← c.read records
    let (as, rest) ← readMany c n rest
    return (a :: as, rest)

theorem readMany_write (c : Codec α) (as : List α) (rest : List ByteArray) :
    readMany c as.length (as.flatMap c.write ++ rest) = some (as, rest) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [readMany, List.append_assoc, c.sound, ih]

/-- How many, then each. -/
def list (c : Codec α) : Codec (List α) where
  write as := nat.write as.length ++ as.flatMap c.write
  read records := do
    let (n, rest) ← nat.read records
    readMany c n rest
  sound as rest := by simp [List.append_assoc, nat.sound, readMany_write]

end Codec

end Lanes
