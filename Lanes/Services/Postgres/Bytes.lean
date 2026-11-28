/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Proof.Utf8

/-!
The fields PostgreSQL's messages are made of, each written as a list of bytes and read back by a
parser, with the law that a parser reads back what its writer wrote whatever follows
(`Postgres.Inverse`): unsigned integers of two and four bytes, big-endian; strings ended by a
NUL; values with a length of four bytes, `-1` for SQL's `NULL`; lists with a count before them,
and lists ended by a zero byte. The messages (`Lanes/Services/Postgres/Message.lean`) are built from
these, and their round trips from these laws.

The fields are over `List UInt8`, so that the laws are about lists; a message's body is turned
into a list once, when its frame has been read.
-/

@[expose] public section

namespace Lanes.Postgres

/-- What reads a field from the front of some bytes: the field and the bytes after it. -/
abbrev Parse (α : Type) := List UInt8 → Option (α × List UInt8)

/-- `dec` reads back what `enc` writes of a value for which `ok` holds, whatever follows. -/
def Inverse {α : Type} (enc : α → List UInt8) (dec : Parse α) (ok : α → Prop) : Prop :=
  ∀ a rest, ok a → dec (enc a ++ rest) = some (a, rest)

def byte : Parse UInt8
  | b :: rest => some (b, rest)
  | [] => none

def putU16 (n : Nat) : List UInt8 := [(n / 256 % 256).toUInt8, (n % 256).toUInt8]

def getU16 : Parse Nat
  | a :: b :: rest => some (a.toNat * 256 + b.toNat, rest)
  | _ => none

def putU32 (n : Nat) : List UInt8 :=
  [(n / 16777216 % 256).toUInt8, (n / 65536 % 256).toUInt8, (n / 256 % 256).toUInt8,
    (n % 256).toUInt8]

def getU32 : Parse Nat
  | a :: b :: c :: d :: rest =>
    some (((a.toNat * 256 + b.toNat) * 256 + c.toNat) * 256 + d.toNat, rest)
  | _ => none

/-- The bytes up to the first NUL, and those after it. -/
def untilNul : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | b :: rest => if b = 0 then some ([], rest) else (untilNul rest).map fun (s, r) => (b :: s, r)

/-- A string has no NUL, so that it can be written ended by one. -/
def Plain (s : String) : Prop := '\u0000' ∉ s.toList

instance (s : String) : Decidable (Plain s) := inferInstanceAs (Decidable (_ ∉ _))

def putStr (s : String) : List UInt8 := s.toByteArray.data.toList ++ [0]

def getStr : Parse String := fun bytes => do
  let (raw, rest) ← untilNul bytes
  let s ← String.fromUTF8? ⟨raw.toArray⟩
  pure (s, rest)

def take (n : Nat) : Parse (List UInt8) := fun bytes =>
  if n ≤ bytes.length then some (bytes.take n, bytes.drop n) else none

/-- A value of four bytes of length and then its bytes, or `-1` and no bytes for `NULL`. -/
def putValue : Option ByteArray → List UInt8
  | none => putU32 0xFFFFFFFF
  | some v => putU32 v.size ++ v.data.toList

def getValue : Parse (Option ByteArray) := fun bytes =>
  match getU32 bytes with
  | none => none
  | some (n, rest) =>
    if n = 0xFFFFFFFF then some (none, rest)
    else (take n rest).map fun (v, rest) => (some ⟨v.toArray⟩, rest)

def ValueOk : Option ByteArray → Prop
  | none => True
  | some v => v.size < 0x80000000

def many {α : Type} (p : Parse α) : Nat → Parse (List α)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes => do
    let (a, rest) ← p bytes
    let (as, rest) ← many p n rest
    pure (a :: as, rest)

/-- A list with its length in two bytes before it. -/
def putList16 {α : Type} (enc : α → List UInt8) (as : List α) : List UInt8 :=
  putU16 as.length ++ as.flatMap enc

def getList16 {α : Type} (p : Parse α) : Parse (List α) := fun bytes => do
  let (n, rest) ← getU16 bytes
  many p n rest

/-- A list ended by a zero byte; each item starts with a byte that is not zero. `fuel` bounds the
items read: the bytes there are is enough. -/
def getTerminated {α : Type} (p : Parse α) : Nat → Parse (List α)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, b :: rest =>
    if b = 0 then some ([], rest)
    else do
      let (a, rest) ← p (b :: rest)
      let (as, rest) ← getTerminated p fuel rest
      pure (a :: as, rest)

def putTerminated {α : Type} (enc : α → List UInt8) (as : List α) : List UInt8 :=
  as.flatMap enc ++ [0]

/-- Reads with `p` and needs every byte read. -/
def whole {α : Type} (p : Parse α) (bytes : List UInt8) : Option α :=
  match p bytes with
  | some (a, []) => some a
  | _ => none

/-! ## The laws -/

theorem toNat_toUInt8 (n : Nat) : n.toUInt8.toNat = n % 256 := by
  simp [Nat.toUInt8, UInt8.toNat_ofNat']

theorem inverse_byte : Inverse (fun b => [b]) byte fun _ => True := by
  intro b rest _
  rfl

theorem inverse_u16 : Inverse putU16 getU16 (· < 65536) := by
  intro n rest h
  simp only [putU16, List.cons_append, List.nil_append, getU16, toNat_toUInt8, Option.some.injEq,
    Prod.mk.injEq, and_true]
  omega

theorem inverse_u32 : Inverse putU32 getU32 (· < 4294967296) := by
  intro n rest h
  simp only [putU32, List.cons_append, List.nil_append, getU32, toNat_toUInt8, Option.some.injEq,
    Prod.mk.injEq, and_true]
  omega

theorem untilNul_append {raw : List UInt8} (h : 0 ∉ raw) (rest : List UInt8) :
    untilNul (raw ++ 0 :: rest) = some (raw, rest) := by
  induction raw with
  | nil => simp [untilNul]
  | cons b raw ih =>
    simp only [List.mem_cons, not_or] at h
    simp [untilNul, Ne.symm h.1, ih h.2]

theorem zero_not_mem_toByteArray {s : String} (h : Plain s) : (0 : UInt8) ∉ s.toByteArray.data.toList := by
  rw [data_toList_toByteArray, List.mem_flatMap]
  rintro ⟨c, hc, hb⟩
  have := utf8EncodeChar_ascii hb (by decide)
  apply h
  have hc0 : c = '\u0000' := Char.ext (UInt32.toNat_inj.mp (by simpa using this.symm))
  exact hc0 ▸ hc

theorem inverse_str : Inverse putStr getStr Plain := by
  intro s rest h
  simp only [putStr, List.append_assoc, List.cons_append, List.nil_append, getStr,
    untilNul_append (zero_not_mem_toByteArray h), Option.bind_eq_bind, Option.bind_some]
  have : (⟨s.toByteArray.data.toList.toArray⟩ : ByteArray) = s.toByteArray := rfl
  rw [this, fromUTF8?_toByteArray]
  rfl

theorem take_append (xs rest : List UInt8) : take xs.length (xs ++ rest) = some (xs, rest) := by
  simp [take]

theorem inverse_value : Inverse putValue getValue ValueOk := by
  intro v rest h
  cases v with
  | none =>
    simp only [putValue, getValue]
    rw [inverse_u32 _ _ (show 0xFFFFFFFF < 4294967296 by decide)]
    rfl
  | some v =>
    simp only [ValueOk] at h
    have hlen : v.data.toList.length = v.size := Array.length_toList
    rw [putValue, List.append_assoc, getValue, inverse_u32 _ _ (show v.size < 4294967296 by omega)]
    dsimp only
    rw [ite_eq_right (show v.size ≠ 0xFFFFFFFF by omega), ← hlen, take_append]
    rfl

theorem many_append {α : Type} {enc : α → List UInt8} {p : Parse α} {ok : α → Prop}
    (law : Inverse enc p ok) (as : List α) (h : ∀ a ∈ as, ok a) (rest : List UInt8) :
    many p as.length (as.flatMap enc ++ rest) = some (as, rest) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, many,
      law a _ (h a (by simp)), ih (fun b hb => h b (by simp [hb])), Option.bind_eq_bind,
      Option.bind_some]
    rfl

theorem inverse_list16 {α : Type} {enc : α → List UInt8} {p : Parse α} {ok : α → Prop}
    (law : Inverse enc p ok) :
    Inverse (putList16 enc) (getList16 p) fun as => as.length < 65536 ∧ ∀ a ∈ as, ok a := by
  intro as rest ⟨hlen, h⟩
  simp only [putList16, List.append_assoc, getList16, inverse_u16 _ _ hlen, Option.bind_eq_bind,
    Option.bind_some, many_append law as h]

/-- What a list ended by a zero byte needs of its items' writer: every item is written starting
with a byte that is not zero. -/
def StartsNonzero {α : Type} (enc : α → List UInt8) (ok : α → Prop) : Prop :=
  ∀ a, ok a → ∃ b bs, enc a = b :: bs ∧ b ≠ 0

theorem getTerminated_append {α : Type} {enc : α → List UInt8} {p : Parse α} {ok : α → Prop}
    (law : Inverse enc p ok) (starts : StartsNonzero enc ok) (as : List α) (h : ∀ a ∈ as, ok a)
    (rest : List UInt8) (fuel : Nat) (hfuel : as.length < fuel) :
    getTerminated p fuel (putTerminated enc as ++ rest) = some (as, rest) := by
  induction as generalizing fuel with
  | nil =>
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    simp [putTerminated, getTerminated]
  | cons a as ih =>
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    obtain ⟨b, bs, henc, hb⟩ := starts a (h a (by simp))
    have hrest := ih (fun c hc => h c (by simp [hc])) fuel (by simp at hfuel; omega)
    simp only [putTerminated, List.flatMap_cons, List.append_assoc] at hrest ⊢
    rw [henc, List.cons_append, getTerminated, ite_eq_right hb, ← List.cons_append, ← henc,
      law a _ (h a (by simp))]
    simp only [Option.bind_eq_bind, Option.bind_some, hrest]
    rfl

theorem length_le_flatMap {α : Type} {enc : α → List UInt8} {ok : α → Prop}
    (starts : StartsNonzero enc ok) (as : List α) (h : ∀ a ∈ as, ok a) :
    as.length ≤ (as.flatMap enc).length := by
  induction as with
  | nil => simp
  | cons a as ih =>
    obtain ⟨b, bs, henc, _⟩ := starts a (h a (by simp))
    simp only [List.length_cons, List.flatMap_cons, List.length_append, henc]
    have := ih (fun c hc => h c (by simp [hc]))
    omega

theorem whole_append {α : Type} {enc : α → List UInt8} {p : Parse α} {ok : α → Prop}
    (law : Inverse enc p ok) {a : α} (h : ok a) : whole p (enc a) = some a := by
  have := law a [] h
  rw [List.append_nil] at this
  simp [whole, this]

end Lanes.Postgres
