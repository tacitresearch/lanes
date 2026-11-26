/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.Sha256

/-!
HMAC-SHA-256 (RFC 2104) and PBKDF2-HMAC-SHA-256 (RFC 8018), in pure Lean, with what a signed
token needs around them: hex, and a comparison that reads every byte whatever it finds.

A `Hmac.Key` holds the state after each padded key block, so a key is hashed once and each MAC
costs two blocks more than its message. PBKDF2 does nothing else, so its cost is two blocks per
iteration. Tested against RFC 4231 and RFC 7914 in `Tests/Crypto.lean`.
-/

@[expose] public section

namespace Lanes

namespace Hmac

structure Key where
  inner : Sha256.State
  outer : Sha256.State

def blockOf (key : ByteArray) (pad : UInt8) : Vector UInt32 16 :=
  let key := if key.size > 64 then Sha256.hash key else key
  let bytes : ByteArray := ⟨Array.ofFn fun (k : Fin 64) => (key[k.val]?.getD 0) ^^^ pad⟩
  have h : bytes.size = 64 := Array.size_ofFn
  Sha256.blockAt bytes 0 (by omega)

def Key.of (key : ByteArray) : Key where
  inner := Sha256.compress Sha256.initial (blockOf key 0x36)
  outer := Sha256.compress Sha256.initial (blockOf key 0x5c)

def Key.mac (key : Key) (msg : ByteArray) : ByteArray :=
  (Sha256.digestFrom key.outer 64 (Sha256.digestFrom key.inner 64 msg).bytes).bytes

theorem size_mac (key : Key) (msg : ByteArray) : (key.mac msg).size = 32 :=
  Sha256.size_bytes _

end Hmac

def hmac (key msg : ByteArray) : ByteArray :=
  (Hmac.Key.of key).mac msg

namespace Bytes

def xor (a b : ByteArray) : ByteArray :=
  ⟨Array.ofFn fun (k : Fin a.size) => a[k] ^^^ (b[k.val]?.getD 0)⟩

theorem size_xor (a b : ByteArray) : (xor a b).size = a.size :=
  Array.size_ofFn

def bigEndian32 (n : Nat) : ByteArray :=
  ⟨#[(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]⟩

/-- Whether two byte strings are equal, reading every byte of `a` whatever it finds, so that
how long it takes says nothing of where they differ. That the compiled code keeps to this is
trusted (`TRUSTED.md`). -/
def same (a b : ByteArray) : Bool :=
  a.size == b.size
    && (List.finRange a.size).foldl (fun acc k => acc ||| (a[k] ^^^ (b[k.val]?.getD 0))) 0 == 0

private theorem foldl_or_eq_zero {n : Nat} (f : Fin n → UInt8) (l : List (Fin n)) (acc : UInt8) :
    l.foldl (fun acc k => acc ||| f k) acc = 0 ↔ acc = 0 ∧ ∀ k ∈ l, f k = 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons k l ih => simp [ih, and_assoc]

theorem same_iff (a b : ByteArray) : same a b = true ↔ a = b := by
  simp only [same, Bool.and_eq_true, beq_iff_eq, foldl_or_eq_zero, List.mem_finRange,
    forall_const, true_and, UInt8.xor_eq_zero_iff]
  constructor
  · rintro ⟨hsize, heach⟩
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    congr 1
    apply Array.ext hsize
    intro k ha hb
    have := heach ⟨k, ha⟩
    simp only [Fin.getElem_fin] at this
    rw [getElem?_pos (⟨b⟩ : ByteArray) k hb, Option.getD_some] at this
    exact this
  · rintro rfl
    exact ⟨rfl, fun k => by simp⟩

def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

def hex (bytes : ByteArray) : String :=
  String.ofList (bytes.data.toList.flatMap fun (b : UInt8) => [hexDigit (b >>> 4), hexDigit (b &&& 15)])

def nibble? (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87).toUInt8
  else none

def unhexList : List Char → Option (List UInt8)
  | [] => some []
  | hi :: lo :: rest => do
    let h ← nibble? hi
    let l ← nibble? lo
    return (h <<< 4 ||| l) :: (← unhexList rest)
  | [_] => none

/-- Lowercase hex only, so that one byte string has one spelling. -/
def unhex? (s : String) : Option ByteArray :=
  (unhexList s.toList).map fun bytes => ⟨bytes.toArray⟩

private theorem nibbles : ∀ b : UInt8, nibble? (hexDigit (b >>> 4)) = some (b >>> 4)
    ∧ nibble? (hexDigit (b &&& 15)) = some (b &&& 15) ∧ ((b >>> 4) <<< 4 ||| (b &&& 15)) = b := by
  decide

private theorem unhexList_hex (bytes : List UInt8) :
    unhexList (bytes.flatMap fun (b : UInt8) => [hexDigit (b >>> 4), hexDigit (b &&& 15)]) = some bytes := by
  induction bytes with
  | nil => rfl
  | cons b bytes ih =>
    obtain ⟨hi, lo, joined⟩ := nibbles b
    simp [unhexList, hi, lo, joined, ih]

theorem unhex?_hex (bytes : ByteArray) : unhex? (hex bytes) = some bytes := by
  simp [unhex?, hex, unhexList_hex]

end Bytes

namespace Pbkdf2

def block (key : Hmac.Key) (salt : ByteArray) (iterations index : Nat) : ByteArray :=
  let first := key.mac (salt ++ Bytes.bigEndian32 index)
  ((List.range (iterations - 1)).foldl (fun (u, t) _ =>
    let u := key.mac u
    (u, Bytes.xor t u)) (first, first)).2

end Pbkdf2

/-- PBKDF2 with HMAC-SHA-256: `length` bytes derived from `password` and `salt`. The cost is two
SHA-256 blocks per iteration and 32 bytes of output. -/
def pbkdf2 (password salt : ByteArray) (iterations length : Nat) : ByteArray :=
  let key := Hmac.Key.of password
  let blocks := (List.range ((length + 31) / 32)).foldl
    (fun acc k => acc ++ Pbkdf2.block key salt iterations (k + 1)) ByteArray.empty
  blocks.extract 0 length

end Lanes
