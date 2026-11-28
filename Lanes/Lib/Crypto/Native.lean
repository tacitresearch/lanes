/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Crypto.Hmac

/-!
Cryptography from OpenSSL's libcrypto, the copy Lean's toolchain ships (`native/lanes.c`),
because Lean's compiler promises nothing about how long code takes: a comparison or a hash
written in Lean may branch on a secret.

A function with a Lean reference has the reference as its body, so its theorems are about the
reference, and what is trusted is that the C computes the same (`Tests/Crypto.lean` compares
them). Argon2id has no reference here: it is tested against RFC 9106 and against hashes
libsodium made.
-/

@[expose] public section

namespace Lanes

@[extern "lanes_sha256"]
def Sha256.hash (msg : @& ByteArray) : ByteArray := Sha256.reference msg

theorem Sha256.size_hash (msg : ByteArray) : (hash msg).size = 32 := size_reference msg

@[extern "lanes_hmac_sha256"]
def hmac (key msg : @& ByteArray) : ByteArray := Hmac.reference key msg

theorem Hmac.size_hmac (key msg : ByteArray) : (hmac key msg).size = 32 := size_reference key msg

/-- Whether two byte strings are equal, in a time that depends on their lengths only. -/
@[extern "lanes_same"]
def Bytes.same (a b : @& ByteArray) : Bool := sameReference a b

theorem Bytes.same_iff (a b : ByteArray) : same a b = true ↔ a = b := sameReference_iff a b

/-- Bytes from OpenSSL's cryptographically secure generator (`RAND_bytes`), which seeds itself
from the operating system. It throws if the generator cannot be had. -/
@[extern "lanes_random_bytes"]
def randomBytes (size : USize) : IO ByteArray := IO.getRandomBytes size

/-- The cost of an Argon2id hash: `ops` passes over `mem_kib` KiB of memory, at least what
RFC 9106 allows for one lane. -/
structure Argon2id where
  ops : UInt32
  mem_kib : UInt32
  ops_pos : 0 < ops := by decide
  mem_min : 8 ≤ mem_kib := by decide

theorem Argon2id.oneLane (cost : Argon2id) :
    0 < (1 : UInt32).toNat ∧ (1 : UInt32).toNat < 2 ^ 24 ∧ 8 * (1 : UInt32).toNat ≤ cost.mem_kib.toNat :=
  ⟨by decide, by decide, by have := UInt32.le_iff_toNat_le.mp cost.mem_min; simpa using this⟩

@[extern "lanes_argon2id"]
private opaque argon2id (password salt secret ad : @& ByteArray) (ops mem_kib lanes : UInt32) :
  ByteArray

/-- The 32-byte Argon2id tag of RFC 9106, version 19, with every input: a salt of at least 8
bytes, `lanes` lanes, which need `8 * lanes` KiB, a secret key and associated data. -/
@[no_expose]
def Argon2id.derive (cost : Argon2id) (lanes : UInt32) (password salt secret ad : ByteArray)
    (_ : 8 ≤ salt.size)
    (_ : 0 < lanes.toNat ∧ lanes.toNat < 2 ^ 24 ∧ 8 * lanes.toNat ≤ cost.mem_kib.toNat) :
    ByteArray :=
  argon2id password salt secret ad cost.ops cost.mem_kib lanes

/-- The 32-byte Argon2id hash of `password` with a 16-byte salt, in one lane and with no secret,
as libsodium's `crypto_pwhash` computes it. It is slow by design: run it where a request
arrives, not in a step. The process ends if the memory cannot be had. -/
def Argon2id.hash (cost : Argon2id) (password salt : ByteArray) (h : salt.size = 16) : ByteArray :=
  cost.derive 1 password salt .empty .empty (by omega) cost.oneLane

end Lanes
