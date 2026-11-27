/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Crypto.Hmac

/-!
Cryptography from libsodium (`native/lanes.c`), because Lean's compiler promises nothing about
how long code takes: a comparison or a hash written in Lean may branch on a secret.

A function with a Lean reference has the reference as its body, so its theorems are about the
reference, and what is trusted is that the C computes the same (`Tests/Crypto.lean` compares
them). Argon2id has no reference here.
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

/-- Bytes from the operating system's secure source, through libsodium. -/
@[extern "lanes_random_bytes"]
opaque randomBytes (size : USize) : IO ByteArray

/-- The cost of an Argon2id hash: `ops` passes over `mem_kib` KiB of memory, at least what
libsodium accepts. -/
structure Argon2id where
  ops : UInt32
  mem_kib : UInt32
  ops_pos : 0 < ops := by decide
  mem_min : 8 ≤ mem_kib := by decide

@[extern "lanes_argon2id"]
private opaque argon2id (password salt : @& ByteArray) (ops mem_kib : UInt32) : ByteArray

/-- The 32-byte Argon2id hash of `password` with a 16-byte salt. It is slow by design: run it
where a request arrives, not in a shard. The process ends if the memory cannot be had. -/
@[no_expose]
def Argon2id.hash (cost : Argon2id) (password salt : ByteArray) (_ : salt.size = 16) : ByteArray :=
  argon2id password salt cost.ops cost.mem_kib

end Lanes
