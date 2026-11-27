/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Crypto.Native

/-!
PBKDF2 with HMAC-SHA-256 (RFC 8018), which SCRAM-SHA-256 calls `Hi`. It is for authenticating
to a server that asks for it, not for digesting passwords: those are Argon2id
(`docs/decisions/D46-bind-what-touches-physics.md`).

It composes OpenSSL's HMAC (`hmac`), so what takes time that may depend on the password is
OpenSSL's; the loop around it does the same work whatever the bytes are. Tested against RFC
7914's vectors and Python's `hashlib` (`Tests/Crypto.lean`).
-/

@[expose] public section

namespace Lanes.Pbkdf2

def xor (a b : ByteArray) : ByteArray :=
  ⟨(a.data.zip b.data).map fun (x, y) => x ^^^ y⟩

def be32 (n : Nat) : ByteArray :=
  ⟨#[(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]⟩

/-- `U_1 ⊕ … ⊕ U_c` for the block numbered `index`, from one. -/
def block (password salt : ByteArray) (iterations index : Nat) : ByteArray :=
  let first := hmac password (salt ++ be32 index)
  let rec go : Nat → ByteArray → ByteArray → ByteArray
    | 0, _, acc => acc
    | n + 1, u, acc =>
      let u := hmac password u
      go n u (xor acc u)
  go (iterations - 1) first first

/-- The first `length` bytes of the key derived from `password` and `salt`. -/
def derive (password salt : ByteArray) (iterations length : Nat) : ByteArray :=
  let blocks := (length + 31) / 32
  let key := (List.range blocks).foldl (fun acc k => acc ++ block password salt iterations (k + 1)) .empty
  key.extract 0 length

end Lanes.Pbkdf2
