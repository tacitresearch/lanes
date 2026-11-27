/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Crypto.Sha512
public import Lanes.Lib.Crypto.Sodium

/-!
What channel binding of type `tls-server-end-point` (RFC 5929 §4.1) binds to: the hash of the
server's certificate, as DER, with the hash function of the certificate's signature algorithm,
or SHA-256 when that is MD5 or SHA-1. The algorithm is read from the certificate's outer
`signatureAlgorithm` (RFC 5280 §4.1.1.2), the only part of the DER read here. An algorithm whose
hash is not one of SHA-256, SHA-384 and SHA-512 (RSASSA-PSS, whose hash is in its parameters,
Ed25519, which has none, SHA-224) gives no binding, as libpq gives none.
-/

@[expose] public section

namespace Lanes.Certificate

inductive Hash where
  | sha256
  | sha384
  | sha512
  deriving DecidableEq, Repr

def Hash.apply : Hash → ByteArray → ByteArray
  | .sha256 => Sha256.hash
  | .sha384 => Sha512.hash384
  | .sha512 => Sha512.hash

/-- The tag, the body and what follows of the DER element at the front of `bytes`: a length in
one byte below 128, or in one to four bytes after `0x81` to `0x84`. -/
def element (bytes : List UInt8) : Option (UInt8 × List UInt8 × List UInt8) :=
  match bytes with
  | tag :: first :: rest =>
    let (size, rest) :=
      if first < 0x80 then (some first.toNat, rest)
      else if 0x80 < first ∧ first ≤ 0x84 then
        let n := (first - 0x80).toNat
        (if n ≤ rest.length then some ((rest.take n).foldl (fun a b => a * 256 + b.toNat) 0)
         else none, rest.drop n)
      else (none, rest)
    match size with
    | some size => if size ≤ rest.length then some (tag, rest.take size, rest.drop size) else none
    | none => none
  | _ => none

/-- The object identifier of a certificate's `signatureAlgorithm`, as its DER body. -/
def signatureAlgorithm (der : ByteArray) : Option (List UInt8) := do
  let (0x30, cert, _) ← element der.data.toList | none
  let (0x30, _, rest) ← element cert | none
  let (0x30, algorithm, _) ← element rest | none
  let (0x06, oid, _) ← element algorithm | none
  pure oid

/-- `1.2.840.113549.1.1`, PKCS #1. -/
def pkcs1 : List UInt8 := [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01]

/-- `1.2.840.10045.4`, ECDSA's signatures. -/
def ecdsa : List UInt8 := [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04]

/-- The hash RFC 5929 says to use for a signature algorithm: MD5 and SHA-1 become SHA-256. -/
def hashOf (oid : List UInt8) : Option Hash :=
  if oid = pkcs1 ++ [4] ∨ oid = pkcs1 ++ [5] ∨ oid = pkcs1 ++ [11] then some .sha256
  else if oid = pkcs1 ++ [12] then some .sha384
  else if oid = pkcs1 ++ [13] then some .sha512
  else if oid = ecdsa ++ [1] ∨ oid = ecdsa ++ [3, 2] then some .sha256
  else if oid = ecdsa ++ [3, 3] then some .sha384
  else if oid = ecdsa ++ [3, 4] then some .sha512
  else none

/-- The channel binding data of `tls-server-end-point` for the certificate `der`. -/
def endPoint (der : ByteArray) : Option ByteArray := do
  let hash ← (signatureAlgorithm der).bind hashOf
  pure (hash.apply der)

end Lanes.Certificate
