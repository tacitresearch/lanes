/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Crypto.PublicKey

/-!
Signatures made with a private key, by OpenSSL's libcrypto (`native/sign.c`), the copy Lean's
toolchain ships. The key is read from PEM once, kept by OpenSSL, and never seen by Lean: a
`SigningKey` prints as `<signing key>`, and a key that is refused is refused without saying
what it held. Which keys are taken is decided here, from the public half OpenSSL gives as DER:
those `PublicKey.valid` takes, RSA of 2048 to 8192 bits and P-256.

Signing is a function, so it is pure: RSASSA-PKCS1-v1_5 is deterministic, and ECDSA takes its
nonce from the key and the message as RFC 6979 says, so one key signs one message one way.
-/

@[expose] public section

namespace Lanes

/-- The hash a signature is made over. -/
inductive Digest where
  | sha1
  | sha256
  deriving DecidableEq, Repr, Hashable

opaque PrivateKeyImpl : NonemptyType

/-- A private key as OpenSSL holds it. -/
def PrivateKey : Type := PrivateKeyImpl.type

instance : Nonempty PrivateKey := PrivateKeyImpl.property

namespace PrivateKey

/-- The first private key in `pem`, if OpenSSL reads one that is not encrypted. -/
@[extern "lanes_private_key_read"]
opaque readPem (pem : @& ByteArray) : Option PrivateKey

/-- The DER `SubjectPublicKeyInfo` of the key's public half. -/
@[extern "lanes_private_key_spki"]
opaque spki (key : @& PrivateKey) : ByteArray

@[extern "lanes_private_key_sign"]
private opaque signWith (key : @& PrivateKey) (sha256 rfc6979 : Bool) (msg : @& ByteArray) :
  Option ByteArray

end PrivateKey

/-- A private key whose public half is a key `PublicKey.valid` takes. -/
structure SigningKey where
  key : PrivateKey
  publicKey : PublicKey
  read : PublicKey.ofSpki? key.spki = some publicKey
  valid : publicKey.valid = true

instance : Repr SigningKey := ⟨fun _ _ => "<signing key>"⟩

namespace SigningKey

/-- The key in `pem`, PKCS #8 or the traditional form of RSA or EC. -/
def ofPem (pem : ByteArray) : Except String SigningKey :=
  match PrivateKey.readPem pem with
  | none => .error "signing key: not a private key in PEM, or encrypted"
  | some key =>
    match h : PublicKey.ofSpki? key.spki with
    | none => .error "signing key: neither RSA nor P-256"
    | some publicKey =>
      if hv : publicKey.valid then .ok ⟨key, publicKey, h, hv⟩
      else .error "signing key: RSA of fewer than 2048 or more than 8192 bits"

/-- The signature of `msg` over `digest`: RSASSA-PKCS1-v1_5 under an RSA key, and under a P-256
key ECDSA with RFC 6979's nonce, written as DER. `none` only if OpenSSL fails. -/
@[no_expose]
def sign (k : SigningKey) (digest : Digest) (msg : ByteArray) : Option ByteArray :=
  k.key.signWith (digest == .sha256) (k.publicKey matches .p256 ..) msg

end SigningKey

end Lanes
