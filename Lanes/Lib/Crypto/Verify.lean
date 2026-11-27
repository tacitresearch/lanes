/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Crypto.PublicKey

/-!
A signature checked under a public key, by OpenSSL's libcrypto (`native/verify.c`): the copy
Lean's toolchain ships, as the TLS client uses. Everything but the arithmetic is decided in
`Lanes/Lib/Crypto/PublicKey.lean`: the key's DER, the signature's, and the size a signature must
have; RSA's arithmetic has a Lean reference there too, `Rsa.verifyReference`, which
`Tests/Signature.lean` compares with this.
-/

@[expose] public section

namespace Lanes

@[extern "lanes_verify_sha256"]
private opaque verifySpki (spki msg sig : @& ByteArray) : Bool

/-- Whether `sig` signs `msg` under `key` with SHA-256: RSASSA-PKCS1-v1_5 under an RSA key,
ECDSA under a P-256 one, its signature written `r ‖ s` as JWS writes it. -/
@[no_expose]
def PublicKey.verifies (key : PublicKey) (msg sig : ByteArray) : Bool :=
  match key.derSignature sig with
  | some der => verifySpki key.spki msg der
  | none => false

end Lanes
