/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
SHA-256 against the examples of FIPS 180-4 (as NIST publishes them) and HMAC-SHA-256 against
RFC 4231, each run on OpenSSL's and on the Lean reference; then the two compared on thousands
of random inputs of every length around a block, which is what the trust in the binding rests on
(`TRUSTED.md`). SHA-512 and SHA-384, pure Lean, against the same examples, as `openssl dgst`
computes them. Argon2id has no reference: it is tested against RFC 9106's example, against
hashes libsodium made when Lanes linked it, and for its properties.
-/

namespace Tests.Crypto

open Lanes

def bytesOf (s : String) : ByteArray := s.toUTF8

def repeated (b : UInt8) (n : Nat) : ByteArray := ⟨Array.replicate n b⟩

def sha256Vectors : List (String × ByteArray × String) :=
  [ ("the empty message", .empty,
      "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ("abc", bytesOf "abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
    ("the 448-bit message, two blocks",
      bytesOf "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
      "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
    ("the 896-bit message",
      bytesOf ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno"
        ++ "ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"),
      "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"),
    ("a million times a", repeated 0x61 1000000,
      "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0") ]

def sha256Tests : List (String × Bool) :=
  sha256Vectors.flatMap (fun (name, msg, digest) =>
    [ (s!"sha-256: {name}", Bytes.hex (Sha256.hash msg) == digest),
      (s!"sha-256 reference: {name}", Bytes.hex (Sha256.reference msg) == digest) ])
  ++ [ ("sha-256: every length from 0 to 130 pads to whole blocks",
      (List.range 131).all fun n => (n + (Sha256.padding n).size) % 64 == 0
        && (Sha256.reference (repeated 0 n)).size == 32) ]

def sha512Vectors : List (String × ByteArray × String × String) :=
  [ ("the empty message", .empty,
      "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e",
      "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b"),
    ("abc", bytesOf "abc",
      "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f",
      "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7"),
    ("the 896-bit message, two blocks",
      bytesOf ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno"
        ++ "ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"),
      "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909",
      "09330c33f71147e83d192fc782cd1b4753111b173b3b05d22fa08086e3b0f712fcc7c71a557e2db966c3e9fa91746039"),
    ("a million times a", repeated 0x61 1000000,
      "e718483d0ce769644e2e42c7bc15b4638e1f98b13b2044285632a803afa973ebde0ff244877ea60a4cb0432ce577c31beb009c5c2c49aa2e4eadb217ad8cc09b",
      "9d0e1809716474cb086e834e310a4a1ced149e9c00f248527972cec5704c2a5b07b8b3dc38ecc4ebae97ddd87f3d8985") ]

def sha512Tests : List (String × Bool) :=
  sha512Vectors.flatMap (fun (name, msg, d512, d384) =>
    [ (s!"sha-512: {name}", Bytes.hex (Sha512.hash msg) == d512),
      (s!"sha-384: {name}", Bytes.hex (Sha512.hash384 msg) == d384) ])
  ++ [ ("sha-512: every length from 0 to 260 pads to whole blocks of 128",
      (List.range 261).all fun n => (n + (Sha512.padding n).size) % 128 == 0) ]

def hmacVectors : List (String × ByteArray × ByteArray × String) :=
  [ ("RFC 4231 case 1", repeated 0x0b 20, bytesOf "Hi There",
      "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"),
    ("RFC 4231 case 2, a key shorter than the output", bytesOf "Jefe",
      bytesOf "what do ya want for nothing?",
      "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"),
    ("RFC 4231 case 3", repeated 0xaa 20, repeated 0xdd 50,
      "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe"),
    ("RFC 4231 case 4", ⟨(List.range 25).toArray.map fun k => (k + 1).toUInt8⟩, repeated 0xcd 50,
      "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b"),
    ("RFC 4231 case 6, a key longer than a block", repeated 0xaa 131,
      bytesOf "Test Using Larger Than Block-Size Key - Hash Key First",
      "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"),
    ("RFC 4231 case 7, key and data longer than a block", repeated 0xaa 131,
      bytesOf ("This is a test using a larger than block-size key and a "
        ++ "larger than block-size data. The key needs to be hashed before being used by the HMAC "
        ++ "algorithm."),
      "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2") ]

def hmacTests : List (String × Bool) :=
  hmacVectors.flatMap fun (name, key, msg, tag) =>
    [ (s!"hmac-sha-256: {name}", Bytes.hex (hmac key msg) == tag),
      (s!"hmac-sha-256 reference: {name}", Bytes.hex (Hmac.reference key msg) == tag) ]

def bytesTests : List (String × Bool) :=
  let a := bytesOf "same bytes"
  [ ("bytes: equal strings are the same", Bytes.same a (bytesOf "same bytes")),
    ("bytes: a string differing in its last byte is not",
      !Bytes.same a (bytesOf "same bytez")),
    ("bytes: a prefix is not", !Bytes.same a (bytesOf "same")),
    ("bytes: nor a longer string", !Bytes.same (bytesOf "same") a),
    ("bytes: hex reads back", Bytes.unhex? (Bytes.hex a) == some a),
    ("bytes: uppercase hex and odd lengths are refused",
      Bytes.unhex? "AB" == none && Bytes.unhex? "abc" == none && Bytes.unhex? "zz" == none) ]

def noise (size : Nat) (gen : StdGen) : ByteArray × StdGen :=
  (List.range size).foldl (init := (.empty, gen)) fun (bytes, gen) _ =>
    let (b, gen) := randNat gen 0 255
    (bytes.push b.toUInt8, gen)

/-- `count` byte strings of random lengths up to `maxSize`, after one of each length up to
`exhaustive`. -/
def inputs (seed count maxSize exhaustive : Nat) : List ByteArray :=
  let (each, gen) := (List.range (exhaustive + 1)).foldl (init := ([], mkStdGen seed))
    fun (acc, gen) size => let (b, gen) := noise size gen; (b :: acc, gen)
  ((List.range count).foldl (init := (each, gen)) fun (acc, gen) _ =>
    let (size, gen) := randNat gen 0 maxSize
    let (b, gen) := noise size gen
    (b :: acc, gen)).1

/-- A pair of byte strings that are equal, differ in one byte, differ in length, or are a string
and a start of it, chosen at random. -/
def pair (gen : StdGen) : (ByteArray × ByteArray) × StdGen :=
  let (size, gen) := randNat gen 0 100
  let (a, gen) := noise size gen
  let (kind, gen) := randNat gen 0 3
  let (at_, gen) := randNat gen 0 (size - 1)
  let (flip, gen) := randNat gen 1 255
  let (other, gen) := noise (size + 1) gen
  let b := match kind with
    | 0 => a
    | 1 => if size = 0 then a else a.set! at_ (a[at_]! ^^^ flip.toUInt8)
    | 2 => other
    | _ => a.extract 0 at_
  ((a, b), gen)

def pairs (seed count : Nat) : List (ByteArray × ByteArray) :=
  ((List.range count).foldl (init := ([], mkStdGen seed)) fun (acc, gen) _ =>
    let (p, gen) := pair gen
    (p :: acc, gen)).1

def differentialTests : List (String × Bool) :=
  let messages := inputs 1 2000 1000 300
  let keys := inputs 2 400 200 130
  let compared := pairs 3 5000
  [ ("openssl: sha-256 equals the reference on 2301 messages of every length to 300 and to 1000",
      messages.all fun m => Sha256.hash m == Sha256.reference m),
    ("openssl: hmac-sha-256 equals the reference on 531 keys of every length to 130, each with a message",
      (keys.zip messages).all fun (k, m) => hmac k m == Hmac.reference k m),
    ("openssl: comparison equals the reference on 5000 pairs, equal, one byte apart, or not",
      compared.all fun (a, b) => Bytes.same a b == Bytes.sameReference a b),
    ("openssl: and those pairs are equal and unequal, and unequal in their last byte",
      compared.any (fun (a, b) => Bytes.same a b && a.size > 0)
        && compared.any (fun (a, b) => !Bytes.same a b && a.size == b.size)
        && Bytes.same (repeated 0 64) (repeated 0 64)
        && !Bytes.same (repeated 0 64) ((repeated 0 64).set! 63 1)) ]

def cost : Argon2id := { ops := 1, mem_kib := 64 }

def salt (b : UInt8) : {s : ByteArray // s.size = 16} := ⟨repeated b 16, by simp [repeated, ByteArray.size]⟩

def argon2idTests : List (String × Bool) :=
  let hash (cost : Argon2id) (password : String) (s : UInt8) :=
    cost.hash (bytesOf password) (salt s).1 (salt s).2
  let h := hash cost "password" 1
  [ ("argon2id: 32 bytes, the same each time", h.size == 32 && h == hash cost "password" 1),
    ("argon2id: another password, salt, number of passes or memory gives another hash",
      h != hash cost "passwore" 1 && h != hash cost "password" 2
        && h != hash { ops := 2, mem_kib := 64 } "password" 1
        && h != hash { ops := 1, mem_kib := 128 } "password" 1),
    ("argon2id: the least cost, and an empty password",
      (hash { ops := 1, mem_kib := 8 } "" 0).size == 32) ]

/-- Hashes made by libsodium 1.0.18's `crypto_pwhash` (Argon2id, version 19, one lane, 32 bytes)
before Lanes dropped it: password, salt and hash in hex, then passes and KiB. A digest stored
then must verify now. The memory of 9, 13 and 1023 KiB is not a multiple of 4, which Argon2
rounds down. -/
def libsodiumVectors : List (String × String × Nat × Nat × String) :=
  [ ("70617373776f7264", "01010101010101010101010101010101", 1, 64,
      "f630e220ef8ab2bc6bc39ff1dc6a039847b68849ca3c96371937ef53db99db55"),
    ("", "00000000000000000000000000000000", 1, 8,
      "cfa0d2d242da6703d311d7eefc922e39cc60c9f4ec93a67d20995be541a06be4"),
    ("636f727265637420686f727365206261747465727920737461706c65",
      "000102030405060708090a0b0c0d0e0f", 2, 19456,
      "818259b6310026a8e0dbac5d2e6927abcfdb07b32258fac4f61b18b80f929085"),
    ("70c3a4737377c3b6726420e29c9300", "f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff", 3, 4096,
      "930e7c2a0884d4d65932f4699f4945ca0085a18023218dc9e3a8b69fc029ed86"),
    (String.join (List.replicate 7 "6162636465666768696a6b6c6d6e6f707172737475767778797a")
        ++ "6162636465666768696a6b6c6d6e6f707172",
      "5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a", 1, 9,
      "423cbc7de648527dc7bd9e7b0bee04f3d0fd4b31abe704da7e6c8a1068c85662"),
    ("746869727465656e", "a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5", 4, 13,
      "36977690d21e6a85c32451f702149aa86ff4f4955661714ade441a305bcdccc7"),
    ("6f6464206d656d6f7279", "77777777777777777777777777777777", 1, 1023,
      "9e2d8c722f6d670e2b21f592e6a69ca98a6c9e6bce66422c17c2304e7044791a") ]

def libsodiumTests : List (String × Bool) :=
  (libsodiumVectors.map fun (password, salt, ops, kib, digest) =>
    (s!"argon2id: as libsodium made it, {password.length / 2} bytes, {ops} passes over {kib} KiB",
      match Bytes.unhex? password, Bytes.unhex? salt with
      | some password, some salt =>
        if h : salt.size = 16 ∧ 0 < ops.toUInt32 ∧ 8 ≤ kib.toUInt32 then
          let cost : Argon2id := { ops := ops.toUInt32, mem_kib := kib.toUInt32,
                                   ops_pos := h.2.1, mem_min := h.2.2 }
          Bytes.hex (cost.hash password salt h.1) == digest
        else false
      | _, _ => false))
  ++ [ ("argon2id: a password digest stored when libsodium made it",
      (({ cost := { ops := 2, mem_kib := 64 }, pepper := bytesOf "pepper of the deployment" }
        : Auth.Password).digest "alice" "longenough").hex
        == "d8da2482ae31637fd29537b3d11e1dd5960a0677b6ca8f3fabc11ea8301296da") ]

/-- Strings libsodium 1.0.18's `crypto_pwhash_str` made, each with its password: the PHC strings
Lanes stores (`Auth.Phc`). -/
def libsodiumStrings : List (String × String) :=
  [ ("password",
      "$argon2id$v=19$m=65536,t=2,p=1$E+tvRm1Cu4oTuZFABAPCHw$LsKhhcuq+lm2cwEIYZpzPqBwajj1j8tESD/wTFB7y7s"),
    ("", "$argon2id$v=19$m=8,t=1,p=1$yI8PO5+wXyL1PST2IX2uKQ$5x9249jB5yknGVeLbz2vmyfo/ACC/wO0iO/DPRDNDik"),
    ("correct horse battery staple",
      "$argon2id$v=19$m=19456,t=2,p=1$zzMGlkKU3Ui8mxjYogWDIQ$o9Qpy1K8M5YKtnbOCFdB2qU7nPt9/Y0zJ30MGJayw5M"),
    ("pässwörd",
      "$argon2id$v=19$m=1023,t=3,p=1$8AnvIv1+aZqutOp1asgPtA$Xqgs3JYhyhyNs8kck9wdtKu6nLCsy+I6ZHk9mqMifOk") ]

def verifiesString (password encoded : String) : Bool :=
  (Auth.Phc.parse? encoded).any (·.check (bytesOf password))

def libsodiumStringTests : List (String × Bool) :=
  (libsodiumStrings.map fun (password, encoded) =>
    (s!"argon2id: libsodium's string {encoded.take 30}… reads, verifies and is written back alike",
      verifiesString password encoded
        && (Auth.Phc.parse? encoded).map (·.encode) == some encoded))
  ++ [ ("argon2id: and not with another password",
      !verifiesString "passwore" (libsodiumStrings.head?.map (·.2) |>.getD "")),
    ("argon2id: a stored string verifies under a deployment of another cost, and asks to be hashed again",
      (Auth.Stored.read? (libsodiumStrings.head?.map (·.2) |>.getD "")).map
        (({ cost := { ops := 1, mem_kib := 64 }, pepper := .empty } : Auth.Password).verify "u" "password")
        == some .rehash) ]

/-- RFC 9106 §5.3:32 bytes of 1 as the password, 16 of 2 as the salt, 8 of 3 as the secret and 12
of 4 as associated data, three passes over 32 KiB in four lanes. -/
def rfc9106Tests : List (String × Bool) :=
  let tag := ({ ops := 3, mem_kib := 32 } : Argon2id).derive 4 (repeated 1 32) (salt 2).1
    (repeated 3 8) (repeated 4 12) (by rw [(salt 2).2]; decide) ⟨by decide, by decide, by decide⟩
  [ ("argon2id: RFC 9106's example",
      Bytes.hex tag == "0d640df58d78766c08c037a34a8b53c9d01ef0452d75b65eb52520e96b01e659") ]

def tests : List (String × Bool) :=
  sha256Tests ++ sha512Tests ++ hmacTests ++ bytesTests ++ differentialTests ++ argon2idTests
    ++ libsodiumTests ++ libsodiumStringTests ++ rfc9106Tests

def live : IO (List (String × Bool)) := do
  let a ← Lanes.randomBytes 32
  let b ← Lanes.randomBytes 32
  let none ← Lanes.randomBytes 0
  let dir := (← IO.getEnv "TMPDIR").getD "/tmp"
  let path : System.FilePath := s!"{dir}/lanes-fsync-{← IO.monoNanosNow}"
  Lanes.File.replace path "first"
  Lanes.File.replace path "second"
  let text ← IO.FS.readFile path
  Lanes.File.fsync path.toString
  Lanes.File.fsync dir
  let missing ← (Lanes.File.fsync (path.toString ++ ".missing")).toBaseIO
  let scratch ← (path.addExtension "tmp").pathExists
  IO.FS.removeFile path
  return [("random bytes: as many as asked, and two draws differ",
    a.size == 32 && b.size == 32 && a != b && none.size == 0),
    ("fsync: a file and its directory are synced, and a path that is not there is an error",
      missing matches .error _),
    ("File.replace: the file holds what was written last, and nothing is left beside it",
      text == "second" && !scratch)]

end Tests.Crypto
