/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
SHA-256 against the examples of FIPS 180-4 (as NIST publishes them), HMAC-SHA-256 against
RFC 4231 and PBKDF2-HMAC-SHA-256 against RFC 7914 section 11 and the vectors in common use.
-/

namespace Tests.Crypto

open Lanes

def bytesOf (s : String) : ByteArray := s.toUTF8

def repeated (b : UInt8) (n : Nat) : ByteArray := ⟨Array.replicate n b⟩

def sha (msg : ByteArray) : String := Bytes.hex (Sha256.hash msg)

def mac (key msg : ByteArray) : String := Bytes.hex (hmac key msg)

def kdf (password salt : String) (iterations length : Nat) : String :=
  Bytes.hex (pbkdf2 (bytesOf password) (bytesOf salt) iterations length)

def sha256Tests : List (String × Bool) :=
  [ ("sha-256: the empty message",
      sha .empty == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ("sha-256: abc",
      sha (bytesOf "abc") == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
    ("sha-256: the 448-bit message, two blocks",
      sha (bytesOf "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
        == "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
    ("sha-256: the 896-bit message",
      sha (bytesOf ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno"
        ++ "ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"))
        == "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"),
    ("sha-256: a million times a",
      sha (repeated 0x61 1000000)
        == "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"),
    ("sha-256: every length from 0 to 130 pads to whole blocks",
      (List.range 131).all fun n => (n + (Sha256.padding n).size) % 64 == 0
        && (Sha256.hash (repeated 0 n)).size == 32) ]

def hmacTests : List (String × Bool) :=
  [ ("hmac-sha-256: RFC 4231 case 1",
      mac (repeated 0x0b 20) (bytesOf "Hi There")
        == "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"),
    ("hmac-sha-256: RFC 4231 case 2, a key shorter than the output",
      mac (bytesOf "Jefe") (bytesOf "what do ya want for nothing?")
        == "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"),
    ("hmac-sha-256: RFC 4231 case 3",
      mac (repeated 0xaa 20) (repeated 0xdd 50)
        == "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe"),
    ("hmac-sha-256: RFC 4231 case 4",
      mac ⟨(List.range 25).toArray.map fun k => (k + 1).toUInt8⟩ (repeated 0xcd 50)
        == "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b"),
    ("hmac-sha-256: RFC 4231 case 6, a key longer than a block",
      mac (repeated 0xaa 131) (bytesOf "Test Using Larger Than Block-Size Key - Hash Key First")
        == "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"),
    ("hmac-sha-256: RFC 4231 case 7, key and data longer than a block",
      mac (repeated 0xaa 131) (bytesOf ("This is a test using a larger than block-size key and a "
        ++ "larger than block-size data. The key needs to be hashed before being used by the HMAC "
        ++ "algorithm."))
        == "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2") ]

def pbkdf2Tests : List (String × Bool) :=
  [ ("pbkdf2-hmac-sha-256: RFC 7914, passwd and salt, one iteration, 64 bytes",
      kdf "passwd" "salt" 1 64 == "55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57c20dacbc"
        ++ "49ca9cccf179b645991664b39d77ef317c71b845b1e30bd509112041d3a19783"),
    ("pbkdf2-hmac-sha-256: password and salt, one iteration",
      kdf "password" "salt" 1 32
        == "120fb6cffcf8b32c43e7225256c4f837a86548c92ccc35480805987cb70be17b"),
    ("pbkdf2-hmac-sha-256: password and salt, two iterations",
      kdf "password" "salt" 2 32
        == "ae4d0c95af6b46d32d0adff928f06dd02a303f8ef3c251dfd6e2d85a95474c43"),
    ("pbkdf2-hmac-sha-256: password and salt, 4096 iterations",
      kdf "password" "salt" 4096 32
        == "c5e478d59288c841aa530db6845c4c8d962893a001ce4e11a4963873aa98134a"),
    ("pbkdf2-hmac-sha-256: RFC 7914, Password and NaCl, 80000 iterations, 64 bytes",
      kdf "Password" "NaCl" 80000 64
        == "4ddcd8f60b98be21830cee5ef22701f9641a4418d04c0414aeff08876b34ab56"
          ++ "a1d425a1225833549adb841b51c9b3176a272bdebba1d078478f62b397f33c8d"),
    ("pbkdf2-hmac-sha-256: an output length that is not a whole block",
      (kdf "password" "salt" 1 20).length == 40
        && "120fb6cffcf8b32c43e7225256c4f837a86548c9".isPrefixOf (kdf "password" "salt" 1 20)) ]

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

def tests : List (String × Bool) :=
  sha256Tests ++ hmacTests ++ pbkdf2Tests ++ bytesTests

end Tests.Crypto
