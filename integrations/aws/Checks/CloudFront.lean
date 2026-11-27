/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Aws
import Tests.Oracle.Basic

/-!
CloudFront's signed URLs, `Aws.CloudFront.Signer.url`, against botocore's `CloudFrontSigner`
(`oracles/botocore`): the policy signed and the URL, byte for byte, signature included. Both sign
with the keys of `oracles/botocore/keys/`, published test keys: ours by OpenSSL
(`native/sign.c`), botocore's through `cryptography`, RSA with PKCS #1 v1.5 and ECDSA with RFC
6979's nonce, so the two signatures are the same bytes. The unit tests check the cookies, a link
CloudFront documents the shape of, and the keys a signer refuses.
-/

namespace Checks.CloudFront

open Lanes Tests.Oracle Aws.CloudFront

def testing (pem : String) : ByteArray := (pem.replace "TESTING KEY" "PRIVATE KEY").toUTF8

def rsaPem : ByteArray := testing (include_str "../../../oracles/botocore/keys/rsa2048.pem")

def p256Pem : ByteArray := testing (include_str "../../../oracles/botocore/keys/p256.pem")

structure Spec where
  key : String
  hash : String
  keyId : String
  url : String
  canned : Bool
  expires : Nat
  resource : String := ""
  start : Option Nat := none
  ip : Option (Nat × Nat) := none

def Spec.json (s : Spec) : Json :=
  Json.mkObj ([("key", Json.str s.key), ("hash", .str s.hash), ("keyId", .str s.keyId),
    ("url", .str s.url), ("canned", .bool s.canned), ("expires", (s.expires : Json))]
    ++ (if s.canned then [] else [("resource", Json.str s.resource)])
    ++ (s.start.map fun t => ("start", (t : Json))).toList
    ++ (s.ip.map fun (a, b) => ("ip", Json.arr #[(a : Json), (b : Json)])).toList)

def readSpec (input : ByteArray) : Except String Spec := do
  let some text := String.fromUTF8? input | throw "not UTF-8"
  let j ← Json.parse text
  let str (name : String) : Except String String := do (← j.getObjVal? name).getStr?
  let nat (name : String) : Except String Nat := do (← j.getObjVal? name).getNat?
  let canned ← (← j.getObjVal? "canned").getBool?
  let ip ← match j.getObjVal? "ip" with
    | .ok v => match v.getArr?.toOption.map (·.toList) with
      | some [a, b] => pure (some (← a.getNat?, ← b.getNat?))
      | _ => throw "ip"
    | .error _ => pure none
  return { key := ← str "key", hash := ← str "hash", keyId := ← str "keyId", url := ← str "url",
           canned, expires := ← nat "expires", resource := (str "resource").toOption.getD "",
           start := (nat "start").toOption, ip }

def signer (s : Spec) : Option Signer :=
  (Signer.ofPem s.keyId (if s.key == "p256" then p256Pem else rsaPem)
    (if s.hash == "sha256" then .sha256 else .sha1)).toOption

def Spec.grant (s : Spec) : Option Grant := do
  if s.canned then return .canned s.expires
  let resource ← Resource.of? s.resource
  let ipAddress ← match s.ip with
    | some (a, b) => if h : a < 2 ^ 32 ∧ b < 33 then pure (some ⟨⟨a, h.1⟩, ⟨b, h.2⟩⟩) else none
    | none => pure none
  return .custom { resource, dateLessThan_s := s.expires, dateGreaterThan_s := s.start, ipAddress }

def answer (c : Case) : Answer := do
  let s ← (readSpec c.input).toOption
  let url ← Resource.of? s.url
  let g ← s.grant
  let link ← ((← signer s).url url g).toOption
  return Json.mkObj [("policy", (g.policy url).text), ("url", link)]

/-! ## Cases -/

def hosts : List String := ["https://d111111abcdef8.cloudfront.net", "https://media.example.com",
  "http://d111111abcdef8.cloudfront.net"]

def segments : List String :=
  ["videos", "a.mp4", "horizon.jpg", "a%20b", "a+b", "~x", "*", "", "2026", "x.m3u8", "#frag",
    "a=b&c", "%C3%A9"]

/-- Segments ours refuses and botocore signs. -/
def odd : List String := ["a b", "\"q\"", "a\\b", "é"]

def queries : List String := ["", "", "", "?size=large&license=yes", "?a=1", "?", "?x=%2F"]

def keyIds : List String := ["K2JCJMDEHXQW5F", "APKAEIBAERJR2EXAMPLE"]

def time : Gen Nat := do
  match ← Gen.below 4 with
  | 0 => Gen.pick [0, 1, 2 ^ 31 - 1, 2 ^ 31, 1767225600, 253402300799]
  | _ => return 1700000000 + (← Gen.below 100000000)

def genUrl : Gen String := do
  let path ← Gen.list (← Gen.below 4) (Gen.pick segments)
  let path ← if ← Gen.chance 10 then pure (path ++ [← Gen.pick odd]) else pure path
  return (← Gen.pick hosts) ++ "/" ++ "/".intercalate path ++ (← Gen.pick queries)

def genSpec : Gen Spec := do
  let url ← genUrl
  let canned ← Gen.chance 50
  let wild ← Gen.chance 50
  let resource := if wild then (url.splitOn "?").headD url ++ "*" else url
  let start ← if ← Gen.chance 50 then some <$> time else pure none
  let ip ← if ← Gen.chance 50 then
      pure (some ((← Gen.below (2 ^ 32)), (← Gen.pick [0, 8, 16, 24, 31, 32, 32])))
    else pure none
  return { key := ← Gen.pick ["rsa2048", "p256"], hash := ← Gen.pick ["sha1", "sha256"],
           keyId := ← Gen.pick keyIds, url, canned, expires := ← time, resource, start, ip }

def case : Gen Case := do return ⟨"cloudfront", (← genSpec).json.compress.toUTF8⟩

/-- AWS's examples: a canned link to a file with a query, and a custom policy for a directory
from an address range. -/
def edges : List Case :=
  [ { key := "rsa2048", hash := "sha1", keyId := "K2JCJMDEHXQW5F", canned := true,
      url := "https://d111111abcdef8.cloudfront.net/image.jpg?color=red&size=medium",
      expires := 1767290400 },
    { key := "rsa2048", hash := "sha1", keyId := "K2JCJMDEHXQW5F", canned := false,
      url := "https://d111111abcdef8.cloudfront.net/training/orientation.avi",
      resource := "https://d111111abcdef8.cloudfront.net/training/*", expires := 1767290400,
      ip := some (0xC0000200, 24) },
    { key := "p256", hash := "sha256", keyId := "K2JCJMDEHXQW5F", canned := true,
      url := "https://media.example.com/a.mp4", expires := 0 },
    { key := "p256", hash := "sha1", keyId := "K2JCJMDEHXQW5F", canned := false,
      url := "https://media.example.com/a.mp4", resource := "https://media.example.com/*",
      expires := 253402300799, start := some 0, ip := some (1, 32) } ].map
    fun (s : Spec) => ⟨"cloudfront", s.json.compress.toUTF8⟩

/-! ## Where ours departs from botocore -/

/-- Ours takes a resource of visible ASCII but `"` and `\`, which JSON writes as they are and a
browser sends as they are; botocore signs any string, escaping in JSON what needs it. -/
def outsideResource (s : Spec) : Bool :=
  !(s.url.toList.all resourceChar && (s.canned || s.resource.toList.all resourceChar))

def package : Package where
  name := "cloudfront"
  reference := .python "botocore"
  answers := "cloudfront.jsonl"
  edges := edges
  case := case
  answer := answer
  shrinks := false
  recorded := 200
  known c _ := (readSpec c.input).toOption.bind fun s =>
    if (answer c).isNone && outsideResource s then
      some "ours signs a resource of visible ASCII but \" and \\; botocore any string"
    else none

/-! ## Unit tests -/

def sample : Option Signer := (Signer.ofPem "K2JCJMDEHXQW5F" rsaPem).toOption

def url : Resource := ⟨"https://d111111abcdef8.cloudfront.net/image.jpg", by decide⟩

def directory : Policy :=
  { resource := ⟨"https://d111111abcdef8.cloudfront.net/*", by decide⟩, dateLessThan_s := 9 }

def tests : List (String × Bool) :=
  let ok {α : Type} (r : Except String α) := r.toOption.isSome
  [ ("cloudfront: a canned link is the URL, Expires, Signature and Key-Pair-Id",
      sample.any fun s => match s.url url (.canned 1767290400) with
        | .ok link => link.startsWith (url.val ++ "?Expires=1767290400&Signature=")
            && link.endsWith "&Key-Pair-Id=K2JCJMDEHXQW5F"
        | .error _ => false),
    ("cloudfront: the signature in a link reads back and checks under the public key",
      (Signer.ofPem "K2JCJMDEHXQW5F" rsaPem .sha256).toOption.any fun s =>
        match s.fields url (.canned 5) with
        | .ok fs => (fs.lookup "Signature").bind decode |>.any fun sig =>
            s.key.publicKey.verifies (cannedPolicy url 5).toUTF8 sig
              && fs.lookup "Hash-Algorithm" == some "SHA256"
        | .error _ => false),
    ("cloudfront: the cookies carry what the link does, under CloudFront- names, and are set",
      sample.any fun s => match s.fields url (.canned 9), s.cookies url (.canned 9) "/media" with
        | .ok fs, .ok cs =>
          cs.map (fun c => (c.name, c.value)) == fs.map (fun (k, v) => ("CloudFront-" ++ k, v))
            && cs.map (·.name) == ["CloudFront-Expires", "CloudFront-Signature", "CloudFront-Key-Pair-Id"]
            && cs.all fun c => c.path == "/media" && c.secure && c.httpOnly
            && c.valid
        | _, _ => false),
    ("cloudfront: custom cookies are CloudFront-Policy, -Signature, -Key-Pair-Id",
      sample.any fun s =>
        match s.cookies url (.custom directory) with
        | .ok cs => cs.map (·.name) == ["CloudFront-Policy", "CloudFront-Signature", "CloudFront-Key-Pair-Id"]
        | .error _ => false),
    ("cloudfront: a P-256 key signs, an ID that is not letters and digits is refused",
      ok (Signer.ofPem "K2JCJMDEHXQW5F" p256Pem) && !ok (Signer.ofPem "" rsaPem)
        && !ok (Signer.ofPem "K2 X" rsaPem) && !ok (Signer.ofPem "K2JCJMDEHXQW5F" "x".toUTF8)),
    ("cloudfront: RSA keys of other than 2048 bits are refused",
      !accepted (.rsa (Bytes.ofNat 384 (2 ^ 3071 + 1)) ⟨#[1, 0, 1]⟩)
        && accepted (.rsa (Bytes.ofNat 256 (2 ^ 2047 + 1)) ⟨#[1, 0, 1]⟩)),
    ("cloudfront: CloudFront's base64 has no +, = or /, and reads back",
      ([ByteArray.empty, ⟨#[0xfb, 0xff]⟩, ⟨#[0xff, 0xfe, 0xfd, 0xfc]⟩].all fun b =>
        decode (encode b) == some b && !(encode b).any fun c => c == '+' || c == '=' || c == '/')
        && encode ⟨#[0xfb, 0xff]⟩ == "-~8_"),
    ("cloudfront: a resource with a space, a quote, a backslash or é is refused",
      ["", "a b", "a\"b", "a\\b", "é"].all fun s => (Resource.of? s).isNone) ]

end Checks.CloudFront
