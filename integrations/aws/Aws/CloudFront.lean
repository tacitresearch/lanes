/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
# Signed URLs and signed cookies for Amazon CloudFront

A link to private content behind CloudFront that works until a time: the URL with the query
parameters `Expires` (a canned policy) or `Policy` (a custom one), `Signature` and
`Key-Pair-Id`. Signed cookies carry the same, named `CloudFront-Expires` or `CloudFront-Policy`,
`CloudFront-Signature` and `CloudFront-Key-Pair-Id`, and grant every file a custom policy's
resource matches.

The signature is of the policy, a JSON document. For a canned policy CloudFront builds the
document again from the URL and `Expires`, so it must be byte for byte the one AWS documents,
which it is (`cannedPolicy_eq`); a custom policy travels in the link. The signature is
RSASSA-PKCS1-v1_5 under an RSA key of 2048 bits, or ECDSA under a P-256 key, over SHA-1, or over
SHA-256 when the link says `Hash-Algorithm=SHA256` (the cookie `CloudFront-Hash-Algorithm`), as
AWS's Go and JavaScript SDKs sign. It is made by `Lanes.SigningKey` (`native/sign.c`). The
policy and the signature are written in base64 with `+`, `=` and `/` as `-`, `_` and `~`, which
reads back (`decode_encode`) and needs no escaping in a URL or a cookie (`cookies_valid`).
-/

namespace Aws.CloudFront

open Lanes Lanes.Http

/-! ## Policies -/

/-- What a resource may hold: visible ASCII but `"` and `\`, so that JSON writes it as it is.
A URL's other characters are escaped as `%XX` before it is signed, as the browser sends them. -/
def resourceChar (c : Char) : Bool :=
  '!' ≤ c && c ≤ '~' && c != '"' && c != '\\'

/-- The URL a policy is for; in a custom policy `*` stands for any characters. -/
abbrev Resource := {s : String // s ≠ "" ∧ s.toList.all resourceChar = true}

def Resource.of? (s : String) : Option Resource :=
  if h : s ≠ "" ∧ s.toList.all resourceChar = true then some ⟨s, h⟩ else none

/-- A range of IPv4 addresses, `a.b.c.d/bits`. A policy cannot name IPv6 addresses. -/
structure Cidr where
  addr : Fin (2 ^ 32)
  bits : Fin 33
  deriving DecidableEq, Repr

def Cidr.text (c : Cidr) : String := String.ofList (Ip.print4 c.addr.val) ++ "/" ++ toString c.bits.val

/-- What a custom policy grants: `resource` before the second `dateLessThan_s`, from the second
`dateGreaterThan_s` if it is given, to the addresses of `ipAddress` if it is given. Seconds are
counted from 1970. -/
structure Policy where
  resource : Resource
  dateLessThan_s : Nat
  dateGreaterThan_s : Option Nat := none
  ipAddress : Option Cidr := none
  deriving DecidableEq, Repr

def epoch (s : Nat) : Json := .obj #[("AWS:EpochTime", (s : Json))]

/-- The conditions in the order botocore writes them; CloudFront reads them in any order. -/
def Policy.conditions (p : Policy) : Array (String × Json) :=
  #[("DateLessThan", epoch p.dateLessThan_s)]
    ++ (p.ipAddress.map fun c => ("IpAddress", Json.obj #[("AWS:SourceIp", .str c.text)])).toArray
    ++ (p.dateGreaterThan_s.map fun s => ("DateGreaterThan", epoch s)).toArray

/-- The document, its fields in the order AWS documents them: `Json.obj` keeps the order given,
where `Json.mkObj` would sort it. -/
def Policy.document (p : Policy) : Json :=
  .obj #[("Statement", .arr #[.obj #[("Resource", .str p.resource.val),
    ("Condition", .obj p.conditions)]])]

def Policy.text (p : Policy) : String := p.document.compress

/-- The policy CloudFront builds from a link to `resource` with `Expires=expires_s`. -/
def cannedPolicy (resource : Resource) (expires_s : Nat) : String :=
  Policy.text { resource, dateLessThan_s := expires_s }

/-! ## CloudFront's base64 -/

/-- `+`, `=` and `/` as `-`, `_` and `~`, and the other way: the characters base64 writes that
a URL or a cookie cannot carry, swapped with ones base64 never writes. -/
def swap (c : Char) : Char :=
  if c = '+' then '-' else if c = '-' then '+'
  else if c = '=' then '_' else if c = '_' then '='
  else if c = '/' then '~' else if c = '~' then '/' else c

/-- What `encode` writes: letters, digits, `-`, `_` and `~`, none of which a URL escapes. -/
def urlSafe (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == '~'

def encode (bytes : ByteArray) : String :=
  String.ofList ((Base64.encode .std bytes).toList.map swap)

def decode (s : String) : Option ByteArray :=
  Base64.decode .std (String.ofList (s.toList.map swap))

/-! ## Links and cookies -/

/-- The ID CloudFront gives a public key, `K2JCJMDEHXQW5F`: letters and digits. -/
abbrev KeyId := {s : String // s ≠ "" ∧ s.toList.all (fun c => c.isAlphanum && c.toNat < 128) = true}

def KeyId.of? (s : String) : Option KeyId :=
  if h : s ≠ "" ∧ s.toList.all (fun c => c.isAlphanum && c.toNat < 128) = true then some ⟨s, h⟩
  else none

/-- What a link or cookies grant. -/
inductive Grant where
  /-- The URL itself, before `expires_s`. -/
  | canned (expires_s : Nat)
  /-- What the policy says. -/
  | custom (policy : Policy)
  deriving DecidableEq, Repr

/-- The policy that is signed for a link to `url`. -/
def Grant.policy (url : Resource) : Grant → Policy
  | .canned e => { resource := url, dateLessThan_s := e }
  | .custom p => p

/-- The parameters of a link, in the order AWS writes them, given the signature of the policy;
the names of the cookies are these with `CloudFront-` before them. -/
def fields (keyId : KeyId) (digest : Digest) (g : Grant) (signature : ByteArray) :
    List (String × String) :=
  (match g with
    | .canned e => ("Expires", toString e)
    | .custom p => ("Policy", encode p.text.toUTF8))
  :: [("Signature", encode signature), ("Key-Pair-Id", keyId.val)]
  ++ if digest = .sha256 then [("Hash-Algorithm", "SHA256")] else []

/-- `url` with `fields` added to its query. -/
def link (url : Resource) (fields : List (String × String)) : String :=
  url.val ++ (if url.val.contains '?' then "&" else "?")
    ++ "&".intercalate (fields.map fun (k, v) => k ++ "=" ++ v)

/-- The cookies of `fields`, for `path`. They are sent only to the host that set them, since a
`Cookie` has no `Domain`: the site and CloudFront must be one host, the site behind CloudFront. -/
def cookies (fields : List (String × String)) (path : String := "/") : List Cookie :=
  fields.map fun (k, v) => { name := "CloudFront-" ++ k, value := v, path }

/-- A private key, the ID of its public half in CloudFront, and the hash to sign over. -/
structure Signer where
  keyId : KeyId
  key : SigningKey
  digest : Digest := .sha1
  deriving Repr

/-- The keys CloudFront takes: RSA of 2048 bits and P-256. -/
def accepted : PublicKey → Bool
  | .rsa n _ => Bytes.toNat n < 2 ^ 2048
  | .p256 .. => true

/-- A signer with the key in `pem`. -/
def Signer.ofPem (keyId : String) (pem : ByteArray) (digest : Digest := .sha1) :
    Except String Signer := do
  let some keyId := KeyId.of? keyId | throw "cloudfront: a key's ID is letters and digits"
  let key ← SigningKey.ofPem pem
  unless accepted key.publicKey do throw "cloudfront: the key is neither RSA of 2048 bits nor P-256"
  return { keyId, key, digest }

def Signer.fields (s : Signer) (url : Resource) (g : Grant) : Except String (List (String × String)) :=
  match s.key.sign s.digest (g.policy url).text.toUTF8 with
  | some signature => .ok (CloudFront.fields s.keyId s.digest g signature)
  | none => .error "cloudfront: OpenSSL could not sign"

/-- The link to `url` that `g` grants. -/
def Signer.url (s : Signer) (url : Resource) (g : Grant) : Except String String :=
  return link url (← s.fields url g)

/-- The cookies that grant `g`, for `url` if it is canned. -/
def Signer.cookies (s : Signer) (url : Resource) (g : Grant) (path : String := "/") :
    Except String (List Cookie) :=
  return CloudFront.cookies (← s.fields url g) path

end Aws.CloudFront
