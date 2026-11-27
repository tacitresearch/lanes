/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.S3.Basic
public import Lanes.Lib.Encoding.Json
public import Lanes.Lib.Encoding.Base64

/-!
A browser's upload by `POST`, under a policy: the form a page carries for S3 to take one file,
whose policy, a JSON document in base64 signed with Signature Version 4, says what the upload may
be. Unlike a presigned `PUT`, it bounds the file's size (`content-length-range`), and it may let
the browser choose the key under a prefix.

`form` writes the policy and the fields; `check` is what S3 does with a form it receives, apart
from the signature: the policy unexpired, each condition met, and each field named by one. Proved
(`Lanes/Web/S3/PostSound.lean`): the policy a form carries reads back as exactly the conditions
given, its expiry is the one given, and a file `check` admits has a size within the range.
-/

@[expose] public section

namespace Lanes.S3.Post

open Http SigV4

/-- A condition of a policy. A field is named as the form names it, without `$`. -/
inductive Condition where
  | eq (field value : String)
  | startsWith (field «prefix» : String)
  /-- The file's size in bytes, both ends included: `content-length-range`. -/
  | length (min max : Nat)
  deriving DecidableEq, Repr

def Condition.json : Condition → Json
  | .eq field value => .obj #[(field, .str value)]
  | .startsWith field p => .arr #[.str "starts-with", .str ("$" ++ field), .str p]
  | .length min max => .arr #[.str "content-length-range", .num min, .num max]

/-- A field as a condition names it, `$key`. -/
def field? (s : String) : Option String :=
  match s.toList with
  | '$' :: rest => some (String.ofList rest)
  | _ => none

/-- A condition in each form S3 reads: `{"field": "value"}`, `["eq", "$field", "value"]`,
`["starts-with", "$field", "prefix"]` and `["content-length-range", min, max]`. -/
def Condition.read? : Json → Option Condition
  | .obj fields => match fields.toList with
    | [(field, .str value)] => some (.eq field value)
    | _ => none
  | .arr elems => match elems.toList with
    | [.str op, .str f, .str v] =>
      if op = "eq" then (field? f).map (.eq · v)
      else if op = "starts-with" then (field? f).map (.startsWith · v)
      else none
    | [.str op, .num min, .num max] =>
      if op = "content-length-range" then do return .length (← min.toNat?) (← max.toNat?)
      else none
    | _ => none
  | _ => none

structure Document where
  /-- RFC 3339, in UTC. -/
  expiration : String
  conditions : List Condition
  deriving DecidableEq, Repr

/-- Its fields in the order of their names, as `Json.mkObj` keeps them. -/
def Document.json (d : Document) : Json :=
  .obj #[("conditions", .arr (d.conditions.map Condition.json).toArray),
    ("expiration", .str d.expiration)]

def Document.read? (j : Json) : Option Document := do
  let expiration ← (j.getObjVal? "expiration" >>= Json.getStr?).toOption
  let conditions ← (j.getObjVal? "conditions" >>= Json.getArr?).toOption
  return { expiration, conditions := ← conditions.toList.mapM Condition.read? }

/-- The policy as a form carries it: the document's JSON in base64. -/
def Document.encode (d : Document) : String := Base64.encode .std (Json.compress d.json).toUTF8

/-- The document a form's policy holds, as S3 reads it. -/
def decode? (policy : String) : Option Document := do
  let text ← String.fromUTF8? (← Base64.decode .std policy)
  Document.read? (← (Json.parse text).toOption)

/-- The policy's signature: the policy itself is the string to sign. -/
def signature (secret : Secret) (t : Civil.DateTime) (scope : Scope) (policy : String) : String :=
  Bytes.hex (hmac (signingKey secret t scope) policy.toUTF8)

/-! ## What S3 checks -/

/-- Why S3 refuses a form, its signature apart. -/
inductive Refusal where
  | unreadable
  | expired
  | unmet (c : Condition)
  /-- A field no condition names. -/
  | unnamed (field : String)
  deriving DecidableEq, Repr

/-- A field's value, its name compared without regard to case, as S3 compares them. -/
def lookup (fields : List (String × String)) (name : String) : Option String :=
  (fields.find? (·.1.toLower == name.toLower)).map (·.2)

/-- Whether a file of `size` bytes, sent with `fields` (the bucket's name among them, as
`bucket`), meets `c`. -/
def Condition.holds (fields : List (String × String)) (size : Nat) : Condition → Bool
  | .eq field value => lookup fields field == some value
  | .startsWith field p => (lookup fields field).any (·.startsWith p)
  | .length min max => min ≤ size && size ≤ max

def Condition.field? : Condition → Option String
  | .eq field _ | .startsWith field _ => some field.toLower
  | .length .. => none

/-- The fields no condition need name: the policy, its signature, the file, and those S3
ignores. -/
def exempt (name : String) : Bool :=
  let n := name.toLower
  n == "policy" || n == "x-amz-signature" || n == "file" || n.startsWith "x-ignore-"

/-- What S3 does with the form `fields` and a file of `size` bytes for `bucket` at `now_s`,
under the policy `d`, the signature checked apart. -/
def check (d : Document) (bucket : String) (fields : List (String × String)) (size : Nat)
    (now_s : Int) : Except Refusal Unit :=
  let named := d.conditions.filterMap Condition.field?
  match TimeFormat.parseRfc3339 d.expiration with
  | none => .error .unreadable
  | some expires =>
    if now_s < expires.toUnix then
      match d.conditions.find? (!·.holds (("bucket", bucket) :: fields) size) with
      | some c => .error (.unmet c)
      | none =>
        match fields.find? fun (n, _) => !exempt n && !named.contains n.toLower with
        | some (name, _) => .error (.unnamed name)
        | none => .ok ()
    else .error .expired

/-! ## A form for a browser -/

/-- What the key may be: one, or any under a prefix, which the browser chooses. -/
inductive KeyRule where
  | exact (key : Key)
  | startsWith (keyPrefix : String)
  deriving DecidableEq, Repr

def KeyRule.condition : KeyRule → Condition
  | .exact key => .eq "key" key.val
  | .startsWith p => .startsWith "key" p

/-- The `key` field: the key, or the prefix and `${filename}`, which S3 replaces with the name
of the file the browser sends. -/
def KeyRule.field : KeyRule → String
  | .exact key => key.val
  | .startsWith p => p ++ "${filename}"

/-- The most S3 takes in one `POST`: 5 GiB. -/
def maxObject_bytes : Nat := 5 * 1024 ^ 3

/-- How large the file may be. -/
structure Length where
  min : Nat
  max : Nat
  ordered : min ≤ max
  bounded : max ≤ maxObject_bytes
  deriving DecidableEq, Repr

structure Policy where
  key : KeyRule
  length : Length
  /-- The `Content-Type` the browser must send, which S3 stores with the object. -/
  contentType : Option String := none
  expiry : Expiry
  deriving DecidableEq, Repr

/-- The moment `expiry` seconds after `t`, in RFC 3339. -/
def expiration (t : Civil.DateTime) (expiry : Expiry) : String :=
  String.ofList (TimeFormat.rfc3339Chars ⟨.ofUnix (t.toUnix + expiry.val), 0, ⟨0, by decide⟩⟩)

def credential (b : Bucket) (creds : Credentials) (t : Civil.DateTime) : String :=
  creds.accessKeyId ++ "/" ++ credentialScope t b.scope

def typed (p : Policy) : List (String × String) := (p.contentType.map ("Content-Type", ·)).toList

/-- The fields that say who signed and when, which the policy names exactly. -/
def signer (b : Bucket) (creds : Credentials) (t : Civil.DateTime) : List (String × String) :=
  [("x-amz-algorithm", algorithm), ("x-amz-credential", credential b creds t), ("x-amz-date", stamp t)]
    ++ (creds.sessionToken.map fun s => ("x-amz-security-token", s.reveal)).toList

def eqs (fields : List (String × String)) : List Condition := fields.map fun (n, v) => .eq n v

/-- In the order botocore writes them. -/
def conditions (b : Bucket) (creds : Credentials) (t : Civil.DateTime) (p : Policy) :
    List Condition :=
  .length p.length.min p.length.max :: eqs (typed p)
    ++ [.eq "bucket" b.name, p.key.condition] ++ eqs (signer b creds t)

def document (b : Bucket) (creds : Credentials) (t : Civil.DateTime) (p : Policy) : Document :=
  { expiration := expiration t p.expiry, conditions := conditions b creds t p }

/-- What a page needs to upload: where to post, and the fields to send before the file, which
goes last, as `file`. -/
structure Form where
  url : String
  policy : String
  signature : String
  /-- Every field but the policy and its signature, in order. -/
  named : List (String × String)
  deriving DecidableEq, Repr

/-- The fields of the form, in the order they are sent. -/
def Form.fields (f : Form) : List (String × String) :=
  f.named ++ [("policy", f.policy), ("x-amz-signature", f.signature)]

/-- Where a form for `b` is posted: the bucket's root, `https://bucket.host/` or
`http://host:port/bucket`. -/
def _root_.Lanes.S3.Bucket.url (b : Bucket) : String :=
  let call : Client.Call := { host := b.host, port := b.endpoint.port, scheme := b.endpoint.scheme
                              request := { method := .post, path := [] } }
  let scheme := match b.endpoint.scheme with | .http => "http" | .https => "https"
  scheme ++ "://" ++ call.authority ++ "/" ++ "/".intercalate (b.path [])

/-- The form for one upload to `b` under `p`, signed with `creds` at `t`. -/
def form (b : Bucket) (creds : Credentials) (t : Civil.DateTime) (p : Policy) : Form :=
  let policy := (document b creds t p).encode
  { url := b.url, policy, signature := signature creds.secretAccessKey t b.scope policy
    named := typed p ++ ("key", p.key.field) :: signer b creds t }

end Lanes.S3.Post
