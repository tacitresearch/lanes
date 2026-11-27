/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.Wire
public import Lanes.Lib.Crypto.Sodium
public import Lanes.Lib.Time.Format

/-!
Signature Version 4: how a request to an AWS API, or to a store that speaks the S3 API, says who
sends it. A canonical form of the request is hashed into a string to sign, which is signed with
a key derived from the secret, the day, the region and the service; the signature goes in an
`Authorization` header or, for a link a browser follows, in the query (`presign`).

The canonical form is written from the same request the client sends, and what the client
writes as the target is the canonical path and query (`SigV4.target_sign`), so the bytes signed
are the bytes sent. A path is signed as S3 signs it: each segment escaped once. Services that
escape the path twice sign the same unless a segment needs escaping. HMAC-SHA-256 and SHA-256
are libsodium's, with the Lean references as their bodies (`Lanes/Lib/Crypto/Sodium.lean`).
-/

@[expose] public section

namespace Lanes.SigV4

open Http

/-- A secret, such as an access key or a session token. Printed, it shows nothing of itself, so
a value that holds one may derive `Repr`. -/
structure Secret where
  /-- Read only to sign with it or to send it where it belongs. -/
  reveal : String

instance : Repr Secret := ⟨fun _ _ => "<secret>"⟩

instance : ToString Secret := ⟨fun _ => "<secret>"⟩

structure Credentials where
  accessKeyId : String
  secretAccessKey : Secret
  /-- Given with credentials of a role, sent as `X-Amz-Security-Token`. -/
  sessionToken : Option Secret := none
  deriving Repr

/-- Where a signature is good, besides its day. -/
structure Scope where
  region : String
  service : String
  deriving DecidableEq, Repr

/-- The moment of signing in the basic ISO 8601 form, `20130524T000000Z`, in UTC; the year
written with four digits. -/
def stamp (t : Civil.DateTime) : String :=
  String.ofList (TimeFormat.d4 t.date.year.toNat ++ TimeFormat.d2 t.date.month
    ++ TimeFormat.d2 t.date.day ++ 'T' :: TimeFormat.d2 t.time.hour.val
    ++ TimeFormat.d2 t.time.minute.val ++ TimeFormat.d2 t.time.second.val ++ ['Z'])

def day (t : Civil.DateTime) : String :=
  String.ofList (TimeFormat.d4 t.date.year.toNat ++ TimeFormat.d2 t.date.month
    ++ TimeFormat.d2 t.date.day)

def credentialScope (t : Civil.DateTime) (scope : Scope) : String :=
  day t ++ "/" ++ scope.region ++ "/" ++ scope.service ++ "/aws4_request"

/-! ## The canonical request -/

/-- Escaped as AWS escapes: every byte but letters, digits and `-._~` as `%XX`, in capitals. -/
def encode (s : String) : String := percentEncode s

def canonicalPath (segments : List String) : String := "/" ++ "/".intercalate (segments.map encode)

def encodePair (p : String × String) : String × String := (encode p.1, encode p.2)

/-- The order of the canonical query: by escaped name, then by escaped value. -/
def pairLe (a b : String × String) : Bool := decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 ≤ b.2))

/-- The parameters in the canonical order, unescaped. -/
def sortQuery (query : List (String × String)) : List (String × String) :=
  query.mergeSort fun a b => pairLe (encodePair a) (encodePair b)

def canonicalQuery (query : List (String × String)) : String :=
  "&".intercalate ((sortQuery query).map fun p => (encodePair p).1 ++ "=" ++ (encodePair p).2)

def blank (c : Char) : Bool := c == ' ' || c == '\t'

/-- Runs of blanks as one space. -/
def squeeze : List Char → List Char
  | a :: b :: rest => if blank a && blank b then squeeze (' ' :: rest) else
      (if blank a then ' ' else a) :: squeeze (b :: rest)
  | [a] => [if blank a then ' ' else a]
  | [] => []
termination_by l => l.length

/-- A header's value as signed: without blanks at either end, and a run of them inside as one
space. -/
def trimValue (v : String) : String :=
  String.ofList ((squeeze (v.toList.dropWhile blank)).reverse.dropWhile blank).reverse

/-- Adds a header to canonical ones kept in order of name: a name already there gets the value
after a comma. -/
def insertHeader : List (String × String) → String × String → List (String × String)
  | [], h => [h]
  | (n, v) :: rest, (m, w) =>
    if m < n then (m, w) :: (n, v) :: rest
    else if m = n then (n, v ++ "," ++ w) :: rest
    else (n, v) :: insertHeader rest (m, w)

/-- The headers as signed: names in lowercase and in order, each once, with the values given
for it joined by commas in the order given. -/
def canonicalHeaders (headers : List (String × String)) : List (String × String) :=
  headers.foldl (fun acc (n, v) => insertHeader acc (n.toLower, trimValue v)) []

def signedHeaders (headers : List (String × String)) : String :=
  ";".intercalate ((canonicalHeaders headers).map (·.1))

/-- `headers` include `host`. -/
def canonicalRequest (verb : String) (path : List String) (query headers : List (String × String))
    (payloadHash : String) : String :=
  "\n".intercalate [verb, canonicalPath path, canonicalQuery query,
    String.join ((canonicalHeaders headers).map fun (n, v) => n ++ ":" ++ v ++ "\n"),
    signedHeaders headers, payloadHash]

/-! ## Signing -/

def algorithm : String := "AWS4-HMAC-SHA256"

/-- What `x-amz-content-sha256` says of a body that is not signed. -/
def unsignedPayload : String := "UNSIGNED-PAYLOAD"

def payloadHash (body : ByteArray) : String := Bytes.hex (Sha256.hash body)

def stringToSign (t : Civil.DateTime) (scope : Scope) (canonical : String) : String :=
  "\n".intercalate [algorithm, stamp t, credentialScope t scope,
    Bytes.hex (Sha256.hash canonical.toUTF8)]

/-- The key for one day, region and service, derived from the secret. -/
def signingKey (secret : Secret) (t : Civil.DateTime) (scope : Scope) : ByteArray :=
  let date := hmac ("AWS4" ++ secret.reveal).toUTF8 (day t).toUTF8
  let region := hmac date scope.region.toUTF8
  let service := hmac region scope.service.toUTF8
  hmac service "aws4_request".toUTF8

def signature (secret : Secret) (t : Civil.DateTime) (scope : Scope) (canonical : String) :
    String :=
  Bytes.hex (hmac (signingKey secret t scope) (stringToSign t scope canonical).toUTF8)

/-- The `Authorization` header of a request whose signed headers are `headers`. -/
def authorization (creds : Credentials) (t : Civil.DateTime) (scope : Scope) (verb : String)
    (path : List String) (query headers : List (String × String)) (payloadHash : String) :
    String :=
  let canonical := canonicalRequest verb path query headers payloadHash
  algorithm ++ " Credential=" ++ creds.accessKeyId ++ "/" ++ credentialScope t scope
    ++ ", SignedHeaders=" ++ signedHeaders headers
    ++ ", Signature=" ++ signature creds.secretAccessKey t scope canonical

def verb : Method → String
  | .get => "GET" | .post => "POST" | .put => "PUT" | .patch => "PATCH" | .delete => "DELETE"

/-- The headers of `r` that are signed: `host` and every header of its own the client writes. -/
def signedFields (host : String) (r : Request) : List (String × String) :=
  ("host", host) :: r.headers.filter Request.kept

/-- `r` signed in its `Authorization` header, for the `Host` header `host`, sent as `verb` (its
method's, unless it goes as `HEAD`). It gets `x-amz-date`, `x-amz-security-token` when the
credentials have one, and its query in the canonical order. `payloadHash` is the body's hash or
`unsignedPayload`; S3 also wants it in `x-amz-content-sha256`, which is the caller's to add. -/
def sign (creds : Credentials) (t : Civil.DateTime) (scope : Scope) (host verb : String)
    (payloadHash : String) (r : Request) : Request :=
  let token := (creds.sessionToken.map fun s => ("x-amz-security-token", s.reveal)).toList
  let r := { r with query := sortQuery r.query, headers := r.headers ++ ("x-amz-date", stamp t) :: token }
  let auth := authorization creds t scope verb r.path r.query (signedFields host r) payloadHash
  { r with headers := r.headers ++ [("authorization", auth)] }

/-- How long a presigned link is good for, in seconds: at most seven days, as AWS allows. -/
abbrev Expiry := {s : Nat // 0 < s ∧ s ≤ 604800}

/-- The query of a link that does what `verb` on `path` does, for `expiry` from `t`, signed for
`host` and for `headers` the browser must send as given (none for most links). The body is not
signed. The parameters are in canonical order, the signature last. -/
def presign (creds : Credentials) (t : Civil.DateTime) (scope : Scope) (host verb : String)
    (path : List String) (query : List (String × String)) (expiry : Expiry)
    (headers : List (String × String) := []) : List (String × String) :=
  let fields := ("host", host) :: headers
  let token := (creds.sessionToken.map fun s => ("X-Amz-Security-Token", s.reveal)).toList
  let query := sortQuery (query ++ [("X-Amz-Algorithm", algorithm),
    ("X-Amz-Credential", creds.accessKeyId ++ "/" ++ credentialScope t scope),
    ("X-Amz-Date", stamp t), ("X-Amz-Expires", toString expiry.val),
    ("X-Amz-SignedHeaders", signedHeaders fields)] ++ token)
  let canonical := canonicalRequest verb path query fields unsignedPayload
  query ++ [("X-Amz-Signature", signature creds.secretAccessKey t scope canonical)]

end Lanes.SigV4
