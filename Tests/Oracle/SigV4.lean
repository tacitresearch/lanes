/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic

/-!
`Lanes.SigV4.sign` against botocore's signers on generated requests: the `Authorization` header
and `X-Amz-Date` each adds. A case is a request as JSON, unescaped: botocore's side writes the URL
as botocore's serializers do, ours signs the `Request` it describes as `S3.call` and `Ses.call`
do, with `x-amz-content-sha256` for S3.
-/

namespace Tests.Oracle.SigV4

open Lanes Lanes.Http Lanes.SigV4

structure Spec where
  service : String
  region : String
  unix : Nat
  key : String
  secret : String
  token : Option String
  verb : String
  host : String
  path : List String
  query : List (String × String)
  headers : List (String × String)
  body : ByteArray
  signed : Bool

def pairsJson (ps : List (String × String)) : Json := .arr (ps.map fun (a, b) => Json.arr #[a, b]).toArray

def Spec.json (s : Spec) : Json :=
  Json.mkObj ([("service", Json.str s.service), ("region", .str s.region), ("unix", (s.unix : Json)),
    ("key", .str s.key), ("secret", .str s.secret), ("method", .str s.verb), ("host", .str s.host),
    ("path", .arr (s.path.map Json.str).toArray), ("query", pairsJson s.query),
    ("headers", pairsJson s.headers), ("body", .str (Bytes.hex s.body)), ("signed", .bool s.signed)]
    ++ (s.token.map fun t => ("token", Json.str t)).toList)

def readPairs (j : Json) : Except String (List (String × String)) := do
  (← j.getArr?).toList.mapM fun p => do
    match (← p.getArr?).toList with
    | [a, b] => return (← a.getStr?, ← b.getStr?)
    | _ => throw "a pair"

def str (j : Json) (name : String) : Except String String := do (← j.getObjVal? name).getStr?

def readSpec (input : ByteArray) : Except String Spec := do
  let some text := String.fromUTF8? input | throw "not UTF-8"
  let j ← Json.parse text
  let some body := Bytes.unhex? (← str j "body") | throw "body"
  return { service := ← str j "service", region := ← str j "region",
           unix := ← (← j.getObjVal? "unix").getNat?, key := ← str j "key",
           secret := ← str j "secret", token := (str j "token").toOption, verb := ← str j "method",
           host := ← str j "host", path := ← (← (← j.getObjVal? "path").getArr?).toList.mapM Json.getStr?,
           query := ← readPairs (← j.getObjVal? "query"), headers := ← readPairs (← j.getObjVal? "headers"),
           body, signed := ← (← j.getObjVal? "signed").getBool? }

def method : String → Method
  | "PUT" => .put | "POST" => .post | "DELETE" => .delete | "PATCH" => .patch | _ => .get

/-- The request ours sends for `s`, signed. -/
def Spec.sign (s : Spec) : Request :=
  let hash := if s.signed then payloadHash s.body else unsignedPayload
  let headers := s.headers ++ (if s.service == "s3" then [("x-amz-content-sha256", hash)] else [])
  let creds : Credentials :=
    { accessKeyId := s.key, secretAccessKey := ⟨s.secret⟩, sessionToken := s.token.map (⟨·⟩) }
  SigV4.sign creds (Civil.DateTime.ofUnix s.unix) ⟨s.region, s.service⟩ s.host s.verb hash
    { method := method s.verb, path := s.path, query := s.query, headers, body := s.body }

def answer (c : Case) : Answer :=
  match readSpec c.input with
  | .ok s =>
    let r := s.sign
    some (Json.mkObj [("authorization", (r.headers.lookup "authorization").getD ""),
      ("x-amz-date", (r.headers.lookup "x-amz-date").getD "")])
  | .error _ => none

/-! ## Cases -/

def segmentPool : List String :=
  ["", "a", "photos", "2006", "a b", "ሴ", "%", "~", "a+b", "$", "=", ".", "..", "x:y", "é", "😀",
    "a&b", "test.txt", "-_.~"]

def queryPool : List String :=
  ["prefix", "list-type", "2", "a", "", "a b", "é", "A", "Z", "~", "=", "&", "+", "photos/2006/"]

def headerNames : List String :=
  ["content-type", "x-amz-meta-a", "X-Amz-Meta-B", "range", "x-amz-storage-class", "My-Header",
    "content-md5"]

def headerValues : List String :=
  ["text/plain", "  a  b  ", "a\tb", " ", "", "é", "x,y", "bytes=0-9", "a \t b", "STANDARD"]

/-- Rarer headers, each a known difference: not signed by botocore, not written by ours, or with
whitespace only Python takes for a blank. -/
def oddHeaders : List (String × String) :=
  [("user-agent", "lanes"), ("expect", "100-continue"), ("a b", "x"), ("x-a", "line\nbreak"),
    ("x-b", "no break"), ("x-c", "em space")]

def hosts : List String :=
  ["examplebucket.s3.us-east-1.amazonaws.com", "localhost:9000", "email.eu-west-1.amazonaws.com",
    "s3.amazonaws.com"]

def genSpec : Gen Spec := do
  let service ← Gen.pick ["s3", "s3", "s3", "ses", "sts"]
  let headers ← Gen.list (← Gen.below 4) (return (← Gen.pick headerNames, ← Gen.pick headerValues))
  let odd ← Gen.chance 8
  let extra ← Gen.pick oddHeaders
  let clean ← Gen.chance 70
  let pool := if service != "s3" && clean then ["v2", "email", "outbound-emails", "a", "2006"] else segmentPool
  let path ← Gen.list (← Gen.below 4) (Gen.pick pool)
  let query ← Gen.list (← Gen.below 4) (return (← Gen.pick queryPool, ← Gen.pick queryPool))
  let region ← Gen.pick ["us-east-1", "eu-west-1"]
  let unix := (← Gen.below 4000000) * 1000 + (← Gen.below 1000)
  let key ← Gen.pick ["AKIAIOSFODNN7EXAMPLE", "AKIDEXAMPLE"]
  let secret ← Gen.pick ["wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY",
    "wJalrXUtnFEMI/K7MDENG+bPxRfiCYEXAMPLEKEY"]
  let tokened ← Gen.chance 30
  let verb ← Gen.pick ["GET", "PUT", "POST", "DELETE", "HEAD"]
  let host ← Gen.pick hosts
  let hasBody ← Gen.chance 50
  let body ← Gen.bytes 16
  let signed ← Gen.chance 80
  return { service, region, unix, key, secret, verb, host, path, query,
           token := if tokened then some "IQoJb3JpZ2luX2VjE//token+/=" else none,
           headers := if odd then headers ++ [extra] else headers,
           body := if hasBody then body else .empty,
           signed := service != "s3" || signed }

def case : Gen Case := do return ⟨"sign", (← genSpec).json.compress.toUTF8⟩

def awsDoc : Spec :=
  { service := "s3", region := "us-east-1", unix := 1369353600, key := "AKIAIOSFODNN7EXAMPLE",
    secret := "wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY", token := none, verb := "GET",
    host := "examplebucket.s3.amazonaws.com", path := ["test.txt"], query := [],
    headers := [("range", "bytes=0-9")], body := .empty, signed := true }

def putDoc : Spec :=
  { awsDoc with verb := "PUT", path := ["test$file.text"], body := String.toUTF8 "Welcome to Amazon S3.",
                headers := [("x-amz-storage-class", "REDUCED_REDUNDANCY")] }

def sesDoc : Spec :=
  { awsDoc with service := "ses", region := "eu-west-1", host := "email.eu-west-1.amazonaws.com",
                verb := "POST", path := ["v2", "email", "outbound-emails"], body := String.toUTF8 "{}",
                headers := [("content-type", "application/json")] }

def edges : List Case :=
  [awsDoc, putDoc, { awsDoc with path := [], query := [("max-keys", "2"), ("prefix", "J")] },
    { awsDoc with token := some "tok", signed := false }, sesDoc].map
    fun s => ⟨"sign", s.json.compress.toUTF8⟩

/-! ## Where ours departs from botocore -/

def spec? (c : Case) : Option Spec := (readSpec c.input).toOption

/-- Services other than S3 escape the path twice and remove its dot segments and empty ones
(botocore's `normalize_url_path`); ours signs a path as S3 does, which is the same for a path
that needs neither, as `Ses.call`'s does not. -/
def normalizedPath (s : Spec) : Bool :=
  s.service != "s3" && s.path != [] && s.path != [""] &&
    s.path.any fun seg => encode seg != seg || seg == "." || seg == ".." || seg == ""

/-- botocore does not sign `User-Agent`, `Expect` or `X-Amzn-Trace-Id`; ours signs every header
it writes. Either is a valid signature. -/
def unsignedNames (s : Spec) : Bool :=
  s.headers.any fun (n, _) => ["user-agent", "expect", "x-amzn-trace-id"].contains n.toLower

/-- Ours neither writes nor signs a header whose name is not a token or whose value holds a
control character (`Request.kept`); botocore signs what it is given. -/
def unwritten (s : Spec) : Bool := s.headers.any (!Request.kept ·)

/-- botocore squeezes every character Python's `str.split` takes for whitespace; ours squeezes
spaces and tabs, HTTP's blanks. -/
def pythonWhitespace (s : Spec) : Bool :=
  let py (c : Char) := c.val == 0x85 || c.val == 0xa0 || c.val == 0x1680
    || (0x2000 ≤ c.val && c.val ≤ 0x200a) || c.val == 0x2028 || c.val == 0x2029
    || c.val == 0x202f || c.val == 0x205f || c.val == 0x3000 || (0x1c ≤ c.val && c.val ≤ 0x1f)
    || c.val == 0x0b || c.val == 0x0c
  s.headers.any fun (_, v) => v.any py

def package : Package where
  name := "sigv4"
  reference := .python "botocore"
  edges := edges
  case := case
  answer := answer
  shrinks := false
  recorded := 300
  known c _ := spec? c |>.bind fun s =>
    if normalizedPath s then
      some "services but S3 escape the path twice and normalize it; ours signs it as S3 does"
    else if unsignedNames s then some "botocore does not sign User-Agent or Expect; ours signs them"
    else if unwritten s then some "a header ours does not write, so does not sign"
    else if pythonWhitespace s then some "botocore squeezes Unicode whitespace in a value; ours spaces and tabs"
    else none

end Tests.Oracle.SigV4
