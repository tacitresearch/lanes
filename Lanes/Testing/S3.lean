/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Testing.Http

/-!
A fake S3 for tests, over plain HTTP on a local port: one bucket, named by path, whose objects
are kept in a reference. It reads each request off the wire and checks its signature as S3
would, from the bytes it received, with the same secret: in the `Authorization` header, with the
payload's hash, and the session token when the credentials have one; or in the query of a
presigned link, with its expiry. A request not signed so is refused as S3 refuses it, `403
SignatureDoesNotMatch`. It answers `PUT`, `GET` (with a range), `HEAD`, `DELETE` and
ListObjectsV2. `follow` fetches a link as a browser does, with no credentials.
-/

@[expose] public section

namespace Lanes.Testing.S3

open Lanes Lanes.S3 Lanes.Http Std Std.Async

/-- A request as the fake read it off the wire. -/
structure Raw where
  verb : String
  target : String
  /-- Lowercase names, values trimmed, in order. -/
  headers : List (String × String)
  body : ByteArray

def raw? (received : ByteArray) : Option Raw := do
  let bodyStart ← headEnd received
  let head ← String.fromUTF8? (received.extract 0 (bodyStart - 4))
  let lines := head.splitOn "\r\n"
  let [verb, target, _] := (lines.headD "").splitOn " " | none
  let headers := (lines.drop 1).filterMap fun line =>
    match line.splitOn ":" with
    | name :: rest => some (name.toLower, (":".intercalate rest).trimAscii.toString)
    | [] => none
  let length := ((headers.lookup "content-length").bind (·.toNat?)).getD 0
  if bodyStart + length ≤ received.size then
    some { verb, target, headers, body := received.extract bodyStart (bodyStart + length) }
  else none

def answer (status : Nat) (headers : List (String × String)) (body : ByteArray)
    (head : Bool := false) : ByteArray :=
  let lines := s!"HTTP/1.1 {status} S3" :: (headers.map fun (n, v) => n ++ ": " ++ v)
    ++ (if headers.any (·.1 == "Content-Length") then [] else [s!"Content-Length: {body.size}"])
    ++ ["Connection: close"]
  ("\r\n".intercalate lines ++ "\r\n\r\n").toUTF8 ++ (if head then .empty else body)

def failure (status : Nat) (code : String) (head : Bool := false) : ByteArray :=
  answer status [("Content-Type", "application/xml")]
    s!"<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<Error><Code>{code}</Code></Error>".toUTF8 head

/-- `yyyymmddThhmmssZ` as the time it names. -/
def time? (s : String) : Option Civil.DateTime := do
  let cs := s.toList
  unless cs.length == 16 && cs[8]? == some 'T' && cs[15]? == some 'Z' do none
  let num (from_ n : Nat) := (String.ofList ((cs.drop from_).take n)).toNat?
  let date ← Civil.Date.mk? (← num 0 4) (← num 4 2) (← num 6 2)
  return Civil.DateTime.ofUnix (date.toDays * 86400 + (← num 9 2) * 3600 + (← num 11 2) * 60
    + (← num 13 2))

def decodePair (pair : String) : Option (String × String) :=
  match pair.splitOn "=" with
  | [k] => (percentDecode k).map (·, "")
  | k :: v => do return (← percentDecode k, ← percentDecode ("=".intercalate v))
  | [] => none

def splitTarget (target : String) : Option (List String × List (String × String)) := do
  let (path, query) := match target.splitOn "?" with
    | [p] => (p, "")
    | p :: q => (p, "?".intercalate q)
    | [] => ("", "")
  let path ← match path.toList with
    | '/' :: rest => some rest
    | _ => none
  let segments ← (path.splitOn '/').mapM fun s => percentDecode (String.ofList s)
  let query ← if query.isEmpty then some [] else (query.splitOn "&").mapM decodePair
  return (segments, query)

/-- The value after `name=` in an `Authorization` header. -/
def authField (auth name : String) : Option String :=
  (auth.splitOn (name ++ "="))[1]? |>.map fun rest => (rest.splitOn ",").headD ""

/-- Whether `r` is signed with `creds` for `scope`, in its header or in its query, as S3 would
check it from the bytes received; and the path and query it names. S3 wants the payload's hash
in `x-amz-content-sha256`; another service hashes the body it received. -/
def verified (creds : SigV4.Credentials) (scope : SigV4.Scope) (r : Raw) :
    Option (List String × List (String × String)) := do
  let (path, query) ← splitTarget r.target
  let s3 := scope.service == "s3"
  let signedPairs (names : List String) := names.flatMap fun name =>
    (r.headers.filter (·.1 == name)).map fun (_, v) => (name, v)
  match r.headers.lookup "authorization" with
  | some auth =>
    let names := ((authField auth "SignedHeaders").getD "").splitOn ";"
    let t ← time? (← r.headers.lookup "x-amz-date")
    let payload ← if s3 then r.headers.lookup "x-amz-content-sha256"
      else some (SigV4.payloadHash r.body)
    unless payload == SigV4.unsignedPayload || payload == SigV4.payloadHash r.body do none
    unless names.contains "host" && (!s3 || names.contains "x-amz-content-sha256") do none
    unless (creds.sessionToken.map (·.reveal)) == r.headers.lookup "x-amz-security-token" do none
    unless creds.sessionToken.isNone || names.contains "x-amz-security-token" do none
    let expected := SigV4.authorization creds t scope r.verb path query (signedPairs names) payload
    if expected == auth then some (path, query) else none
  | none =>
    let signature ← query.lookup "X-Amz-Signature"
    let rest := query.filter (·.1 != "X-Amz-Signature")
    let t ← time? (← query.lookup "X-Amz-Date")
    let expires ← (← query.lookup "X-Amz-Expires").toNat?
    unless 0 < expires && expires ≤ 604800 do none
    let names := (← query.lookup "X-Amz-SignedHeaders").splitOn ";"
    let canonical := SigV4.canonicalRequest r.verb path rest (signedPairs names) SigV4.unsignedPayload
    if SigV4.signature creds.secretAccessKey t scope canonical == signature then
      some (path, rest.filter fun (k, _) => !k.startsWith "X-Amz-")
    else none

/-- A key as S3 escapes it with `encoding-type=url`: a space as `+`. -/
def escapeKey (k : String) : String :=
  String.join (k.toList.map fun c => if c == ' ' then "+" else SigV4.encode c.toString)

/-- What the fake keeps: of each key, the body and the content type. -/
abbrev Objects := List (String × ByteArray × String)

def listXml (objects : Objects) (query : List (String × String)) : ByteArray :=
  let keyPrefix := (query.lookup "prefix").getD ""
  let after := (query.lookup "continuation-token").getD ""
  let max := ((query.lookup "max-keys").bind (·.toNat?)).getD 1000
  let matching := (objects.map (·.1)).filter fun k => k.startsWith keyPrefix && after < k
  let sorted := matching.mergeSort (· ≤ ·)
  let rolled (k : String) : Option String := (query.lookup "delimiter").bind fun d =>
    let rest := (k.drop keyPrefix.length).toString
    match rest.splitOn d with
    | first :: _ :: _ => some (keyPrefix ++ first ++ d)
    | _ => none
  let page := sorted.take max
  let truncated := sorted.length > max
  let contents := page.filterMap fun k =>
    if (rolled k).isSome then none
    else (objects.lookup k).map fun (body, _) =>
      s!"<Contents><Key>{escapeKey k}</Key><Size>{body.size}</Size><ETag>&quot;e&quot;</ETag></Contents>"
  let prefixes := (page.filterMap rolled).eraseDups.map fun p =>
    s!"<CommonPrefixes><Prefix>{escapeKey p}</Prefix></CommonPrefixes>"
  ("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<ListBucketResult><IsTruncated>"
    ++ toString (decide truncated) ++ "</IsTruncated>" ++ String.join contents ++ String.join prefixes
    ++ (if truncated then
          s!"<NextContinuationToken>{Xml.escape (page.getLast?.getD "")}</NextContinuationToken>"
        else "") ++ "</ListBucketResult>").toUTF8

def range? (header : String) (size : Nat) : Option (Nat × Nat) :=
  match (header.drop 6).toString.splitOn "-", header.startsWith "bytes=" with
  | ["", n], true => n.toNat?.map fun n => (size - n, size)
  | [a, ""], true => a.toNat?.map fun a => (a, size)
  | [a, b], true => do return (← a.toNat?, min size ((← b.toNat?) + 1))
  | _, _ => none

/-- What the fake answers, and the objects after, for the bucket `bucket` of `region`. -/
def serve (creds : SigV4.Credentials) (bucket region : String) (objects : Objects) (r : Raw) :
    ByteArray × Objects :=
  let head := r.verb == "HEAD"
  match verified creds ⟨region, "s3"⟩ r with
  | none => (failure 403 "SignatureDoesNotMatch" head, objects)
  | some (path, query) =>
    match path with
    | [b] =>
      if b == bucket && r.verb == "GET" && query.lookup "list-type" == some "2" then
        (answer 200 [("Content-Type", "application/xml")] (listXml objects query), objects)
      else if b == bucket then (failure 400 "InvalidRequest", objects)
      else (failure 404 "NoSuchBucket" head, objects)
    | b :: segments =>
      if b != bucket then (failure 404 "NoSuchBucket" head, objects) else
      let k := "/".intercalate segments
      match r.verb, objects.lookup k with
      | "PUT", _ =>
        let type := (r.headers.lookup "content-type").getD "binary/octet-stream"
        (answer 200 [("ETag", "\"" ++ (SigV4.payloadHash r.body).take 32 ++ "\"")] .empty,
          (k, r.body, type) :: objects.filter (·.1 != k))
      | "DELETE", _ => (answer 204 [] .empty, objects.filter (·.1 != k))
      | "GET", some (body, type) =>
        match (r.headers.lookup "range").map (range? · body.size) with
        | some (some (first, stop)) =>
          (answer 206 [("Content-Type", type)] (body.extract first stop), objects)
        | some none => (failure 416 "InvalidRange", objects)
        | none => (answer 200 [("Content-Type", type), ("ETag", "\"e\"")] body, objects)
      | "HEAD", some (body, type) =>
        (answer 200 [("Content-Type", type), ("Content-Length", toString body.size)] body true,
          objects)
      | _, none => (failure 404 "NoSuchKey" head, objects)
      | _, _ => (failure 405 "MethodNotAllowed", objects)
    | [] => (failure 404 "NoSuchBucket" head, objects)

/-- A fake S3 that is running. -/
structure Fake where
  server : TCP.Socket.Server
  /-- Its bucket, at its port, named by path. -/
  bucket : Bucket
  objects : IO.Ref Objects

/-- A fake S3 on a local port that checks signatures made with `creds`. Each request is read
whole, answered, and the connection closed. -/
def Fake.start (creds : SigV4.Credentials) (bucket : String := "test")
    (region : String := "us-east-1") : Async Fake := do
  let objects ← IO.mkRef []
  let server ← TCP.Socket.Server.mk
  server.bind (.v4 ⟨.ofParts 127 0 0 1, 0⟩)
  server.listen 128
  let tcpPort := (← server.getSockName).port
  background do
    try
      repeat
        let client ← server.accept
        background do
          try
            let mut received := ByteArray.empty
            repeat
              let some arrived ← client.recv? 65536 | break
              received := received ++ arrived
              if let some r := raw? received then
                let reply ← objects.modifyGet fun objs => serve creds bucket region objs r
                client.send reply
                break
          catch _ => pure ()
          client.close
    catch _ => pure ()
  return { server, objects, bucket := {
    name := bucket, region,
    endpoint := { host := "127.0.0.1", port := tcpPort, scheme := .http, addressing := .path } } }

def Fake.holds (f : Fake) (key : String) : IO Bool :=
  return ((← f.objects.get).lookup key).isSome

def Fake.keys (f : Fake) : IO (List String) :=
  return (← f.objects.get).map (·.1)

def Fake.stop (f : Fake) : Async Unit := f.server.close

/-- A link fetched as a browser would: no credentials, the link's own target. -/
def follow (url : String) (method : Method) (body : ByteArray := .empty)
    (headers : List (String × String) := []) (config : Client.Config := { timeout_ms := 5000 }) :
    Async (Option Response) := do
  let parts := url.splitOn "/"
  let origin := "/".intercalate (parts.take 3)
  let target := "/" ++ "/".intercalate (parts.drop 3)
  let some (path, query) := splitTarget target | return none
  let some c := Client.Call.at origin { method, path, query, headers, body } | return none
  if c.request.target != target then return none
  try Client.exchange c config catch _ => return none

end Lanes.Testing.S3
