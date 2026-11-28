/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Testing.Http
public import Lanes.Web.IO.S3
public import Lanes.Web.S3.Post
public import Lanes.Lib.Crypto.Md5

/-!
A fake S3 for tests, over plain HTTP on a local port: one bucket, named by path, whose objects
are kept in a reference. It reads each request off the wire and checks its signature as S3
would, from the bytes it received, with the same secret: in the `Authorization` header, with the
payload's hash, and the session token when the credentials have one; or in the query of a
presigned link, with its expiry. A request not signed so is refused as S3 refuses it, `403
SignatureDoesNotMatch`. It answers `PUT`, `GET` (with a range), `HEAD`, `DELETE` and
ListObjectsV2. It takes a browser's `POST` form only with its policy's signature, before its
expiry, with every condition met and every field named, and refuses as S3 does
(`EntityTooLarge`, `EntityTooSmall`, `AccessDenied`), and answers one it takes with the redirect
or the status the form names (`uploaded`). It takes multipart uploads with S3's part
sizes, part order and ETags, and answers a Complete made twice the same. `Fake.refuse n` has it
answer the next `n` signed requests `503 SlowDown`, as S3 does under load, so that a test can
see a retry. `follow` fetches a link as a browser does, with no credentials, and `postForm`
posts a form as a browser's `FormData`.
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
      | "PUT", some _ =>
        if r.headers.lookup "if-none-match" == some "*" then (failure 412 "PreconditionFailed", objects)
        else
          let type := (r.headers.lookup "content-type").getD "binary/octet-stream"
          (answer 200 [("ETag", "\"" ++ (SigV4.payloadHash r.body).take 32 ++ "\"")] .empty,
            (k, r.body, type) :: objects.filter (·.1 != k))
      | "PUT", none =>
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

/-! ## Forms posted under a policy -/

structure FormPart where
  name : String
  filename : Option String
  value : ByteArray

def formParts (contentType : String) (body : ByteArray) : Option (List FormPart) := do
  let boundary ← Request.boundary?
    { method := .post, path := [], headers := [("content-type", contentType)] }
  let parts ← (Multipart.parse {} boundary body).toOption
  parts.mapM fun p => return { name := ← p.name?, filename := p.filename?, value := p.body }

/-- A body as a browser's `FormData` sends it: the fields, then the file. -/
def formBody (boundary : String) (fields : List (String × String)) (filename : String)
    (file : ByteArray) : ByteArray :=
  Multipart.write boundary ((fields.map fun (n, v) => Multipart.Part.field n v)
    ++ [Multipart.Part.file "file" filename "application/octet-stream" file])

/-- An object's ETag, as S3 makes one put whole: the MD5 of its body. -/
def etag (body : ByteArray) : String := "\"" ++ Bytes.hex (Md5.hash body) ++ "\""

/-- What S3 answers an upload it took, as the form asks: a `303` to `success_action_redirect`
with the bucket, the key and the ETag added to its query; else the status
`success_action_status` names, `201` with a document that names the object, `200`, or `204`,
which it answers to any other value or none. -/
def uploaded (fields : List (String × String)) (bucket key etag : String) : ByteArray :=
  let located := [("ETag", etag), ("Location", s!"/{bucket}/{key}")]
  match Post.lookup fields "success_action_redirect" with
  | some url =>
    let query := Url.encodeQuery [("bucket", bucket), ("key", key), ("etag", etag)]
    answer 303 [("Location", url ++ (if url.contains '?' then "&" else "?") ++ query)] .empty
  | none =>
    match Post.lookup fields "success_action_status" with
    | some "200" => answer 200 located .empty
    | some "201" =>
      answer 201 (("Content-Type", "application/xml") :: located)
        ("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<PostResponse><Location>/" ++ bucket ++ "/"
          ++ Xml.escape key ++ "</Location><Bucket>" ++ bucket ++ "</Bucket><Key>"
          ++ Xml.escape key ++ "</Key><ETag>" ++ Xml.escape etag ++ "</ETag></PostResponse>").toUTF8
    | _ => answer 204 located .empty

/-- What the fake answers a form posted to `bucket` at `now_s`, and the objects after. -/
def servePost (creds : SigV4.Credentials) (bucket : String) (now_s : Int) (objects : Objects)
    (r : Raw) : ByteArray × Objects :=
  let refuse (status : Nat) (code : String) := (failure status code, objects)
  match (r.headers.lookup "content-type").bind (formParts · r.body) with
  | none => refuse 400 "MalformedPOSTRequest"
  | some parts =>
    let fields := (parts.filter fun p => p.filename.isNone && p.name != "file").map fun p =>
      (p.name, (String.fromUTF8? p.value).getD "")
    let get := Post.lookup fields
    match parts.find? (·.name == "file"), get "policy", get "x-amz-signature",
        get "x-amz-credential", (get "x-amz-date").bind time? with
    | some file, some policy, some signature, some credential, some t =>
      match credential.splitOn "/" with
      | [id, _, region, service, "aws4_request"] =>
        if id != creds.accessKeyId
            || Post.signature creds.secretAccessKey t ⟨region, service⟩ policy != signature then
          refuse 403 "SignatureDoesNotMatch"
        else if (creds.sessionToken.map (·.reveal)) != get "x-amz-security-token" then
          refuse 403 "InvalidToken"
        else match Post.decode? policy with
          | none => refuse 400 "InvalidPolicyDocument"
          | some d =>
            let filename := file.filename.getD ""
            let fields := fields.map fun (n, v) =>
              if n.toLower == "key" then (n, v.replace "${filename}" filename) else (n, v)
            match Post.check d bucket fields file.value.size now_s, Post.lookup fields "key" with
            | .ok (), some k =>
              let type := (Post.lookup fields "content-type").getD "binary/octet-stream"
              (uploaded fields bucket k (etag file.value),
                (k, file.value, type) :: objects.filter (·.1 != k))
            | .error (.unmet (.length _ max)), _ =>
              if file.value.size > max then refuse 400 "EntityTooLarge" else refuse 400 "EntityTooSmall"
            | .error .unreadable, _ => refuse 400 "InvalidPolicyDocument"
            | _, _ => refuse 403 "AccessDenied"
      | _ => refuse 403 "AuthorizationQueryParametersError"
    | _, _, _, _, _ => refuse 403 "AccessDenied"

/-! ## Multipart uploads -/

structure Upload where
  id : String
  key : String
  contentType : String
  /-- By number: the body and its ETag. -/
  parts : List (Nat × ByteArray × String)

/-- What the fake keeps: its objects, the uploads in progress, and those completed. -/
structure State where
  objects : Objects := []
  uploads : List Upload := []
  /-- Uploads completed: the id, the key, the listing and the object's ETag. -/
  completed : List (String × String × List (Nat × String) × String) := []
  next : Nat := 0
  /-- The signed requests still to answer `503 SlowDown`. -/
  refusing : Nat := 0

def unquote (s : String) : String := s.replace "\"" ""

/-- A multipart object's ETag, as S3 makes it: the MD5 of the parts' MD5s, and their number. -/
def multipartEtag (parts : List ByteArray) : String :=
  "\"" ++ Bytes.hex (Md5.hash (parts.foldl (fun acc p => acc ++ Md5.hash p) .empty)) ++ "-"
    ++ toString parts.length ++ "\""

def xmlAnswer (body : String) : ByteArray :=
  answer 200 [("Content-Type", "application/xml")]
    ("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++ body).toUTF8

def listPartsXml (bucket : String) (u : Upload) (after : Nat) : String :=
  let parts := (u.parts.filter (·.1 > after)).mergeSort (fun a b => a.1 ≤ b.1)
  s!"<ListPartsResult><Bucket>{bucket}</Bucket><Key>" ++ Xml.escape u.key ++ "</Key><UploadId>" ++ u.id
    ++ "</UploadId><IsTruncated>false</IsTruncated>"
    ++ String.join (parts.map fun (n, body, e) => s!"<Part><PartNumber>{n}</PartNumber><ETag>{Xml.escape e}</ETag><Size>{body.size}</Size></Part>")
    ++ "</ListPartsResult>"

def completedXml (bucket k e : String) : String :=
  s!"<CompleteMultipartUploadResult><Location>/{bucket}/" ++ Xml.escape k ++ s!"</Location><Bucket>{bucket}</Bucket><Key>"
    ++ Xml.escape k ++ "</Key><ETag>" ++ Xml.escape e ++ "</ETag></CompleteMultipartUploadResult>"

def manifest? (body : ByteArray) : Option (List (Nat × String)) := do
  let root ← (String.fromUTF8? body).bind Xml.parse
  unless root.name == "CompleteMultipartUpload" do none
  (root.all "Part").mapM fun p => do return (← decimal? (← p.text? "PartNumber"), ← p.text? "ETag")

/-- A Complete of `u` with `listing`: S3 refuses parts out of order, an ETag not the part's, and
a part but the last under 5 MiB. -/
def complete (bucket : String) (st : State) (u : Upload) (listing : List (Nat × String)) :
    ByteArray × State :=
  let refuse (status : Nat) (code : String) := (failure status code, st)
  if listing.isEmpty then refuse 400 "MalformedXML"
  else if !decide ((listing.map (·.1)).Pairwise (· < ·)) then refuse 400 "InvalidPartOrder"
  else match listing.mapM fun ((n, e) : Nat × String) =>
      (u.parts.lookup n).filter fun ((_, held) : ByteArray × String) => unquote held == unquote e with
    | none => refuse 400 "InvalidPart"
    | some held =>
      if (held.dropLast.any fun ((body, _) : ByteArray × String) =>
          body.size < Multipart.minPart_bytes) then
        refuse 400 "EntityTooSmall"
      else
        let bodies := held.map (·.1)
        let e := multipartEtag bodies
        let listing := listing.map fun (n, e) => (n, unquote e)
        (xmlAnswer (completedXml bucket u.key e),
          { st with objects := (u.key, bodies.foldl (· ++ ·) .empty, u.contentType) :: st.objects.filter (·.1 != u.key)
                    uploads := st.uploads.filter (·.id != u.id)
                    completed := (u.id, u.key, listing, e) :: st.completed })

/-- A request of a multipart upload of `k`, if it is one. -/
def serveMultipart (bucket : String) (st : State) (r : Raw) (k : String)
    (query : List (String × String)) : Option (ByteArray × State) :=
  let upload := (query.lookup "uploadId").bind fun id => st.uploads.find? (·.id == id)
  let gone := (failure 404 "NoSuchUpload", st)
  match r.verb, query.lookup "uploads", query.lookup "uploadId" with
  | "POST", some _, _ =>
    let id := s!"upload-{st.next}"
    let type := (r.headers.lookup "content-type").getD "binary/octet-stream"
    some (xmlAnswer s!"<InitiateMultipartUploadResult><Bucket>{bucket}</Bucket><Key>{Xml.escape k}</Key><UploadId>{id}</UploadId></InitiateMultipartUploadResult>",
      { st with next := st.next + 1, uploads := ⟨id, k, type, []⟩ :: st.uploads })
  | "PUT", _, some _ => some <| match upload, (query.lookup "partNumber").bind String.toNat? with
    | some u, some n =>
      if n < 1 || n > 10000 then (failure 400 "InvalidArgument", st)
      else
        let u := { u with parts := (n, r.body, etag r.body) :: u.parts.filter (·.1 != n) }
        (answer 200 [("ETag", etag r.body)] .empty,
          { st with uploads := u :: st.uploads.filter (·.id != u.id) })
    | _, _ => gone
  | "GET", _, some _ => some <| match upload with
    | some u =>
      (xmlAnswer (listPartsXml bucket u
        (((query.lookup "part-number-marker").bind String.toNat?).getD 0)), st)
    | none => gone
  | "POST", _, some id => some <| match upload, manifest? r.body with
    | some u, some listing => complete bucket st u listing
    | none, some listing =>
      match st.completed.find? (·.1 == id) with
      | some (_, k', done, e) =>
        if done == listing.map (fun (n, e) => (n, unquote e)) then
          (xmlAnswer (completedXml bucket k' e), st)
        else gone
      | none => gone
    | _, none => (failure 400 "MalformedXML", st)
  | "DELETE", _, some id => some <| match upload with
    | some _ => (answer 204 [] .empty, { st with uploads := st.uploads.filter (·.id != id) })
    | none => gone
  | _, _, _ => none

/-- What the fake answers at `now_s`, and its state after: a form, a multipart upload's
request, or one `serve` answers. -/
def serveAll (creds : SigV4.Credentials) (bucket region : String) (now_s : Int) (st : State)
    (r : Raw) : ByteArray × State :=
  if 0 < st.refusing && (r.headers.lookup "authorization").isSome then
    (failure 503 "SlowDown" (r.verb == "HEAD"), { st with refusing := st.refusing - 1 })
  else
  let byForm := r.verb == "POST" && (r.headers.lookup "authorization").isNone
    && ((r.headers.lookup "content-type").getD "").startsWith "multipart/form-data"
  if byForm then
    match splitTarget r.target with
    | some ([b], _) =>
      if b == bucket then
        let (reply, objects) := servePost creds bucket now_s st.objects r
        (reply, { st with objects })
      else (failure 404 "NoSuchBucket", st)
    | _ => (failure 404 "NoSuchBucket", st)
  else
    let plain : Unit → ByteArray × State := fun () =>
      let (reply, objects) := serve creds bucket region st.objects r
      (reply, { st with objects })
    match verified creds ⟨region, "s3"⟩ r with
    | some (b :: segments, query) =>
      if b == bucket then (serveMultipart bucket st r ("/".intercalate segments) query).getD (plain ())
      else plain ()
    | _ => plain ()

/-- A fake S3 that is running. -/
structure Fake where
  server : TCP.Socket.Server
  /-- Its bucket, at its port, named by path. -/
  bucket : Bucket
  state : IO.Ref State

/-- A fake S3 on a local port that checks signatures made with `creds`. Each request is read
whole, answered, and the connection closed. -/
def Fake.start (creds : SigV4.Credentials) (bucket : String := "test")
    (region : String := "us-east-1") : Async Fake := do
  let state ← IO.mkRef ({} : State)
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
                let now_s := (← S3.now).toUnix
                let reply ← state.modifyGet fun st => serveAll creds bucket region now_s st r
                client.send reply
                break
          catch _ => pure ()
          client.close
    catch _ => pure ()
  return { server, state, bucket := {
    name := bucket, region,
    endpoint := { host := "127.0.0.1", port := tcpPort, scheme := .http, addressing := .path } } }

/-- The body and the content type the fake holds under `key`. -/
def Fake.object? (f : Fake) (key : String) : IO (Option (ByteArray × String)) :=
  return (← f.state.get).objects.lookup key

def Fake.holds (f : Fake) (key : String) : IO Bool :=
  return (← f.object? key).isSome

def Fake.keys (f : Fake) : IO (List String) :=
  return (← f.state.get).objects.map (·.1)

/-- The next `n` signed requests are answered `503 SlowDown`. -/
def Fake.refuse (f : Fake) (n : Nat) : IO Unit :=
  f.state.modify fun st => { st with refusing := n }

/-- How many signed requests are still to be refused. -/
def Fake.refusing (f : Fake) : IO Nat :=
  return (← f.state.get).refusing

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

/-- The code of the error S3 answered, or `""`. -/
def code (r : Option Response) : String := (r.map (errorCode ·.body)).getD ""

/-- Posts `fields` and then `file` to `url`, as a browser's `fetch` of a `FormData` does. -/
def postForm (url : String) (fields : List (String × String)) (file : ByteArray)
    (filename : String := "clip.mp4") (config : Client.Config := { timeout_ms := 5000 }) :
    Async (Option Response) := do
  let parts := url.splitOn "/"
  let origin := "/".intercalate (parts.take 3)
  let path := (parts.drop 3).filter (!·.isEmpty)
  let boundary := "----LanesFormBoundary7MA4YWxkTrZu0gW"
  let body := formBody boundary fields filename file
  let headers := [("content-type", s!"multipart/form-data; boundary={boundary}")]
  let some c := Client.Call.at origin { method := .post, path, headers, body } | return none
  try Client.exchange c config catch _ => return none

end Lanes.Testing.S3
