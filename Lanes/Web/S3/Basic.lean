/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.SigV4
public import Lanes.Web.S3.Xml
public import Lanes.Web.IO.Client
public import Lanes.Outside.ObjectStore

/-!
The S3 API as pure functions: an operation on a bucket as a signed call for the HTTP client,
what its response means, and links a browser follows to get or put an object itself. AWS's S3
speaks it, and so do the stores that copy it (MinIO, Ceph, R2, LocalStack); `Endpoint` says where
one is and how it names buckets.

A body is whole and in memory, in `Op.put` and in `Answer.object`, and its hash is signed or
`UNSIGNED-PAYLOAD` (`Payload`). That is the one place a streamed body will change: the request
written and the answer read, while the signing, which never needs the body unsigned, stays.
-/

@[expose] public section

namespace Lanes.S3

open Http SigV4

inductive Addressing where
  /-- `bucket.host/key`, which AWS prefers. A bucket whose name has a dot does not match AWS's
  certificate over HTTPS, and needs `path`. -/
  | virtualHosted
  /-- `host/bucket/key`, which MinIO and LocalStack answer without set-up. -/
  | path
  deriving DecidableEq, Repr

structure Endpoint where
  host : String
  port : UInt16 := 443
  scheme : Client.Scheme := .https
  addressing : Addressing := .virtualHosted
  deriving DecidableEq, Repr

/-- AWS's endpoint of a region. -/
def Endpoint.aws (region : String) : Endpoint := { host := "s3." ++ region ++ ".amazonaws.com" }

structure Bucket where
  name : String
  region : String
  endpoint : Endpoint
  deriving DecidableEq, Repr

/-- A key S3 accepts: one to 1024 bytes of UTF-8. A `/` in it is kept as it is. -/
abbrev Key := {k : String // 0 < k.utf8ByteSize ∧ k.utf8ByteSize ≤ 1024}

def Key.of? (s : String) : Option Key :=
  if h : 0 < s.utf8ByteSize ∧ s.utf8ByteSize ≤ 1024 then some ⟨s, h⟩ else none

/-- Bytes of an object, counted from zero. -/
inductive Range where
  | span (first last : Nat) (ordered : first ≤ last)
  | starting (first : Nat)
  /-- The last `bytes` bytes. -/
  | final (bytes : Nat)
  deriving DecidableEq, Repr, Hashable

def Range.header : Range → String
  | .span first last _ => "bytes=" ++ toString first ++ "-" ++ toString last
  | .starting first => "bytes=" ++ toString first ++ "-"
  | .final bytes => "bytes=-" ++ toString bytes

/-- How many keys a page of a listing holds at most: S3 gives at most 1000. -/
abbrev PageSize := {n : Nat // 0 < n ∧ n ≤ 1000}

/-- A part's number in a multipart upload: S3 takes 1 to 10,000. -/
abbrev PartNumber := {n : Nat // 1 ≤ n ∧ n ≤ 10000}

def PartNumber.of? (n : Nat) : Option PartNumber := if h : 1 ≤ n ∧ n ≤ 10000 then some ⟨n, h⟩ else none

/-- What completes a multipart upload: each part by its number, with the ETag its upload was
answered, at least one, in ascending order of number, as S3 requires. -/
abbrev Manifest :=
  {parts : List (PartNumber × String) // parts ≠ [] ∧ (parts.map (·.1.val)).Pairwise (· < ·)}

def Manifest.of? (parts : List (PartNumber × String)) : Option Manifest :=
  if h : parts ≠ [] ∧ (parts.map (·.1.val)).Pairwise (· < ·) then some ⟨parts, h⟩ else none

/-- The body of CompleteMultipartUpload. -/
def Manifest.xml (m : Manifest) : String :=
  "<CompleteMultipartUpload xmlns=\"http://s3.amazonaws.com/doc/2006-03-01/\">"
    ++ String.join (m.val.map fun (n, etag) => "<Part><PartNumber>" ++ toString n.val
      ++ "</PartNumber><ETag>" ++ Xml.escape etag ++ "</ETag></Part>")
    ++ "</CompleteMultipartUpload>"

inductive Op where
  | put (key : Key) (body : ByteArray) (contentType : Option String := none)
  | get (key : Key) (range : Option Range := none)
  | head (key : Key)
  | delete (key : Key)
  /-- ListObjectsV2: the keys that start with `keyPrefix`, after `continuation` if given, those
  with `delimiter` after the prefix rolled up into one prefix each. -/
  | list (keyPrefix : String := "") (delimiter : Option String := none)
    (continuation : Option String := none) (pageSize : PageSize := ⟨1000, by decide⟩)
  /-- CreateMultipartUpload: the object `key` will be, with `contentType`. -/
  | createUpload (key : Key) (contentType : Option String := none)
  | uploadPart (key : Key) (uploadId : String) (part : PartNumber) (body : ByteArray)
  /-- CompleteMultipartUpload: the object is the parts listed, in order. -/
  | completeUpload (key : Key) (uploadId : String) (parts : Manifest)
  | abortUpload (key : Key) (uploadId : String)
  /-- ListParts: the parts S3 holds, at most 1000, after `marker`. -/
  | listParts (key : Key) (uploadId : String) (marker : Option PartNumber := none)
  deriving DecidableEq, Repr, Hashable

namespace Op

def method : Op → Method
  | .put .. | .uploadPart .. => .put
  | .delete _ | .abortUpload .. => .delete
  | .createUpload .. | .completeUpload .. => .post
  | _ => .get

def verb (op : Op) : String := if op matches .head _ then "HEAD" else SigV4.verb op.method

def segments : Op → List String
  | .put key .. | .get key _ | .head key | .delete key | .createUpload key _
  | .uploadPart key .. | .completeUpload key .. | .abortUpload key _ | .listParts key .. =>
    SigV4.segments key.val
  | .list .. => []

/-- Keys come back escaped (`encoding-type=url`), so a key XML cannot carry still lists. -/
def query : Op → List (String × String)
  | .list keyPrefix delimiter continuation pageSize =>
    [("list-type", "2"), ("encoding-type", "url"), ("max-keys", toString pageSize.val)]
      ++ (if keyPrefix.isEmpty then [] else [("prefix", keyPrefix)])
      ++ (delimiter.map (("delimiter", ·))).toList
      ++ (continuation.map (("continuation-token", ·))).toList
  | .createUpload .. => [("uploads", "")]
  | .uploadPart _ uploadId part _ => [("partNumber", toString part.val), ("uploadId", uploadId)]
  | .completeUpload _ uploadId _ | .abortUpload _ uploadId => [("uploadId", uploadId)]
  | .listParts _ uploadId marker =>
    ("uploadId", uploadId) :: (marker.map (("part-number-marker", toString ·.val))).toList
  | _ => []

def headers : Op → List (String × String)
  | .put _ _ (some contentType) | .createUpload _ (some contentType) =>
    [("content-type", contentType)]
  | .get _ (some range) => [("range", range.header)]
  | .completeUpload .. => [("content-type", "application/xml")]
  | _ => []

def body : Op → ByteArray
  | .put _ body _ | .uploadPart _ _ _ body => body
  | .completeUpload _ _ parts => parts.xml.toUTF8
  | _ => .empty

end Op

/-- Whether a body is signed by its hash, or sent as `UNSIGNED-PAYLOAD`, which S3 accepts over
HTTPS and which a streamed body needs. -/
inductive Payload where
  | signed
  | unsigned
  deriving DecidableEq, Repr

def Bucket.host (b : Bucket) : String :=
  match b.endpoint.addressing with
  | .virtualHosted => b.name ++ "." ++ b.endpoint.host
  | .path => b.endpoint.host

def Bucket.path (b : Bucket) (segments : List String) : List String :=
  match b.endpoint.addressing with
  | .virtualHosted => segments
  | .path => b.name :: segments

def Bucket.scope (b : Bucket) : Scope := ⟨b.region, "s3"⟩

/-- The call for `op` on `b`, signed with `creds` at `t`. -/
def call (b : Bucket) (creds : Credentials) (t : Civil.DateTime) (op : Op)
    (payload : Payload := .signed) : Client.Call :=
  let hash := match payload with
    | .signed => payloadHash op.body
    | .unsigned => unsignedPayload
  let request : Request :=
    { method := op.method, path := b.path op.segments, query := op.query
      headers := op.headers ++ [("x-amz-content-sha256", hash)], body := op.body }
  let unsigned : Client.Call :=
    { host := b.host, port := b.endpoint.port, scheme := b.endpoint.scheme, request
      headOnly := op matches .head _ }
  { unsigned with request := sign creds t b.scope unsigned.authority op.verb hash unsigned.request }

/-! ## Answers -/

structure Info where
  /-- Of the body sent, a range's included. -/
  size : Nat
  etag : Option String := none
  contentType : Option String := none
  lastModified : Option String := none
  deriving DecidableEq, Repr, Hashable

structure Entry where
  key : String
  size : Nat
  etag : String := ""
  lastModified : String := ""
  deriving DecidableEq, Repr, Hashable

structure Page where
  entries : List Entry
  /-- With a delimiter: the prefixes the keys under them were rolled up into. -/
  prefixes : List String := []
  /-- What `Op.list` takes to go on, when the listing goes on. -/
  next : Option String := none
  deriving DecidableEq, Repr, Hashable

structure Part where
  number : Nat
  etag : String
  size : Nat
  deriving DecidableEq, Repr, Hashable

/-- A page of ListParts. -/
structure Parts where
  parts : List Part
  /-- The marker of the next page, when there is one. -/
  next : Option Nat := none
  deriving DecidableEq, Repr, Hashable

inductive Answer where
  | stored (etag : Option String)
  | object (info : Info) (body : ByteArray)
  | found (info : Info)
  | deleted
  | listed (page : Page)
  /-- A multipart upload begun, with its id. -/
  | started (uploadId : String)
  /-- A multipart upload completed: the object is there, with its ETag. -/
  | completed (etag : Option String)
  | parts (page : Parts)
  /-- No such key: `404` to a get or a head. -/
  | missing
  /-- An error the store gave, with its code (`NoSuchBucket`, `SignatureDoesNotMatch`), or `""`
  when it gave none. -/
  | refused (status : Nat) (code : String)
  /-- A success whose body this reader does not understand. -/
  | unreadable
  deriving DecidableEq, Repr, Hashable

def unescapeKey (s : String) : Option String := percentDecode s (plusIsSpace := true)

def entry? (n : Xml.Node) : Option Entry := do
  let key ← unescapeKey (← n.text? "Key")
  let size ← decimal? (← n.text? "Size")
  return { key, size, etag := (n.text? "ETag").getD "", lastModified := (n.text? "LastModified").getD "" }

/-- A page of ListObjectsV2, with its keys escaped as `Op.list` asks. -/
def page? (body : ByteArray) : Option Page := do
  let root ← Xml.parse (← String.fromUTF8? body)
  unless root.name == "ListBucketResult" do none
  let entries ← (root.all "Contents").mapM entry?
  let prefixes ← (root.all "CommonPrefixes").mapM fun n => do unescapeKey (← n.text? "Prefix")
  let truncated := root.text? "IsTruncated" == some "true"
  return { entries, prefixes, next := if truncated then root.text? "NextContinuationToken" else none }

/-- The `Code` of an S3 error document, or `""`. -/
def errorCode (body : ByteArray) : String :=
  ((String.fromUTF8? body).bind Xml.parse |>.filter (·.name == "Error")).bind (·.text? "Code")
    |>.getD ""

def root? (body : ByteArray) : Option Xml.Node := (String.fromUTF8? body).bind Xml.parse

def started? (body : ByteArray) : Option String := do
  let root ← root? body
  unless root.name == "InitiateMultipartUploadResult" do none
  root.text? "UploadId"

def part? (n : Xml.Node) : Option Part := do
  return { number := ← decimal? (← n.text? "PartNumber"), etag := ← n.text? "ETag"
           size := ← decimal? (← n.text? "Size") }

def parts? (body : ByteArray) : Option Parts := do
  let root ← root? body
  unless root.name == "ListPartsResult" do none
  let parts ← (root.all "Part").mapM part?
  let truncated := root.text? "IsTruncated" == some "true"
  return { parts, next := if truncated then (root.text? "NextPartNumberMarker").bind decimal? else none }

/-- S3 may answer CompleteMultipartUpload `200` and an error in the body. -/
def completed (body : ByteArray) : Answer :=
  match root? body with
  | some root =>
    if root.name == "CompleteMultipartUploadResult" then .completed (root.text? "ETag")
    else if root.name == "Error" then .refused 200 ((root.text? "Code").getD "")
    else .unreadable
  | none => .unreadable

def info (r : Response) (size : Nat) : Info :=
  { size, etag := r.headers.lookup "etag", contentType := r.headers.lookup "content-type",
    lastModified := r.headers.lookup "last-modified" }

def interpret (op : Op) (r : Response) : Answer :=
  match op, r.status with
  | .put .., 200 => .stored (r.headers.lookup "etag")
  | .get .., 200 | .get .., 206 => .object (info r r.body.size) r.body
  | .head _, 200 =>
    match (r.headers.lookup "content-length").bind decimal? with
    | some size => .found (info r size)
    | none => .unreadable
  | .delete _, 204 | .delete _, 200 => .deleted
  | .list .., 200 => match page? r.body with
    | some page => .listed page
    | none => .unreadable
  | .createUpload .., 200 => match started? r.body with
    | some id => .started id
    | none => .unreadable
  | .uploadPart .., 200 => .stored (r.headers.lookup "etag")
  | .completeUpload .., 200 => completed r.body
  | .abortUpload .., 204 | .abortUpload .., 200 => .deleted
  | .listParts .., 200 => match parts? r.body with
    | some page => .parts page
    | none => .unreadable
  | .get .., 404 | .head _, 404 => .missing
  | _, status => .refused status (errorCode r.body)

/-! ## As the model of an object store -/

/-- The request `op` is in `Lanes.Outside.ObjectStore`'s model, for the operations it has: a
ranged get and a listing are not in it. -/
def Op.modelled : Op → Option (ObjectStore.Request String ByteArray)
  | .put key body _ => some (.put key.val body)
  | .get key none => some (.get key.val)
  | .head key => some (.head key.val)
  | .delete key => some (.delete key.val)
  | _ => none

def Answer.modelled : Answer → Option (ObjectStore.Answer ByteArray)
  | .stored _ => some .stored
  | .object _ body => some (.found body)
  | .found _ => some .present
  | .missing => some .missing
  | .deleted => some .deleted
  | .refused .. | .unreadable => some .refused
  | _ => none

/-! ## Links for a browser -/

/-- A link that gets (`Method.get`) or puts (`Method.put`) the object at `key` for `expiry`
from `t`, with no credentials of its own. A put through it must send `contentType`, when one is
given, as its `Content-Type`. -/
def presign (b : Bucket) (creds : Credentials) (t : Civil.DateTime) (method : Method) (key : Key)
    (expiry : Expiry) (contentType : Option String := none) : String :=
  let call : Client.Call :=
    { host := b.host, port := b.endpoint.port, scheme := b.endpoint.scheme
      request := { method, path := [] } }
  let path := b.path (SigV4.segments key.val)
  let headers := (contentType.map (("content-type", ·))).toList
  let query := SigV4.presign creds t b.scope call.authority (SigV4.verb method) path [] expiry headers
  let scheme := match b.endpoint.scheme with | .http => "http" | .https => "https"
  scheme ++ "://" ++ call.authority ++ ({ method, path, query } : Request).target

/-- A link that uploads part `part` of the upload `uploadId` of `key`, for `expiry` from `t`.
With `length`, the `Content-Length` is signed, so the store takes a part of exactly that many
bytes and no other; the browser sends it as the size of what it puts. -/
def presignPart (b : Bucket) (creds : Credentials) (t : Civil.DateTime) (key : Key)
    (uploadId : String) (part : PartNumber) (expiry : Expiry) (length : Option Nat := none) :
    String :=
  let call : Client.Call :=
    { host := b.host, port := b.endpoint.port, scheme := b.endpoint.scheme
      request := { method := .put, path := [] } }
  let path := b.path (SigV4.segments key.val)
  let headers := (length.map (("content-length", toString ·))).toList
  let own := [("partNumber", toString part.val), ("uploadId", uploadId)]
  let query := SigV4.presign creds t b.scope call.authority "PUT" path own expiry headers
  let scheme := match b.endpoint.scheme with | .http => "http" | .https => "https"
  scheme ++ "://" ++ call.authority ++ ({ method := .put, path, query } : Request).target

end Lanes.S3
