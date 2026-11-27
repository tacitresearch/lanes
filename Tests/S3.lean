/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The S3 client: the XML reader on ListObjectsV2 and error documents as S3 writes them, and on
what it must refuse; the calls built for each operation and each way of naming a bucket; what a
response means; the model of an object store; and the client against a fake S3 in the test, over
plain HTTP, which reads each request off the wire, checks its signature with the same key as S3
would, from the bytes it received, and keeps the objects. A system calling the fake through
`S3.handler` is checked against the model. Nothing here calls AWS.
-/

namespace Tests.S3

open Lanes Lanes.S3 Lanes.Http Std Std.Async

def bytes (s : String) : ByteArray := s.toUTF8

/-! ## The XML reader -/

def listing : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
    ++ "<ListBucketResult xmlns=\"http://s3.amazonaws.com/doc/2006-03-01/\">"
    ++ "<Name>examplebucket</Name><Prefix>photos%2F</Prefix><KeyCount>2</KeyCount>"
    ++ "<MaxKeys>2</MaxKeys><Delimiter>%2F</Delimiter><EncodingType>url</EncodingType>"
    ++ "<IsTruncated>true</IsTruncated>\n  <Contents>\n    <Key>photos%2F2006%2Fa+b.jpg</Key>\n"
    ++ "    <LastModified>2009-10-12T17:50:30.000Z</LastModified>\n"
    ++ "    <ETag>&quot;fba9dede5f27731c9771645a39863328&quot;</ETag>\n"
    ++ "    <Size>434234</Size>\n    <StorageClass>STANDARD</StorageClass>\n  </Contents>\n"
    ++ "  <Contents><Key>photos%2F%E1%88%B4%2B1</Key><LastModified>2009-10-12T17:50:31.000Z"
    ++ "</LastModified><ETag>\"x\"</ETag><Size>0</Size><Owner><ID>1</ID></Owner></Contents>"
    ++ "<CommonPrefixes><Prefix>photos%2F2007%2F</Prefix></CommonPrefixes>"
    ++ "<!-- a comment --><NextContinuationToken>1ueGcxLPRx1Tr/XYExHnhbYLgveDs2J/wm36Hy4vbOwM="
    ++ "</NextContinuationToken></ListBucketResult>\n"

def errorDocument : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<Error><Code>NoSuchKey</Code><Message>The "
    ++ "resource you requested does not exist</Message><Resource>/mybucket/myfoto.jpg</Resource>"
    ++ "<RequestId>4442587FB7D0A2F9</RequestId></Error>"

def deep (n : Nat) : String :=
  String.join (List.replicate n "<a>") ++ String.join (List.replicate n "</a>")

def expectedPage : Page where
  entries := [
    { key := "photos/2006/a b.jpg", size := 434234, etag := "\"fba9dede5f27731c9771645a39863328\"",
      lastModified := "2009-10-12T17:50:30.000Z" },
    { key := "photos/ሴ+1", size := 0, etag := "\"x\"", lastModified := "2009-10-12T17:50:31.000Z" }]
  prefixes := ["photos/2007/"]
  next := some "1ueGcxLPRx1Tr/XYExHnhbYLgveDs2J/wm36Hy4vbOwM="

def xmlTests : List (String × Bool) :=
  let page := page? (bytes listing)
  [ ("s3 xml: a ListObjectsV2 page, its keys unescaped, a + as a space", page == some expectedPage),
    ("s3 xml: a page not truncated has no next, and an empty one no entries",
      page? (bytes "<ListBucketResult><IsTruncated>false</IsTruncated><NextContinuationToken>t\
        </NextContinuationToken><Prefix/></ListBucketResult>")
        == some { entries := [] }),
    ("s3 xml: an error's code", errorCode (bytes errorDocument) == "NoSuchKey"
      && errorCode (bytes "not xml") == "" && errorCode (bytes listing) == ""),
    ("s3 xml: references, decimal and hex, and attributes in either quote",
      ((Xml.parse "<a x='1>' y=\"&\">&lt;&#65;&#x42;&amp;&apos;</a>").map (·.content))
        == some "<AB&'"),
    ("s3 xml: an element's children by name, its first, and the text of that",
      match Xml.parse "<r><a>1</a><b>x</b><a>2</a></r>" with
      | some root => (root.all "a").map (·.content) == ["1", "2"]
          && (root.child? "b").map (·.content) == some "x" && root.text? "a" == some "1"
          && root.text? "c" == none
      | none => false),
    ("s3 xml: escape reads back", ((Xml.parse ("<a>" ++ Xml.escape "<&>\"'é" ++ "</a>")).map
      (·.content)) == some "<&>\"'é"),
    ("s3 xml: a document type, CDATA and an unknown entity are refused",
      (Xml.parse "<!DOCTYPE a [<!ENTITY e \"x\">]><a>&e;</a>").isNone
        && (Xml.parse "<a><![CDATA[x]]></a>").isNone && (Xml.parse "<a>&e;</a>").isNone
        && (Xml.parse "<a>&#0;</a>").isNone && (Xml.parse "<a>&#xD800;</a>").isNone),
    ("s3 xml: an end tag that does not match, one missing, two roots, text outside are refused",
      (Xml.parse "<a></b>").isNone && (Xml.parse "<a>").isNone && (Xml.parse "<a/><b/>").isNone
        && (Xml.parse "x<a/>").isNone && (Xml.parse "").isNone && (Xml.parse "<a>x<b></a>").isNone),
    ("s3 xml: nesting is bounded", (Xml.parse (deep 16)).isSome && (Xml.parse (deep 17)).isNone),
    ("s3 xml: what is not a page is not read as one",
      page? (bytes errorDocument) == none
        && page? (bytes "<ListBucketResult><Contents><Key>a</Key></Contents></ListBucketResult>")
          == none
        && page? (bytes "<ListBucketResult><Contents><Key>%zz</Key><Size>1</Size></Contents>\
          </ListBucketResult>") == none),
    ("s3 xml: every cut of a page is read or refused, never more",
      let chars := listing.toList
      (List.range chars.length).all fun n =>
        let cut := String.ofList (chars.take n)
        (Xml.parse cut).isNone || (page? (bytes cut)).isSome) ]

/-! ## Calls -/

def creds : SigV4.Credentials :=
  { accessKeyId := "AKIAIOSFODNN7EXAMPLE",
    secretAccessKey := ⟨"wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY"⟩ }

def docTime : Civil.DateTime := Civil.DateTime.ofUnix 1369353600

def key (s : String) : Key := (Key.of? s).getD ⟨"k", by decide⟩

def aws : Bucket := { name := "examplebucket", region := "us-east-1", endpoint := Endpoint.aws "us-east-1" }

def minio : Bucket :=
  { name := "videos", region := "us-east-1",
    endpoint := { host := "localhost", port := 9000, scheme := .http, addressing := .path } }

def callTests : List (String × Bool) :=
  let get := call aws creds docTime (.get (key "test.txt") (some (.span 0 9 (by decide))))
  let put := call minio creds docTime (.put (key "a b/c.mp4") (bytes "x") (some "video/mp4"))
  let head := call minio creds docTime (.head (key "a"))
  let list := call minio creds docTime (.list "a/" (some "/") (some "t") ⟨2, by decide⟩)
  let unsigned := call minio creds docTime (.put (key "k") (bytes "x")) .unsigned
  [ ("s3 call: virtual-hosted, over https, the range and the payload signed",
      get.host == "examplebucket.s3.us-east-1.amazonaws.com" && get.port == 443
        && get.scheme == .https && get.authority == get.host && get.request.target == "/test.txt"
        && get.request.headers.lookup "range" == some "bytes=0-9"
        && get.request.headers.lookup "x-amz-date" == some "20130524T000000Z"
        && (get.request.headers.lookup "authorization").any
          (·.startsWith ("AWS4-HMAC-SHA256 Credential=AKIAIOSFODNN7EXAMPLE/20130524/us-east-1/s3/"
            ++ "aws4_request, SignedHeaders=host;range;x-amz-content-sha256;x-amz-date, ")) ),
    ("s3 call: path-style, over http on a port of its own, which the Host names",
      put.host == "localhost" && put.authority == "localhost:9000" && put.scheme == .http
        && put.request.target == "/videos/a%20b/c.mp4" && put.request.method == .put
        && put.request.headers.lookup "content-type" == some "video/mp4"
        && put.request.headers.lookup "x-amz-content-sha256" == some (SigV4.payloadHash (bytes "x"))),
    ("s3 call: a head goes as HEAD, a listing with its parameters in canonical order",
      head.headOnly && !put.headOnly && (head.request.wireHead head.authority).any
          (fun w => (String.fromUTF8? w).any (·.startsWith "HEAD /videos/a HTTP/1.1\r\n"))
        && list.request.target == "/videos?continuation-token=t&delimiter=%2F&encoding-type=url"
          ++ "&list-type=2&max-keys=2&prefix=a%2F"),
    ("s3 call: a body sent unsigned says so",
      unsigned.request.headers.lookup "x-amz-content-sha256" == some "UNSIGNED-PAYLOAD"),
    ("s3 call: a session token is sent and signed",
      let c := call minio { creds with sessionToken := some ⟨"tok"⟩ } docTime (.delete (key "a"))
      c.request.headers.lookup "x-amz-security-token" == some "tok"
        && (c.request.headers.lookup "authorization").any fun a =>
          (a.splitOn "x-amz-security-token").length == 2),
    ("s3 presign: AWS's example, as a link",
      presign aws creds docTime .get (key "test.txt") ⟨86400, by decide⟩
        == "https://examplebucket.s3.us-east-1.amazonaws.com/test.txt?X-Amz-Algorithm=AWS4-HMAC-"
          ++ "SHA256&X-Amz-Credential=AKIAIOSFODNN7EXAMPLE%2F20130524%2Fus-east-1%2Fs3%2Faws4_"
          ++ "request&X-Amz-Date=20130524T000000Z&X-Amz-Expires=86400&X-Amz-SignedHeaders=host&X-"
          ++ "Amz-Signature=" ++ (SigV4.presign creds docTime ⟨"us-east-1", "s3"⟩
            "examplebucket.s3.us-east-1.amazonaws.com" "GET" ["test.txt"] [] ⟨86400, by decide⟩
            |>.getLast!.2)),
    ("s3 presign: a put whose content type is signed, path-style with a port",
      (presign minio creds docTime .put (key "x/y z") ⟨60, by decide⟩ (some "image/png")).startsWith
        "http://localhost:9000/videos/x/y%20z?X-Amz-Algorithm=AWS4-HMAC-SHA256&"
        && ((presign minio creds docTime .put (key "x") ⟨60, by decide⟩ (some "image/png")).splitOn
          "X-Amz-SignedHeaders=content-type%3Bhost").length == 2),
    ("s3 key: one to 1024 bytes", (Key.of? "").isNone && (Key.of? "a").isSome
      && (Key.of? (String.ofList (List.replicate 1024 'k'))).isSome
      && (Key.of? (String.ofList (List.replicate 1025 'k'))).isNone) ]

def interpretTests : List (String × Bool) :=
  let k := key "a"
  let r (status : Nat) (headers : List (String × String) := []) (body := "") : Response :=
    { status, headers, body := bytes body }
  [ ("s3 answer: stored, with its tag", interpret (.put k .empty) (r 200 [("etag", "\"e\"")])
      == .stored (some "\"e\"")),
    ("s3 answer: an object, whole or a range",
      interpret (.get k) (r 200 [("content-type", "text/plain")] "hello")
          == .object { size := 5, contentType := some "text/plain" } (bytes "hello")
        && interpret (.get k (some (.starting 1))) (r 206 [] "ello")
          == .object { size := 4 } (bytes "ello")),
    ("s3 answer: a head's size is its Content-Length",
      interpret (.head k) (r 200 [("content-length", "12")]) == .found { size := 12 }
        && interpret (.head k) (r 200) == .unreadable),
    ("s3 answer: missing, deleted, and refused with S3's code",
      interpret (.get k) (r 404 [] errorDocument) == .missing && interpret (.head k) (r 404) == .missing
        && interpret (.delete k) (r 204) == .deleted
        && interpret (.put k .empty) (r 403 [] "<Error><Code>AccessDenied</Code></Error>")
          == .refused 403 "AccessDenied"
        && interpret (.list) (r 404 [] "<Error><Code>NoSuchBucket</Code></Error>")
          == .refused 404 "NoSuchBucket"),
    ("s3 answer: a listing, or what cannot be one",
      interpret .list (r 200 [] listing) == .listed expectedPage
        && interpret .list (r 200 [] "<x/>") == .unreadable) ]

/-! ## The model of an object store -/

/-- A caller of the store: asked, it calls with a deadline; told, it reports. -/
inductive In where
  | ask (id : Nat) (op : Op)
  | reply (id : Nat) (answer : Rpc.Reply Answer)
  deriving DecidableEq, Repr, Hashable

inductive Out where
  | call (c : Rpc.Call Op)
  | done (id : Nat) (answer : Rpc.Reply Answer)
  deriving DecidableEq, Repr, Hashable

abbrev storeSig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

abbrev caller : System storeSig where
  State _ := Unit
  actor _ :=
    { init := ()
      step := fun s msg =>
        match msg with
        | .ask id op => (s, [.emit (.call ⟨id, 3000, op⟩)])
        | .reply id answer => (s, [.emit (.done id answer)])
      recover := fun s => (s, []) }
  accept x := ⟨(), x⟩

instance : storeSig.Inspect := {}
instance : caller.Inspect := {}

def s3Port : S3.Port storeSig where
  called | .call c => some c | .done .. => none
  reply id answer := .reply id answer

/-- The store's model sees the calls and answers it has a request and an answer for. -/
def modelPort : Rpc.Port storeSig (ObjectStore.Request String ByteArray)
    (ObjectStore.Answer ByteArray) Empty where
  called
    | .call c => c.request.modelled.map fun r => ⟨c.id, c.deadline_ms, r⟩
    | .done .. => none
  replied
    | .reply id .unknown => some (id, .unknown)
    | .reply id (.answer a) => a.modelled.map fun a => (id, .answer a)
    | .ask .. => none

def world := Outside.any.both (Rpc.outside modelPort ObjectStore.server) fun x => x matches .ask ..

def store := Rpc.outside modelPort ObjectStore.server

def run (events : List (Event storeSig)) : Bool := store.allows events

def out (c : Nat) (op : Op) : Event storeSig := .output (.call ⟨c, 3000, op⟩)

def answered (c : Nat) (a : Answer) : Event storeSig := .input (.reply c (.answer a))

def timedOut (c : Nat) : Event storeSig := .input (.reply c .unknown)

def obj (body : String) : Answer := .object { size := body.length } (bytes body)

def modelTests : List (String × Bool) :=
  let k := key "k"
  let put (c : Nat) (v : String) := out c (.put k (bytes v))
  [ ("object store: a get sees the last write answered",
      run [put 0 "a", answered 0 (.stored none), out 1 (.get k), answered 1 (obj "a")]
        && !run [put 0 "a", answered 0 (.stored none), out 1 (.get k), answered 1 (obj "b")]
        && !run [put 0 "a", answered 0 (.stored none), out 1 (.get k), answered 1 .missing]),
    ("object store: nothing is read that was not put",
      run [out 0 (.get k), answered 0 .missing] && !run [out 0 (.get k), answered 0 (obj "a")]),
    ("object store: a write that timed out may have taken effect, or not, or later",
      let timed := [put 0 "a", timedOut 0]
      run (timed ++ [out 1 (.get k), answered 1 (obj "a")])
        && run (timed ++ [out 1 (.get k), answered 1 .missing])
        && run (timed ++ [put 2 "b", answered 2 (.stored none), out 3 (.get k), answered 3 (obj "a")])),
    ("object store: so may one refused, and one answered while another overlapped it",
      run [put 0 "a", answered 0 (.refused 500 ""), out 1 (.get k), answered 1 (obj "a")]
        && run [put 0 "a", put 1 "b", answered 1 (.stored none), answered 0 (.stored none),
          out 2 (.get k), answered 2 (obj "b")]
        && !run [put 0 "a", answered 0 (.stored none), put 1 "b", answered 1 (.stored none),
          out 2 (.get k), answered 2 (obj "a")]),
    ("object store: a delete answered leaves nothing",
      run [put 0 "a", answered 0 (.stored none), out 1 (.delete k), answered 1 .deleted,
          out 2 (.get k), answered 2 .missing]
        && !run [put 0 "a", answered 0 (.stored none), out 1 (.delete k), answered 1 .deleted,
          out 2 (.get k), answered 2 (obj "a")]),
    ("object store: a call is answered once, and only one that was made",
      !run [put 0 "a", answered 0 (.stored none), answered 0 (.stored none)]
        && !run [answered 0 (.stored none)]) ]

def tests : List (String × Bool) :=
  xmlTests ++ callTests ++ interpretTests ++ modelTests

/-! ## A fake S3 -/

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
    (bytes s!"<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<Error><Code>{code}</Code></Error>") head

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
def field (auth name : String) : Option String :=
  (auth.splitOn (name ++ "="))[1]? |>.map fun rest => (rest.splitOn ",").headD ""

/-- Whether `r` is signed with `creds`, in its header or in its query, as S3 would check it
from the bytes received; and the path and query it names. -/
def verified (creds : SigV4.Credentials) (r : Raw) :
    Option (List String × List (String × String)) := do
  let (path, query) ← splitTarget r.target
  let scope : SigV4.Scope := ⟨"us-east-1", "s3"⟩
  let signedPairs (names : List String) := names.flatMap fun name =>
    (r.headers.filter (·.1 == name)).map fun (_, v) => (name, v)
  match r.headers.lookup "authorization" with
  | some auth =>
    let names := ((field auth "SignedHeaders").getD "").splitOn ";"
    let t ← time? (← r.headers.lookup "x-amz-date")
    let payload ← r.headers.lookup "x-amz-content-sha256"
    unless payload == SigV4.unsignedPayload || payload == SigV4.payloadHash r.body do none
    unless names.contains "host" && names.contains "x-amz-content-sha256" do none
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

def listXml (objects : List (String × ByteArray × String)) (query : List (String × String)) :
    ByteArray :=
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
  bytes ("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<ListBucketResult><IsTruncated>"
    ++ toString (decide truncated) ++ "</IsTruncated>" ++ String.join contents ++ String.join prefixes
    ++ (if truncated then s!"<NextContinuationToken>{Xml.escape page.getLast!}</NextContinuationToken>"
      else "") ++ "</ListBucketResult>")

def range? (header : String) (size : Nat) : Option (Nat × Nat) :=
  match (header.drop 6).toString.splitOn "-", header.startsWith "bytes=" with
  | ["", n], true => n.toNat?.map fun n => (size - n, size)
  | [a, ""], true => a.toNat?.map fun a => (a, size)
  | [a, b], true => do return (← a.toNat?, min size ((← b.toNat?) + 1))
  | _, _ => none

/-- What the fake answers, and the objects after: path-style, one bucket, `videos`. -/
def serve (creds : SigV4.Credentials) (objects : List (String × ByteArray × String)) (r : Raw) :
    ByteArray × List (String × ByteArray × String) :=
  let head := r.verb == "HEAD"
  match verified creds r with
  | none => (failure 403 "SignatureDoesNotMatch" head, objects)
  | some (path, query) =>
    match path, r.verb with
    | ["videos"], "GET" =>
      if query.lookup "list-type" == some "2" then
        (answer 200 [("Content-Type", "application/xml")] (listXml objects query), objects)
      else (failure 400 "InvalidRequest", objects)
    | "videos" :: segments, verb =>
      let k := "/".intercalate segments
      match verb, objects.lookup k with
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
    | _, _ => (failure 404 "NoSuchBucket" head, objects)

/-- The fake on a local port, with the objects in a reference; each request is read whole, then
answered, then the connection closed. -/
def fake (creds : SigV4.Credentials) : Async (TCP.Socket.Server × UInt16 × IO.Ref (List (String × ByteArray × String))) := do
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
                let reply ← objects.modifyGet fun objs => serve creds objs r
                client.send reply
                break
          catch _ => pure ()
          client.close
    catch _ => pure ()
  return (server, tcpPort, objects)

def bucketAt (tcpPort : UInt16) : Bucket :=
  { name := "videos", region := "us-east-1",
    endpoint := { host := "127.0.0.1", port := tcpPort, scheme := .http, addressing := .path } }

def config : Client.Config := { timeout_ms := 3000 }

/-- A link fetched as a browser would: no credentials, the link's own target. -/
def follow (url : String) (method : Method) (body : ByteArray := .empty)
    (headers : List (String × String) := []) : Async (Option Response) := do
  let parts := url.splitOn "/"
  let origin := "/".intercalate (parts.take 3)
  let target := "/" ++ "/".intercalate (parts.drop 3)
  let some (path, query) := splitTarget target | return none
  let some c := Client.Call.at origin { method, path, query, headers, body } | return none
  if c.request.target != target then return none
  Client.exchange c config

def endToEnd : Async (List (String × Bool)) := do
  let (server, tcpPort, objects) ← fake creds
  let b := bucketAt tcpPort
  let ex (op : Op) := exchange b creds op config
  let clip := bytes "0123456789 a video"
  let k := key "clips/a b/ሴ.mp4"
  let put ← ex (.put k clip (some "video/mp4"))
  let got ← ex (.get k)
  let part ← ex (.get k (some (.span 2 5 (by decide))))
  let tail ← ex (.get k (some (.final 5)))
  let head ← ex (.head k)
  let _ ← exchange b creds (.put (key "clips/b.mp4") (bytes "b")) config .unsigned
  let _ ← ex (.put (key "clips/c.mp4") (bytes "cc"))
  let _ ← ex (.put (key "thumbs/a.png") (bytes "png"))
  let rolled ← ex (.list "clips/" (some "/"))
  let first ← ex (.list "clips/" none none ⟨1, by decide⟩)
  let next := match first with | some (.listed p) => p.next | _ => none
  let second ← ex (.list "clips/" none next ⟨1, by decide⟩)
  let forged ← exchange b { creds with secretAccessKey := ⟨"not the secret"⟩ } (.get k) config
  let withToken := { creds with sessionToken := some ⟨"tok"⟩ }
  let (tokenServer, tokenPort, _) ← fake withToken
  let tokened ← exchange (bucketAt tokenPort) withToken (.put k clip) config
  let untokened ← exchange (bucketAt tokenPort) creds (.put k clip) config
  tokenServer.close
  let deleted ← ex (.delete k)
  let gone ← ex (.get k)
  let goneHead ← ex (.head k)
  let expiry : SigV4.Expiry := ⟨600, by decide⟩
  let t ← now
  let upload := presign b creds t .put (key "up/a b.png") expiry (some "image/png")
  let uploaded ← follow upload .put (bytes "picture") [("content-type", "image/png")]
  let wrongType ← follow upload .put (bytes "picture") [("content-type", "text/html")]
  let download := presign b creds t .get (key "up/a b.png") expiry
  let downloaded ← follow download .get
  let tampered ← follow (download.replace "a%20b" "x") .get
  server.close
  let kept := (← objects.get).map (·.1)
  return [
    ("s3 fake: a put is signed as S3 checks it, and stored", put.any (· matches .stored (some _))),
    ("s3 fake: a get brings it back, with its type",
      got == some (.object { size := clip.size, etag := some "\"e\"", contentType := some "video/mp4" } clip)),
    ("s3 fake: a range, and the last bytes",
      part == some (.object { size := 4, contentType := some "video/mp4" } (bytes "2345"))
        && tail == some (.object { size := 5, contentType := some "video/mp4" } (bytes "video"))),
    ("s3 fake: a head, sent as HEAD and read without a body",
      head == some (.found { size := clip.size, contentType := some "video/mp4" })),
    ("s3 fake: a listing rolled up by a delimiter, and one page at a time",
      (match rolled with
        | some (.listed p) => p.entries.map (·.key) == ["clips/b.mp4", "clips/c.mp4"]
            && p.prefixes == ["clips/a b/"] && p.next.isNone
        | _ => false)
      && (match first, second with
        | some (.listed p), some (.listed q) => p.entries.map (·.key) == ["clips/a b/ሴ.mp4"]
            && p.next.isSome && q.entries.map (·.key) == ["clips/b.mp4"]
        | _, _ => false)),
    ("s3 fake: a body sent unsigned is accepted", kept.contains "clips/b.mp4"),
    ("s3 fake: a request signed with another secret is refused as S3 refuses it",
      forged == some (.refused 403 "SignatureDoesNotMatch")),
    ("s3 fake: a session token is sent and signed, and one missing refused",
      tokened.any (· matches .stored _) && untokened.any (· matches .refused 403 _)),
    ("s3 fake: deleted, then missing to a get and to a head",
      deleted == some .deleted && gone == some .missing && goneHead == some .missing),
    ("s3 fake: a presigned put, with the type it was signed for, stores",
      uploaded.any (·.status == 200) && wrongType.any (·.status == 403) && kept.contains "up/a b.png"),
    ("s3 fake: a presigned get brings it back, and a link changed is refused",
      (downloaded.map (·.body)) == some (bytes "picture") && tampered.any (·.status == 403)) ]

/-- A system calls the fake through `S3.handler`, and the run is one the model allows. -/
def conformance : Async (List (String × Bool)) := do
  let (server, tcpPort, _) ← fake creds
  let b := bucketAt tcpPort
  let done ← IO.mkRef 0
  let all ← IO.Promise.new
  let calls := 7
  let rt ← Runtime.startWith caller { record := true } fun rt out => do
    S3.handler s3Port b creds config rt out
    if let .done .. := out then
      if (← done.modifyGet fun n => (n + 1, n + 1)) == calls then all.resolve ()
  let k := key "k"
  let steps : List Op := [.get k, .put k (bytes "one"), .get k, .put k (bytes "two"), .get k,
    .delete k, .get k]
  for (op, id) in steps.zipIdx do
    rt.input (.ask id op)
    -- One at a time, so the run reads as a sequence.
    let before := id + 1
    for _ in [0:300] do
      if (← done.get) ≥ before then break
      Async.sleep 10
  let answered : Async Unit := discard <| await all.result?
  Async.race answered (Async.sleep 5000)
  rt.idle
  let events := (← rt.trace).toList
  rt.stop
  server.close
  let answers := events.filterMap fun | .output (.done id a) => some (id, a) | _ => none
  return [
    ("s3 handler: each call answered, in the order made",
      answers.map (fun (_, a) => match a with | .answer a => a.modelled | .unknown => none)
        == [some .missing, some .stored, some (.found (bytes "one")), some .stored,
          some (.found (bytes "two")), some .deleted, some .missing]),
    ("s3 handler: the run with the fake is one the model of an object store allows",
      world.allows events) ]

def live : Async (List (String × Bool)) := do
  return (← endToEnd) ++ (← conformance)

end Tests.S3
