/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Lanes.Testing
import Tests.S3

/-!
Bounded and large uploads: the browser's `POST` under a policy, and multipart uploads.

- AWS's documented example of a `POST` policy (SigV4, `sigv4examplebucket`, 29 December 2015),
  whose signature is computed from its policy and read back; and botocore 1.44's
  `generate_presigned_post` and presigned `UploadPart` at a fixed time, as vectors: the
  conditions read from botocore's policy are those `Post.conditions` gives, the fields are the
  same, and the signature of botocore's policy is botocore's.
- What `Post.check` refuses, the multipart calls and the answers read.
- The test kit's fake S3 (`Lanes/Services/S3/Testing.lean`): it takes a `POST` form only with the
  policy's signature, before its expiry, with every condition met and every field named, and
  refuses as S3 does (`EntityTooLarge`, `EntityTooSmall`, `AccessDenied`); and multipart
  uploads, with S3's part sizes, part order, ETags and a Complete made twice. A server's multipart upload
  (`S3.upload`), a browser's parts through presigned links with their length signed, and the run
  checked against the multipart model.
-/

namespace Tests.S3Upload

open Lanes Lanes.S3 Lanes.Http Std Std.Async
open Tests.S3 (bytes creds key docTime config)
open Lanes.Testing (status)
open Lanes.Testing.S3 (Fake follow postForm code etag)

/-! ## AWS's documented example -/

def awsPolicy : String :=
  "eyAiZXhwaXJhdGlvbiI6ICIyMDE1LTEyLTMwVDEyOjAwOjAwLjAwMFoiLA0KICAiY29uZGl0aW9ucyI6IFsNCiAgICB7ImJ1Y2tldCI6ICJzaWd2NGV4YW1wbGVidWNrZXQifSwNCiAgICBbInN0YXJ0cy13aXRoIiwgIiRrZXkiLCAidXNlci91c2VyMS8iXSwNCiAgICB7ImFjbCI6ICJwdWJsaWMtcmVhZCJ9LA0KICAgIHsic3VjY2Vzc19hY3Rpb25fcmVkaXJlY3QiOiAiaHR0cDovL3NpZ3Y0ZXhhbXBsZWJ1Y2tldC5zMy5hbWF6b25hd3MuY29tL3N1Y2Nlc3NmdWxfdXBsb2FkLmh0bWwifSwNCiAgICBbInN0YXJ0cy13aXRoIiwgIiRDb250ZW50LVR5cGUiLCAiaW1hZ2UvIl0sDQogICAgeyJ4LWFtei1tZXRhLXV1aWQiOiAiMTQzNjUxMjM2NTEyNzQifSwNCiAgICB7IngtYW16LXNlcnZlci1zaWRlLWVuY3J5cHRpb24iOiAiQUVTMjU2In0sDQogICAgWyJzdGFydHMtd2l0aCIsICIkeC1hbXotbWV0YS10YWciLCAiIl0sDQoNCiAgICB7IngtYW16LWNyZWRlbnRpYWwiOiAiQUtJQUlPU0ZPRE5ON0VYQU1QTEUvMjAxNTEyMjkvdXMtZWFzdC0xL3MzL2F3czRfcmVxdWVzdCJ9LA0KICAgIHsieC1hbXotYWxnb3JpdGhtIjogIkFXUzQtSE1BQy1TSEEyNTYifSwNCiAgICB7IngtYW16LWRhdGUiOiAiMjAxNTEyMjlUMDAwMDAwWiIgfQ0KICBdDQp9"

def awsCredential : String := "AKIAIOSFODNN7EXAMPLE/20151229/us-east-1/s3/aws4_request"

def awsConditions : List Post.Condition :=
  [ .eq "bucket" "sigv4examplebucket", .startsWith "key" "user/user1/", .eq "acl" "public-read",
    .eq "success_action_redirect" "http://sigv4examplebucket.s3.amazonaws.com/successful_upload.html",
    .startsWith "Content-Type" "image/", .eq "x-amz-meta-uuid" "14365123651274",
    .eq "x-amz-server-side-encryption" "AES256", .startsWith "x-amz-meta-tag" "",
    .eq "x-amz-credential" awsCredential, .eq "x-amz-algorithm" "AWS4-HMAC-SHA256",
    .eq "x-amz-date" "20151229T000000Z" ]

/-- The example's form, the file's name put into its key as S3 does. -/
def awsFields : List (String × String) :=
  [ ("key", "user/user1/photo.jpg"), ("acl", "public-read"),
    ("success_action_redirect", "http://sigv4examplebucket.s3.amazonaws.com/successful_upload.html"),
    ("Content-Type", "image/jpeg"), ("x-amz-meta-uuid", "14365123651274"),
    ("x-amz-server-side-encryption", "AES256"), ("X-Amz-Credential", awsCredential),
    ("X-Amz-Algorithm", "AWS4-HMAC-SHA256"), ("X-Amz-Date", "20151229T000000Z"),
    ("x-amz-meta-tag", ""), ("Policy", awsPolicy), ("X-Amz-Signature", "") ]

/-- What `Post.check` refused, if anything. -/
def verdict : Except Post.Refusal Unit → Option Post.Refusal
  | .ok () => none
  | .error r => some r

/-- The manifest of `parts`, which the test gives in order. -/
def manifest (parts : List (PartNumber × String)) : Manifest :=
  match Manifest.of? parts with
  | some m => m
  | none => ⟨[(⟨1, by decide⟩, "")], by decide⟩

def day (y m d : Nat) (s : Nat := 0) : Civil.DateTime :=
  Civil.DateTime.ofUnix (((Civil.Date.mk? y m d).map (·.toDays)).getD 0 * 86400 + s)

def awsTests : List (String × Bool) :=
  let t := day 2015 12 29
  let d := Post.decode? awsPolicy
  let check (at_ : Civil.DateTime) (fields := awsFields) :=
    d.map fun d => verdict (Post.check d "sigv4examplebucket" fields 1000 at_.toUnix)
  [ ("post policy: AWS's example is signed as documented",
      Post.signature creds.secretAccessKey t ⟨"us-east-1", "s3"⟩ awsPolicy
        == "8afdbf4008c03f22c2cd3cdb72e4afbb1f6a588f3255ac628749a66d7f09699e"),
    ("post policy: AWS's example reads as its conditions, in order",
      d == some { expiration := "2015-12-30T12:00:00.000Z", conditions := awsConditions }),
    ("post policy: AWS's example form is admitted before its expiry, and not after",
      check t == some none && check (day 2015 12 30 43200) == some (some .expired)),
    ("post policy: a key outside the prefix, a type not an image, an unnamed field, refused",
      check t (awsFields.map fun (n, v) => if n == "key" then (n, "user/user2/a") else (n, v))
          == some (some (.unmet (.startsWith "key" "user/user1/")))
        && check t (awsFields.map fun (n, v) => if n == "Content-Type" then (n, "text/html") else (n, v))
          == some (some (.unmet (.startsWith "Content-Type" "image/")))
        && check t (awsFields ++ [("x-amz-meta-other", "1")])
          == some (some (.unnamed "x-amz-meta-other"))) ]

/-! ## botocore's `generate_presigned_post` -/

def boto : Bucket := { name := "examplebucket", region := "us-east-1", endpoint := { host := "s3.amazonaws.com" } }

def minio : Bucket :=
  { name := "examplebucket", region := "us-east-1",
    endpoint := { host := "localhost", port := 9000, scheme := .http, addressing := .path } }

def range (min max : Nat) : Post.Length :=
  if h : min ≤ max ∧ max ≤ Post.maxObject_bytes then ⟨min, max, h.1, h.2⟩
  else ⟨0, 0, by decide, by decide⟩

def expiry (s : Nat) : SigV4.Expiry := if h : 0 < s ∧ s ≤ 604800 then ⟨s, h⟩ else ⟨1, by decide⟩

structure Vector where
  bucket : Bucket
  creds : SigV4.Credentials
  policy : Post.Policy
  url : String
  fields : List (String × String)
  botoPolicy : String
  botoSignature : String

def vectors : List (String × Vector) :=
  [ ("an exact key with a type, 1 byte to 2 GiB, 15 minutes",
      { bucket := boto, creds, url := "https://examplebucket.s3.amazonaws.com/"
        policy := { key := .exact (key "videos/7"), length := range 1 2147483648
                    contentType := some "video/mp4", expiry := expiry 900 }
        fields := [("Content-Type", "video/mp4"), ("key", "videos/7"),
          ("x-amz-algorithm", "AWS4-HMAC-SHA256"),
          ("x-amz-credential", "AKIAIOSFODNN7EXAMPLE/20130524/us-east-1/s3/aws4_request"),
          ("x-amz-date", "20130524T000000Z")]
        botoPolicy := "eyJleHBpcmF0aW9uIjogIjIwMTMtMDUtMjRUMDA6MTU6MDBaIiwgImNvbmRpdGlvbnMiOiBbWyJjb250ZW50LWxlbmd0aC1yYW5nZSIsIDEsIDIxNDc0ODM2NDhdLCB7IkNvbnRlbnQtVHlwZSI6ICJ2aWRlby9tcDQifSwgeyJidWNrZXQiOiAiZXhhbXBsZWJ1Y2tldCJ9LCB7ImtleSI6ICJ2aWRlb3MvNyJ9LCB7IngtYW16LWFsZ29yaXRobSI6ICJBV1M0LUhNQUMtU0hBMjU2In0sIHsieC1hbXotY3JlZGVudGlhbCI6ICJBS0lBSU9TRk9ETk43RVhBTVBMRS8yMDEzMDUyNC91cy1lYXN0LTEvczMvYXdzNF9yZXF1ZXN0In0sIHsieC1hbXotZGF0ZSI6ICIyMDEzMDUyNFQwMDAwMDBaIn1dfQ=="
        botoSignature := "33c85669b849b4140e7cf8d8f9e8b1e82dde61594667bce309a381cd34bd2e74" }),
    ("a key under a prefix, with a session token, up to 1 MiB, an hour",
      { bucket := boto, creds := { creds with sessionToken := some ⟨"the-token"⟩ }
        url := "https://examplebucket.s3.amazonaws.com/"
        policy := { key := .startsWith "user/alice/", length := range 0 1048576, expiry := expiry 3600 }
        fields := [("key", "user/alice/${filename}"), ("x-amz-algorithm", "AWS4-HMAC-SHA256"),
          ("x-amz-credential", "AKIAIOSFODNN7EXAMPLE/20130524/us-east-1/s3/aws4_request"),
          ("x-amz-date", "20130524T000000Z"), ("x-amz-security-token", "the-token")]
        botoPolicy := "eyJleHBpcmF0aW9uIjogIjIwMTMtMDUtMjRUMDE6MDA6MDBaIiwgImNvbmRpdGlvbnMiOiBbWyJjb250ZW50LWxlbmd0aC1yYW5nZSIsIDAsIDEwNDg1NzZdLCB7ImJ1Y2tldCI6ICJleGFtcGxlYnVja2V0In0sIFsic3RhcnRzLXdpdGgiLCAiJGtleSIsICJ1c2VyL2FsaWNlLyJdLCB7IngtYW16LWFsZ29yaXRobSI6ICJBV1M0LUhNQUMtU0hBMjU2In0sIHsieC1hbXotY3JlZGVudGlhbCI6ICJBS0lBSU9TRk9ETk43RVhBTVBMRS8yMDEzMDUyNC91cy1lYXN0LTEvczMvYXdzNF9yZXF1ZXN0In0sIHsieC1hbXotZGF0ZSI6ICIyMDEzMDUyNFQwMDAwMDBaIn0sIHsieC1hbXotc2VjdXJpdHktdG9rZW4iOiAidGhlLXRva2VuIn1dfQ=="
        botoSignature := "16543f530dacedf111978251497012a25e424e8698a84daae1bd088694023afb" }),
    ("path-style at a port, a key with a space, 10 to 20 bytes, a minute",
      { bucket := minio, creds, url := "http://localhost:9000/examplebucket"
        policy := { key := .exact (key "a b/c.png"), length := range 10 20
                    contentType := some "image/png", expiry := expiry 60 }
        fields := [("Content-Type", "image/png"), ("key", "a b/c.png"),
          ("x-amz-algorithm", "AWS4-HMAC-SHA256"),
          ("x-amz-credential", "AKIAIOSFODNN7EXAMPLE/20130524/us-east-1/s3/aws4_request"),
          ("x-amz-date", "20130524T000000Z")]
        botoPolicy := "eyJleHBpcmF0aW9uIjogIjIwMTMtMDUtMjRUMDA6MDE6MDBaIiwgImNvbmRpdGlvbnMiOiBbWyJjb250ZW50LWxlbmd0aC1yYW5nZSIsIDEwLCAyMF0sIHsiQ29udGVudC1UeXBlIjogImltYWdlL3BuZyJ9LCB7ImJ1Y2tldCI6ICJleGFtcGxlYnVja2V0In0sIHsia2V5IjogImEgYi9jLnBuZyJ9LCB7IngtYW16LWFsZ29yaXRobSI6ICJBV1M0LUhNQUMtU0hBMjU2In0sIHsieC1hbXotY3JlZGVudGlhbCI6ICJBS0lBSU9TRk9ETk43RVhBTVBMRS8yMDEzMDUyNC91cy1lYXN0LTEvczMvYXdzNF9yZXF1ZXN0In0sIHsieC1hbXotZGF0ZSI6ICIyMDEzMDUyNFQwMDAwMDBaIn1dfQ=="
        botoSignature := "a3f36b45c6e7d8039ffa1c53046bca67d10ca91f75a0b95e0718393087f2b865" }) ]

def vectorTests : List (String × Bool) :=
  vectors.map fun (name, v) =>
    let f := Post.form v.bucket v.creds docTime v.policy
    (s!"post policy, botocore: {name}",
      Post.decode? v.botoPolicy == some (Post.document v.bucket v.creds docTime v.policy)
        && Post.decode? f.policy == some (Post.document v.bucket v.creds docTime v.policy)
        && Post.signature v.creds.secretAccessKey docTime v.bucket.scope v.botoPolicy == v.botoSignature
        && f.signature == Post.signature v.creds.secretAccessKey docTime v.bucket.scope f.policy
        && f.url == v.url && f.named == v.fields
        && f.fields.map (·.1) == v.fields.map (·.1) ++ ["policy", "x-amz-signature"])

/-- botocore's `generate_presigned_url('upload_part', …)` for 15 minutes, which signs only
`host`; its query is in another order, and the signature is the same. -/
def partTests : List (String × Bool) :=
  let url := presignPart boto creds docTime (key "videos/big.mp4") "VXBsb2FkIElE" ⟨3, by decide⟩
    ⟨900, by decide⟩
  let sized := presignPart boto creds docTime (key "videos/big.mp4") "VXBsb2FkIElE" ⟨3, by decide⟩
    ⟨900, by decide⟩ (some 5242880)
  [ ("presigned part, botocore: the same signature",
      url.startsWith "https://examplebucket.s3.amazonaws.com/videos/big.mp4?X-Amz-Algorithm=AWS4-HMAC-SHA256&"
        && (url.splitOn "X-Amz-Signature=1c8645fe37d0e8e7ef7d89211018dcb508a784858049993aa6feb2d703a3226f").length == 2
        && (url.splitOn "&partNumber=3&uploadId=VXBsb2FkIElE&").length == 2),
    ("presigned part: with a length, Content-Length is signed",
      (sized.splitOn "X-Amz-SignedHeaders=content-length%3Bhost").length == 2) ]

/-! ## What S3 refuses, and the multipart calls -/

def checkTests : List (String × Bool) :=
  let p : Post.Policy := { key := .exact (key "up/a"), length := range 2 10, contentType := some "image/png"
                           expiry := expiry 60 }
  let d := Post.document minio creds docTime p
  let f := Post.form minio creds docTime p
  let at_ := docTime.toUnix + 30
  let fields := f.fields
  let set (name value : String) := fields.map fun (n, v) => if n == name then (n, value) else (n, v)
  let ok (size : Nat) (fs := fields) (now := at_) := verdict (Post.check d "examplebucket" fs size now)
  [ ("post check: the form's own fields and a file in range are admitted",
      ok 2 == none && ok 10 == none),
    ("post check: a file too large or too small is refused by its range",
      ok 11 == some (.unmet (.length 2 10)) && ok 1 == some (.unmet (.length 2 10))),
    ("post check: another key, another type, another bucket, an unnamed field, refused",
      ok 5 (set "key" "up/b") == some (.unmet (.eq "key" "up/a"))
        && ok 5 (set "Content-Type" "text/html") == some (.unmet (.eq "Content-Type" "image/png"))
        && verdict (Post.check d "other" fields 5 at_) == some (.unmet (.eq "bucket" "examplebucket"))
        && ok 5 (fields ++ [("acl", "public-read")]) == some (.unnamed "acl")),
    ("post check: at its expiry and after, refused; names compared without case",
      ok 5 fields (docTime.toUnix + 60) == some .expired
        && ok 5 (fields.map fun (n, v) => (n.toUpper, v)) == none),
    ("post check: the expiration is RFC 3339 in UTC", Post.expiration docTime (expiry 900) == "2013-05-24T00:15:00Z") ]

def callTests : List (String × Bool) :=
  let k := key "big video.mp4"
  let c (op : Op) := (S3.call minio creds docTime op).request
  let m := (manifest [(⟨1, by decide⟩, "\"a\""), (⟨2, by decide⟩, "\"b\"")])
  [ ("multipart call: create is a POST of ?uploads, with the type",
      (c (.createUpload k (some "video/mp4"))).method == .post
        && (c (.createUpload k (some "video/mp4"))).target == "/examplebucket/big%20video.mp4?uploads="
        && (c (.createUpload k (some "video/mp4"))).headers.lookup "content-type" == some "video/mp4"),
    ("multipart call: a part is a PUT with its number and upload, its body signed",
      (c (.uploadPart k "u1" ⟨3, by decide⟩ (bytes "abc"))).target
          == "/examplebucket/big%20video.mp4?partNumber=3&uploadId=u1"
        && (c (.uploadPart k "u1" ⟨3, by decide⟩ (bytes "abc"))).headers.lookup "x-amz-content-sha256"
          == some (SigV4.payloadHash (bytes "abc"))),
    ("multipart call: complete is a POST of the parts in XML, their ETags escaped",
      (c (.completeUpload k "u1" m)).method == .post
        && (c (.completeUpload k "u1" m)).body == bytes ("<CompleteMultipartUpload xmlns=\"http://s3.amazonaws.com/doc/2006-03-01/\">"
          ++ "<Part><PartNumber>1</PartNumber><ETag>&quot;a&quot;</ETag></Part>"
          ++ "<Part><PartNumber>2</PartNumber><ETag>&quot;b&quot;</ETag></Part></CompleteMultipartUpload>")),
    ("multipart call: abort is a DELETE, list parts a GET after a marker",
      (c (.abortUpload k "u1")).method == .delete
        && (c (.listParts k "u1" (some ⟨2, by decide⟩))).target
          == "/examplebucket/big%20video.mp4?part-number-marker=2&uploadId=u1"),
    ("multipart: a manifest must be ascending and not empty",
      (Manifest.of? []).isNone && (Manifest.of? [(⟨2, by decide⟩, "a"), (⟨1, by decide⟩, "b")]).isNone
        && (Manifest.of? [(⟨1, by decide⟩, "a"), (⟨1, by decide⟩, "b")]).isNone
        && (PartNumber.of? 0).isNone && (PartNumber.of? 10001).isNone && (PartNumber.of? 10000).isSome) ]

def initiated : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<InitiateMultipartUploadResult xmlns=\"http://s3.amazonaws.com/doc/2006-03-01/\">"
    ++ "<Bucket>example-bucket</Bucket><Key>example-object</Key>"
    ++ "<UploadId>VXBsb2FkIElEIGZvciA2aWWpbmcncyBteS1tb3ZpZS5tMnRzIHVwbG9hZA</UploadId>"
    ++ "</InitiateMultipartUploadResult>"

def listed : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<ListPartsResult xmlns=\"http://s3.amazonaws.com/doc/2006-03-01/\">"
    ++ "<Bucket>example-bucket</Bucket><Key>example-object</Key><UploadId>XXBsb2FkIElEIGZvciBlbHZpbmcncyVcdS1tb3ZpZS5tMnRzEEEwbG9hZA</UploadId>"
    ++ "<PartNumberMarker>1</PartNumberMarker><NextPartNumberMarker>3</NextPartNumberMarker>"
    ++ "<MaxParts>2</MaxParts><IsTruncated>true</IsTruncated>"
    ++ "<Part><PartNumber>2</PartNumber><LastModified>2010-11-10T20:48:34.000Z</LastModified>"
    ++ "<ETag>\"7778aef83f66abc1fa1e8477f296d394\"</ETag><Size>10485760</Size></Part>"
    ++ "<Part><PartNumber>3</PartNumber><LastModified>2010-11-10T20:48:33.000Z</LastModified>"
    ++ "<ETag>\"aaaa18db4cc2f85cedef654fccc4a4x8\"</ETag><Size>10485760</Size></Part></ListPartsResult>"

def answerTests : List (String × Bool) :=
  let k := key "k"
  let m := (manifest [(⟨1, by decide⟩, "\"a\"")])
  let r (status : Nat) (headers : List (String × String) := []) (body := "") : Response :=
    { status, headers, body := bytes body }
  [ ("multipart answer: an upload begun, with its id",
      interpret (.createUpload k) (r 200 [] initiated)
        == .started "VXBsb2FkIElEIGZvciA2aWWpbmcncyBteS1tb3ZpZS5tMnRzIHVwbG9hZA"),
    ("multipart answer: a part's ETag, and the parts held, a page at a time",
      interpret (.uploadPart k "u" ⟨1, by decide⟩ .empty) (r 200 [("etag", "\"e1\"")]) == .stored (some "\"e1\"")
        && interpret (.listParts k "u") (r 200 [] listed) == .parts {
          parts := [⟨2, "\"7778aef83f66abc1fa1e8477f296d394\"", 10485760⟩,
            ⟨3, "\"aaaa18db4cc2f85cedef654fccc4a4x8\"", 10485760⟩], next := some 3 }),
    ("multipart answer: completed, or a 200 whose body is an error, or no such upload",
      interpret (.completeUpload k "u" m) (r 200 [] ("<CompleteMultipartUploadResult><Location>x</Location>"
          ++ "<ETag>&quot;3858f62230ac3c915f300c664312c11f-9&quot;</ETag></CompleteMultipartUploadResult>"))
          == .completed (some "\"3858f62230ac3c915f300c664312c11f-9\"")
        && interpret (.completeUpload k "u" m) (r 200 [] "<Error><Code>InternalError</Code></Error>")
          == .refused 200 "InternalError"
        && interpret (.completeUpload k "u" m) (r 404 [] "<Error><Code>NoSuchUpload</Code></Error>")
          == .refused 404 "NoSuchUpload"),
    ("multipart answer: aborted", interpret (.abortUpload k "u") (r 204) == .deleted) ]

def planTests : List (String × Bool) :=
  let mib := 1024 ^ 2
  let p0 := Multipart.Plan.auto 0 (by decide)
  let p1 := Multipart.Plan.auto (5 * mib + 3) (by decide)
  let big := Multipart.Plan.auto Multipart.maxObject_bytes (by decide)
  [ ("multipart plan: an empty body is one empty part", p0.count == 1 && p0.range 0 == (0, 0)),
    ("multipart plan: 5 MiB and 3 bytes are a part of 5 MiB and one of 3 bytes",
      p1.partSize.val == 5 * mib && p1.count == 2 && p1.range 1 == (5 * mib, 5 * mib + 3)),
    ("multipart plan: 5 TiB in at most 10,000 parts of whole MiB",
      big.count ≤ 10000 && big.partSize.val % mib == 0 && big.partSize.val == 525 * mib),
    ("multipart plan: too many parts are refused",
      (Multipart.Plan.of? (10001 * 5 * mib) ⟨5 * mib, by decide⟩).isNone) ]

def tests : List (String × Bool) :=
  awsTests ++ vectorTests ++ partTests ++ checkTests ++ callTests ++ answerTests ++ planTests

/-! ## Forms against the fake S3 of the test kit -/

/-- Posts `form` with `file`; `change` alters the fields first. -/
def post (form : Post.Form) (file : ByteArray) (filename : String := "clip.mp4")
    (change : List (String × String) → List (String × String) := id) : Async (Option Response) :=
  postForm form.url (change form.fields) file filename config

def postTests : Async (List (String × Bool)) := do
  let store ← Fake.start creds "videos"
  let b := store.bucket
  let t ← S3.now
  let policy : Post.Policy := { key := .exact (key "up/a.mp4"), length := range 1 100
                                contentType := some "video/mp4", expiry := expiry 600 }
  let form := Post.form b creds t policy
  let clip := bytes "twenty bytes of clip"
  let ok ← post form clip
  let stored ← store.object? "up/a.mp4"
  let large ← post form (ByteArray.mk (Array.replicate 101 65))
  let empty ← post form .empty
  let set (name value : String) (fs : List (String × String)) :=
    fs.map fun (n, v) => if n == name then (n, value) else (n, v)
  let otherKey ← post form clip (change := set "key" "up/b.mp4")
  let otherType ← post form clip (change := set "Content-Type" "text/html")
  let extra ← post form clip (change := fun fs => ("acl", "public-read") :: fs)
  let wider := Post.document b creds t { policy with length := range 1 1000 }
  let tampered ← post form clip (change := set "policy" wider.encode)
  let prefixed := Post.form b creds t { policy with key := .startsWith "user/alice/", contentType := none }
  let chosen ← post prefixed clip "cat.png"
  let outside ← post prefixed clip (change := set "key" "user/bob/cat.png")
  let old := Post.form b creds (Civil.DateTime.ofUnix (t.toUnix - 3600)) { policy with expiry := expiry 60 }
  let expired ← post old clip
  let chosenKept ← store.holds "user/alice/cat.png"
  store.stop
  let withToken := { creds with sessionToken := some ⟨"tok"⟩ }
  let tokenStore ← Fake.start withToken "videos"
  let tb := tokenStore.bucket
  let tokened ← post (Post.form tb withToken t policy) clip
  let untokened ← post (Post.form tb creds t policy) clip
  tokenStore.stop
  return [
    ("s3 fake, post: a form under its policy stores the file, with its type",
      status ok == 204 && stored == some (clip, "video/mp4")),
    ("s3 fake, post: a file larger or smaller than the range is refused as S3 refuses it",
      status large == 400 && code large == "EntityTooLarge" && status empty == 400
        && code empty == "EntityTooSmall"),
    ("s3 fake, post: another key, another type, a field the policy does not name, refused",
      status otherKey == 403 && status otherType == 403 && status extra == 403),
    ("s3 fake, post: a policy changed after signing is refused",
      status tampered == 403 && code tampered == "SignatureDoesNotMatch"),
    ("s3 fake, post: under a prefix the file's name is the key's end, and a key outside it refused",
      status chosen == 204 && chosenKept && status outside == 403),
    ("s3 fake, post: an expired policy is refused", status expired == 403 && code expired == "AccessDenied"),
    ("s3 fake, post: a session token is a field the policy names, and one missing refused",
      status tokened == 204 && status untokened == 403) ]

/-! ## Multipart against the fake -/

def mib : Nat := 1024 ^ 2

def filled (n : Nat) (byte : UInt8) : ByteArray := ByteArray.mk (Array.replicate n byte)

/-- The events of a run of the flow, for the multipart model: each call and its answer. -/
abbrev Request := Lanes.Multipart.Request Unit ByteArray String

inductive In where
  | reply (call : Nat) (r : Rpc.Reply (Lanes.Multipart.Answer ByteArray String))
  deriving DecidableEq, Repr, Hashable

abbrev runSig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Rpc.Call Request

def runPort : Rpc.Port runSig Request (Lanes.Multipart.Answer ByteArray String) Empty where
  called c := some c
  replied | .reply call r => some (call, r)

def uploadNumber (id : String) : Nat := ((id.drop 7).toString.toNat?).getD 0

def modelled (body : ByteArray) : Multipart.Step → Request
  | .create => .create ()
  | .part id n first stop => .part (uploadNumber id) n.val (body.extract first stop)
  | .complete id m => .complete () (uploadNumber id) (m.val.map fun (n, e) => (n.val, e))
  | .abort id => .abort (uploadNumber id)
  | .check => .get ()

def answerOf : Option Answer → Rpc.Reply (Lanes.Multipart.Answer ByteArray String)
  | some (.started id) => .answer (.created (uploadNumber id))
  | some (.stored (some e)) => .answer (.stored e)
  | some (.completed _) => .answer .completed
  | some .deleted => .answer .aborted
  | some _ => .answer .refused
  | none => .unknown

/-- `S3.upload`'s loop, with its calls and answers kept as events for the model. -/
def recorded (b : Bucket) (flow : Multipart.Flow) (body : ByteArray) :
    Async (Multipart.Phase × List (Event runSig)) := do
  let mut f := flow
  let mut events := #[]
  for i in [0:flow.bound] do
    let some step := f.next | break
    let answer ← try exchange b creds (f.op body step) config catch _ => pure none
    events := events.push (.output ⟨i, 1000, modelled body step⟩) |>.push (.input (.reply i (answerOf answer)))
    f := f.answer answer
  return (f.phase, events.toList)

def multipartTests : Async (List (String × Bool)) := do
  let store ← Fake.start creds "videos"
  let b := store.bucket
  let ex (op : Op) := exchange b creds op { config with maxResponseBytes := 16 * mib }
  let body := filled (5 * mib) 97 ++ bytes "end"
  let k := key "big/a.mp4"
  let flow := Multipart.Flow.start k (Multipart.Plan.auto (5 * mib + 3) (by decide)) (some "video/mp4")
  let (phase, events) ← recorded b flow body
  let whole ← ex (.get k)
  -- Parts by hand: out of order, one sent again with other bytes.
  let k2 := key "big/b.mp4"
  let started ← ex (.createUpload k2)
  let id := match started with | some (.started id) => id | _ => ""
  let tail := bytes "tail"
  let first := filled (5 * mib) 98
  let p2 ← ex (.uploadPart k2 id ⟨2, by decide⟩ tail)
  let _ ← ex (.uploadPart k2 id ⟨1, by decide⟩ (filled (5 * mib) 97))
  let p1 ← ex (.uploadPart k2 id ⟨1, by decide⟩ first)
  let held ← ex (.listParts k2 id)
  let etagOf (a : Option Answer) := match a with | some (.stored (some e)) => e | _ => ""
  let listing := (manifest [(⟨1, by decide⟩, etagOf p1), (⟨2, by decide⟩, etagOf p2)])
  let stale := (manifest [(⟨1, by decide⟩, etag (filled (5 * mib) 97)), (⟨2, by decide⟩, etagOf p2)])
  let wrong ← ex (.completeUpload k2 id stale)
  let done ← ex (.completeUpload k2 id listing)
  let again ← ex (.completeUpload k2 id listing)
  let object ← ex (.get k2)
  -- Parts too small, and an abort.
  let k3 := key "big/c.mp4"
  let id3 := match ← ex (.createUpload k3) with | some (.started id) => id | _ => ""
  let s1 ← ex (.uploadPart k3 id3 ⟨1, by decide⟩ (bytes "small"))
  let s2 ← ex (.uploadPart k3 id3 ⟨2, by decide⟩ (bytes "parts"))
  let small := (manifest [(⟨1, by decide⟩, etagOf s1), (⟨2, by decide⟩, etagOf s2)])
  let tooSmall ← ex (.completeUpload k3 id3 small)
  let aborted ← ex (.abortUpload k3 id3)
  let afterAbort ← ex (.uploadPart k3 id3 ⟨1, by decide⟩ (bytes "x"))
  -- A browser's parts through presigned links, the first with its length signed.
  let k4 := key "big/d.mp4"
  let id4 := match ← ex (.createUpload k4) with | some (.started id) => id | _ => ""
  let t ← S3.now
  let link1 := presignPart b creds t k4 id4 ⟨1, by decide⟩ ⟨600, by decide⟩ (some (5 * mib))
  let link2 := presignPart b creds t k4 id4 ⟨2, by decide⟩ ⟨600, by decide⟩
  let short ← follow link1 .put (filled (5 * mib - 1) 99)
  let put1 ← follow link1 .put (filled (5 * mib) 99)
  let put2 ← follow link2 .put tail
  let browserEtag (r : Option Response) := ((r.bind (·.headers.lookup "etag")).getD "")
  let byLinks := (manifest [(⟨1, by decide⟩, browserEtag put1), (⟨2, by decide⟩, browserEtag put2)])
  let linked ← ex (.completeUpload k4 id4 byLinks)
  let linkedObject ← ex (.get k4)
  store.stop
  return [
    ("s3 fake, multipart: the server's upload of 5 MiB and 3 bytes, in two parts, completes",
      match phase with
      | .done (some e) => e.endsWith "-2\"" | _ => false),
    ("s3 fake, multipart: the object is the body, whole and in order",
      match whole with | some (.object _ got) => got == body | _ => false),
    ("s3 fake, multipart: the run is one the multipart model allows",
      (Rpc.outside runPort (Lanes.Multipart.server etag)).allows events),
    ("s3 fake, multipart: parts sent out of order and one sent again are listed with the last ETags",
      match held with
      | some (.parts p) => p.parts.map (·.number) == [1, 2] && p.parts.map (·.etag) == [etagOf p1, etagOf p2]
      | _ => false),
    ("s3 fake, multipart: a stale ETag is refused, and the parts listed make the object, in order",
      wrong == some (.refused 400 "InvalidPart")
        && (match object with | some (.object _ got) => got == first ++ tail | _ => false)),
    ("s3 fake, multipart: complete made twice is answered the same",
      done.isSome && done == again && (done matches some (.completed (some _)))),
    ("s3 fake, multipart: a part under 5 MiB but the last is refused, an abort ends the upload",
      tooSmall == some (.refused 400 "EntityTooSmall") && aborted == some .deleted
        && afterAbort == some (.refused 404 "NoSuchUpload")),
    ("s3 fake, multipart: a browser puts parts through presigned links, the length signed refusing another",
      status short == 403 && status put1 == 200 && status put2 == 200
        && (linked matches some (.completed _))
        && (match linkedObject with | some (.object _ got) => got == filled (5 * mib) 99 ++ tail | _ => false)) ]

def live : Async (List (String × Bool)) := do
  return (← postTests) ++ (← multipartTests)

end Tests.S3Upload
