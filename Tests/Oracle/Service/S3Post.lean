/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Service.S3
import Tests.S3Upload

/-!
Uploads by `POST` under a policy (`S3.Post`) against moto's S3 (`oracles/moto`): forms made by
`Post.form` and posted as a browser posts them (`Testing.S3.postForm`, through the HTTP client),
in a bucket made for the run: one within its policy, one over its `content-length-range`, one
with another key, and one whose policy has expired. After each, the object at the form's key is
read through the S3 client. Recorded in `oracles/moto/s3-post.jsonl`.

Two things are checked, in the run and again from the record. What `Post.check` decides on each
form, at the time it was posted, is what S3 documents (admitted; `EntityTooLarge`;
`AccessDenied` for the key and the expiry), and moto's answer agrees or is a known difference:
moto 5.2.6 stores a posted file without reading its policy, so it admits all four. And the run
is one the object store's model allows, each upload a write granted to a browser
(`ObjectStore.Request.granted`), which may land or not, and each read after it answered.
-/

namespace Tests.Oracle.Service.S3Post

open Lanes Lanes.S3 Lanes.Http Std Std.Async
open Tests.Oracle.Service.S3 (creds bucket createBucket k opJson readOp answerJson readAnswer)
open Tests.S3Upload (range expiry verdict post)

/-! ## The store's model, which sees the uploads as writes granted -/

abbrev Req := ObjectStore.Request String ByteArray

abbrev Ans := ObjectStore.Answer ByteArray

inductive In where
  | reply (id : Nat) (answer : Rpc.Reply Ans)
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Rpc.Call Req

def port : Rpc.Port sig Req Ans Empty where
  called c := some c
  replied | .reply id r => some (id, r)

def model := Rpc.outside port ObjectStore.server

/-! ## An upload, as recorded -/

structure Upload where
  call : Nat
  /-- `within`, `over`, `key` or `expired`. -/
  case : String
  bucket : String
  now_s : Nat
  fields : List (String × String)
  file : ByteArray
  status : Nat
  code : String

def Upload.key (u : Upload) : String := (Post.lookup u.fields "key").getD ""

def Upload.json (u : Upload) : Json :=
  Json.mkObj [("call", u.call), ("post", u.case), ("bucket", u.bucket), ("now_s", u.now_s),
    ("fields", .arr (u.fields.map fun (n, v) => Json.arr #[.str n, .str v]).toArray),
    ("file", Bytes.hex u.file), ("status", u.status), ("code", u.code)]

def readField (j : Json) : Option (String × String) :=
  match j with
  | .arr #[.str n, .str v] => some (n, v)
  | _ => none

def readUpload (j : Json) : Option Upload := do
  let fields ← (j.getObjVal? "fields" >>= Json.getArr?).toOption
  return { call := ← nat? j "call", case := ← str? j "post", bucket := ← str? j "bucket",
           now_s := ← nat? j "now_s", fields := ← fields.toList.mapM readField,
           file := ← bytes? j "file", status := ← nat? j "status", code := ← str? j "code" }

/-! ## What S3 documents, what ours decides, and what moto answers -/

def lengthRange : Post.Length := range 1 100

/-- What `Post.check` must decide on each case: S3's documented answer. -/
def expected : String → Option (Option Post.Refusal)
  | "within" => some none
  | "over" => some (some (.unmet (.length lengthRange.min lengthRange.max)))
  | "key" => some (some (.unmet (.eq "key" "up/key.txt")))
  | "expired" => some (some .expired)
  | _ => none

/-- The status and code S3 refuses with. -/
def s3Refuses : Post.Refusal → Nat × String
  | .unmet (.length ..) => (400, "EntityTooLarge")
  | _ => (403, "AccessDenied")

def Upload.verdict (u : Upload) : Option (Option Post.Refusal) := do
  let d ← Post.decode? (← Post.lookup u.fields "policy")
  return Tests.S3Upload.verdict (Post.check d u.bucket u.fields u.file.size u.now_s)

def admitted (status : Nat) : Bool := status == 200 || status == 201 || status == 204

/-- Moto's answer agrees with ours: admitted when ours admits, refused as S3 refuses when ours
refuses. -/
def agrees (u : Upload) : Option Post.Refusal → Bool
  | none => admitted u.status
  | some r => (u.status, u.code) == s3Refuses r

/-- A known difference: moto 5.2.6's `POST` handler stores the file under the form's `key`
without decoding the policy, so it checks no condition, no expiry and no signature. -/
def known (u : Upload) : Option Post.Refusal → Bool
  | some _ => admitted u.status
  | none => false

def describe : Option Post.Refusal → String
  | none => "admitted"
  | some .expired => "expired"
  | some (.unmet (.length ..)) => "over its range"
  | some (.unmet (.eq field _)) | some (.unmet (.startsWith field _)) => s!"{field} unmet"
  | some r => s!"{repr r}"

def judge (u : Upload) : String × Bool :=
  match u.verdict with
  | none => (s!"s3 post on moto: {u.case}: the policy reads", false)
  | some v =>
    let kind := if agrees u v then "agrees" else if known u v then "known: moto reads no policy" else "differs"
    (s!"s3 post on moto: {u.case}: ours {describe v}, as S3 documents; moto {u.status}{if u.code.isEmpty then "" else " " ++ u.code}: {kind}",
      expected u.case == some v && (agrees u v || known u v))

/-! ## The record -/

def readEvent (j : Json) : Option (Event sig) :=
  match readUpload j, nat? j "call", nat? j "reply" with
  | some u, _, _ => some (.output ⟨u.call, 0, .granted u.key u.file⟩)
  | none, some id, _ => do
    let op ← readOp (← (j.getObjVal? "request").toOption)
    return .output ⟨id, ← nat? j "deadline_ms", ← op.modelled⟩
  | none, none, some id => do
    let r ← readAnswer (← (j.getObjVal? "answer").toOption)
    match r with
    | .unknown => return .input (.reply id .unknown)
    | .answer a => return .input (.reply id (.answer (← a.modelled)))
  | none, none, none => none

def checks (lines : List Json) : List (String × Bool) :=
  let uploads := lines.filterMap readUpload
  let events := lines.filterMap readEvent
  ("s3 post on moto: every line reads, four uploads", events.length == lines.length
      && uploads.map (·.case) == ["within", "over", "key", "expired"])
    :: uploads.map judge
    ++ [("s3 post on moto: the run is one the object store's model allows", model.allows events),
      ("s3 post on moto: and not with a read of an object no form sent",
        !model.allows (events ++ [.output ⟨1000000, 0, .get "up/within.txt"⟩,
          .input (.reply 1000000 (.answer (.found "never sent".toUTF8)))]))]

/-! ## Against moto -/

def policy (key : String) : Post.Policy :=
  { key := .exact (k key), length := lengthRange, contentType := some "text/plain",
    expiry := expiry 600 }

def setKey (key : String) (fields : List (String × String)) : List (String × String) :=
  fields.map fun (n, v) => if n == "key" then (n, key) else (n, v)

def exercise (b : Bucket) : Async (List (String × Bool) × List Json) := do
  let made ← createBucket b
  unless (made.map (·.status)) == some 200 do
    return ([("s3 post on moto: the bucket is made", false)], [])
  let t ← S3.now
  let twenty := "twenty bytes of text".toUTF8
  let cases : List (String × Post.Form × ByteArray × (List (String × String) → List (String × String))) :=
    [ ("within", Post.form b creds t (policy "up/within.txt"), twenty, id),
      ("over", Post.form b creds t (policy "up/over.txt"), ByteArray.mk (Array.replicate 101 120), id),
      ("key", Post.form b creds t (policy "up/key.txt"), twenty, setKey "up/elsewhere.txt"),
      ("expired", Post.form b creds (Civil.DateTime.ofUnix (t.toUnix - 3600))
        { policy "up/expired.txt" with expiry := expiry 60 }, twenty, id) ]
  let mut lines := #[]
  let mut stored := []
  let mut call := 0
  for (case, form, file, change) in cases do
    let now_s := (← S3.now).toUnix.toNat
    let answer ← post form file "file.txt" change
    let u : Upload := { call, case, bucket := b.name, now_s, fields := change form.fields, file,
                        status := Lanes.Testing.status answer, code := Lanes.Testing.S3.code answer }
    lines := lines.push u.json
    let get := Op.get (k u.key)
    let got ← try exchange b creds get Tests.S3.config catch _ => pure none
    let reply : Rpc.Reply Answer := match got with | some a => .answer a | none => .unknown
    let id : Nat := call + 1
    lines := lines.push (Json.mkObj [("call", id), ("deadline_ms", 3000), ("request", (opJson get).getD .null)])
      |>.push (Json.mkObj [("reply", id), ("answer", answerJson reply)])
    if admitted u.status then
      stored := stored ++ [(case, match got with | some (.object _ body) => body == file | _ => false)]
    call := call + 2
  let record := lines.toList
  return ((s!"s3 post on moto: each file moto took is the object at the form's key: {stored}",
      stored.all (·.2)) :: checks record, record)

def run (host : String) (tcpPort : UInt16) : IO (List (String × Bool) × List Json) := do
  (exercise (bucket host tcpPort ((← IO.monoNanosNow) % 1000000000))).block

def oracle : Oracle where
  name := "s3-post"
  reference := "moto"
  envVar := "LANES_MOTO"
  live := run
  replay := checks

end Tests.Oracle.Service.S3Post
