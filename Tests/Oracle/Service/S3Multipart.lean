/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Service.S3

/-!
Multipart uploads (`S3.Multipart`) against moto's S3 (`oracles/moto`), checked against the
multipart model (`Lanes.Multipart.server`) and recorded in `oracles/moto/s3-multipart.jsonl`, in
a bucket made for the run:

- the server's upload of 5 MiB and 3 bytes, as `S3.Multipart.Flow` makes it, and the object read;
- an upload by hand: part 2, then part 1 twice with other bytes, the parts listed, a Complete
  with the first part 1's ETag and one with an ETag no part has, both refused, the Complete with
  the parts listed, made twice, and the object read;
- an upload of two parts under 5 MiB, whose Complete is refused, aborted, a part sent after the
  abort, and the key read.

A part is recorded as its size and its MD5 and SHA-256, not its bytes, and the model's tag of a
part is the ETag S3 gives it, the MD5 in quotes; an object read is recorded as its pieces, cut at
the sizes of the parts it should be made of. Uploads are numbered in the order they began.
-/

namespace Tests.Oracle.Service.S3Multipart

open Lanes Lanes.S3 Lanes.Http Std Std.Async
open Tests.Oracle.Service.S3 (creds bucket createBucket k)

/-! ## A part by its digests -/

structure Digest where
  size : Nat
  md5 : String
  sha256 : String
  deriving DecidableEq, Repr, Hashable

def digest (b : ByteArray) : Digest := ⟨b.size, Bytes.hex (Md5.hash b), SigV4.payloadHash b⟩

/-- The ETag S3 gives a part. -/
def tag (d : Digest) : String := "\"" ++ d.md5 ++ "\""

def Digest.json (d : Digest) : Json := Json.mkObj [("size", d.size), ("md5", d.md5), ("sha256", d.sha256)]

def readDigest (j : Json) : Option Digest :=
  return { size := ← nat? j "size", md5 := ← str? j "md5", sha256 := ← str? j "sha256" }

/-- `body` cut at `sizes`, the last piece what is left. -/
def pieces (body : ByteArray) : List Nat → List ByteArray
  | [] => []
  | [_] => [body]
  | n :: rest => body.extract 0 n :: pieces (body.extract n body.size) rest

/-! ## The model -/

abbrev Req := Lanes.Multipart.Request String Digest String

abbrev Ans := Lanes.Multipart.Answer Digest String

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

def model := Rpc.outside port (Lanes.Multipart.server tag)

/-! ## The record -/

def listingJson (parts : List (Nat × String)) : Json :=
  .arr (parts.map fun (n, t) => Json.arr #[(n : Json), .str t]).toArray

def readListing (j : Json) : Option (List (Nat × String)) := do
  let parts ← j.getArr?.toOption
  parts.toList.mapM fun
    | .arr #[n, .str t] => do return (← n.getNat?.toOption, t)
    | _ => none

def requestJson : Req → Json
  | .create key => Json.mkObj [("op", "create"), ("key", key)]
  | .part u n v => Json.mkObj [("op", "part"), ("upload", u), ("number", n), ("part", v.json)]
  | .complete key u parts =>
    Json.mkObj [("op", "complete"), ("key", key), ("upload", u), ("parts", listingJson parts)]
  | .abort u => Json.mkObj [("op", "abort"), ("upload", u)]
  | .get key => Json.mkObj [("op", "get"), ("key", key)]

def readRequest (j : Json) : Option Req := do
  match ← str? j "op" with
  | "create" => return .create (← str? j "key")
  | "part" => return .part (← nat? j "upload") (← nat? j "number") (← readDigest (← (j.getObjVal? "part").toOption))
  | "complete" =>
    return .complete (← str? j "key") (← nat? j "upload") (← readListing (← (j.getObjVal? "parts").toOption))
  | "abort" => return .abort (← nat? j "upload")
  | "get" => return .get (← str? j "key")
  | _ => none

/-- An answer, with the status and code of a refusal, which the model does not read. -/
def answerJson (status : Nat) (code : String) : Rpc.Reply Ans → Json
  | .unknown => Json.mkObj [("answer", "unknown")]
  | .answer (.created u) => Json.mkObj [("answer", "created"), ("upload", u)]
  | .answer (.stored t) => Json.mkObj [("answer", "stored"), ("tag", t)]
  | .answer .completed => Json.mkObj [("answer", "completed")]
  | .answer .aborted => Json.mkObj [("answer", "aborted")]
  | .answer (.found vs) => Json.mkObj [("answer", "found"), ("parts", .arr (vs.map (·.json)).toArray)]
  | .answer .missing => Json.mkObj [("answer", "missing")]
  | .answer .refused => Json.mkObj [("answer", "refused"), ("status", status), ("code", code)]

def readAnswer (j : Json) : Option (Rpc.Reply Ans) := do
  match ← str? j "answer" with
  | "unknown" => return .unknown
  | "created" => return .answer (.created (← nat? j "upload"))
  | "stored" => return .answer (.stored (← str? j "tag"))
  | "completed" => return .answer .completed
  | "aborted" => return .answer .aborted
  | "found" =>
    let parts ← (j.getObjVal? "parts" >>= Json.getArr?).toOption
    return .answer (.found (← parts.toList.mapM readDigest))
  | "missing" => return .answer .missing
  | "refused" => return .answer .refused
  | _ => none

def readEvent (j : Json) : Option (Event sig) :=
  match nat? j "call", nat? j "reply" with
  | some id, _ => do return .output ⟨id, ← nat? j "deadline_ms", ← readRequest (← (j.getObjVal? "request").toOption)⟩
  | none, some id => do return .input (.reply id (← readAnswer (← (j.getObjVal? "answer").toOption)))
  | none, none => none

/-- A ListParts answer, which the model does not have: the upload, and each part's number, ETag
and size. -/
def readListed (j : Json) : Option (Nat × List (Nat × String × Nat)) := do
  let parts ← (j.getObjVal? "parts" >>= Json.getArr?).toOption
  return (← nat? j "listed", ← parts.toList.mapM fun
    | .arr #[n, .str t, size] => do return (← n.getNat?.toOption, t, ← size.getNat?.toOption)
    | _ => none)

/-- What the run's parts left under each number of `upload`, in order of number: the ETag of the
last one stored and its size. -/
def held (events : List (Event sig)) (upload : Nat) : List (Nat × String × Nat) :=
  let sent := events.filterMap fun
    | .output ⟨id, _, .part u n v⟩ => if u == upload then some (id, n, v.size) else none
    | _ => none
  let stored := events.foldl (init := []) fun acc e => match e with
    | .input (.reply id (.answer (.stored t))) =>
      match sent.find? (·.1 == id) with
      | some (_, n, size) => (n, t, size) :: acc.filter (·.1 != n)
      | none => acc
    | _ => acc
  stored.mergeSort (·.1 ≤ ·.1)

def checks (lines : List Json) : List (String × Bool) :=
  let events := lines.filterMap readEvent
  let listed := lines.filterMap readListed
  [ ("s3 multipart on moto: every line reads",
      events.length + listed.length == lines.length && !events.isEmpty && !listed.isEmpty),
    ("s3 multipart on moto: the run is one the multipart model allows", model.allows events),
    ("s3 multipart on moto: and not with a read of an object of a part never sent",
      !model.allows (events ++ [.output ⟨1000000, 0, .get "big/b.bin"⟩,
        .input (.reply 1000000 (.answer (.found [digest "never sent".toUTF8])))])),
    ("s3 multipart on moto: ListParts gives the last part stored under each number, with its ETag and size",
      listed.all fun (u, parts) => parts == held events u) ]

/-! ## Against moto -/

def config : Client.Config := { timeout_ms := 10000, maxResponseBytes := 16 * 1024 ^ 2 }

structure Run where
  bucket : Bucket
  lines : IO.Ref (Array Json)
  next : IO.Ref Nat
  /-- S3's id of each upload, numbered in the order they began. -/
  uploads : IO.Ref (List String)

def Run.upload (r : Run) (id : String) : IO Nat := do
  let t ← r.uploads.get
  match t.idxOf? id with
  | some i => return i
  | none => r.uploads.set (t ++ [id]); return t.length

/-- What the model sees of `a`; a read is cut at `sizes`. -/
def Run.modelled (r : Run) (sizes : List Nat) : Option Answer → IO (Rpc.Reply Ans)
  | none => return .unknown
  | some (.started id) => return .answer (.created (← r.upload id))
  | some (.stored (some t)) => return .answer (.stored t)
  | some (.completed _) => return .answer .completed
  | some .deleted => return .answer .aborted
  | some (.object _ body) => return .answer (.found ((pieces body sizes).map digest))
  | some .missing => return .answer .missing
  | some _ => return .answer .refused

/-- Makes `op`, recording it as `request` and its answer as the model sees it. -/
def Run.call (r : Run) (op : Op) (request : Option Req) (sizes : List Nat := []) :
    Async (Option Answer) := do
  let id ← r.next.modifyGet fun n => (n, n + 1)
  if let some q := request then
    r.lines.modify (·.push (Json.mkObj [("call", id), ("deadline_ms", config.timeout_ms), ("request", requestJson q)]))
  let a ← try exchange r.bucket creds op config catch _ => pure none
  if let some _ := request then
    let (status, code) := match a with | some (.refused s c) => (s, c) | _ => (0, "")
    let reply ← r.modelled sizes a
    r.lines.modify (·.push (Json.mkObj [("reply", id), ("answer", answerJson status code reply)]))
  return a

def manifest (parts : List (Nat × String)) : Option Manifest :=
  Manifest.of? (parts.filterMap fun (n, t) => (PartNumber.of? n).map (·, t))

def Run.create (r : Run) (key : String) : Async String := do
  match ← r.call (.createUpload (k key)) (some (.create key)) with
  | some (.started id) => return id
  | _ => return ""

def Run.part (r : Run) (key id : String) (n : PartNumber) (body : ByteArray) : Async (Option Answer) := do
  r.call (.uploadPart (k key) id n body) (some (.part (← r.upload id) n.val (digest body)))

def Run.complete (r : Run) (key id : String) (parts : List (Nat × String)) : Async (Option Answer) := do
  match manifest parts with
  | some m => r.call (.completeUpload (k key) id m) (some (.complete key (← r.upload id) parts))
  | none => return none

def Run.get (r : Run) (key : String) (sizes : List Nat) : Async (Option Answer) :=
  r.call (.get (k key)) (some (.get key)) sizes

def etagOf : Option Answer → String
  | some (.stored (some e)) => e
  | _ => ""

def mib : Nat := 1024 ^ 2

def filled (n : Nat) (byte : UInt8) : ByteArray := ByteArray.mk (Array.replicate n byte)

/-- What the model sees of a step of the flow: not the `HEAD` of a check, which it does not have. -/
def Run.request (r : Run) (key : String) (body : ByteArray) : S3.Multipart.Step → IO (Option Req)
  | .create => return some (.create key)
  | .part id n first stop => return some (.part (← r.upload id) n.val (digest (body.extract first stop)))
  | .complete id m => return some (.complete key (← r.upload id) (m.val.map fun (n, e) => (n.val, e)))
  | .abort id => return some (.abort (← r.upload id))
  | .check => return none

/-- The server's upload of `body` to `key` under `plan`, as `S3.upload` runs it. -/
def Run.flow (r : Run) (key : String) (plan : S3.Multipart.Plan) (body : ByteArray) :
    Async S3.Multipart.Phase := do
  let mut f := S3.Multipart.Flow.start (k key) plan
  for _ in [0:f.bound] do
    let some step := f.next | break
    f := f.answer (← r.call (f.op body step) (← r.request key body step))
  return f.phase

def Run.listParts (r : Run) (key id : String) : Async (List Part) := do
  let parts := match ← (try exchange r.bucket creds (.listParts (k key) id) config catch _ => pure none) with
    | some (.parts p) => p.parts
    | _ => []
  let listed := parts.map fun p => Json.arr #[(p.number : Json), .str p.etag, (p.size : Json)]
  r.lines.modify (·.push (Json.mkObj [("listed", ← r.upload id), ("parts", .arr listed.toArray)]))
  return parts

def said : Option Answer → String
  | some (.refused status code) => s!"{status} {code}"
  | some (.completed _) => "completed"
  | some .deleted => "aborted"
  | some _ => "answered"
  | none => "no answer"

def body (a : Option Answer) : ByteArray :=
  match a with
  | some (.object _ got) => got
  | _ => .empty

/-- A part sent after its upload was aborted: S3 answers `404 NoSuchUpload`. A known difference:
moto 5.2.6 looks the upload up without checking that it is there, and answers `500`. Either is a
refusal to the model. -/
def goneOrKnown : Option Answer → Bool
  | some (.refused 404 "NoSuchUpload") | some (.refused 500 _) => true
  | _ => false

def exercise (b : Bucket) : Async (List (String × Bool) × List Json) := do
  let made ← createBucket b
  unless (made.map (·.status)) == some 200 do
    return ([("s3 multipart on moto: the bucket is made", false)], [])
  let r : Run := { bucket := b, lines := ← IO.mkRef #[], next := ← IO.mkRef 0, uploads := ← IO.mkRef [] }
  let whole := filled (5 * mib) 97 ++ "end".toUTF8
  let phase ← r.flow "big/a.bin" (S3.Multipart.Plan.auto (5 * 1024 ^ 2 + 3) (by decide)) whole
  let read ← r.get "big/a.bin" [5 * mib, 3]
  let key := "big/b.bin"
  let id ← r.create key
  let earlier := filled (5 * mib) 97
  let first := filled (5 * mib) 98
  let tail := "tail".toUTF8
  let p2 ← r.part key id ⟨2, by decide⟩ tail
  let _ ← r.part key id ⟨1, by decide⟩ earlier
  let p1 ← r.part key id ⟨1, by decide⟩ first
  let listed ← r.listParts key id
  let stale ← r.complete key id [(1, tag (digest earlier)), (2, etagOf p2)]
  let bogus ← r.complete key id [(1, "\"" ++ String.ofList (List.replicate 32 '0') ++ "\""), (2, etagOf p2)]
  let listing := [(1, etagOf p1), (2, etagOf p2)]
  let done ← r.complete key id listing
  let again ← r.complete key id listing
  let object ← r.get key [5 * mib, 4]
  let small := "big/c.bin"
  let id3 ← r.create small
  let s1 ← r.part small id3 ⟨1, by decide⟩ "small".toUTF8
  let s2 ← r.part small id3 ⟨2, by decide⟩ "parts".toUTF8
  let tooSmall ← r.complete small id3 [(1, etagOf s1), (2, etagOf s2)]
  let aborted ← r.call (.abortUpload (k small) id3) (some (.abort (← r.upload id3)))
  let afterAbort ← r.part small id3 ⟨1, by decide⟩ "x".toUTF8
  let nothing ← r.get small []
  let lines := (← r.lines.get).toList
  return ([
    (s!"s3 multipart on moto: the server's upload of 5 MiB and 3 bytes completes in two parts: {repr phase}",
      match phase with | .done (some e) => e.endsWith "-2\"" | _ => false),
    ("s3 multipart on moto: its object is the body, whole and in order", body read == whole),
    ("s3 multipart on moto: ListParts gives parts 1 and 2, with the last ETags",
      listed.map (·.number) == [1, 2] && listed.map (·.etag) == [etagOf p1, etagOf p2]),
    (s!"s3 multipart on moto: a Complete with the first part 1's ETag, and one with an ETag no part has, refused: {said stale}, {said bogus}",
      stale == some (.refused 400 "InvalidPart") && bogus == some (.refused 400 "InvalidPart")),
    (s!"s3 multipart on moto: the Complete with the parts listed completes: {said done}; made again: {said again}",
      done matches some (.completed _)),
    ("s3 multipart on moto: its object is the second part 1, then part 2", body object == first ++ tail),
    (s!"s3 multipart on moto: parts under 5 MiB refused at Complete: {said tooSmall}; then aborted: {said aborted}; a part after: {said afterAbort}",
      tooSmall == some (.refused 400 "EntityTooSmall") && aborted == some .deleted
        && goneOrKnown afterAbort),
    ("s3 multipart on moto: the aborted upload's key holds nothing", nothing == some .missing) ]
      ++ checks lines,
    lines)

def run (host : String) (tcpPort : UInt16) : IO (List (String × Bool) × List Json) := do
  (exercise (bucket host tcpPort ((← IO.monoNanosNow) % 1000000000))).block

def oracle : Oracle where
  name := "s3-multipart"
  reference := "moto"
  envVar := "LANES_MOTO"
  live := run
  replay := checks

end Tests.Oracle.Service.S3Multipart
