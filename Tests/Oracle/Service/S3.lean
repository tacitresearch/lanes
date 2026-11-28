/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Service.Basic
import Tests.S3

/-!
The S3 client against moto's S3 (`oracles/moto`): a system calls the store through `S3.handler`,
path-style over plain HTTP, in a bucket made for the run, with gets, puts, deletes, two puts in flight at once and a put whose
deadline is too short to be answered; the run is checked against the object store's model
(`ObjectStore.server`) and recorded, its calls and their answers, in `oracles/moto/s3.jsonl`.
-/

namespace Tests.Oracle.Service.S3

open Lanes Lanes.S3 Lanes.Http Std Std.Async Tests.S3

/-! ## A caller whose asks carry their deadline -/

inductive In where
  | ask (c : Rpc.Call Op)
  | reply (id : Nat) (answer : Rpc.Reply Answer)
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Tests.S3.Out

abbrev caller : System sig where
  State _ := Unit
  actor _ :=
    { init := ()
      step := fun s msg =>
        match msg with
        | .ask c => (s, [.emit (.call c)])
        | .reply id answer => (s, [.emit (.done id answer)])
      recover := fun s => (s, []) }
  accept x := ⟨(), x⟩

instance : sig.Inspect := {}
instance : caller.Inspect := {}

def port : S3.Port sig where
  called | .call c => some c | .done .. => none
  reply id answer := .reply id answer

/-- What the store's model sees: as `Tests.S3.modelPort` sees it. -/
def modelPort : Rpc.Port sig (ObjectStore.Request String ByteArray) (ObjectStore.Answer ByteArray) Empty where
  called
    | .call c => c.request.modelled.map fun r => ⟨c.id, c.deadline_ms, r⟩
    | .done .. => none
  replied
    | .reply id .unknown => some (id, .unknown)
    | .reply id (.answer a) => a.modelled.map fun a => (id, .answer a)
    | .ask .. => none

def model := Rpc.outside modelPort ObjectStore.server

/-! ## The run, as JSON -/

def opJson : Op → Option Json
  | .put key body _ => some (Json.mkObj [("op", "put"), ("key", key.val), ("body", Bytes.hex body)])
  | .get key none => some (Json.mkObj [("op", "get"), ("key", key.val)])
  | .delete key => some (Json.mkObj [("op", "delete"), ("key", key.val)])
  | _ => none

def readOp (j : Json) : Option Op := do
  let key ← Key.of? (← str? j "key")
  match ← str? j "op" with
  | "put" => return .put key (← bytes? j "body")
  | "get" => return .get key
  | "delete" => return .delete key
  | _ => none

def opt (o : Option String) : Json := (o.map Json.str).getD .null

def readOpt (j : Json) (name : String) : Option String := str? j name

def answerJson : Rpc.Reply Answer → Json
  | .unknown => Json.mkObj [("answer", "unknown")]
  | .answer (.stored etag) => Json.mkObj [("answer", "stored"), ("etag", opt etag)]
  | .answer (.object info body) => Json.mkObj [("answer", "object"), ("size", info.size),
      ("etag", opt info.etag), ("type", opt info.contentType), ("modified", opt info.lastModified),
      ("body", Bytes.hex body)]
  | .answer .missing => Json.mkObj [("answer", "missing")]
  | .answer .deleted => Json.mkObj [("answer", "deleted")]
  | .answer (.refused status code) => Json.mkObj [("answer", "refused"), ("status", status), ("code", code)]
  | .answer _ => Json.mkObj [("answer", "unreadable")]

def readAnswer (j : Json) : Option (Rpc.Reply Answer) := do
  match ← str? j "answer" with
  | "unknown" => return .unknown
  | "stored" => return .answer (.stored (readOpt j "etag"))
  | "object" =>
    let size ← nat? j "size"
    let body ← bytes? j "body"
    let info : Info := { size, etag := readOpt j "etag", contentType := readOpt j "type",
                         lastModified := readOpt j "modified" }
    return .answer (.object info body)
  | "missing" => return .answer .missing
  | "deleted" => return .answer .deleted
  | "refused" => return .answer (.refused (← nat? j "status") ((readOpt j "code").getD ""))
  | "unreadable" => return .answer .unreadable
  | _ => none

/-- The events the store's model sees, as lines: a call made, or a call answered. -/
def eventJson : Event sig → Option Json
  | .output (.call c) => (opJson c.request).map fun op =>
      Json.mkObj [("call", c.id), ("deadline_ms", c.deadline_ms), ("request", op)]
  | .input (.reply id r) => some (Json.mkObj [("reply", id), ("answer", answerJson r)])
  | _ => none

def readEvent (j : Json) : Option (Event sig) :=
  match nat? j "call", nat? j "reply" with
  | some id, _ => do
    let op ← readOp (← (j.getObjVal? "request").toOption)
    return .output (.call ⟨id, ← nat? j "deadline_ms", op⟩)
  | none, some id => do return .input (.reply id (← readAnswer (← (j.getObjVal? "answer").toOption)))
  | none, none => none

/-! ## Against moto -/

def creds : SigV4.Credentials :=
  { accessKeyId := "AKIAIOSFODNN7EXAMPLE", secretAccessKey := ⟨"wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY"⟩ }

/-- A bucket of its own for each run, since the model starts from an empty store. -/
def bucket (host : String) (port : UInt16) (run : Nat) : Bucket :=
  { name := s!"lanes-oracle-{run}", region := "us-east-1",
    endpoint := { host, port, scheme := .http, addressing := .path } }

/-- CreateBucket, which the client does not have. -/
def createBucket (b : Bucket) : Async (Option Lanes.Http.Response) := do
  let hash := SigV4.payloadHash .empty
  let request : Request :=
    { method := .put, path := [b.name], headers := [("x-amz-content-sha256", hash)] }
  let call : Client.Call := { host := b.endpoint.host, port := b.endpoint.port, request }
  let signed := SigV4.sign creds (← now) b.scope call.authority "PUT" hash request
  Client.exchange { call with request := signed } { timeout_ms := 5000 }

inductive Ask where
  | one (op : Op) (deadline_ms : Nat := 3000)
  /-- Several calls in flight at once. -/
  | together (ops : List Op)

def k (s : String) : Key := (Key.of? s).getD ⟨"k", by decide⟩

def script : List Ask :=
  let key := k "videos/a b/ሴ.mp4"
  let other := k "thumbs/missing.png"
  [ .one (.get key), .one (.put key "one".toUTF8), .one (.get key),
    .together [.put key "two".toUTF8, .put key "three".toUTF8], .one (.get key),
    .one (.put key "four".toUTF8) 1, .one (.get key), .one (.get other), .one (.delete key),
    .one (.get key), .one (.delete other), .one (.put other ByteArray.empty), .one (.get other) ]

def exercise (b : Bucket) : Async (List (String × Bool) × List Json) := do
  let made ← createBucket b
  let status := made.map fun (r : Lanes.Http.Response) => r.status
  unless status == some 200 do
    return ([(s!"s3 on moto: the bucket is made, {status}", false)], [])
  let answered ← IO.mkRef 0
  let rt ← Runtime.startWith caller { record := true } fun rt out => do
    match out with
    | .call _ => S3.handler port b creds {} rt out
    | .done .. => answered.modify (· + 1)
  let mut id := 0
  for ask in script do
    let ops := match ask with
      | .one op deadline => [(op, deadline)]
      | .together ops => ops.map (·, 3000)
    for (op, deadline) in ops do
      rt.input (.ask ⟨id, deadline, op⟩)
      id := id + 1
    let want := id
    for _ in [0:500] do
      if (← answered.get) ≥ want then break
      Async.sleep 10
  -- The put that timed out may still land: wait, then read once more.
  Async.sleep 300
  rt.input (.ask ⟨id, 3000, .get (k "videos/a b/ሴ.mp4")⟩)
  for _ in [0:300] do
    if (← answered.get) ≥ id + 1 then break
    Async.sleep 10
  rt.idle
  let events : List (Event sig) := (← rt.trace).toList
  rt.stop
  let seen := events.filterMap eventJson
  let run := seen.filterMap readEvent
  let made := run.countP fun (e : Event sig) => match e with | .output _ => true | _ => false
  let replies := run.countP fun (e : Event sig) => match e with | .input _ => true | _ => false
  return ([
    (s!"s3 on moto: {made} calls through S3.handler, {replies} answered or unknown",
      made == id + 1 && replies == made && run.length == seen.length),
    ("s3 on moto: the run is one the object store's model allows", model.allows run) ],
    seen)

def run (host : String) (tcpPort : UInt16) : IO (List (String × Bool) × List Json) := do
  (exercise (bucket host tcpPort ((← IO.monoNanosNow) % 1000000000))).block

/-- The record, checked again: each line read, and the run one the model allows. -/
def replay (lines : List Json) : List (String × Bool) :=
  let events := lines.filterMap readEvent
  [ ("s3 on moto, recorded: every line reads", events.length == lines.length && !lines.isEmpty),
    ("s3 on moto, recorded: the run is one the object store's model allows", model.allows events) ]

def oracle : Oracle where
  name := "s3"
  reference := "moto"
  envVar := "LANES_MOTO"
  live := run
  replay := replay

end Tests.Oracle.Service.S3
