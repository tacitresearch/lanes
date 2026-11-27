/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Aws.Sqs
import Tests.Oracle.Service.Basic

/-!
SQS's calls (`Aws.Sqs`), read without a service, and run against moto's SQS (`oracles/moto`),
checked against the queue model (`Lanes.Queue.outside`) and recorded in
`oracles/moto/sqs.jsonl`. A standard queue, whose messages go to a dead-letter queue after three
receives: two sent and received with a visibility timeout of a second, one deleted with its
receipt, the other received again once its timeout passed and then deleted with its first, stale
receipt; a third received three times and then found in the dead-letter queue. A FIFO queue: three messages in two groups and a resend of the
first, which its deduplication drops; the second of a group not given while the first is out,
and given once it is deleted.

The record is in the model's terms: messages, receipts and groups are numbered in the order
the run met them, and the calls that are not the model's (a receive, the answers to a send or a
delete) are lines the model reads as outputs that change nothing.
-/

namespace Checks.SqsMoto

open Lanes Lanes.Http Aws Aws.Sqs Std Std.Async Tests.Oracle.Service

abbrev Msg := Queue.Message String

inductive Out where
  | send (queue : Nat) (m : Msg) (answer : String)
  /-- A receive of up to `count`, and how many came. -/
  | receive (queue : Nat) (count visibility_s got : Nat)
  | delete (queue : Nat) (receipt : Nat) (answer : String)
  deriving DecidableEq, Repr, Hashable

inductive In where
  | received (queue : Nat) (receipt : Nat) (m : Msg)
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

def port (q : Nat) : Queue.Port sig String where
  sent | .send q' m _ => if q' == q then some m else none | _ => none
  deleted | .delete q' r _ => if q' == q then some r else none | _ => none
  received | .received q' r m => if q' == q then some (r, m) else none

def Out.queue : Out → Nat
  | .send q .. | .receive q .. | .delete q .. => q

def queueOf : Event sig → Option Nat
  | .output o => some o.queue
  | .input (.received q ..) => some q
  | _ => none

/-- The standard queue, the FIFO queue, and the standard queue's dead-letter queue. -/
def standard : Nat := 0
def fifo : Nat := 1
def deadLetters : Nat := 2

def maxReceives : Nat := 3

/-- The run's events on queue `q`, which its model reads alone. -/
def on (q : Nat) (run : List (Event sig)) : List (Event sig) := run.filter (queueOf · == some q)

/-- A receive of message 1, which the run deletes with its latest receipt, at the end. -/
def redelivered (run : List (Event sig)) : List (Event sig) :=
  run ++ [.input (.received standard 999999 { id := 1, body := "one" })]

def models (run : List (Event sig)) : List (String × Bool) :=
  let standardQueue := Queue.outside (port standard) { maxReceives } []
  [ ("the standard queue's events are a run the queue model allows",
      standardQueue.allows (on standard run)),
    ("and not with the message deleted with its latest receipt received again",
      !standardQueue.allows (on standard (redelivered run))),
    ("the FIFO queue's events are a run the FIFO queue model allows",
      (Queue.outside (port fifo) { maxReceives := 10, fifo := true } []).allows (on fifo run)) ]

/-! ## The run, as JSON -/

def msgFields (m : Msg) : List (String × Json) :=
  [("id", m.id), ("group", m.group), ("body", m.body)]

def eventJson : Event sig → Option Json
  | .output (.send q m a) => some (Json.mkObj [("queue", q), ("send", m.id), ("group", m.group),
      ("body", m.body), ("answer", a)])
  | .output (.receive q n v got) =>
    some (Json.mkObj [("queue", q), ("receive", n), ("visibility_s", v), ("got", got)])
  | .output (.delete q r a) => some (Json.mkObj [("queue", q), ("delete", r), ("answer", a)])
  | .input (.received q r m) => some (Json.mkObj (([("queue", q), ("received", r)] : List (String × Json)) ++ msgFields m))
  | _ => none

def readMsg (j : Json) (idField : String) : Option Msg := do
  return { id := ← nat? j idField, group := ← nat? j "group", body := ← str? j "body" }

def readEvent (j : Json) : Option (Event sig) := do
  let q ← nat? j "queue"
  match nat? j "send", nat? j "receive", nat? j "delete", nat? j "received" with
  | some _, _, _, _ => return .output (.send q (← readMsg j "send") (← str? j "answer"))
  | _, some n, _, _ => return .output (.receive q n (← nat? j "visibility_s") (← nat? j "got"))
  | _, _, some r, _ => return .output (.delete q r (← str? j "answer"))
  | _, _, _, some r => return .input (.received q r (← readMsg j "id"))
  | _, _, _, _ => none

/-! ## The calls and answers, without a service -/

def creds : SigV4.Credentials :=
  { accessKeyId := "AKIAIOSFODNN7EXAMPLE", secretAccessKey := ⟨"wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY"⟩ }

def response (status : Nat) (body : String) : Response := { status, body := body.toUTF8 }

def unitTests : List (String × Bool) :=
  let op := Op.send "https://sqs.eu-west-1.amazonaws.com/1/q.fifo" "hi" (some "g") (some "d")
  let c := call (.aws "eu-west-1") creds (Civil.DateTime.ofUnix 1764244800) op
  let md5 := Bytes.hex (Md5.hash "hi".toUTF8)
  let message (sum : String) := "{\"Messages\":[{\"MessageId\":\"m\",\"ReceiptHandle\":\"r\",\"MD5OfBody\":\""
    ++ sum ++ "\",\"Body\":\"hi\",\"Attributes\":{\"MessageGroupId\":\"g\"}}]}"
  let receive := Op.receive "q" ⟨1, by decide⟩ ⟨30, by decide⟩
  [ ("sqs request: a POST of JSON 1.0 to the region's endpoint, its action named, signed for sqs",
      c.host == "sqs.eu-west-1.amazonaws.com" && c.request.method == .post && c.request.target == "/"
        && c.request.headers.lookup "x-amz-target" == some "AmazonSQS.SendMessage"
        && c.request.headers.lookup "content-type" == some "application/x-amz-json-1.0"
        && c.request.headers.any fun (n, v) => n == "authorization"
          && (v.splitOn "/eu-west-1/sqs/aws4_request").length == 2),
    ("sqs request: a FIFO send carries its group and its deduplication id",
      c.request.body == ("{\"QueueUrl\":\"https://sqs.eu-west-1.amazonaws.com/1/q.fifo\",\"MessageBody\":\"hi\","
        ++ "\"MessageGroupId\":\"g\",\"MessageDeduplicationId\":\"d\"}").toUTF8),
    ("sqs answer: a message with its receipt and group, none, and one whose MD5 is not its body's",
      interpret receive (response 200 (message md5))
          == .received [{ messageId := "m", receipt := "r", body := "hi", group := some "g" }]
        && interpret receive (response 200 "{}") == .received []
        && interpret receive (response 200 (message "00")) == .unreadable),
    ("sqs answer: an error by its type, without the namespace",
      interpret (.delete "q" "r") (response 400 "{\"__type\":\"com.amazonaws.sqs#ReceiptHandleIsInvalid\"}")
        == .refused 400 "ReceiptHandleIsInvalid") ]

/-! ## Against moto -/

def exchange (e : Endpoint) (op : Op) : Async (Option Answer) := do
  let r ← try Client.exchange (call e creds (← S3.now) op) { timeout_ms := 5000 } catch _ => pure none
  return r.map (interpret op)

def answerText : Option Answer → String
  | some (.sent _) => "sent"
  | some .deleted => "deleted"
  | some (.refused _ code) => "refused " ++ code
  | some _ => "unreadable"
  | none => "none"

/-- The number of `s` among those met so far, a new one for a new one. -/
def intern (table : IO.Ref (List String)) (s : String) : IO Nat := do
  let t ← table.get
  match t.idxOf? s with
  | some i => return i
  | none => table.set (t ++ [s]); return t.length

/-- What a run keeps: where SQS is, the queues' URLs, the events, and the numbers given to
receipts, groups and SQS's message ids. -/
structure Run where
  endpoint : Endpoint
  urls : IO.Ref (Array String)
  events : IO.Ref (Array (Event sig))
  receipts : IO.Ref (List String)
  groups : IO.Ref (List String)
  /-- SQS's id of each message sent, with the model's id it was sent as. -/
  ids : IO.Ref (List (String × Nat))

def Run.url (r : Run) (q : Nat) : IO String := return (← r.urls.get).getD q ""

def Run.create (r : Run) (name : String) (attributes : List (String × String) := []) :
    Async (Option String) := do
  match ← exchange r.endpoint (.createQueue name attributes) with
  | some (.created url) => r.urls.modify (·.push url); return some url
  | _ => return none

def Run.send (r : Run) (q id : Nat) (body : String) (group : Option String := none)
    (dedup : Option String := none) : Async Unit := do
  let a ← exchange r.endpoint (.send (← r.url q) body group dedup)
  if let some (.sent sqsId) := a then r.ids.modify (· ++ [(sqsId, id)])
  let g ← match group with | some g => intern r.groups g | none => pure 0
  r.events.modify (·.push (.output (.send q { id, group := g, body } (answerText a))))

/-- A receive of up to `count` with a visibility timeout: the receipts given, in order, with the
model's ids of their messages. A message SQS did not say it sent gets an id no send has. -/
def Run.receive (r : Run) (q : Nat) (count : Count := ⟨10, by decide⟩)
    (visibility_s : Visibility_s := ⟨1, by decide⟩) : Async (List (Nat × Nat)) := do
  let a ← exchange r.endpoint (.receive (← r.url q) count visibility_s)
  let got := match a with | some (.received ms) => ms | _ => []
  r.events.modify (·.push (.output (.receive q count.val visibility_s.val got.length)))
  let mut out := []
  for m in got do
    let receipt ← intern r.receipts m.receipt
    let id := ((← r.ids.get).lookup m.messageId).getD (1000 + receipt)
    let group ← match m.group with | some g => intern r.groups g | none => pure 0
    r.events.modify (·.push (.input (.received q receipt { id, group, body := m.body })))
    out := out ++ [(receipt, id)]
  return out

def Run.delete (r : Run) (q receipt : Nat) : Async String := do
  let handle := (← r.receipts.get).getD receipt ""
  let a := answerText (← exchange r.endpoint (.delete (← r.url q) handle))
  r.events.modify (·.push (.output (.delete q receipt a)))
  return a

/-- The receipt of message `id` in what a receive gave, or one no message has. -/
def receiptOf (got : List (Nat × Nat)) (id : Nat) : Nat :=
  ((got.find? (·.2 == id)).map (·.1)).getD 1000000

/-- The ARN moto gives a queue whose URL is `…/account/name`. -/
def arn (region url : String) : String :=
  match (url.splitOn "/").reverse with
  | name :: account :: _ => s!"arn:aws:sqs:{region}:{account}:{name}"
  | _ => ""

def ids (got : List (Nat × Nat)) : List Nat := got.map (·.2)

/-- A delete with a stale receipt: SQS documents that it succeeds and may leave the message, to
be received again. A known difference: moto 5.2.6 deletes a message with any receipt it was ever
given. The model allows both, as it never requires a receive. -/
def staleKind (afterStale : List (Nat × Nat)) : String :=
  if afterStale.isEmpty then "deleted, known: moto deletes with any receipt" else "left, as SQS documents"

/-- The standard queue: a delete with the latest receipt, a timeout passing, a stale receipt,
and the dead-letter queue. -/
def standardRun (r : Run) : Async (List (String × Bool)) := do
  r.send standard 0 "zero"
  r.send standard 1 "one"
  let first ← r.receive standard
  let fresh ← r.delete standard (receiptOf first 1)
  let hidden ← r.receive standard
  Async.sleep 1500
  let again ← r.receive standard
  let stale ← r.delete standard (receiptOf first 0)
  Async.sleep 1500
  let afterStale ← r.receive standard
  r.send standard 2 "two"
  let mut cycles := []
  for _ in [0:maxReceives + 1] do
    cycles := cycles ++ [(← r.receive standard (visibility_s := ⟨0, by decide⟩)).length]
  let dead ← r.receive deadLetters
  return [
    (s!"sqs on moto: two sent, received, one deleted with its receipt: {ids first}, {fresh}",
      ids first == [0, 1] && fresh == "deleted"),
    (s!"sqs on moto: the other hidden until its timeout passed, then received again: {ids hidden}, {ids again}",
      hidden.isEmpty && ids again == [0]),
    (s!"sqs on moto: deleted with its first, stale receipt: {stale}; then received: {ids afterStale}, {staleKind afterStale}",
      stale == "deleted" && (afterStale.isEmpty || ids afterStale == [0])),
    (s!"sqs on moto: received {maxReceives} times, then in the dead-letter queue: {cycles}, {dead.length}",
      cycles == [1, 1, 1, 0] && dead.length == 1) ]

/-- The FIFO queue: two groups, a group held while its first is out, a resend dropped. -/
def fifoRun (r : Run) : Async (List (String × Bool)) := do
  r.send fifo 0 "first" (some "g0") (some "f0")
  r.send fifo 1 "second" (some "g0") (some "f1")
  r.send fifo 2 "other" (some "g1") (some "f2")
  r.send fifo 0 "first" (some "g0") (some "f0")
  let head ← r.receive fifo ⟨1, by decide⟩
  let blocked ← r.receive fifo
  let d0 ← r.delete fifo (receiptOf head 0)
  let next ← r.receive fifo
  let d1 ← r.delete fifo (receiptOf next 1)
  let d2 ← r.delete fifo (receiptOf blocked 2)
  let empty ← r.receive fifo
  return [
    (s!"sqs on moto, FIFO: the first of a group, then only the other group's: {ids head}, {ids blocked}",
      ids head == [0] && ids blocked == [2]),
    (s!"sqs on moto, FIFO: the second once the first is deleted, and the resend dropped: {ids next}, {ids empty}",
      ids next == [1] && empty.isEmpty && [d0, d1, d2].all (· == "deleted")) ]

def exercise (e : Endpoint) (run : Nat) : Async (List (String × Bool) × List Json) := do
  let r : Run := { endpoint := e, urls := ← IO.mkRef #[], events := ← IO.mkRef #[],
                   receipts := ← IO.mkRef [], groups := ← IO.mkRef [], ids := ← IO.mkRef [] }
  -- The dead-letter queue is made first, for the standard queue to name, and numbered last.
  let dlqUrl := match ← exchange e (.createQueue s!"lanes-oracle-{run}-dead") with
    | some (.created url) => url
    | _ => ""
  let redrive := Json.compress (Json.mkObj [("deadLetterTargetArn", arn e.region dlqUrl),
    ("maxReceiveCount", toString maxReceives)])
  let made ← r.create s!"lanes-oracle-{run}" [("RedrivePolicy", redrive)]
  let madeFifo ← r.create s!"lanes-oracle-{run}.fifo" [("FifoQueue", "true")]
  r.urls.modify (·.push dlqUrl)
  unless made.isSome && madeFifo.isSome && dlqUrl != "" do
    return ([("sqs on moto: the queues are made", false)], [])
  let checks := (← standardRun r) ++ (← fifoRun r)
  let events := (← r.events.get).toList
  let seen := events.filterMap eventJson
  let run := seen.filterMap readEvent
  return (checks ++ ("sqs on moto: every event reads back as itself", run == events)
      :: (models run).map fun (name, ok) => (s!"sqs on moto: {name}", ok),
    seen)

def runLive (host : String) (tcpPort : UInt16) : IO (List (String × Bool) × List Json) := do
  (exercise { region := "us-east-1", host, port := tcpPort, scheme := .http }
    ((← IO.monoNanosNow) % 1000000000)).block

def replay (lines : List Json) : List (String × Bool) :=
  let events := lines.filterMap readEvent
  ("sqs on moto, recorded: every line reads", events.length == lines.length && !lines.isEmpty)
    :: (models events).map fun (name, ok) => (s!"sqs on moto, recorded: {name}", ok)

def oracle : Oracle where
  name := "sqs"
  reference := "moto"
  envVar := "LANES_MOTO"
  live := runLive
  replay := replay

end Checks.SqsMoto
