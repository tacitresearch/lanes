/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Aws.Ses

/-!
# Amazon SQS's calls

The calls of a queue as `Lanes.Queue` models it: `SendMessage`, `ReceiveMessage` with a
visibility timeout, `DeleteMessage` with a receipt, and `CreateQueue` to make one. Each is a
`POST /` in AWS's JSON protocol 1.0, its action in `X-Amz-Target`, signed with Signature
Version 4 for the service `sqs`; the answer is read as the queue's terms. A message received is
kept only when its body's MD5 is the one SQS sent with it, as botocore checks.

Only the calls and their answers, as data: no handler. The bounds are SQS's: 1 to 10 messages a
receive, a visibility timeout of at most 12 hours, a wait of at most 20 seconds.
-/

namespace Aws.Sqs

open Lanes Lanes.Http

structure Endpoint where
  region : String
  host : String
  port : UInt16 := 443
  scheme : Client.Scheme := .https

/-- AWS's endpoint of SQS in a region. -/
def Endpoint.aws (region : String) : Endpoint := { region, host := "sqs." ++ region ++ ".amazonaws.com" }

abbrev Count := {n : Nat // 1 ≤ n ∧ n ≤ 10}

abbrev Visibility_s := {n : Nat // n ≤ 43200}

abbrev Wait_s := {n : Nat // n ≤ 20}

inductive Op where
  /-- A queue named `name`, FIFO when the name ends in `.fifo`, with SQS's attributes. -/
  | createQueue (name : String) (attributes : List (String × String) := [])
  /-- `group` and `dedup` are a FIFO queue's `MessageGroupId` and `MessageDeduplicationId`. -/
  | send (queue : String) (body : String) (group : Option String := none)
    (dedup : Option String := none)
  | receive (queue : String) (count : Count := ⟨1, by decide⟩) (visibility_s : Visibility_s)
    (wait_s : Wait_s := ⟨0, by decide⟩)
  | delete (queue : String) (receipt : String)
  deriving DecidableEq, Repr

def Op.action : Op → String
  | .createQueue .. => "CreateQueue"
  | .send .. => "SendMessage"
  | .receive .. => "ReceiveMessage"
  | .delete .. => "DeleteMessage"

def optional (name : String) : Option String → List (String × Json)
  | some v => [(name, .str v)]
  | none => []

def Op.json : Op → Json
  | .createQueue name attributes =>
    .obj #[("QueueName", .str name),
      ("Attributes", .obj (attributes.map fun (n, v) => (n, Json.str v)).toArray)]
  | .send queue body group dedup =>
    .obj (#[("QueueUrl", .str queue), ("MessageBody", .str body)]
      ++ (optional "MessageGroupId" group ++ optional "MessageDeduplicationId" dedup).toArray)
  | .receive queue count visibility wait =>
    .obj #[("QueueUrl", .str queue), ("MaxNumberOfMessages", count.val),
      ("VisibilityTimeout", visibility.val), ("WaitTimeSeconds", wait.val),
      ("MessageSystemAttributeNames", .arr #[.str "MessageGroupId"])]
  | .delete queue receipt => .obj #[("QueueUrl", .str queue), ("ReceiptHandle", .str receipt)]

/-- `op` at `e`, signed with `creds` at `t`. -/
def call (e : Endpoint) (creds : SigV4.Credentials) (t : Civil.DateTime) (op : Op) : Client.Call :=
  let body := (Json.compress op.json).toUTF8
  let request : Request :=
    { method := .post, path := [],
      headers := [("content-type", "application/x-amz-json-1.0"),
        ("x-amz-target", "AmazonSQS." ++ op.action)], body }
  let unsigned : Client.Call := { host := e.host, port := e.port, scheme := e.scheme, request }
  let signed := SigV4.sign creds t ⟨e.region, "sqs"⟩ unsigned.authority "POST"
    (SigV4.payloadHash body) request
  { unsigned with request := signed }

/-! ## The answer -/

structure Received where
  messageId : String
  receipt : String
  body : String
  group : Option String := none
  deriving DecidableEq, Repr, Hashable

inductive Answer where
  | created (queueUrl : String)
  | sent (messageId : String)
  /-- No message is an empty list: none was visible. -/
  | received (messages : List Received)
  | deleted
  /-- An error SQS gave, with its code (`ReceiptHandleIsInvalid`, `QueueDoesNotExist`). -/
  | refused (status : Nat) (code : String)
  /-- A success this reader does not understand, or a body whose MD5 is not the one sent. -/
  | unreadable
  deriving DecidableEq, Repr, Hashable

def field? (j : Json) (name : String) : Option String := (j.getObjValAs? String name).toOption

def received? (j : Json) : Option Received := do
  let body ← field? j "Body"
  unless field? j "MD5OfBody" == some (Bytes.hex (Md5.hash body.toUTF8)) do none
  let group := (j.getObjVal? "Attributes").toOption.bind (field? · "MessageGroupId")
  return { messageId := ← field? j "MessageId", receipt := ← field? j "ReceiptHandle", body, group }

def messages? (j : Json) : Option (List Received) :=
  match j.getObjVal? "Messages" with
  | .ok (.arr ms) => ms.toList.mapM received?
  | .ok _ => none
  | .error _ => some []

def interpret (op : Op) (r : Response) : Answer :=
  if r.status != 200 then .refused r.status (Ses.errorCode r)
  else
    let j := ((String.fromUTF8? r.body).bind fun s => (Json.parse s).toOption).getD (.obj #[])
    let read (o : Option Answer) := o.getD .unreadable
    match op with
    | .createQueue .. => read ((field? j "QueueUrl").map .created)
    | .send .. => read ((field? j "MessageId").map .sent)
    | .receive .. => read ((messages? j).map .received)
    | .delete .. => .deleted

end Aws.Sqs
