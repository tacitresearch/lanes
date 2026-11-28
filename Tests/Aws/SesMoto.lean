/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Aws.Ses
import Tests.Oracle.Service.Basic

/-!
The SES adapter against moto's SES (`oracles/moto`): a system sends through `Ses.handler`, over
plain HTTP, a message from a sender SES has not verified, then, once the sender is verified, to
one recipient, to three, and one whose deadline is too short to be answered; the run is checked
against the email model (`Ses.outside`) and recorded, its sends and their answers, in
`oracles/moto/ses.jsonl`.
-/

namespace Checks.SesMoto

open Lanes Lanes.Http Aws Aws.Ses Std Std.Async Tests.Oracle.Service

/-! ## A mailer whose asks carry their deadline -/

inductive In where
  | ask (c : Rpc.Call Message)
  | reply (id : Nat) (answer : Rpc.Reply Answer)
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Checks.Ses.Out

abbrev mailer : System sig where
  State _ := Unit
  actor _ :=
    { init := ()
      step := fun s msg =>
        match msg with
        | .ask c => (s, [.emit (.send c)])
        | .reply id answer => (s, [.emit (.done id answer)]) }
  accept x := ⟨(), x⟩

instance : sig.Inspect := {}
instance : mailer.Inspect := {}

def port : Ses.Port sig where
  called | .send c => some c | .done .. => none
  reply id answer := .reply id answer
  replied | .reply id answer => some (id, answer) | .ask .. => none

def model := Ses.outside port

/-! ## The run, as JSON -/

def bodyJson : Body → Json
  | .text t => Json.mkObj [("text", t)]
  | .html h => Json.mkObj [("html", h)]
  | .both t h => Json.mkObj [("text", t), ("html", h)]

def readBody (j : Json) : Option Body :=
  match str? j "text", str? j "html" with
  | some t, none => some (.text t)
  | none, some h => some (.html h)
  | some t, some h => some (.both t h)
  | none, none => none

def messageJson (m : Message) : Json :=
  Json.mkObj [("source", m.source.val), ("to", .arr (m.to.val.map fun a => Json.str a.val).toArray),
    ("subject", m.subject.val), ("body", bodyJson m.body)]

def readMessage (j : Json) : Option Message := do
  let to ← (j.getObjVal? "to" >>= Json.getArr? >>= (·.toList.mapM Json.getStr?)).toOption
  let body ← readBody (← (j.getObjVal? "body").toOption)
  (Message.of? (← str? j "source") to (← str? j "subject") body).toOption

def answerJson : Rpc.Reply Answer → Json
  | .unknown => Json.mkObj [("answer", "unknown")]
  | .answer (.sent id) => Json.mkObj [("answer", "sent"), ("id", id)]
  | .answer (.rejected status code) => Json.mkObj [("answer", "rejected"), ("status", status), ("code", code)]
  | .answer (.uncertain status code) => Json.mkObj [("answer", "uncertain"), ("status", status), ("code", code)]

def readAnswer (j : Json) : Option (Rpc.Reply Answer) := do
  match ← str? j "answer" with
  | "unknown" => return .unknown
  | "sent" => return .answer (.sent (← str? j "id"))
  | "rejected" => return .answer (.rejected (← nat? j "status") ((str? j "code").getD ""))
  | "uncertain" => return .answer (.uncertain (← nat? j "status") ((str? j "code").getD ""))
  | _ => none

def eventJson : Event sig → Option Json
  | .output (.send c) => some (Json.mkObj [("call", c.id), ("deadline_ms", c.deadline_ms),
      ("request", messageJson c.request)])
  | .input (.reply id r) => some (Json.mkObj [("reply", id), ("answer", answerJson r)])
  | _ => none

def readEvent (j : Json) : Option (Event sig) :=
  match nat? j "call", nat? j "reply" with
  | some id, _ => do
    let m ← readMessage (← (j.getObjVal? "request").toOption)
    return .output (.send ⟨id, ← nat? j "deadline_ms", m⟩)
  | none, some id => do return .input (.reply id (← readAnswer (← (j.getObjVal? "answer").toOption)))
  | none, none => none

/-! ## Against moto -/

def creds : SigV4.Credentials := Tests.S3.creds

def sender : String := "noreply@videos.example"

/-- `CreateEmailIdentity`, which the adapter does not have: SES sends only from an identity it
has verified, and moto takes this as verifying it. -/
def verify (e : Endpoint) : Async (Option Lanes.Http.Response) := do
  let body := (Json.compress (Json.mkObj [("EmailIdentity", sender)])).toUTF8
  let request : Request :=
    { method := .post, path := ["v2", "email", "identities"],
      headers := [("content-type", "application/json")], body }
  let call : Client.Call := { host := e.host, port := e.port, request }
  let signed := SigV4.sign creds (← S3.now) ⟨e.region, "ses"⟩ call.authority "POST"
    (SigV4.payloadHash body) request
  Client.exchange { call with request := signed } { timeout_ms := 5000 }

def msg (to : List String) (deadline : Nat := 3000) (id : Nat) : Option (Rpc.Call Message) :=
  (Message.of? sender to "A comment on your video" (.both "Hi" "<p>Hi</p>")).toOption.map
    (⟨id, deadline, ·⟩)

def exercise (e : Endpoint) : Async (List (String × Bool) × List Json) := do
  let answered ← IO.mkRef 0
  let rt ← Runtime.startWith mailer { record := true } fun rt out => do
    match out with
    | .send _ => Ses.handler port e creds {} rt out
    | .done .. => answered.modify (· + 1)
  let send (c : Option (Rpc.Call Message)) : Async Unit := do
    if let some c := c then
      rt.input (.ask c)
      for _ in [0:500] do
        if (← answered.get) ≥ c.id + 1 then break
        Async.sleep 10
  send (msg ["ann@b.co"] 3000 0)
  let verified ← verify e
  send (msg ["ann@b.co"] 3000 1)
  send (msg ["ann@b.co", "bo@c.co", "cy@d.co"] 3000 2)
  send (msg ["slow@b.co"] 1 3)
  Async.sleep 300
  send (msg ["dee@b.co"] 3000 4)
  rt.idle
  let events : List (Event sig) := (← rt.trace).toList
  rt.stop
  let seen := events.filterMap eventJson
  let run := seen.filterMap readEvent
  let answers := run.filterMap fun (e : Event sig) => match e with
    | .input (.reply _ a) => some (Checks.Ses.kind a)
    | _ => none
  let status := verified.map fun (r : Lanes.Http.Response) => r.status
  return ([
    (s!"ses on moto: the sender is verified, {status}", status == some 200),
    (s!"ses on moto: rejected before the sender is verified, then sent: {answers}",
      answers.take 3 == ["rejected", "sent", "sent"] && answers.length == 5
        && answers.getLast? == some "sent" && run.length == seen.length),
    ("ses on moto: the run is one the email model allows", model.allows run) ],
    seen)

def run (host : String) (tcpPort : UInt16) : IO (List (String × Bool) × List Json) :=
  (exercise { region := "us-east-1", host, port := tcpPort, scheme := .http }).block

def replay (lines : List Json) : List (String × Bool) :=
  let events := lines.filterMap readEvent
  [ ("ses on moto, recorded: every line reads", events.length == lines.length && !lines.isEmpty),
    ("ses on moto, recorded: the run is one the email model allows", model.allows events) ]

def oracle : Oracle where
  name := "ses"
  reference := "moto"
  envVar := "LANES_MOTO"
  live := run
  replay := replay

end Checks.SesMoto
