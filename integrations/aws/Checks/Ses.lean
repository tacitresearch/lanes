/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Aws
import Checks.Fake

/-!
The SES adapter: addresses and messages refused before anything is sent, the document and the
call, what an answer means and how the email model reads it; then the adapter against a fake
SES in the test, which checks each request's signature for the service `ses` from the bytes it
received (the fake S3's check, `Tests.S3.verified`), reads the recipients from the JSON, and
answers as SES does: a `MessageId`, `MessageRejected`, a `500`, or nothing. A system sending
through `Ses.handler` records a run, which the email model allows (`Outside.allows`).
-/

namespace Checks.Ses

open Lanes Lanes.Http Aws Aws.Ses Std Std.Async

def msg? (to : List String) (body : Body := .text "Hello") : Option Message :=
  (Message.of? "noreply@videos.example" to "A comment on your video" body).toOption

def addressTests : List (String × Bool) :=
  let good := ["a@b.co", "first.last+tag@mail.example.com", "o'brien@x.example", "x_y-z@sub-1.example.org"]
  let bad := ["", "a", "a@b", "@b.co", "a@.co", "a..b@c.co", ".a@b.co", "a.@b.co", "a@b..co",
    "a@-b.co", "a@b-.co", "a b@c.co", "a@b@c.co", "Name <a@b.co>", "\"q\"@b.co", "é@b.co",
    "a@b.co\r\nBcc: x@y.co", String.ofList (List.replicate 65 'a') ++ "@b.co"]
  [ ("ses address: plain addresses are taken", good.all (Address.of? · |>.isSome)),
    ("ses address: what is not local@domain, or is too long, is refused",
      bad.all (Address.of? · |>.isNone)),
    ("ses message: no recipient, 51, an address refused, a line break in the subject",
      (msg? []).isNone
        && (msg? ((List.range 51).map fun n => s!"u{n}@b.co")).isNone
        && (msg? ((List.range 50).map fun n => s!"u{n}@b.co")).isSome
        && (msg? ["ok@b.co", "bad"]).isNone
        && (Message.of? "a@b.co" ["c@d.co"] "Hi\r\nBcc: x@y.co" (.text "t")).toOption.isNone) ]

def requestTests : List (String × Bool) :=
  match msg? ["ann@b.co", "bo@c.co"] (.both "Hi" "<p>Hi</p>") with
  | none => [("ses request: the message", false)]
  | some m =>
    let c := call (.aws "eu-west-1") Tests.S3.creds (Civil.DateTime.ofUnix 1764244800) m
    let parsed := Json.parse (json m)
    [ ("ses request: the document, as SES v2 SendEmail takes it",
        json m == "{\"FromEmailAddress\":\"noreply@videos.example\",\"Destination\":{\"ToAddresses\":"
          ++ "[\"ann@b.co\",\"bo@c.co\"]},\"Content\":{\"Simple\":{\"Subject\":{\"Data\":"
          ++ "\"A comment on your video\",\"Charset\":\"UTF-8\"},\"Body\":{\"Text\":{\"Data\":\"Hi\","
          ++ "\"Charset\":\"UTF-8\"},\"Html\":{\"Data\":\"<p>Hi</p>\",\"Charset\":\"UTF-8\"}}}}}"),
      ("ses request: it reads back with exactly the recipients",
        match parsed.toOption.map toAddresses with
        | some (.ok to) => to == ["ann@b.co", "bo@c.co"]
        | _ => false),
      ("ses request: POST to the region's endpoint over HTTPS, signed for ses",
        c.host == "email.eu-west-1.amazonaws.com" && c.port == 443 && c.scheme == .https
          && c.request.method == .post && c.request.target == "/v2/email/outbound-emails"
          && c.request.headers.any fun (n, v) => n == "authorization"
            && (v.splitOn "/eu-west-1/ses/aws4_request").length == 2) ]

def answerTests : List (String × Bool) :=
  let r (status : Nat) (body : String) (headers : List (String × String) := []) : Response :=
    { status, headers, body := body.toUTF8 }
  [ ("ses answer: a MessageId is a message accepted",
      interpret (r 200 "{\"MessageId\":\"0100018c-abc\"}") == .sent "0100018c-abc"
        && (Answer.modelled 3 (.sent "0100018c-abc")) == .answer (.made (.message "0100018c-abc") .accepted)),
    ("ses answer: a 4xx is rejected, under SES's name for it, and not sent",
      interpret (r 400 "{\"message\":\"Email address is not verified.\"}"
          [("x-amzn-errortype", "MessageRejected:http://internal.amazon.com/coral/com.amazonaws.sesv2/")])
        == .rejected 400 "MessageRejected"
        && interpret (r 429 "{\"__type\":\"com.amazonaws#TooManyRequestsException\"}")
          == .rejected 429 "TooManyRequestsException"
        && Answer.modelled 3 (.rejected 400 "MessageRejected") == .answer (.made (.unsent 3) .rejected)),
    ("ses answer: a 5xx, or a 200 without a MessageId, may have been sent: unknown",
      interpret (r 500 "") == .uncertain 500 "" && interpret (r 200 "{}") == .uncertain 200 ""
        && Answer.modelled 3 (.uncertain 500 "") == .unknown) ]

/-! ## A fake SES -/

def scope : SigV4.Scope := ⟨"us-east-1", "ses"⟩

def endpointAt (port : UInt16) : Endpoint :=
  { region := "us-east-1", host := "127.0.0.1", port, scheme := .http }

/-- SES as a fake: signatures checked for `ses`, the document read, and an answer chosen by
the first recipient: `rejected@` is `MessageRejected`, `flaky@` a `500`, `slow@` none. -/
def handle (creds : SigV4.Credentials) (seen : IO.Ref (List (List String))) (r : Tests.S3.Raw) :
    IO (Option ByteArray) := do
  let some (path, _) := Tests.S3.verified creds r scope
    | return some (Fake.json 403 "{\"message\":\"The request signature we calculated does not match\"}"
        [("x-amzn-ErrorType", "SignatureDoesNotMatch:http://internal.amazon.com/")])
  unless r.verb == "POST" && path == ["v2", "email", "outbound-emails"] do
    return some (Fake.json 404 "{}")
  let some to := (String.fromUTF8? r.body).bind fun s => ((Json.parse s).toOption.bind
      (toAddresses · |>.toOption))
    | return some (Fake.json 400 "{\"message\":\"bad\"}" [("x-amzn-ErrorType", "BadRequestException")])
  let n ← seen.modifyGet fun l => (l.length, l ++ [to])
  match to.head? with
  | some first =>
    if first.startsWith "rejected@" then
      return some (Fake.json 400 "{\"message\":\"Email address is not verified.\"}"
        [("x-amzn-ErrorType", "MessageRejected:http://internal.amazon.com/coral/com.amazonaws.sesv2/")])
    else if first.startsWith "flaky@" then return some (Fake.json 500 "{}")
    else if first.startsWith "slow@" then return none
    else return some (Fake.json 200 s!"\{\"MessageId\":\"m-{n}\"}")
  | none => return some (Fake.json 400 "{}")

def config : Client.Config := { timeout_ms := 1000 }

/-- Sends a message to `to`, or nothing if it is not one. -/
def send (e : Endpoint) (creds : SigV4.Source) (to : List String) : Async (Option Answer) :=
  match msg? to with
  | some m => exchange e creds m config
  | none => pure none

def exchanges : Async (List (String × Bool)) := do
  let seen ← IO.mkRef []
  let creds := { Tests.S3.creds with sessionToken := some ⟨"role-token"⟩ }
  let (server, port) ← Fake.serve (handle creds seen)
  let e := endpointAt port
  let sent ← send e creds ["ann@b.co", "bo@c.co"]
  let rejected ← send e creds ["rejected@b.co"]
  let flaky ← send e creds ["flaky@b.co"]
  let slow ← send e creds ["slow@b.co"]
  let forged ← send e ({ creds with secretAccessKey := ⟨"not it"⟩ } : SigV4.Credentials) ["ann@b.co"]
  let untokened ← send e Tests.S3.creds ["ann@b.co"]
  server.close
  return [
    ("ses fake: a message signed for ses, with the role's token, is sent to exactly its recipients",
      sent == some (.sent "m-0") && (← seen.get).head? == some ["ann@b.co", "bo@c.co"]),
    ("ses fake: MessageRejected is rejected, a 500 uncertain, and no answer is none",
      rejected == some (.rejected 400 "MessageRejected") && flaky == some (.uncertain 500 "")
        && slow.isNone),
    ("ses fake: another secret, and a token missing, are refused as SES refuses them",
      forged == some (.rejected 403 "SignatureDoesNotMatch")
        && untokened == some (.rejected 403 "SignatureDoesNotMatch")) ]

/-! ## A recorded run, against the email model -/

inductive In where
  | ask (id : Nat) (m : Message)
  | reply (id : Nat) (answer : Rpc.Reply Answer)
  deriving DecidableEq, Repr, Hashable

inductive Out where
  | send (c : Rpc.Call Message)
  | done (id : Nat) (answer : Rpc.Reply Answer)
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

/-- A mailer: asked, it sends with a deadline; told, it reports. -/
abbrev mailer : System sig where
  State _ := Unit
  actor _ :=
    { init := ()
      step := fun s msg =>
        match msg with
        | .ask id m => (s, [.emit (.send ⟨id, 1000, m⟩)])
        | .reply id answer => (s, [.emit (.done id answer)]) }
  accept x := ⟨(), x⟩

instance : sig.Inspect := {}
instance : mailer.Inspect := {}

def port : Port sig where
  called | .send c => some c | .done .. => none
  reply id answer := .reply id answer
  replied | .reply id answer => some (id, answer) | .ask .. => none

def world := Outside.any.both (Ses.outside port) fun x => x matches .ask ..

def kind : Rpc.Reply Answer → String
  | .answer (.sent _) => "sent"
  | .answer (.rejected ..) => "rejected"
  | .answer (.uncertain ..) => "uncertain"
  | .unknown => "unknown"

def conformance : Async (List (String × Bool)) := do
  let seen ← IO.mkRef []
  let (server, port_) ← Fake.serve (handle Tests.S3.creds seen)
  let done ← IO.mkRef 0
  let rt ← Runtime.startWith mailer { record := true } fun rt out => do
    Ses.handler port (endpointAt port_) Tests.S3.creds config rt out
    if let .done .. := out then done.modify (· + 1)
  let asks := [["ann@b.co"], ["rejected@b.co"], ["flaky@b.co"], ["slow@b.co"], ["bo@c.co", "cy@d.co"]]
  for (to, id) in asks.zipIdx do
    if let some m := msg? to then rt.input (.ask id m)
    let _ ← Fake.waitFor 3000 do return (← done.get) ≥ id + 1
  rt.idle
  let events := (← rt.trace).toList
  rt.stop
  server.close
  let answers := events.filterMap fun | .output (.done _ a) => some a | _ => none
  let replies := events.filter fun | .input (.reply ..) => true | _ => false
  let twice := events ++ replies.take 1
  return [
    ("ses handler: each send answered: sent, rejected, a 500, none by the deadline, sent",
      answers.map kind == ["sent", "rejected", "uncertain", "unknown", "sent"]),
    ("ses handler: the run with the fake is one the email model allows",
      world.allows events),
    ("ses handler: and the model refuses an answer given twice", !world.allows twice) ]

/-- `handlerOnce` given one key twice, and once more after its state is read back from its
file, sends it once; each repeat is answered `unknown`. -/
def once : Async (List (String × Bool)) := do
  let seen ← IO.mkRef []
  let (server, port_) ← Fake.serve (handle Tests.S3.creds seen)
  let dir := (← IO.getEnv "TMPDIR").getD "/tmp"
  let path : System.FilePath := s!"{dir}/lanes-ses-once-{← IO.monoNanosNow}"
  let done ← IO.mkRef #[]
  let rt ← Runtime.startWith mailer {} fun _ out => do
    if let .done _ a := out then done.modify (·.push (kind a))
  let e := endpointAt port_
  let some m := msg? ["ann@b.co"] | return [("ses once: the message", false)]
  let out : Out := .send ⟨0, 1000, m⟩
  let keyed (k : String) : Out → Option String := fun _ => some k
  let state ← Once.open path
  handlerOnce state port (keyed "welcome-ann") e Tests.S3.creds config rt out
  let _ ← Fake.waitFor 3000 do return (← done.get).size ≥ 1
  handlerOnce state port (keyed "welcome-ann") e Tests.S3.creds config rt out
  let reopened ← Once.open path
  handlerOnce reopened port (keyed "welcome-ann") e Tests.S3.creds config rt out
  handlerOnce reopened port (keyed "welcome-bob") e Tests.S3.creds config rt out
  let _ ← Fake.waitFor 3000 do return (← done.get).size ≥ 4
  rt.stop
  server.close
  IO.FS.removeFile path
  let answers := (← done.get).toList
  return [
    ("ses once: an output whose key was sent is not sent again, also after a restart",
      (← seen.get).length == 2 && answers.count "unknown" == 2 && answers.count "sent" == 2),
    ("ses once: the state reads back as written, and a key that is no line is refused",
      Sent.read (Sent.write ["k", "j"]) == ["k", "j"] && !Sent.admits [] "a\nb"
        && !Sent.admits [] "") ]

def tests : List (String × Bool) := addressTests ++ requestTests ++ answerTests

def live : Async (List (String × Bool)) := do
  return (← exchanges) ++ (← conformance) ++ (← once)

end Checks.Ses
