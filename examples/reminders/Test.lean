import Reminders.Check
import Reminders.Serve
import Lanes.Testing

/-!
`lake test`: the model checks of `Reminders.Check`, then the application over HTTP. A local
notification service answers `503` to the first two deliveries of a reminder and takes the third;
the reminder is sent with the same `Idempotency-Key` each time. Then the server is stopped and
started again on its journal: the reminder sent is still sent, the one due in an hour still
waits, and it can be cancelled.
-/

open Std Std.Async Lanes Lanes.Http Reminders

/-- A service that answers `503` to the first two deliveries under a key and takes the third,
and tells how many deliveries a key had (`GET /count?key=`). -/
abbrev notifySig := Server.sig (ReqId × Request) (ReqId × Response)

def notify : Service (ReqId × Request) (ReqId × Response) (List (String × Nat)) where
  init := []
  step := fun seen (id, request) =>
    match request.method with
    | .get =>
      let key := (request.query.lookup "key").getD ""
      (seen, [(id, .text s!"{(seen.lookup key).getD 0}")])
    | _ =>
      let key := (request.header? "idempotency-key").getD ""
      let n := (seen.lookup key).getD 0 + 1
      ((key, n) :: seen.filter (·.1 != key), [(id, if n ≤ 2 then .text "busy" 503 else .text "taken")])

def notifyBridge : Bridge notifySig where
  decode id request := .ok (id, request)
  encode := some

def deliveries (port : UInt16) (key : String) : Async Nat := do
  let r ← Client.exchange
    { host := "127.0.0.1", port, request := { method := .get, path := ["count"], query := [("key", key)] } } {}
  return ((r.bind fun r => String.fromUTF8? r.body).bind String.toNat?).getD 0

def page (port : UInt16) : Async String := do
  let r ← Client.exchange { host := "127.0.0.1", port, request := { method := .get, path := [] } } {}
  return ((r.bind fun r => String.fromUTF8? r.body)).getD ""

def post (port : UInt16) (path : List String) (form : String) : Async Unit := do
  let request : Request :=
    { method := .post, path, body := form.toUTF8
      headers := [("content-type", "application/x-www-form-urlencoded")] }
  discard <| Client.exchange { host := "127.0.0.1", port, request } {}

/-- The page, once it shows `text` or after `patience_ms`. -/
def waitFor (port : UInt16) (text : String) (patience_ms : Nat := 8000) : Async String := do
  let deadline := (← IO.monoMsNow) + patience_ms
  repeat
    let shown ← page port
    if (shown.splitOn text).length > 1 || deadline ≤ (← IO.monoMsNow) then return shown
    Async.sleep 50
  return ""

def shows (shown text : String) : Bool := (shown.splitOn text).length > 1

def deployment (journal : System.FilePath) (notifyPort : UInt16) : Serve.Deployment :=
  { config :=
      { retry := { maxAttempts := 4, deadline_ms := 1000, base_ms := 50, cap_ms := 200, jitter_ms := 20 }
        sweep_ms := 3600000 }
    server := { port := 0, system := "reminders test" }
    journal := some journal
    notify := { host := "127.0.0.1", port := notifyPort, request := { method := .post, path := ["notify"] } } }

def live : Async (List (String × Bool)) := do
  let service ← serve (Server.system notify) notifyBridge { port := 0 }
  let some notifyPort := service.port | return [("the notification service reports its port", false)]
  let journal : System.FilePath := ".lake" / "reminders-test.journal"
  if ← journal.pathExists then IO.FS.removeFile journal
  let d := deployment journal notifyPort
  let first ← Serve.start d
  let some port := first.port | return [("the server reports its port", false)]
  post port ["remind"] "text=tea&in=0"
  let sent ← waitFor port "tea (sent)"
  post port ["remind"] "text=later&in=3600"
  let waiting ← waitFor port "later (waiting)"
  first.stop
  let again ← Serve.start d
  let some port := again.port | return [("the server reports its port again", false)]
  let replayed ← page port
  post port ["cancel", "1"] ""
  let cancelled ← waitFor port "later (cancelled)"
  again.stop
  let tries ← deliveries notifyPort "reminder-0"
  service.stop
  return [
    ("reminders: a reminder the service refuses twice is sent on its third attempt",
      shows sent "tea (sent)" && tries == 3),
    ("reminders: a reminder due later waits", shows waiting "later (waiting)"),
    ("reminders: after a restart on the journal, what was sent is sent and what waits still waits",
      shows replayed "tea (sent)" && shows replayed "later (waiting)"),
    ("reminders: a reminder that waits is cancelled", shows cancelled "later (cancelled)") ]

def main (args : List String) : IO UInt32 := do
  let checked := Check.check Check.scenario
  let check := Lanes.Testing.Result.check
    "reminders: checked beside a service that fails, answers unknown, late or never"
    checked checked.renderSystem
  let check := if checked.witnesses.length == 4 then check else { check with status := .failed }
  Lanes.Testing.report args (check :: Lanes.Testing.Result.tests (← Lanes.block live))
