import Reminders.Check
import Reminders.Serve
import Lanes.Testing

/-!
`lake test`: the model checks of `Reminders.Check`, then, when `LANES_POSTGRES=host:port` names
a PostgreSQL (`scripts/postgres-test-server`), the application over HTTP on it. A local
notification service answers `503` to the first two deliveries of a reminder and takes the
third; the reminder is sent with the same `Idempotency-Key` each time. A reminder due in an
hour waits, and is cancelled. Then the server is stopped and started again on the same
database: what was sent stays sent, nothing is delivered again, and the cancelled reminder stays
cancelled.
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

def deployment (postgres : Postgres.Client.Config) (notifyPort : UInt16) : Serve.Deployment :=
  { config := { jobs := { attempts_max := 4, lease_ms := 3000, backoff_ms := 50, backoff_max_ms := 200 } }
    server := { port := 0 }
    postgres
    notify := { host := "127.0.0.1", port := notifyPort, request := { method := .post, path := ["notify"] } }
    attempt_ms := 1000, poll_ms := 50 }

/-- Drop the table and make it again from `migrations/`. -/
def fresh (cfg : Postgres.Client.Config) : IO (List String) := do
  let .ok s ← (Postgres.connect cfg).block | return ["cannot connect"]
  discard <| (s.exec (.statement { sql := "DROP TABLE IF EXISTS reminders" })).block
  let errors ← (Postgres.Typed.migrate s [← IO.FS.readFile "migrations/0001_reminders.sql"]).block
  let diff ← (Postgres.Typed.checkSchema s schema).block
  (s.close).block
  return errors ++ diff.filter fun d => (d.splitOn "reminders").length > 1

def live : IO (List (String × Bool)) := do
  let some spec ← IO.getEnv "LANES_POSTGRES"
    | return [("reminders on postgres: skipped, LANES_POSTGRES is not set", true)]
  let [host, portText] := spec.splitOn ":" | return [("LANES_POSTGRES is host:port", false)]
  let pg : Postgres.Client.Config :=
    { host, port := portText.toNat!.toUInt16, sslmode := .disable,
      conn := { user := "lanes_trust", database := "lanes_test" } }
  let errors ← fresh pg
  unless errors.isEmpty do return [(s!"reminders on postgres: the migrations make the schema's table: {errors}", false)]
  Lanes.block do
    let service ← serve (Server.system notify) notifyBridge { port := 0 }
    let some notifyPort := service.port | return [("the notification service reports its port", false)]
    let d := deployment pg notifyPort
    let first ← Serve.start d
    let some port := first.server.port | return [("the server reports its port", false)]
    post port ["remind"] "text=tea&in=0"
    let sent ← waitFor port "tea (sent)"
    post port ["remind"] "text=later&in=3600"
    let waiting ← waitFor port "later (waiting)"
    post port ["cancel", "1"] ""
    let cancelled ← waitFor port "later (cancelled)"
    first.stop
    let again ← Serve.start d
    let some port := again.server.port | return [("the server reports its port again", false)]
    let restarted ← page port
    Async.sleep 300
    again.stop
    let tries ← deliveries notifyPort "reminder-0"
    service.stop
    return [
      ("reminders: a reminder the service refuses twice is sent on its third attempt, under one key",
        shows sent "tea (sent)" && tries == 3),
      ("reminders: a reminder due later waits", shows waiting "later (waiting)"),
      ("reminders: a reminder that waits is cancelled", shows cancelled "later (cancelled)"),
      ("reminders: after a restart the reminders are as they were, and none is delivered again",
        shows restarted "tea (sent)" && shows restarted "later (cancelled)" && tries == 3) ]

def main (args : List String) : IO UInt32 := do
  let checked := Check.check [0, 200] Check.scenario
  let check := Lanes.Testing.Result.check
    "reminders: checked beside the store's model and a service that fails, answers unknown or never"
    checked checked.renderSystem
  let check := if checked.witnesses.length == 2 then check else { check with status := .failed }
  Lanes.Testing.report args (check :: Lanes.Testing.Result.tests (← live))
