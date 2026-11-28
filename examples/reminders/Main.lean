import Reminders.Serve

/-!
`reminders [port]`. Each reminder is posted, at its time, to the notification service
`NOTIFY_URL` names (`http://host:port`, at the path `NOTIFY_PATH`, `/` unless set), and retried
until it answers `2xx`. Where to listen comes from `LANES_HOST` (`127.0.0.1` unless set).
-/

open Lanes Reminders

def main (args : List String) : IO Unit := do
  let port := (args.head? >>= String.toNat?).getD 8080
  let host := (← IO.getEnv "LANES_HOST").getD "127.0.0.1"
  let url := (← IO.getEnv "NOTIFY_URL").getD "http://127.0.0.1:9090"
  let path := ((← IO.getEnv "NOTIFY_PATH").getD "/").splitOn "/" |>.filter (· != "")
  let some notify := Http.Client.Call.at url { method := .post, path }
    | throw (IO.userError s!"reminders: NOTIFY_URL is not an origin: {url}")
  let server ← (Serve.start
    { server := { host, port := port.toUInt16 }, notify }).block
  IO.println s!"reminders listening on http://{host}:{server.port.getD 0}"
  (← IO.getStdout).flush
  Lanes.block (server.stopOnSignal 10000)
