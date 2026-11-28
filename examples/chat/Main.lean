import Chat.Web

/-!
`chat [port]`: a chat room over WebSockets. Open `http://127.0.0.1:8080/` in two windows. The
room lives as long as the process.
-/

open Lanes Chat Chat.Web

def main (args : List String) : IO Unit := do
  let port := (args.head? >>= String.toNat?).getD 8080
  let server ← (Http.serve (system {}) bridge (serverConfig port.toUInt16)
    (upgrade := some ws.upgrade)).block
  IO.println s!"chat listening on http://127.0.0.1:{server.port.getD 0}"
  (← IO.getStdout).flush
  Lanes.block server.wait
