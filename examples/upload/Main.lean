import Upload.Web

/-!
`upload [port]`: uploads of any size, each answered with its size and checksum. The uploads
under way live as long as the process.
-/

open Lanes Upload Upload.Web

def main (args : List String) : IO Unit := do
  let port := (args.head? >>= String.toNat?).getD 8080
  let server ← (Http.serve (system {}) bridge (serverConfig port.toUInt16)).block
  IO.println s!"upload listening on http://127.0.0.1:{server.port.getD 0}"
  (← IO.getStdout).flush
  Lanes.block server.wait
