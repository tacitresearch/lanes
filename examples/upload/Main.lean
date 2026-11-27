import Upload.Web

/-!
`upload [port] [journal]`: uploads of any size, each answered with its size and checksum. With a
journal, every piece taken is in it, and the uploads under way survive the process.
-/

open Lanes Upload Upload.Web

def main (args : List String) : IO Unit := do
  let port := (args.head? >>= String.toNat?).getD 8080
  let journal := args[1]?.map System.FilePath.mk
  let server ← (Http.serve (system {}) bridge (serverConfig port.toUInt16 journal)
    { snapshotEvery := 4096 } saving).block
  IO.println s!"upload listening on http://127.0.0.1:{server.port.getD 0}"
  (← IO.getStdout).flush
  Lanes.block server.wait
