import Rookery

/-!
rookery as a web application: `rookery [port] [journal] [secrets] [memory_kib] [maxPerWindow]`.

`secrets` holds the key that signs cookies, API tokens and form tokens and the pepper of
password digests, 64 random bytes made at the first start; with another file, every session,
token and password is another. A password digest is Argon2id, two passes over `memory_kib` KiB
(19 MiB unless given). The journal and its snapshot keep everything else.
-/

open Lanes Rookery Rookery.Web

def loadSecrets (path : System.FilePath) : IO ByteArray := do
  if ← path.pathExists then
    let bytes ← IO.FS.readBinFile path
    if bytes.size != 64 then throw (IO.userError s!"rookery: {path} does not hold 64 bytes")
    return bytes
  let bytes ← Lanes.randomBytes 64
  IO.FS.writeBinFile path bytes
  return bytes

def main (args : List String) : IO UInt32 := do
  let port := (args[0]? >>= String.toNat?).getD 8080
  let journal := args[1]?.map System.FilePath.mk
  let secrets ← loadSecrets ((args[2]?.map System.FilePath.mk).getD "rookery.secrets")
  let mem_kib := ((args[3]? >>= String.toNat?).getD 19456).toUInt32
  let maxPerWindow := (args[4]? >>= String.toNat?).getD 10
  let some cost := if h : 8 ≤ mem_kib then some ({ ops := 2, mem_kib, mem_min := h } : Argon2id)
      else none
    | IO.eprintln "rookery: Argon2id needs at least 8 KiB"; return 2
  let settings : Settings :=
    { key := .of (secrets.extract 0 32)
      password := { cost, pepper := secrets.extract 32 64 }
      origin := s!"http://127.0.0.1:{port}"
      secure := false }
  let config : Config := { maxPerWindow }
  let server ← (Http.serve (Sys config) (bridge settings)
    { port := port.toUInt16, journal, system := "rookery 1" } { snapshotEvery := 256 }
    (some (saving config))).block
  IO.println s!"rookery listening on http://127.0.0.1:{server.port.getD 0}"
  (← IO.getStdout).flush
  server.wait.block
  return 0
