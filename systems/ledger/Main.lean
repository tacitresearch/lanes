import Ledger

/-!
The ledger as a web application: `ledger [port] [journal] [secrets] [admin] [iterations]`.

`secrets` holds the key that signs cookies and form tokens and the pepper of password digests,
64 random bytes made at the first start; with another file, every session and every password is
another. The journal and its snapshot keep everything else.
-/

open Lanes Ledger Ledger.Web

def loadSecrets (path : System.FilePath) : IO ByteArray := do
  if ← path.pathExists then
    let bytes ← IO.FS.readBinFile path
    if bytes.size != 64 then throw (IO.userError s!"ledger: {path} does not hold 64 bytes")
    return bytes
  let bytes ← IO.getRandomBytes 64
  IO.FS.writeBinFile path bytes
  return bytes

def main (args : List String) : IO UInt32 := do
  let port := (args[0]? >>= String.toNat?).getD 8080
  let journal := args[1]?.map System.FilePath.mk
  let secrets ← loadSecrets ((args[2]?.map System.FilePath.mk).getD "ledger.secrets")
  let some admin := Name.ofString? (args[3]?.getD "admin")
    | IO.eprintln "ledger: the administrator's name is lowercase letters and digits"; return 2
  let iterations := (args[4]? >>= String.toNat?).getD 20000
  let settings : Settings :=
    { key := .of (secrets.extract 0 32)
      password := { iterations, pepper := secrets.extract 32 64 }
      origin := s!"http://127.0.0.1:{port}"
      secure := false
      admin }
  let started ← IO.monoMsNow
  let probe := settings.password.digest "admin" s!"a password to time {started}"
  if probe.bytes.size != 32 then return 1
  let digest_ms := (← IO.monoMsNow) - started
  let config : Config Name := { admin }
  let server ← (Http.serve (Sys config) (bridge settings)
    { port := port.toUInt16, journal, system := "ledger 1" } { snapshotEvery := 256 }
    (some (saving config))).block
  IO.println s!"ledger listening on http://127.0.0.1:{server.port.getD 0} (a password digest takes {digest_ms} ms)"
  (← IO.getStdout).flush
  server.wait.block
  return 0
