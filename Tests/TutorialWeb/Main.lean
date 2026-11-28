/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.TutorialWeb.Web

/-!
`shelf [port] [journal] [secrets]`: the site. `secrets` holds the key that signs session cookies
and form tokens, 32 random bytes made at the first start. Everything else comes from the
environment, read once here (rule 2.5); no key or secret is in the code.
-/

open Lanes Shelf

def loadKey (path : System.FilePath) : IO ByteArray := do
  if ← path.pathExists then return ← IO.FS.readBinFile path
  let bytes ← randomBytes 32
  IO.FS.writeBinFile path .empty
  IO.setAccessRights path { user := { read := true, write := true } }
  IO.FS.writeBinFile path bytes
  return bytes

def need (name : String) : IO String := do
  let some value := (← IO.getEnv name).filter (!·.isEmpty)
    | throw (IO.userError s!"shelf: {name} is not set")
  return value

/-- The OpenID Connect provider whose discovery document is the file `SHELF_OIDC_DISCOVERY`,
and the client registered with it. -/
def provider (origin : String) : IO (OAuth.Provider × OAuth.Client) := do
  let path ← need "SHELF_OIDC_DISCOVERY"
  let some d := OAuth.Discovery.read (← IO.FS.readFile path)
    | throw (IO.userError s!"shelf: {path} is not a discovery document")
  let id ← need "SHELF_OIDC_CLIENT_ID"
  let secret ← need "SHELF_OIDC_CLIENT_SECRET"
  return (d.provider "oidc",
    { id, secret := ⟨secret⟩, redirect := s!"{origin}/sign-in/oidc/callback" })

def ms (name : String) (default : Nat) : IO Nat := do
  let some text ← IO.getEnv name | return default
  let some n := text.toNat? | throw (IO.userError s!"shelf: {name} is not a number: {text}")
  return n

def main (args : List String) : IO Unit := do
  let port := (args[0]? >>= String.toNat?).getD 8080
  let journal := args[1]?.map System.FilePath.mk
  let key ← loadKey ((args[2]?.map System.FilePath.mk).getD "shelf.secrets")
  let origin := ((← IO.getEnv "LANES_URL").filter (!·.isEmpty)).getD s!"http://localhost:{port}"
  let region := ((← IO.getEnv "AWS_REGION").filter (!·.isEmpty)).getD "us-east-1"
  let bucket : S3.Bucket :=
    { name := ← need "LANES_MEDIA_BUCKET", region, endpoint := S3.Endpoint.aws region }
  let some creds ← S3.credentialsFromEnv
    | throw (IO.userError "shelf: AWS_ACCESS_KEY_ID and AWS_SECRET_ACCESS_KEY are not set")
  let host := (← IO.getEnv "LANES_HOST").getD "127.0.0.1"
  let settings : Settings := { keys := .of (.of key), origin, bucket, creds, providers := ["oidc"] }
  let server ← (start {
    settings
    server := { host, port := port.toUInt16, journal, system := "shelf 1"
                idle_ms := ← ms "LANES_IDLE_MS" 10000
                ops := { readinessPath := some "/readyz", livenessPath := some "/healthz"
                         metricsPath := some "/metrics", accessLog := .stderr } }
    signIn := { providers := [← provider origin], secure := settings.secure } }).block
  IO.println s!"shelf listening on http://{host}:{server.port.getD 0}"
  (← IO.getStdout).flush
  Lanes.block (server.stopOnSignal (← ms "LANES_DRAIN_MS" 10000))
