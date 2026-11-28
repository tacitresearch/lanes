/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.TutorialWeb.Web

/-!
`shelf [port] [secrets]`: the site. `secrets` holds the key that signs session cookies
and form tokens, 32 random bytes made at the first start. Everything else comes from the
environment, read once by `setup` (rule 2.5); no key or secret is in the code. The shelf
is in PostgreSQL, as libpq's variables say; at the start the migrations of `migrations/` not
yet run are run, and the site refuses to start on tables other than the declared ones.
-/

open Lanes Shelf

def loadKey (path : System.FilePath) : IO ByteArray := do
  if ← path.pathExists then return ← IO.FS.readBinFile path
  let bytes ← randomBytes 32
  IO.FS.writeBinFile path .empty
  IO.setAccessRights path { user := { read := true, write := true } }
  IO.FS.writeBinFile path bytes
  return bytes

structure Setup where
  host : String
  origin : String
  bucket : S3.Bucket
  /-- The path of the OpenID Connect provider's discovery document. -/
  discovery : String
  client : OAuth.Client
  idle_ms : Nat
  drain_ms : Nat

open Environment in
def setup (port : Nat) : Environment.Reader Setup := do
  let host ← get "LANES_HOST" "127.0.0.1" (doc := "The address to listen on.")
  let origin ← get "LANES_URL" s!"http://localhost:{port}" (doc := "The site's public origin.")
  let region ← get "AWS_REGION" "us-east-1" (doc := "The media bucket's region.")
  let name ← need "LANES_MEDIA_BUCKET" (doc := "The media bucket.")
  let discovery ← need "SHELF_OIDC_DISCOVERY" (doc := "The path of the provider's discovery document.")
  let id ← need "SHELF_OIDC_CLIENT_ID" (doc := "The client registered with the provider.")
  let secret ← secret "SHELF_OIDC_CLIENT_SECRET" (doc := "The client's secret.")
  let idle_ms ← get "LANES_IDLE_MS" 10000 (doc := "How long an idle connection is kept.")
  let drain_ms ← get "LANES_DRAIN_MS" 10000
    (doc := "How long SIGTERM or SIGINT waits for the requests in flight.")
  return { host, origin, discovery, idle_ms, drain_ms
           bucket := { name, region, endpoint := S3.Endpoint.aws region }
           client := { id, secret, redirect := s!"{origin}/sign-in/oidc/callback" } }

/-- The OpenID Connect provider whose discovery document is the file at `path`. -/
def provider (path : String) : IO OAuth.Provider := do
  let some d := OAuth.Discovery.read (← IO.FS.readFile path)
    | throw (IO.userError s!"shelf: {path} is not a discovery document")
  return d.provider "oidc"

def main (args : List String) : IO UInt32 := do
  let port := (args[0]? >>= String.toNat?).getD 8080
  let d ← Environment.load (setup port) "shelf"
  let key ← loadKey ((args[1]?.map System.FilePath.mk).getD "shelf.secrets")
  let some creds ← S3.credentialsFromEnv
    | throw (IO.userError "shelf: AWS_ACCESS_KEY_ID and AWS_SECRET_ACCESS_KEY are not set")
  let settings : Settings :=
    { keys := .of (.of key), origin := d.origin, bucket := d.bucket, creds, providers := ["oidc"] }
  let postgres ← Postgres.Client.fromEnv
  let problems ← (Postgres.Typed.prepare postgres schema
    (← Postgres.Typed.readMigrations "migrations")).block
  unless problems.isEmpty do
    IO.eprintln s!"shelf: not started: {problems}"
    return 1
  let store : Postgres.Typed.Store Request Answer :=
    { pool := ← Postgres.Pool.new postgres, handler := handler {} }
  let server ← (start {
    settings
    server := { host := d.host, port := port.toUInt16, idle_ms := d.idle_ms
                ops := { readinessPath := some "/readyz", livenessPath := some "/healthz"
                         metricsPath := some "/metrics", accessLog := .stderr } }
    signIn := { providers := [(← provider d.discovery, d.client)], secure := settings.secure } }
      store.call).block
  IO.println s!"shelf listening on http://{d.host}:{server.port.getD 0}"
  (← IO.getStdout).flush
  Lanes.block (server.stopOnSignal d.drain_ms)
  return 0
