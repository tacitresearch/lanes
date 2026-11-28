/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SignIn
import Lanes.Services.Oidc

/-!
`signIn [port]`: the site, with a provider for each of Google and GitHub whose client is in the
environment: `GOOGLE_CLIENT_ID` and `GOOGLE_CLIENT_SECRET`, `GITHUB_CLIENT_ID` and
`GITHUB_CLIENT_SECRET`. Each is registered with its provider with the redirect URI
`<LANES_URL>/sign-in/<google|github>/callback`, where `LANES_URL` is the site's public origin,
`http://localhost:<port>` if unset. Sessions are signed with a key made at start, so they end
with the process.
-/

open Lanes Lanes.OAuth SignIn

structure Setup where
  origin : String
  /-- Each provider whose client is in the environment, with its client. -/
  providers : List (Provider × Client)

open Environment in
def client (origin : String) (p : Provider) : Environment.Reader (Option (Provider × Client)) := do
  let name := p.name.toUpper
  let id ← opt s!"{name}_CLIENT_ID" (doc := s!"The client registered with {p.name}.")
  let secret ← secret? s!"{name}_CLIENT_SECRET" (doc := s!"The secret of {p.name}'s client.")
  check (id.isSome == secret.isSome) s!"{name}_CLIENT_SECRET"
    s!"{name}_CLIENT_ID and {name}_CLIENT_SECRET are set together or not at all"
  return match id, secret with
    | some id, some secret => some (p, { id, secret, redirect := s!"{origin}/sign-in/{p.name}/callback" })
    | _, _ => none

open Environment in
def setup (port : Nat) : Environment.Reader Setup := do
  let origin ← get "LANES_URL" s!"http://localhost:{port}" (doc := "The site's public origin.")
  let providers ← [Google.provider, GitHub.provider].filterMapM (client origin)
  return { origin, providers }

def main (args : List String) : IO Unit := do
  let port := (args.head? >>= String.toNat?).getD 8080
  let { origin, providers } ← Environment.load (setup port) "signIn"
  let settings : SignIn.Settings :=
    { keys := .of (.of (← randomBytes 32)), secure := origin.startsWith "https:" }
  let signIn ← SignIn.start { providers, secure := settings.secure }
  let server ← (Http.serve (Server.system (service settings)) (bridge settings origin)
    { port := port.toUInt16 } (arrive := some fun r => do
      match ← signIn.arrive r with
      | .ok r => return .ok (stamp ((← Log.wallMs) / 1000) r)
      | .error answer => return .error answer)).block
  IO.println s!"signIn listening on http://127.0.0.1:{server.port.getD 0}, signing in with \
    {", ".intercalate (providers.map (·.1.name))}"
  (← IO.getStdout).flush
  Lanes.block server.wait
