/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos
import Lanes.Services.Oidc

/-!
`signIn [port]`: the site, with a provider for each of Google and GitHub whose client is in the
environment: `GOOGLE_CLIENT_ID` and `GOOGLE_CLIENT_SECRET`, `GITHUB_CLIENT_ID` and
`GITHUB_CLIENT_SECRET`. Each is registered with its provider with the redirect URI
`<LANES_URL>/sign-in/<google|github>/callback`, where `LANES_URL` is the site's public origin,
`http://localhost:<port>` if unset. Sessions are signed with a key made at start, so they end
with the process.
-/

open Lanes Lanes.OAuth Videos

def client (origin name : String) : IO (Option Client) := do
  let some id ← IO.getEnv s!"{name.toUpper}_CLIENT_ID" | return none
  let some secret ← IO.getEnv s!"{name.toUpper}_CLIENT_SECRET" | return none
  return some { id, secret := ⟨secret⟩, redirect := s!"{origin}/sign-in/{name}/callback" }

def main (args : List String) : IO Unit := do
  let port := (args.head? >>= String.toNat?).getD 8080
  let origin := (← IO.getEnv "LANES_URL").getD s!"http://localhost:{port}"
  let mut providers := []
  for p in [Google.provider, GitHub.provider] do
    if let some c ← client origin p.name then providers := providers ++ [(p, c)]
  let settings : Videos.Settings :=
    { keys := .of (.of (← randomBytes 32)), secure := origin.startsWith "https:" }
  let signIn ← SignIn.start { providers, secure := settings.secure }
  let server ← (Http.serve (Server.system (service settings)) (bridge settings origin)
    { port := port.toUInt16 } (arrive := some fun r => do
      match ← signIn.arrive r with
      | .ok r => return .ok (stamp ((← Log.wallMs) / 1000) r)
      | .error answer => return .error answer)).block
  IO.println s!"Videos listening on http://127.0.0.1:{server.port.getD 0}, signing in with \
    {", ".intercalate (providers.map (·.1.name))}"
  (← IO.getStdout).flush
  Lanes.block server.wait
