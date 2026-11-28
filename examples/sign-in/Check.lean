/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SignIn
import Lanes.Testing

/-!
What the bridge makes of requests and what the site answers, run by `lake test`. That the
sign-in gives the system only identities it verified is Lanes' (`Tests/OAuth.lean`).
-/

open Lanes Lanes.Http Lanes.OAuth SignIn

def settings : SignIn.Settings := { keys := .of (.of "a key of the deployment".toUTF8) }

def origin : String := "https://sign-in.example"

def alice : Identity :=
  { issuer := "https://accounts.google.com", subject := "1001", email := some "alice@example.com",
    emailVerified := true }

def run (cmds : List Command) : State × List Response :=
  cmds.foldl (init := ({}, [])) fun (st, out) cmd =>
    let (st, answers) := (service settings).step st (0, cmd)
    (st, out ++ answers.map (·.2))

def body (r : Response) : String := (String.fromUTF8? r.body).getD ""

def has (r : Response) (text : String) : Bool := ((body r).splitOn text).length > 1

def decoded (r : Request) : Option Command :=
  match (bridge settings origin).decode 0 ((bridge settings origin).prepare r) with
  | .ok (_, cmd) => some cmd
  | .error _ => none

def withCookie (token : String) (r : Request) : Request :=
  { r with headers := r.headers ++ [("cookie", s!"sign-in-session={token}")] }

def tests : List (String × Bool) :=
  let (st, out) := run [.signedIn alice 0, .signedIn { alice with email := some "a@example.com" } 0]
  [ ("sign-in: signing in again is the same member, with a new session",
      st.members == [(("https://accounts.google.com", "1001"), 0)]
        && (st.sessions.lookup 0).any (·.ids == [1, 0])),
    ("sign-in: signing in sets a signed session cookie and goes home",
      (out.zip [0, 1]).all fun (r, session) => r.status == 303
        && (r.headers.lookup "set-cookie").any
          (·.startsWith s!"sign-in-session={token settings 0 session 0}")),
    ("sign-in: the home page of a live session shows who signed in, last",
      let (_, pages) := (service settings).step st (0, .home (some (0, 1)))
      pages.all fun (_, r) => has r "a@example.com, member 0" && has r "Sign out"),
    ("sign-in: another provider's identity with the same subject is another member",
      let (st, _) := run [.signedIn alice 0, .signedIn { alice with issuer := "https://github.com" } 0]
      st.members.length == 2),
    ("sign-in: signed out, a session is no longer live",
      let (st, _) := run [.signedIn alice 0, .signOut 0 0]
      let (_, pages) := (service settings).step st (0, .home (some (0, 0)))
      pages.all fun (_, r) => has r "Sign in with Google"),
    ("sign-in: prepare verifies the cookie and drops it, and a forged session header",
      let home : Request := { method := .get, path := [], headers := [("sign-in-session", "0.7")] }
      decoded home == some (.home none)
        && decoded (withCookie (token settings 0 7 0) home) == some (.home (some (0, 7)))
        && decoded (withCookie "0.7" home) == some (.home none)
        && ((bridge settings origin).prepare (withCookie (token settings 0 7 0) home)).headers.all
          (·.1 != "cookie")),
    ("sign-in: a cookie lets in until it expires",
      let home : Request := withCookie (token settings 0 7 0) { method := .get, path := [] }
      decoded (stamp (settings.session_s - 1) home) == some (.home (some (0, 7)))
        && decoded (stamp settings.session_s home) == some (.home none)),
    ("sign-in: a callback the sign-in let in is a sign-in, any other is not found",
      let callback : Request := { method := .get, path := ["sign-in", "google", "callback"] }
      decoded (stamp 5 (withIdentity callback alice)) == some (.signedIn alice 5)
        && decoded callback == none),
    ("sign-in: signing out needs the session's form token, from the site's own pages",
      let post (csrf : String) (headers : List (String × String) := []) : Request :=
        withCookie (token settings 0 0 0) {
          method := .post, path := ["sign-out"], headers, body := s!"csrf={csrf}".toUTF8 }
      let good := Auth.formToken settings.keys (sessionOf 0 0)
      decoded (post good) == some (.signOut 0 0)
        && decoded (post "forged") == none
        && decoded (post good [("origin", "https://evil.example")]) == none) ]

def main (args : List String) : IO UInt32 :=
  Lanes.Testing.report args (Lanes.Testing.Result.tests tests .test)
