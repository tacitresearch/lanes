/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The start of a video site: its members sign in with Google or GitHub and get a session. The
sign-in itself is Lanes' (`Lanes/Web/IO/SignIn.lean`), done where a request arrives: what reaches
this system is the identity it verified, never a code or a token. A member is an identity's
issuer and subject, which do not change, so the same person signing in again is the same member
(`register_again`); the address is shown, not trusted. A session is a signed cookie and an entry
of the member's `Auth.Sessions`, which keeps the newest few.
-/

namespace Videos

open Lanes Lanes.Http Lanes.OAuth
open scoped Lanes.Html

structure Settings where
  /-- The key session cookies are signed with. -/
  key : Hmac.Key
  /-- Sessions a member may have open at once; one more closes the oldest. -/
  maxSessions : Nat := 4
  /-- Whether cookies go over HTTPS only. -/
  secure : Bool := true

inductive Command where
  /-- The sign-in verified this identity. -/
  | signedIn (who : Identity)
  /-- The home page, for the member and session the cookie names when `prepare` verified it. -/
  | home (session : Option (Nat × Nat))
  | signOut (member session : Nat)
  deriving DecidableEq

/-- A member is named by the issuer and the subject. -/
abbrev Key := String × String

structure State where
  members : List (Key × Nat) := []
  /-- Who each member last signed in as. -/
  profiles : List (Nat × Identity) := []
  sessions : List (Nat × Auth.Sessions) := []
  /-- The next session's number: none is used twice. -/
  next : Nat := 0

/-- The member a key names, a new one if none does. -/
def register (members : List (Key × Nat)) (key : Key) : List (Key × Nat) × Nat :=
  match members.lookup key with
  | some n => (members, n)
  | none => ((key, members.length) :: members, members.length)

/-- Signing in again is the same member. -/
theorem register_again (members : List (Key × Nat)) (key : Key) :
    register (register members key).1 key = register members key := by
  cases h : members.lookup key <;> simp [register, h]

/-- The member is the one the key names after. -/
theorem register_lookup (members : List (Key × Nat)) (key : Key) :
    (register members key).1.lookup key = some (register members key).2 := by
  cases h : members.lookup key <;> simp [register, h]

def token (s : Settings) (member session : Nat) : String :=
  Auth.sign s.key "session" s!"{member}.{session}"

def cookie (s : Settings) (value : String) : Cookie :=
  { name := "videos-session", value, secure := s.secure, sameSite := .lax }

def Page (body : List Html) : Html :=
  <html lang="en">
    <head>
      <meta charset="utf-8"/>
      <title>"Videos"</title>
    </head>
    <body>
      <h1>"Videos"</h1>
      {body}
    </body>
  </html>

def SignedOut : Html :=
  Page [
    <p>
      <a href="/sign-in/google">"Sign in with Google"</a>" "
      <a href="/sign-in/github">"Sign in with GitHub"</a>
    </p>]

def SignedIn (s : Settings) (member session : Nat) (who : Identity) : Html :=
  let shown := who.email.getD who.subject
  Page [
    <p>{s!"Signed in as {shown}{if who.emailVerified then "" else " (unverified)"}, member {member}."}</p>,
    <form method="post" action="/sign-out">
      <input type="hidden" name="csrf" value={Auth.formToken s.key (token s member session)}/>
      <button type="submit">"Sign out"</button>
    </form>]

def page (html : Html) : Response := .html html.render

def service (s : Settings) : Service (ReqId × Command) (ReqId × Response) State where
  init := {}
  step st
    | (id, .signedIn who) =>
      let (members, member) := register st.members (who.issuer, who.subject)
      let (held, _) := ((st.sessions.lookup member).getD {}).start s.maxSessions st.next
      ({ members, next := st.next + 1
         profiles := (member, who) :: st.profiles.filter (·.1 != member)
         sessions := (member, held) :: st.sessions.filter (·.1 != member) },
       [(id, (Response.redirect "/").setCookie (cookie s (token s member st.next)))])
    | (id, .home (some (member, session))) =>
      match ((st.sessions.lookup member).getD {}).live session, st.profiles.lookup member with
      | true, some who => (st, [(id, page (SignedIn s member session who))])
      | _, _ => (st, [(id, (page SignedOut).clearCookie (cookie s ""))])
    | (id, .home none) => (st, [(id, page SignedOut)])
    | (id, .signOut member session) =>
      let held := ((st.sessions.lookup member).getD {}).close session
      ({ st with sessions := (member, held) :: st.sessions.filter (·.1 != member) },
       [(id, (Response.redirect "/").clearCookie (cookie s ""))])

/-- The header `prepare` writes with the member and session a cookie it verified names. One a
client sends is dropped, and so are the cookies, which are never journalled. -/
def sessionHeader : String := "videos-session"

def prepare (s : Settings) (r : Request) : Request :=
  let kept := r.headers.filter fun (name, _) => name != "cookie" && name != sessionHeader
  let session := (r.cookie? "videos-session").bind (Auth.verify s.key "session")
  { r with headers := kept ++ (session.map ((sessionHeader, ·))).toList }

def session? (r : Request) : Option (Nat × Nat) := do
  match (← r.header? sessionHeader).splitOn "." with
  | [member, session] => return (← member.toNat?, ← session.toNat?)
  | _ => none

def bridge (s : Settings) (origin : String) : Bridge (Server.sig (ReqId × Command) (ReqId × Response)) where
  decode id r :=
    match r.method, r.path with
    | .get, [] => .ok (id, .home (session? r))
    | .get, ["sign-in", _, "callback"] =>
      match identity? r with
      | some who => .ok (id, .signedIn who)
      | none => .error (.text "not found\n" 404)
    | .post, ["sign-out"] =>
      match session? r with
      | some (member, session) =>
        if r.sameOrigin origin
            && Auth.checkForm s.key (token s member session) ((r.field? "csrf").getD "") then
          .ok (id, .signOut member session)
        else .error (.text "forbidden\n" 403)
      | none => .error (.redirect "/")
    | _, _ => .error (.text "not found\n" 404)
  encode out := some out
  prepare := prepare s

end Videos
