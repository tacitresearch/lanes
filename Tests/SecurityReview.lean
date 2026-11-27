/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Web.Auth.OAuth
import Lanes.Lib.Postgres.Conn

/-!
Findings of a security review, each as a check of the behaviour one would want. Each `#guard`
here FAILS on the code reviewed, which is what demonstrates the finding:

`lake env lean Tests/SecurityReview.lean`

Only pure functions are run, none bound to C, so the interpreter runs them.
-/

open Lanes

namespace SecurityReview

/-! ## 1. Anyone can evict every pending sign-in

`GET /sign-in/<provider>` needs nothing and keeps a pending sign-in; at `maxPending` (1024) the
oldest is dropped. A victim who began a sign-in, followed by 1024 anonymous `GET`s by anyone, is
refused at the callback (`unknownState`). -/

def seedOf (n : Nat) : OAuth.Seed :=
  let b (k : Nat) := (toString (n * 4 + k)).toUTF8
  { state := b 0, nonce := b 1, verifier := b 2, binding := b 3 }

def victim : OAuth.Entry := (seedOf 0).entry "google" 600000

/-- The victim begins at time 0, then an attacker sends 1024 begins within the next second. -/
def afterFlood : OAuth.Pending :=
  (List.range 1024).foldl (fun p i => p.begin 1024 (i + 1) ((seedOf (i + 1)).entry "google" 600000))
    (({} : OAuth.Pending).begin 1024 0 victim)

-- What one would want: the victim's sign-in still waits. It does not.
#guard afterFlood.entries.any (·.state == victim.state)

/-! ## 2. A PostgreSQL server that says `AuthenticationOk` at once is trusted, with SCRAM's
signature never checked

With a password configured, the connection accepts `AuthenticationOk` as the server's first
answer (`trust`) and opens, so an impostor on the network path, or at the address, is never
asked to prove it knows the password. `allowMd5` is on by default, so the same impostor can
instead ask for MD5 and get a digest of the password it can guess against offline. -/

def pgConfig : Postgres.Conn.Config :=
  { user := "lanes", database := "lanes", password := some "pw", nonce := "abcdefghijklmnop" }

def opensWithoutProof : Bool :=
  let (c, _) := Postgres.Conn.start pgConfig
  let (c, _) := Postgres.Conn.step pgConfig c (.received Postgres.Backend.authOk.encode)
  let (_, actions) := Postgres.Conn.step pgConfig c (.received (Postgres.Backend.readyForQuery .idle).encode)
  actions.contains .opened

-- What one would want with a password: an impostor's `AuthenticationOk` refused.
#guard !opensWithoutProof

def sendsMd5 : Bool :=
  let (c, _) := Postgres.Conn.start pgConfig
  let (_, actions) := Postgres.Conn.step pgConfig c (.received (Postgres.Backend.authMd5 ⟨#[1, 2, 3, 4]⟩).encode)
  actions.any fun | .send _ => true | _ => false

-- What one would want by default: no downgrade from SCRAM to MD5.
#guard !sendsMd5

end SecurityReview
