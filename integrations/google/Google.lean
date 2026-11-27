/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Sign-in with Google: its OpenID Connect provider, with the endpoints its discovery document
gives (`https://accounts.google.com/.well-known/openid-configuration`), kept as recorded in
`recorded/` and checked against it by `Check.lean`. Google's ID tokens are signed with RS256 and
name either of two issuers.
-/

namespace Google

open Lanes.OAuth

def issuers : List String := ["https://accounts.google.com", "accounts.google.com"]

def provider (scopes : List String := ["openid", "email"]) : Provider where
  name := "google"
  authorize := "https://accounts.google.com/o/oauth2/v2/auth"
  token := "https://oauth2.googleapis.com/token"
  scopes
  source := .idToken issuers "https://www.googleapis.com/oauth2/v3/certs"

end Google
