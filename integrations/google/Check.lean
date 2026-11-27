/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Google

/-!
The preset against what Google published, as fetched on 2026-11-27 and kept in `recorded/`: its
discovery document and its JWK Set. Nothing is fetched here.
-/

open Lanes Lanes.OAuth

def discovery : String := include_str "recorded/openid-configuration.json"

def certs : String := include_str "recorded/certs.json"

def client : Client :=
  { id := "1234.apps.googleusercontent.com", secret := ⟨"s"⟩,
    redirect := "https://videos.example/sign-in/google/callback" }

def tests : List (String × Bool) :=
  let p := Google.provider
  let (url, _) := begin {} (.of ⟨#[0]⟩) p client 0 ⟨#[1]⟩
  let user (issuer : String) : Identity := { issuer, subject := "1", email := some "u@gmail.com" }
  match Discovery.read discovery, p.source with
  | some d, .idToken issuers jwks =>
    [ ("google: the endpoints are those of the discovery document",
        d.authorize == p.authorize && d.token == p.token && d.jwks == jwks),
      ("google: its issuer is one the preset accepts", issuers.contains d.issuer),
      ("google: a user has one key whichever of Google's two issuers the token names",
        Identity.under issuers (user "accounts.google.com") == user d.issuer
          && Identity.under issuers (user "https://accounts.google.com") == user d.issuer),
      ("google: it signs ID tokens with RS256, and takes S256 challenges",
        d.algs.contains "RS256" && d.challenges.contains "S256"),
      ("google: its JWK Set is read: RSA keys for RS256, each with a kid",
        match Jose.readKeys certs with
        | .ok keys => !keys.isEmpty && keys.all fun k =>
            k.kid.isSome && k.fits .rs256 && (k.key matches .rsa ..)
        | .error _ => false),
      ("google: the sign-in asks for a code with a nonce and an S256 challenge",
        url.startsWith "https://accounts.google.com/o/oauth2/v2/auth?response_type=code"
          && (url.splitOn "nonce=").length == 2 && (url.splitOn "code_challenge_method=S256").length == 2) ]
  | _, _ => [("google: the discovery document is read", false)]

def main : IO UInt32 := do
  let failed := tests.filter (!·.2)
  for (name, _) in failed do IO.println s!"FAIL {name}"
  IO.println s!"{tests.length - failed.length} passed, {failed.length} failed"
  return if failed.isEmpty then 0 else 1
