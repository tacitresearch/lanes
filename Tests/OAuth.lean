/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Lanes.Testing
import Tests.Web

/-!
Sign-in with another service (`Lanes/Web/Auth/OAuth.lean`, `Lanes/Web/IO/SignIn.lean`). The pure
decisions one by one; the pending sign-ins as an actor, model-checked against two browsers, one of
them an attacker's, that replay and swap callbacks; and the whole flow end to end over HTTP,
against the test kit's provider (`Lanes/Testing/OAuth.lean`): an authorization endpoint the test
plays, a token endpoint that checks PKCE and signs ID tokens with an RSA key made by `openssl`, a
JWK Set, and a user API for a provider without ID tokens. No real provider is called.
-/

namespace Tests.OAuth

open Lanes Lanes.OAuth Lanes.Http Std Std.Async
open Lanes.Testing (queryOf)

def seed (n : Nat) : Seed :=
  let b (k : Nat) := ByteArray.mk (Array.replicate 32 (UInt8.ofNat (n * 4 + k)))
  { state := b 0, nonce := b 1, verifier := b 2, binding := b 3 }

def oidc : Provider :=
  { name := "id", authorize := "https://id.example/authorize", token := "https://id.example/token",
    scopes := ["openid", "email"], source := .idToken ["https://id.example"] "https://id.example/jwks" }

def plain : Provider :=
  { oidc with name := "plain", source := .userApi [] fun _ => .error "none" }

def client : Client :=
  { id := "app", secret := ⟨"s3cret"⟩, redirect := "https://app.example/sign-in/id/callback" }

def settings : Settings := { maxPending := 2 }

def get (q : List (String × String)) (name : String) : Option String :=
  (q.find? (·.1 == name)).map (·.2)

def accepted (r : Pending × Except OAuth.Refusal Grant) : Bool := r.2 matches .ok _

def refusal (r : Pending × Except OAuth.Refusal Grant) : Option OAuth.Refusal :=
  match r.2 with
  | .error why => some why
  | .ok _ => none

def claims : IdToken.Claims :=
  { iss := "https://id.example", sub := "u1", aud := ["app"], azp := some "app", exp := 2000,
    nonce := some "n", email := some "u@example.com", emailVerified := true }

def expect : IdToken.Expect :=
  { issuers := ["https://id.example"], clientId := "app", nonce := "n", now_s := 1000, skew_s := 60 }

def checked (c : IdToken.Claims) (x : IdToken.Expect := expect) : Option IdToken.Refusal :=
  match IdToken.check x c with
  | .ok _ => none
  | .error why => some why

def readClaims (json : String) : Option IdToken.Claims := IdToken.Claims.read json.toUTF8

def flowTests : List (String × Bool) :=
  let (p, url, binding) := begin settings oidc client {} 1000 (seed 0)
  let q := queryOf url
  let state := (get q "state").getD ""
  let verifier := b64 (seed 0).verifier
  [ ("oauth: the S256 challenge of RFC 7636 appendix B",
      challenge "dBjftJeZ4CVP-mB92K27uhbUJU1p1r_wW1gFWFOEjXk"
        == "E9Melhoa2OwvFrEMTJguCHaoeK1t8URWbuGJSstw-cM"),
    ("oauth: the authorization URL asks for a code, with the state, the S256 challenge and a nonce",
      url.startsWith "https://id.example/authorize?" && get q "response_type" == some "code"
        && get q "client_id" == some "app" && get q "redirect_uri" == some client.redirect
        && get q "scope" == some "openid email" && state == b64 (seed 0).state
        && get q "code_challenge" == some (challenge verifier)
        && get q "code_challenge_method" == some "S256"
        && get q "nonce" == some (b64 (seed 0).nonce) && binding == b64 (seed 0).binding
        && state.length == 43 && verifier.length == 43),
    ("oauth: OAuth 2.0 alone is asked for no nonce, and extra parameters are added",
      let (_, url, _) := begin settings { plain with extra := [("prompt", "consent")] } client {}
        1000 (seed 0)
      (get (queryOf url) "nonce").isNone && get (queryOf url) "prompt" == some "consent"),
    ("oauth: a callback under the state, from the browser, before it expires, is accepted once",
      match p.callback 2000 "id" binding state with
      | (rest, .ok g) =>
        g.nonce == b64 (seed 0).nonce && g.verifier == ⟨verifier⟩
          && refusal (rest.callback 2000 "id" binding state) == some .unknownState
      | _ => false),
    ("oauth: a state never issued is refused",
      refusal (p.callback 2000 "id" binding "forged") == some .unknownState),
    ("oauth: from another browser the state is refused, and used up",
      let (rest, r) := p.callback 2000 "id" "other" state
      refusal (rest, r) == some .otherBrowser && refusal (rest.callback 2000 "id" binding state) == some .unknownState),
    ("oauth: on another provider's route the state is refused",
      refusal (p.callback 2000 "plain" binding state) == some .otherProvider),
    ("oauth: a callback once the sign-in has expired is refused",
      refusal (p.callback (1000 + settings.ttl_ms) "id" binding state) == some .expired
        && accepted (p.callback (999 + settings.ttl_ms) "id" binding state)),
    ("oauth: at most maxPending sign-ins wait, the oldest dropped first",
      let (p2, _, _) := begin settings oidc client p 1001 (seed 1)
      let (p3, _, _) := begin settings oidc client p2 1002 (seed 2)
      p3.entries.length == 2
        && refusal (p3.callback 2000 "id" binding state) == some .unknownState
        && accepted (p3.callback 2000 "id" (b64 (seed 2).binding) (b64 (seed 2).state))),
    ("oauth: a sign-in that has expired is dropped when another begins",
      let (p2, _, _) := begin { settings with maxPending := 10 } oidc client p
        (1000 + settings.ttl_ms) (seed 1)
      p2.entries.length == 1),
    ("oauth: over a run, a state is accepted as often as it is issued and no more",
      let e := (seed 0).entry "id" 10
      let ops := [Pending.Op.begin 4 0 e, .callback 1 "id" e.binding e.state,
        .callback 1 "id" e.binding e.state, .begin 4 2 e, .callback 3 "id" e.binding e.state]
      (Pending.run {} ops).2 == [e.state, e.state]),
    ("oauth: the provider's answer is a code and the state, or an error",
      (match Answer.read [("state", "s"), ("code", "c")] with
        | .code c s => c == ⟨"c"⟩ && s == "s" | _ => false)
      && (match Answer.read [("error", "access_denied"), ("state", "s")] with
        | .error e s => e == "access_denied" && s == some "s" | _ => false)
      && (Answer.read [("code", "c")] matches .malformed)
      && (Answer.read [] matches .malformed)),
    ("oauth: a discovery document gives a provider of OpenID Connect",
      let doc := "{\"issuer\":\"https://id.example\",\"authorization_endpoint\":\"https://id.example/a\",\
        \"token_endpoint\":\"https://id.example/t\",\"jwks_uri\":\"https://id.example/k\",\
        \"id_token_signing_alg_values_supported\":[\"RS256\",\"ES256\"],\
        \"code_challenge_methods_supported\":[\"S256\"]}"
      match Discovery.read doc with
      | some d =>
        let p := d.provider "id"
        d.algs == ["RS256", "ES256"] && d.challenges == ["S256"] && p.authorize == "https://id.example/a"
          && p.token == "https://id.example/t"
          && (match p.source with
            | .idToken issuers jwks => issuers == ["https://id.example"] && jwks == "https://id.example/k"
            | .userApi .. => false)
          && (Discovery.read "{\"issuer\":\"i\"}").isNone
      | none => false),
    ("oauth: the state of the provider's answer, an error's included",
      (Answer.read [("state", "s"), ("code", "c")]).state == some "s"
        && (Answer.read [("error", "e"), ("state", "s")]).state == some "s"
        && (Answer.read [("error", "e")]).state == none && (Answer.read []).state == none),
    ("oauth: a user API answers JSON with status 200, or the sign-in is refused",
      (userAnswer (some (.text "{\"id\":1}"))).toOption == some (Json.mkObj [("id", (1 : Nat))])
        && (match userAnswer (some (.text "{}" 401)) with
          | .error (.userApi "status 401") => true | _ => false)
        && (userAnswer (some (.text "not json")) matches .error (.userApi _))
        && (userAnswer none matches .error (.userApi _))),
    ("oauth: a refusal is answered 403 with its reason, and no value",
      let r := refusedResponse (.denied "access_denied")
      r.status == 403 && String.fromUTF8? r.body == some "sign-in refused: the provider said access_denied\n"
        && [OAuth.Refusal.unknownProvider, .unknownState, .otherBrowser, .otherProvider, .expired,
            .malformed, .token "x", .idToken .nonce, .userApi "y"].all (!·.describe.isEmpty)),
    ("oauth: the code is exchanged with the verifier and the client's secret",
      tokenForm client ⟨"c"⟩ ⟨"v"⟩ == [("grant_type", "authorization_code"), ("code", "c"),
        ("redirect_uri", client.redirect), ("client_id", "app"), ("client_secret", "s3cret"),
        ("code_verifier", "v")]),
    ("oauth: the token endpoint's answer: a bearer token and an ID token, or its error",
      (match Tokens.read 200 "{\"access_token\":\"a\",\"token_type\":\"Bearer\",\"id_token\":\"i\"}".toUTF8 with
        | .ok t => t.access == ⟨"a"⟩ && t.idToken == some ⟨"i"⟩ | _ => false)
      && (Tokens.read 200 "{\"access_token\":\"a\",\"token_type\":\"bearer\"}".toUTF8 matches .ok _)
      && (match Tokens.read 400 "{\"error\":\"invalid_grant\"}".toUTF8 with
        | .error (.token "invalid_grant") => true | _ => false)
      && (Tokens.read 200 "{\"access_token\":\"a\",\"token_type\":\"mac\"}".toUTF8 matches .error _)
      && (Tokens.read 500 "{\"access_token\":\"a\",\"token_type\":\"Bearer\"}".toUTF8 matches .error _)
      && (Tokens.read 200 "access_token=a".toUTF8 matches .error _)
      && (tokenAnswer none matches .error (.token _))) ]

def keysTests : List (String × Bool) :=
  let s : Settings := { minRefresh_ms := 100, maxAge_ms := 1000 }
  let k1 : Jose.Jwk := { kid := some "k1", key := .p256 .empty .empty }
  let held : Keys := { keys := [k1], fetched_ms := some 0 }
  let isFetch (l : Lookup) := l matches .fetch
  [ ("oauth keys: none fetched is a fetch", isFetch (({} : Keys).lookup s 0 none)),
    ("oauth keys: fresh keys with the kid are used",
      !isFetch (held.lookup s 999 (some "k1")) && !isFetch (held.lookup s 999 none)),
    ("oauth keys: a kid not held is fetched, but not within minRefresh_ms of the last fetch",
      !isFetch (held.lookup s 99 (some "k2")) && isFetch (held.lookup s 100 (some "k2"))),
    ("oauth keys: old keys are fetched again", isFetch (held.lookup s 1000 (some "k1"))),
    ("oauth keys: a fetch that gave nothing keeps the keys held and starts the wait again",
      let after := held.fetched 500 none
      after.keys.length == 1 && after.fetched_ms == some 500 && !isFetch (after.lookup s 599 (some "k2"))),
    ("oauth keys: an answer that is not a JWK Set gives no keys",
      (keysAnswer (some (.text "{}"))).isNone && (keysAnswer none).isNone
        && (keysAnswer (some (.text "{\"keys\":[]}" 404))).isNone
        && (keysAnswer (some (.text "{\"keys\":[]}"))).any (·.isEmpty)) ]

def claimTests : List (String × Bool) :=
  [ ("id token: claims that pass every check give the identity",
      match IdToken.check expect claims with
      | .ok id => id == {
          issuer := "https://id.example", subject := "u1", email := some "u@example.com",
          emailVerified := true }
      | .error _ => false),
    ("id token: another issuer is refused", checked { claims with iss := "https://evil" } == some .issuer),
    ("id token: another audience is refused", checked { claims with aud := ["other"] } == some .audience),
    ("id token: several audiences need this client as authorized party",
      checked { claims with aud := ["app", "other"], azp := none } == some .authorizedParty
        && checked { claims with aud := ["app", "other"] } == none
        && checked { claims with azp := some "other" } == some .authorizedParty
        && checked { claims with azp := none } == none),
    ("id token: expired beyond the skew is refused, within it accepted",
      checked { claims with exp := 940 } == some .expired && checked { claims with exp := 941 } == none),
    ("id token: not valid before a time beyond the skew is refused",
      checked { claims with nbf := some 1061 } == some .notYetValid
        && checked { claims with nbf := some 1060 } == none),
    ("id token: another nonce, or none, is refused",
      checked { claims with nonce := some "m" } == some .nonce
        && checked { claims with nonce := none } == some .nonce),
    ("id token: the claims are read with their types",
      readClaims "{\"iss\":\"i\",\"sub\":\"s\",\"aud\":\"a\",\"exp\":5}"
          == some { iss := "i", sub := "s", aud := ["a"], exp := 5 }
        && (readClaims "{\"iss\":\"i\",\"sub\":\"s\",\"aud\":[\"a\",\"b\"],\"exp\":5,\"nonce\":\"n\",\
            \"email\":\"e\",\"email_verified\":true}").any (·.aud == ["a", "b"])),
    ("id token: claims of other types, a fractional time or an empty subject are refused",
      [ "{\"iss\":\"i\",\"sub\":\"\",\"aud\":\"a\",\"exp\":5}",
        "{\"iss\":\"i\",\"sub\":\"s\",\"aud\":\"a\",\"exp\":5.5}",
        "{\"iss\":\"i\",\"sub\":\"s\",\"aud\":[1],\"exp\":5}",
        "{\"iss\":\"i\",\"sub\":\"s\",\"aud\":\"a\",\"exp\":\"5\"}",
        "{\"iss\":\"i\",\"sub\":\"s\",\"aud\":\"a\",\"exp\":5,\"email_verified\":\"true\"}",
        "{\"iss\":\"i\",\"sub\":\"s\",\"aud\":\"a\",\"exp\":5,\"nonce\":1}",
        "{\"sub\":\"s\",\"aud\":\"a\",\"exp\":5}", "[]", "" ].all (readClaims · |>.isNone)) ]

def edgeTests : List (String × Bool) :=
  let r : Request := {
    method := .get, path := ["sign-in", "id", "callback"], query := [("code", "c"), ("state", "s")],
    headers := [("x-lanes-identity-issuer", "forged"), ("x-lanes-identity-subject", "admin"),
      ("x-lanes-identity-email-verified", "true"), ("cookie", "a=b")] }
  let id : Identity := { issuer := "i", subject := "s", email := some "e", emailVerified := true }
  [ ("oauth edge: the routes of sign-in",
      route "sign-in" { method := .get, path := ["sign-in", "id"] } == .begin "id"
        && route "sign-in" r == .callback "id"
        && route "sign-in" { r with method := .post } == .other
        && route "sign-in" { method := .get, path := ["login", "id"] } == .other
        && route "sign-in" { method := .get, path := ["sign-in"] } == .other),
    ("oauth edge: identity headers a client sends are dropped, and the sign-in's read back",
      identity? r == some { issuer := "forged", subject := "admin", emailVerified := true }
        && identity? (strip r) == none && (strip r).header? "cookie" == some "a=b"
        && identity? (withIdentity (strip r) id) == some id
        && identity? (withIdentity (strip r) { id with email := none, emailVerified := false })
          == some { id with email := none, emailVerified := false }),
    ("oauth edge: the request that enters the system has no code", (withIdentity r id).query == []),
    ("oauth edge: the redirect sets a cookie for the sign-in's routes, HttpOnly, Lax, Secure",
      let response := beginResponse "sign-in" "lanes-sign-in" true {} "https://x" "v"
      response.status == 302 && response.headers.contains ("location", "https://x")
        && response.headers.contains ("set-cookie",
          "lanes-sign-in=v; Path=/sign-in; Max-Age=600; HttpOnly; Secure; SameSite=Lax")),
    ("oauth edge: a secret is never printed",
      toString (⟨"s3cret"⟩ : Secret) == "<secret>"
        && ((toString (repr client)).splitOn "s3cret").length == 1
        && ((toString (repr ({ access := ⟨"tok"⟩, idToken := some ⟨"idt"⟩ } : Tokens))).splitOn "tok").length == 1
        && ((toString (repr ((seed 0).entry "id" 0))).splitOn (b64 (seed 0).verifier)).length == 1),
    ("oauth edge: endpoints are parsed into calls",
      Endpoint.parse "https://oauth2.googleapis.com/token"
          == some { https := true, host := "oauth2.googleapis.com", port := 443, path := ["token"],
                    query := [] }
        && Endpoint.parse "http://127.0.0.1:8080/a/b%20c?x=1&y=2"
          == some { https := false, host := "127.0.0.1", port := 8080, path := ["a", "b c"],
                    query := [("x", "1"), ("y", "2")] }
        && (Endpoint.parse "https://api.github.com").any (·.path == [])
        && [ "ftp://a/b", "https://u@a/b", "https://a/b#f", "https://[::1]/", "/a", "https://a:0/" ].all
          (Endpoint.parse · |>.isNone)) ]

/-! The pending sign-ins as an actor, against two browsers: the victim's, 0, and an attacker's, 1.
A browser's cookie is the binding of the last sign-in it began. The attacker presents the victim's
state, and has the victim's browser present its own (login CSRF); each browser replays. -/

namespace Model

inductive In where
  | begin (state browser : Fin 2)
  | callback (browser state : Fin 2)
  deriving DecidableEq, Repr, Hashable

inductive Out where
  | accepted (browser state : Fin 2)
  | refused (browser state : Fin 2)
  deriving DecidableEq, Repr, Hashable

/-- `issued` and `accepted` are ghosts: pairs of a state and a browser. -/
structure State where
  pending : Pending := {}
  jar : List (Fin 2 × String) := []
  issued : List (Fin 2 × Fin 2) := []
  accepted : List (Fin 2 × Fin 2) := []
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

def entry (i : Fin 2) : Entry :=
  { state := s!"s{i}", binding := s!"k{i}", expires_ms := 10,
    grant := { provider := "p", nonce := "", verifier := ⟨""⟩ } }

/-- The edge's store, which a restart empties. -/
abbrev signIn : System sig where
  State _ := State
  actor _ :=
    { init := {}
      step := fun s msg =>
        match msg with
        | .begin i b =>
          ({ s with pending := s.pending.begin 2 0 (entry i), issued := (i, b) :: s.issued,
                    jar := (b, (entry i).binding) :: s.jar.filter (·.1 != b) }, [])
        | .callback b i =>
          let (pending, answer) :=
            s.pending.callback 0 "p" ((s.jar.lookup b).getD "") (entry i).state
          match answer with
          | .ok _ => ({ s with pending, accepted := (i, b) :: s.accepted }, [.emit (.accepted b i)])
          | .error _ => ({ s with pending }, [.emit (.refused b i)])
      recover := fun s => ({ s with pending := {} }, []) }
  accept x := ⟨(), x⟩

instance : sig.Inspect := {}
instance : signIn.Inspect := {}

def crashing : EnvModel sig where
  mayCrash _ := true

def check (maxCrashes : Nat) :=
  Check.system signIn
    { env := crashing, maxCrashes
      driver := Driver.anyOrder [.begin 0 0, .callback 0 0, .callback 0 0, .callback 1 0,
        .begin 1 1, .callback 0 1] }
    [ .always "no state is accepted more often than it was issued" fun w =>
        let s := w.state.state ()
        [0, 1].all fun (i : Fin 2) =>
          (s.accepted.filter (·.1 == i)).length ≤ (s.issued.filter (·.1 == i)).length,
      .always "a state is accepted only from the browser it was issued to" fun w =>
        let s := w.state.state ()
        s.accepted.all (s.issued.contains ·),
      .sometimes "the victim signs in" fun w => w.state.outbox.contains (.accepted 0 0),
      .sometimes "a replay is refused" fun w =>
        w.state.outbox.contains (.accepted 0 0) && w.state.outbox.contains (.refused 0 0),
      .sometimes "the attacker's browser is refused the victim's state" fun w =>
        w.state.outbox.contains (.refused 1 0) ]

end Model

def modelTests : List (String × Bool) :=
  let r := Model.check 1
  [ ("oauth model: no replay and no state from another browser, under every order and a restart",
      r.ok && r.complete),
    ("oauth model: the check is not vacuous: a sign-in, a replay refused, the attacker refused",
      r.witnesses.length == 3) ]

def tests : List (String × Bool) := flowTests ++ keysTests ++ claimTests ++ edgeTests ++ modelTests

/-! ## End to end, against the test kit's provider (`Lanes/Testing/OAuth.lean`) -/

open Lanes.Testing
open Lanes.Testing.OAuth (Fake Token User)

/-- Answers what the sign-in let in: the identity it verified, and whether a query came with it. -/
def appBridge : Bridge Tests.Gate.echoSig where
  decode _ r :=
    match identity? r with
    | some id => .error (.text s!"{id.issuer} {id.subject} {id.email} {id.emailVerified} \
        query={r.query.length}")
    | none => .error (.text "who?" 401)
  encode id := some (id, .text "ok")

def origin : String := "http://app.example"

def user : User := { subject := "user-1", email := some "u@example.com" }

/-- Begins a sign-in in a browser of its own, plays the user who agrees at the provider, which
then issues a code whose ID token is as `token` says, and calls the callback back, with the
sign-in's cookie, or `cookie` in its place, and the state, or `state` in its place. The
callback's answer is given, with its query and the cookie, to try again. -/
def flow (app : UInt16) (p : Fake) (name : String) (token : Token) (who : User := user)
    (cookie : Option String := none) (state : Option String := none) :
    Async (Option Response × List (String × String) × String) := do
  let b ← Browser.new app origin
  let begun ← b.get ["sign-in", name]
  let binding := (← b.cookie "lanes-sign-in").getD ""
  if let some c := cookie then b.keep { name := "lanes-sign-in", value := c, path := "/sign-in" }
  let query := (← p.approve (location begun) who token).map fun (k, v) =>
    if k == "state" then (k, state.getD v) else (k, v)
  return (← b.get ["sign-in", name, "callback"] query, query, binding)

def refused (r : Option Response) (why : String) : Bool :=
  status r == 403 && shows r why

def live : Async (List (String × Bool)) := do
  unless ← Testing.OAuth.hasOpenssl do
    IO.println "oauth: skipped the flow end to end, there is no openssl command"
    return []
  let p ← Fake.start
  try
    let signIn ← SignIn.start {
      providers := [(p.oidc "id", p.client origin "id"), (p.userApi "hub", p.client origin "hub")]
      secure := false, http := { timeout_ms := 5000 } }
    let app ← serve (Server.system Tests.Web.mute) appBridge { port := 0 }
      (arrive := some signIn.arrive)
    let some appPort := app.port | return [("oauth: the application listens", false)]
    try
      let (good, query, binding) ← flow appPort p "id" .good
      let again ← Browser.new appPort origin
      again.keep { name := "lanes-sign-in", value := binding, path := "/sign-in" }
      let replay ← again.get ["sign-in", "id", "callback"] query
      let (wrongState, _, _) ← flow appPort p "id" .good (state := some "forged")
      let (otherBrowser, _, _) ← flow appPort p "id" .good (cookie := some "other")
      let (expired, _, _) ← flow appPort p "id" .expired
      let (audience, _, _) ← flow appPort p "id" .wrongAudience
      let (issuer, _, _) ← flow appPort p "id" .wrongIssuer
      let (nonce, _, _) ← flow appPort p "id" .wrongNonce
      let (none_, _, _) ← flow appPort p "id" .algNone
      let (hs256, _, _) ← flow appPort p "id" .hs256
      let (unknownKid, _, _) ← flow appPort p "id" .unknownKid
      let (tampered, _, _) ← flow appPort p "id" .tampered
      let fetches ← p.jwksFetches.get
      let viaApi ← Testing.OAuth.signIn (← Browser.new appPort origin) p "hub"
        { subject := "42", login := "octo", email := some "o@example.com" }
      let anon ← Browser.new appPort origin
      let forged ← anon.get [] (headers := [("x-lanes-identity-issuer", "https://id.example"),
        ("x-lanes-identity-subject", "admin"), ("x-lanes-identity-email-verified", "true")])
      let denied ← anon.get ["sign-in", "id", "callback"] [("error", "access_denied"), ("state", "s")]
      let begun ← anon.get ["sign-in", "id"]
      return [
        ("oauth live: a sign-in is begun with a redirect and a cookie for the sign-in's routes",
          begun.any fun r => r.status == 302
            && (r.headers.lookup "set-cookie").any (·.endsWith "Path=/sign-in; Max-Age=600; HttpOnly; SameSite=Lax")),
        ("oauth live: an OpenID Connect sign-in gives the system the identity, and not the code",
          status good == 200
            && text good == "https://id.example user-1 (some u@example.com) true query=0"),
        ("oauth live: the same callback again is refused", refused replay "no sign-in waits"),
        ("oauth live: a state never issued is refused", refused wrongState "no sign-in waits"),
        ("oauth live: a callback from another browser is refused", refused otherBrowser "another browser"),
        ("oauth live: an expired ID token is refused", refused expired "expired"),
        ("oauth live: an ID token for another audience is refused", refused audience "audience"),
        ("oauth live: an ID token from another issuer is refused", refused issuer "issuer"),
        ("oauth live: an ID token for another nonce is refused", refused nonce "nonce"),
        ("oauth live: an ID token with alg none is refused", refused none_ "alg \"none\""),
        ("oauth live: HS256 with the RSA public key as its secret is refused",
          refused hs256 "alg \"HS256\""),
        ("oauth live: an ID token of a kid the set lacks is refused", refused unknownKid "unknownKey"),
        ("oauth live: an ID token whose payload was changed is refused", refused tampered "signature"),
        ("oauth live: the JWK Set is fetched once, an unknown kid within the wait included",
          fetches == 1),
        ("oauth live: a provider without ID tokens is asked its user API with the access token",
          text viaApi == "https://hub.example 42 (some o@example.com) true query=0"),
        ("oauth live: identity headers a client sends do not reach the system", status forged == 401),
        ("oauth live: the provider's error is a refusal", refused denied "access_denied") ]
    finally
      app.stop
  finally
    p.stop

end Tests.OAuth
