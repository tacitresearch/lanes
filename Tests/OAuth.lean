/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Signature
import Tests.Web

/-!
Sign-in with another service (`Lanes/Web/Auth/OAuth.lean`, `Lanes/Web/IO/SignIn.lean`). The pure
decisions one by one; the pending sign-ins as an actor, model-checked against two browsers, one of
them an attacker's, that replay and swap callbacks; and the whole flow end to end over HTTP,
against a provider run in the test: an authorization endpoint the test plays, a token endpoint
that checks PKCE and signs ID tokens with an RSA key made by `openssl`, a JWK Set, and a user API
for a provider without ID tokens. No real provider is called.
-/

namespace Tests.OAuth

open Lanes Lanes.OAuth Lanes.Http Std Std.Async

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

/-- The query of a URL, decoded. -/
def queryOf (url : String) : List (String × String) :=
  ((Url.parse url).bind (·.query)).map parseForm |>.getD []

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

/-! ## End to end, against a provider run in the test -/

/-- What the provider's token endpoint puts in the ID token of a code. -/
inductive Kind where
  | good
  | expired
  | wrongAudience
  | wrongIssuer
  | wrongNonce
  | algNone
  /-- HS256, with the provider's RSA public key, as PEM, for the HMAC secret. -/
  | hs256
  | unknownKid
  /-- The payload changed after it was signed. -/
  | tampered
  deriving DecidableEq, Repr

structure Code where
  kind : Kind
  nonce : String
  challenge : String
  provider : String
  used : Bool := false

structure Provider' where
  dir : System.FilePath
  codes : IO.Ref (List (String × Code))
  jwksFetches : IO.Ref Nat
  issuer : String
  jwks : String

def b64s (s : String) : String := b64 s.toUTF8

def sign (dir : System.FilePath) (input : String) : IO ByteArray := do
  IO.FS.writeFile (dir / "msg") input
  Tests.Signature.run dir #["dgst", "-sha256", "-sign", "key.pem", "-out", "out", "msg"]

def mint (p : Provider') (kind : Kind) (nonce : String) : IO String := do
  let now := (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.toInt.toNat / 1000
  let iss := if kind == .wrongIssuer then "https://evil.example" else p.issuer
  let aud := if kind == .wrongAudience then "other" else "app"
  let exp := if kind == .expired then now - 3600 else now + 600
  let nonce := if kind == .wrongNonce then "forged" else nonce
  let payload (sub : String) :=
    s!"\{\"iss\":\"{iss}\",\"sub\":\"{sub}\",\"aud\":\"{aud}\",\"azp\":\"{aud}\",\"exp\":{exp},\
      \"iat\":{now},\"nonce\":\"{nonce}\",\"email\":\"u@example.com\",\"email_verified\":true}"
  let header := match kind with
    | .algNone => "{\"alg\":\"none\",\"kid\":\"k1\"}"
    | .hs256 => "{\"alg\":\"HS256\",\"kid\":\"k1\"}"
    | .unknownKid => "{\"alg\":\"RS256\",\"kid\":\"k9\"}"
    | _ => "{\"alg\":\"RS256\",\"kid\":\"k1\",\"typ\":\"JWT\"}"
  let input := b64s header ++ "." ++ b64s (payload "user-1")
  let pem ← IO.FS.readBinFile (p.dir / "pub.pem")
  let signature ← match kind with
    | .algNone => pure ByteArray.empty
    | .hs256 => pure (hmac pem input.toUTF8)
    | .good | .expired | .wrongAudience | .wrongIssuer | .wrongNonce | .unknownKid | .tampered =>
      sign p.dir input
  let body := if kind == .tampered then b64s (payload "admin") else b64s (payload "user-1")
  return b64s header ++ "." ++ body ++ "." ++ b64 signature

def json (body : String) (status : Nat := 200) : Response :=
  Response.ofText "application/json" body status

/-- The provider: `/token` and `/hub/token`, `/jwks`, and a user API at `/hub/user` and
`/hub/emails` for the provider without ID tokens. -/
def handle (p : Provider') (r : Request) : IO Response := do
  match r.method, r.path with
  | .get, ["jwks"] =>
    p.jwksFetches.modify (· + 1)
    return json (← IO.FS.readFile (p.dir / "jwks.json"))
  | .post, [_, "token"] | .post, ["token"] =>
    let form := parseForm ((String.fromUTF8? r.body).getD "")
    let field (name : String) := get form name
    let code := (field "code").getD ""
    let found ← p.codes.modifyGet fun codes =>
      match codes.lookup code with
      | some c => (some c, (code, { c with used := true }) :: codes.filter (·.1 != code))
      | none => (none, codes)
    let some c := found | return json "{\"error\":\"invalid_grant\"}" 400
    let redirect := s!"{if c.provider == "hub" then "hub" else "id"}"
    unless !c.used && field "grant_type" == some "authorization_code"
        && field "client_id" == some "app" && field "client_secret" == some "s3cret"
        && (field "redirect_uri").any (·.endsWith s!"/sign-in/{redirect}/callback")
        && (field "code_verifier").any (challenge · == c.challenge) do
      return json "{\"error\":\"invalid_grant\"}" 400
    if c.provider == "hub" then
      return json s!"\{\"access_token\":\"at-{code}\",\"token_type\":\"bearer\"}"
    return json s!"\{\"access_token\":\"at-{code}\",\"token_type\":\"Bearer\",\"expires_in\":3600,\
      \"id_token\":\"{← mint p c.kind c.nonce}\"}"
  | .get, ["hub", "user"] =>
    if (r.header? "authorization").any (·.startsWith "Bearer at-") then
      return json "{\"id\":42,\"login\":\"octo\"}"
    return json "{\"message\":\"Bad credentials\"}" 401
  | .get, ["hub", "emails"] =>
    return json "[{\"email\":\"o@example.com\",\"primary\":true,\"verified\":true}]"
  | _, _ => return .text "not found" 404

/-- A server of `handle`, a request a connection. -/
def fake (handler : Request → IO Response) : Async (TCP.Socket.Server × UInt16) := do
  let server ← TCP.Socket.Server.mk
  server.bind (.v4 ⟨.ofParts 127 0 0 1, 0⟩)
  server.listen 16
  let port := (← server.getSockName).port
  background do
    try
      repeat
        let client ← server.accept
        background do
          try
            let mut got := ByteArray.empty
            repeat
              let some bytes ← client.recv? 65536 | break
              got := got ++ bytes
              match Request.read {} got 0 with
              | .done incoming _ =>
                client.send (Response.wire (← handler incoming.request))
                break
              | .more => pure ()
              | .refuse _ => break
          catch _ => pure ()
          client.close
    catch _ => pure ()
  return (server, port)

/-- The user API's answers, as an integration reads them: the user's number, and the primary
address if it is verified. -/
def yes (j : Json) (key : String) : Bool := (j.getObjValAs? Bool key).toOption == some true

def readHub : List Json → Except String Identity
  | [user, emails] => do
    let id ← user.getObjValAs? Nat "id"
    let primary := match emails with
      | .arr all => all.toList.find? (yes · "primary")
      | _ => none
    return {
      issuer := "https://hub.example", subject := toString id,
      email := primary.bind fun e => (e.getObjValAs? String "email").toOption,
      emailVerified := primary.any (yes · "verified") }
  | _ => .error "two answers expected"

/-- Answers what the sign-in let in: the identity it verified, and whether a query came with it. -/
def appBridge : Bridge Tests.Gate.echoSig where
  decode _ r :=
    match identity? r with
    | some id => .error (.text s!"{id.issuer} {id.subject} {id.email} {id.emailVerified} \
        query={r.query.length}")
    | none => .error (.text "who?" 401)
  encode id := some (id, .text "ok")

def browse (port : UInt16) (path : List String) (query : List (String × String) := [])
    (headers : List (String × String) := []) : Async (Option Response) :=
  Client.exchange { host := "127.0.0.1", port, request := { method := .get, path, query, headers } }
    { timeout_ms := 10000 }

def body (r : Option Response) : String :=
  (r.bind fun r => String.fromUTF8? r.body).getD ""

/-- Begins a sign-in as a browser, plays the user who agrees at the provider, which then issues a
code of `kind`, and calls the callback back. The first response is the callback's; the state,
the cookie and the code are given back to try again. -/
def flow (app : UInt16) (p : Provider') (name : String) (kind : Kind) (n : Nat)
    (cookie : Option String := none) (state : Option String := none) :
    Async (Option Response × String × String × String) := do
  let some begun ← browse app ["sign-in", name] | return (none, "", "", "")
  let location := (begun.headers.lookup "location").getD ""
  let binding := ((begun.headers.lookup "set-cookie").getD "").takeWhile (· != ';')
    |>.toString |>.drop "lanes-sign-in=".length |>.toString
  let q := queryOf location
  let code := s!"code-{n}"
  let issue : Code := {
    kind, nonce := (get q "nonce").getD "", provider := name,
    challenge := (get q "code_challenge").getD "" }
  p.codes.modify ((code, issue) :: ·)
  let issued := (get q "state").getD ""
  let answer ← browse app ["sign-in", name, "callback"]
    [("code", code), ("state", state.getD issued)]
    [("cookie", s!"lanes-sign-in={cookie.getD binding}")]
  return (answer, issued, binding, code)

def refused (r : Option Response) (why : String) : Bool :=
  r.any (·.status == 403) && ((body r).splitOn why).length > 1

def live : Async (List (String × Bool)) := do
  unless ← Tests.Tls.hasOpenssl do
    IO.println "oauth: skipped the flow end to end, there is no openssl command"
    return []
  let dir : System.FilePath :=
    s!"{(← IO.getEnv "TMPDIR").getD "/tmp"}/lanes-oauth-{← IO.monoNanosNow}"
  IO.FS.createDirAll dir
  let servers ← IO.mkRef ([] : List TCP.Socket.Server)
  try
    Tests.Tls.run dir #["genrsa", "-out", "key.pem", "2048"]
    Tests.Tls.run dir #["rsa", "-in", "key.pem", "-pubout", "-out", "pub.pem"]
    let printed ← IO.Process.run
      { cmd := "openssl", args := #["rsa", "-in", "key.pem", "-noout", "-modulus"], cwd := dir }
    let n := b64 (Tests.Signature.modulus printed)
    IO.FS.writeFile (dir / "jwks.json") s!"\{\"keys\":[\{\"kty\":\"RSA\",\"kid\":\"k1\",\
      \"use\":\"sig\",\"alg\":\"RS256\",\"n\":\"{n}\",\"e\":\"AQAB\"},\
      \{\"kty\":\"oct\",\"kid\":\"k1\",\"k\":\"c2VjcmV0\"}]}"
    let providerState : Provider' := {
      dir, codes := ← IO.mkRef [], jwksFetches := ← IO.mkRef 0, issuer := "https://id.example",
      jwks := "" }
    let (fakeServer, fakePort) ← fake (handle providerState)
    servers.modify (fakeServer :: ·)
    let at_ (path : String) := s!"http://127.0.0.1:{fakePort}/{path}"
    let id : Provider := {
      name := "id", authorize := "https://id.example/authorize", token := at_ "token",
      scopes := ["openid", "email"], source := .idToken ["https://id.example"] (at_ "jwks") }
    let hub : Provider := {
      name := "hub", authorize := "https://hub.example/authorize", token := at_ "hub/token",
      scopes := ["read:user"], source := .userApi [at_ "hub/user", at_ "hub/emails"] readHub }
    let appClient (name : String) : Client := {
      id := "app", secret := ⟨"s3cret"⟩, redirect := s!"http://app.example/sign-in/{name}/callback" }
    let signIn ← SignIn.start {
      providers := [(id, appClient "id"), (hub, appClient "hub")], secure := false,
      http := { timeout_ms := 5000 } }
    let app ← serve (Server.system Tests.Web.mute) appBridge { port := 0 }
      (arrive := some signIn.arrive)
    let some appPort := app.port | return [("oauth: the application listens", false)]
    try
      let (good, state, binding, code) ← flow appPort providerState "id" .good 1
      let replay ← browse appPort ["sign-in", "id", "callback"] [("code", code), ("state", state)]
        [("cookie", s!"lanes-sign-in={binding}")]
      let (wrongState, _, _, _) ← flow appPort providerState "id" .good 2 (state := some "forged")
      let (otherBrowser, _, _, _) ← flow appPort providerState "id" .good 3 (cookie := some "other")
      let (expired, _, _, _) ← flow appPort providerState "id" .expired 4
      let (audience, _, _, _) ← flow appPort providerState "id" .wrongAudience 5
      let (issuer, _, _, _) ← flow appPort providerState "id" .wrongIssuer 6
      let (nonce, _, _, _) ← flow appPort providerState "id" .wrongNonce 7
      let (none_, _, _, _) ← flow appPort providerState "id" .algNone 8
      let (hs256, _, _, _) ← flow appPort providerState "id" .hs256 9
      let (unknownKid, _, _, _) ← flow appPort providerState "id" .unknownKid 10
      let (tampered, _, _, _) ← flow appPort providerState "id" .tampered 11
      let fetches ← providerState.jwksFetches.get
      let (viaApi, _, _, _) ← flow appPort providerState "hub" .good 12
      let forged ← browse appPort [] [] [("x-lanes-identity-issuer", "https://id.example"),
        ("x-lanes-identity-subject", "admin"), ("x-lanes-identity-email-verified", "true")]
      let denied ← browse appPort ["sign-in", "id", "callback"]
        [("error", "access_denied"), ("state", "s")]
      let begun ← browse appPort ["sign-in", "id"]
      return [
        ("oauth live: a sign-in is begun with a redirect and a cookie for the sign-in's routes",
          begun.any fun r => r.status == 302
            && (r.headers.lookup "set-cookie").any (·.endsWith "Path=/sign-in; Max-Age=600; HttpOnly; SameSite=Lax")),
        ("oauth live: an OpenID Connect sign-in gives the system the identity, and not the code",
          good.any (·.status == 200)
            && body good == "https://id.example user-1 (some u@example.com) true query=0"),
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
          body viaApi == "https://hub.example 42 (some o@example.com) true query=0"),
        ("oauth live: identity headers a client sends do not reach the system",
          forged.any (·.status == 401)),
        ("oauth live: the provider's error is a refusal", refused denied "access_denied") ]
    finally
      app.stop
  finally
    for server in ← servers.get do server.close
    IO.FS.removeDirAll dir

end Tests.OAuth
