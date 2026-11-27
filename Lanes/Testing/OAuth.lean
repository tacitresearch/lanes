/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Testing.Browser

/-!
A fake identity provider for tests, on a local port, of both kinds `Lanes.OAuth` signs in with:
OpenID Connect, whose token endpoint gives an ID token signed with RS256 under an RSA key made by
the `openssl` command, with a JWK Set; and OAuth 2.0 with a user API shaped as GitHub's
(`/api/user`, `/api/emails`). The test plays the user at the authorization endpoint:
`Fake.approve` reads the redirect a sign-in began with and issues a code for a user. The token
endpoint checks what a provider checks: the code is one it issued and not used before, for this
client and secret, for the redirect URI it was issued to, with the PKCE verifier of its
challenge. A code may be issued for a faulty ID token (`Token`), which the sign-in must refuse.
-/

@[expose] public section

namespace Lanes.Testing.OAuth

open Lanes Lanes.Http Lanes.OAuth Std Std.Async

/-- Whom the provider signs in. -/
structure User where
  /-- The provider's number or name for the user: an ID token's `sub`, the user API's `id`. -/
  subject : String
  /-- The user API's `login`. -/
  login : String := subject
  name : Option String := none
  email : Option String := some (subject ++ "@example.com")
  emailVerified : Bool := true

/-- What the token endpoint puts in the ID token of a code. -/
inductive Token where
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

/-- A code the provider issued. -/
structure Code where
  user : User
  token : Token
  nonce : String
  challenge : String
  redirect : String
  used : Bool := false

structure Fake where
  server : TCP.Socket.Server
  port : UInt16
  /-- The directory of the RSA key, `key.pem` and `pub.pem`, and of the JWK Set; none without
  the `openssl` command, and then no ID token is issued. -/
  keys : Option System.FilePath
  codes : IO.Ref (List (String × Code))
  issued : IO.Ref Nat
  jwksFetches : IO.Ref Nat
  /-- The issuer its ID tokens name. -/
  issuer : String
  clientId : String
  clientSecret : String

def hasOpenssl : IO Bool := do
  try return (← IO.Process.output { cmd := "openssl", args := #["version"] }).exitCode == 0
  catch _ => return false

/-- What `openssl args` prints, run in `dir`; an error when it fails. -/
def openssl (dir : System.FilePath) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := "openssl", args, cwd := dir }
  unless out.exitCode == 0 do throw (.userError s!"openssl {args}: {out.stderr}")
  return out.stdout

def Fake.at (f : Fake) (path : String) : String := s!"http://127.0.0.1:{f.port}/{path}"

/-- The provider of OpenID Connect, to sign in with as `name`. -/
def Fake.oidc (f : Fake) (name : String := "id") (scopes : List String := ["openid", "email"]) :
    Provider :=
  { name, authorize := "https://id.example/authorize", token := f.at "oidc/token", scopes
    source := .idToken [f.issuer] (f.at "oidc/jwks") }

def yes (j : Json) (key : String) : Bool := (j.getObjValAs? Bool key).toOption == some true

/-- An identity of the user API's answers, as GitHub's integration reads GitHub's: the user's
`id`, the primary address if it is verified, the `name` or else the `login`. -/
def readUser (issuer : String) : List Json → Except String Identity
  | [user, emails] => do
    let subject ← match user.getObjValAs? Nat "id" with
      | .ok n => pure (toString n)
      | .error _ => user.getObjValAs? String "id"
    let primary := match emails with
      | .arr all => all.toList.find? (yes · "primary")
      | _ => none
    let name := ((user.getObjValAs? String "name").toOption.bind DisplayName.clean).orElse
      fun _ => (user.getObjValAs? String "login").toOption.bind DisplayName.clean
    return {
      issuer, subject, email := primary.bind fun e => (e.getObjValAs? String "email").toOption,
      emailVerified := primary.any (yes · "verified"), name }
  | _ => .error "two answers expected"

/-- The provider with a user API, to sign in with as `name`; its answers are read by `read`. -/
def Fake.userApi (f : Fake) (name : String := "hub")
    (read : List Json → Except String Identity := readUser "https://hub.example") : Provider :=
  { name, authorize := "https://hub.example/authorize", token := f.at "api/token"
    scopes := ["read:user"], source := .userApi [f.at "api/user", f.at "api/emails"] read }

/-- The client the provider knows, for a site at `origin`, signing in as `name`. -/
def Fake.client (f : Fake) (origin name : String) : Client :=
  { id := f.clientId, secret := ⟨f.clientSecret⟩, redirect := s!"{origin}/sign-in/{name}/callback" }

def b64s (s : String) : String := b64 s.toUTF8

def str (s : String) : String := Json.renderString s

def nowSeconds : IO Nat :=
  return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.toInt.toNat / 1000

/-- An ID token for the code, signed with the provider's key, or faulty as the code says. -/
def Fake.mint (f : Fake) (dir : System.FilePath) (c : Code) : IO String := do
  let now ← nowSeconds
  let kind := c.token
  let iss := if kind == .wrongIssuer then "https://evil.example" else f.issuer
  let aud := if kind == .wrongAudience then "other" else f.clientId
  let exp := if kind == .expired then now - 3600 else now + 600
  let nonce := if kind == .wrongNonce then "forged" else c.nonce
  let u := c.user
  let payload (sub : String) :=
    s!"\{\"iss\":{str iss},\"sub\":{str sub},\"aud\":{str aud},\"azp\":{str aud},\"exp\":{exp},\
      \"iat\":{now},\"nonce\":{str nonce}"
      ++ ((u.email.map fun e => s!",\"email\":{str e},\"email_verified\":{u.emailVerified}").getD "")
      ++ ((u.name.map fun n => s!",\"name\":{str n}").getD "") ++ "}"
  let header := match kind with
    | .algNone => "{\"alg\":\"none\",\"kid\":\"k1\"}"
    | .hs256 => "{\"alg\":\"HS256\",\"kid\":\"k1\"}"
    | .unknownKid => "{\"alg\":\"RS256\",\"kid\":\"k9\"}"
    | _ => "{\"alg\":\"RS256\",\"kid\":\"k1\",\"typ\":\"JWT\"}"
  let input := b64s header ++ "." ++ b64s (payload u.subject)
  let signature ← match kind with
    | .algNone => pure ByteArray.empty
    | .hs256 => pure (hmac (← IO.FS.readBinFile (dir / "pub.pem")) input.toUTF8)
    | .good | .expired | .wrongAudience | .wrongIssuer | .wrongNonce | .unknownKid | .tampered => do
      let n ← f.issued.modifyGet fun n => (n, n + 1)
      IO.FS.writeFile (dir / s!"msg-{n}") input
      discard <| openssl dir #["dgst", "-sha256", "-sign", "key.pem", "-out", s!"sig-{n}", s!"msg-{n}"]
      IO.FS.readBinFile (dir / s!"sig-{n}")
  let body := if kind == .tampered then b64s (payload "admin") else b64s (payload u.subject)
  return b64s header ++ "." ++ body ++ "." ++ b64 signature

/-- The user API's answer of `/api/user`: `id` a number when the subject is one. -/
def userJson (u : User) : String :=
  let id := if u.subject.toNat?.isSome then u.subject else str u.subject
  s!"\{\"id\":{id},\"login\":{str u.login},\"name\":{(u.name.map str).getD "null"}}"

def emailsJson (u : User) : String :=
  match u.email with
  | some e => s!"[\{\"email\":{str e},\"primary\":true,\"verified\":{u.emailVerified}}]"
  | none => "[]"

/-- Takes the code named, once: the second time it is marked used. -/
def Fake.take (f : Fake) (code : String) : IO (Option Code) :=
  f.codes.modifyGet fun codes =>
    match codes.lookup code with
    | some c => (some c, (code, { c with used := true }) :: codes.filter (·.1 != code))
    | none => (none, codes)

def Fake.user? (f : Fake) (r : Request) : IO (Option User) := do
  let some auth := r.header? "authorization" | return none
  let [_, code] := auth.splitOn "Bearer at-" | return none
  return ((← f.codes.get).lookup code).map (·.user)

/-- The token endpoint, the JWK Set and the user API. -/
def Fake.handle (f : Fake) (r : Request) : IO Response := do
  match r.method, r.path with
  | .get, ["oidc", "jwks"] =>
    f.jwksFetches.modify (· + 1)
    match f.keys with
    | some dir => return json (← IO.FS.readFile (dir / "jwks.json"))
    | none => return json "{\"keys\":[]}"
  | .post, [kind, "token"] =>
    let form := parseForm ((String.fromUTF8? r.body).getD "")
    let field (name : String) := form.lookup name
    let code := (field "code").getD ""
    let some c ← f.take code | return json "{\"error\":\"invalid_grant\"}" 400
    unless !c.used && field "grant_type" == some "authorization_code"
        && field "client_id" == some f.clientId && field "client_secret" == some f.clientSecret
        && field "redirect_uri" == some c.redirect
        && (field "code_verifier").any (challenge · == c.challenge) do
      return json "{\"error\":\"invalid_grant\"}" 400
    if kind == "api" then
      return json s!"\{\"access_token\":\"at-{code}\",\"token_type\":\"bearer\"}"
    let some dir := f.keys | return json "{\"error\":\"server_error\"}" 500
    return json s!"\{\"access_token\":\"at-{code}\",\"token_type\":\"Bearer\",\"expires_in\":3600,\
      \"id_token\":\"{← f.mint dir c}\"}"
  | .get, ["api", "user"] =>
    match ← f.user? r with
    | some u => return json (userJson u)
    | none => return json "{\"message\":\"Bad credentials\"}" 401
  | .get, ["api", "emails"] =>
    match ← f.user? r with
    | some u => return json (emailsJson u)
    | none => return json "{\"message\":\"Bad credentials\"}" 401
  | _, _ => return .text "not found" 404

/-- Makes the provider's RSA key and its JWK Set in `dir`, with a second key of another type
under the same `kid`, which a sign-in must not take for it. -/
def makeKeys (dir : System.FilePath) : IO Unit := do
  discard <| openssl dir #["genrsa", "-out", "key.pem", "2048"]
  discard <| openssl dir #["rsa", "-in", "key.pem", "-pubout", "-out", "pub.pem"]
  let printed ← openssl dir #["rsa", "-in", "key.pem", "-noout", "-modulus"]
  let n := b64 ((Bytes.unhex? ((printed.trimAscii.toString.drop 8).toString.toLower)).getD .empty)
  IO.FS.writeFile (dir / "jwks.json") s!"\{\"keys\":[\{\"kty\":\"RSA\",\"kid\":\"k1\",\
    \"use\":\"sig\",\"alg\":\"RS256\",\"n\":\"{n}\",\"e\":\"AQAB\"},\
    \{\"kty\":\"oct\",\"kid\":\"k1\",\"k\":\"c2VjcmV0\"}]}"

/-- The provider on a local port. With `oidc` and the `openssl` command it makes a key, in a
directory of its own that `stop` removes, and issues ID tokens. -/
def Fake.start (oidc : Bool := true) (clientId : String := "app")
    (clientSecret : String := "s3cret") (issuer : String := "https://id.example") : Async Fake := do
  let keys ← if oidc && (← hasOpenssl) then do
      let dir : System.FilePath :=
        s!"{(← IO.getEnv "TMPDIR").getD "/tmp"}/lanes-provider-{← IO.monoNanosNow}"
      IO.FS.createDirAll dir
      makeKeys dir
      pure (some dir)
    else pure none
  let codes ← IO.mkRef []
  let issued ← IO.mkRef 0
  let jwksFetches ← IO.mkRef 0
  let handler ← IO.mkRef (fun (_ : Request) => (pure (.text "starting" 503) : IO Response))
  let (server, port) ← listen fun r => do (← handler.get) r
  let f : Fake := { server, port, keys, codes, issued, jwksFetches, issuer, clientId, clientSecret }
  handler.set f.handle
  return f

def Fake.stop (f : Fake) : Async Unit := do
  f.server.close
  if let some dir := f.keys then IO.FS.removeDirAll dir

/-- Plays the user who agrees at the authorization endpoint the redirect `location` names:
issues a code for `user`, whose ID token is as `token` says, and gives the callback's query,
the code and the state the redirect carried. -/
def Fake.approve (f : Fake) (location : String) (user : User) (token : Token := .good) :
    IO (List (String × String)) := do
  let q := queryOf location
  let get (name : String) := (q.lookup name).getD ""
  let n ← f.issued.modifyGet fun n => (n, n + 1)
  let code := s!"code-{n}"
  f.codes.modify ((code, {
    user, token, nonce := get "nonce", challenge := get "code_challenge"
    redirect := get "redirect_uri" }) :: ·)
  return [("code", code), ("state", get "state")]

/-- Signs `b` in with `provider` as `user`, as a browser: begins at `/sign-in/<provider>`,
agrees at the provider, and comes back to the callback with the ticket the beginning set in its
cookie (`__Host-lanes-sign-in` over HTTPS), which the browser keeps. The callback's answer is
given, with the session cookie it sets kept by the browser. -/
def signIn (b : Browser) (f : Fake) (provider : String) (user : User) (token : Token := .good) :
    Async (Option Response) := do
  let begun ← b.get ["sign-in", provider]
  let query ← f.approve (location begun) user token
  b.get ["sign-in", provider, "callback"] query

end Lanes.Testing.OAuth
