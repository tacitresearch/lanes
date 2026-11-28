/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Auth.OAuth
public import Lanes.Web.IO.Client

/-!
Sign-in with another service, performed: what `Lanes/Web/Auth/OAuth.lean` decides, done where a
request arrives, before the system sees it (`serve`'s `arrive`). It draws the random bytes and
the key that tags the browsers' tickets, keeps the states used and the providers' keys, and calls
the token endpoint, the JWK Set and the user API through the HTTP client. A request to begin is answered here with the redirect; a
callback enters the system with the identity verified in its headers (`OAuth.identity?`) and
without its code, or is answered here with the refusal. So no code, token or secret reaches the
system, and nothing here is printed.

A sign-in begun is kept by the browser, in its cookie. The key and the states used live in
memory: after a restart the callbacks of sign-ins begun before are refused, as tagged by another
key, and the user begins again.
-/

public section

namespace Lanes.OAuth

open Std.Async Lanes.Http

structure SignIn.Config where
  providers : List (Provider × Client)
  settings : Settings := {}
  /-- The first segment of the sign-in's routes. -/
  pathPrefix : String := "sign-in"
  /-- The cookie that binds a sign-in to the browser it was begun in, `__Host-` before it when
  `secure`. -/
  cookie : String := "lanes-sign-in"
  /-- Whether that cookie is sent over HTTPS only; `false` only to test over plain HTTP. -/
  secure : Bool := true
  http : Client.Config := {}

structure SignIn where
  config : SignIn.Config
  key : Hmac.Key
  used : IO.Ref Used
  keys : IO.Ref (List (String × Keys))

def SignIn.start (config : SignIn.Config) : IO SignIn :=
  return { config, key := .of (← randomBytes 32), used := ← IO.mkRef {}, keys := ← IO.mkRef [] }

namespace SignIn

private def wallMs : IO Nat :=
  return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.toInt.toNat

private def call (config : Client.Config) (url : String) (method : Http.Method)
    (headers : List (String × String)) (body : ByteArray := .empty) : IO (Option Response) := do
  let some e := Endpoint.parse url | return none
  let request : Request := {
    method, path := e.path, query := e.query, body
    headers := headers ++ [("accept", "application/json"), ("user-agent", "lanes")] }
  let call : Client.Call :=
    { host := e.host, port := e.port, request, scheme := if e.https then .https else .http }
  try (Client.exchange call config).block catch _ => return none

/-- The provider's keys to check a token naming `kid` with, fetched first if `Keys.lookup` says
so. The fetch is claimed before it is made, so concurrent callbacks do not fetch twice. -/
private def keysFor (s : SignIn) (p : Provider) (jwks : String) (kid : Option String) (now : Nat) :
    IO (List Jose.Jwk) := do
  let decision ← s.keys.modifyGet fun all =>
    let held := (all.lookup p.name).getD {}
    match held.lookup s.config.settings now kid with
    | .use _ => (none, all)
    | .fetch => (some held.keys, (p.name, held.fetched now none) :: all.filter (·.1 != p.name))
  match decision with
  | none => return (((← s.keys.get).lookup p.name).getD {}).keys
  | some held =>
    let got := keysAnswer (← call s.config.http jwks .get [])
    let keys := got.getD held
    s.keys.modify fun all =>
      (p.name, { keys, fetched_ms := some now }) :: all.filter (·.1 != p.name)
    return keys

private def identify (s : SignIn) (p : Provider) (c : Client) (g : Grant) (tokens : Tokens)
    (now : Nat) : IO (Except Refusal Identity) := do
  match p.source with
  | .idToken issuers jwks =>
    let some token := tokens.idToken | return .error (.idToken (.jose .malformed))
    let kid := (Jose.Compact.read token.value).toOption.bind (·.kid)
    let keys ← keysFor s p jwks kid now
    let expect := { issuers, clientId := c.id, nonce := g.nonce, now_s := now / 1000,
                    skew_s := s.config.settings.skew_s }
    return (IdToken.verify keys expect token.value).map (Identity.under issuers) |>.mapError .idToken
  | .userApi urls read =>
    let mut answers := []
    for url in urls do
      match userAnswer (← call s.config.http url .get
          [("authorization", s!"Bearer {tokens.access.value}")]) with
      | .ok j => answers := answers ++ [j]
      | .error why => return .error why
    return (read answers).mapError .userApi

/-- The provider's callback: the browser's ticket checked, then the code exchanged and the user
known, and only then the state claimed, so that a state is used up only by a sign-in that
succeeded and filling the set takes a code from the provider for each state. -/
def finish (s : SignIn) (p : Provider) (c : Client) (r : Request) :
    IO (Except Refusal Identity) := do
  let now ← wallMs
  let limit := s.config.settings.maxUsed
  let answer := Answer.read r.query
  let some state := answer.state | return .error .malformed
  let ticket := check s.key now p.name (r.cookie? (hostCookie s.config.cookie s.config.secure)) state
  match answer, ticket with
  | .error e _, _ => return .error (.denied e)
  | _, .error why => return .error why
  | .malformed, _ => return .error .malformed
  | .code code _, .ok t =>
    if let .error why := ((← s.used.get).claim limit now t).2 then return .error why
    let g := t.grant s.key
    let form := encodeForm (tokenForm c code g.verifier)
    let answered ← call s.config.http p.token .post
      [("content-type", "application/x-www-form-urlencoded")] form.toUTF8
    match tokenAnswer answered with
    | .error why => return .error why
    | .ok tokens =>
      match ← identify s p c g tokens now with
      | .error why => return .error why
      | .ok id =>
        let later ← wallMs
        let claimed ← s.used.modifyGet fun u =>
          let (u, claimed) := u.claim limit later t
          (claimed, u)
        return claimed.map fun () => id

/-- What the server does with a request before it enters the system (`serve`'s `arrive`). -/
def arrive (s : SignIn) (r : Request) : IO (Except Response Request) := do
  let r := strip r
  let provider (name : String) := s.config.providers.find? (·.1.name == name)
  match route s.config.pathPrefix r with
  | .other => return .ok r
  | .begin name =>
    let some (p, c) := provider name | return .ok r
    let (url, ticket) := begin s.config.settings s.key p c (← wallMs) (← randomBytes 32)
    return .error (beginResponse s.config.cookie s.config.secure s.config.settings url ticket)
  | .callback name =>
    let some (p, c) := provider name | return .ok r
    match ← s.finish p c r with
    | .ok id => return .ok (withIdentity r id)
    | .error why => return .error (refusedResponse why)

end SignIn

end Lanes.OAuth
