/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Auth.IdToken
public import Lanes.Web.Http.Cookie
public import Lanes.Lib.Net.Url

/-!
Sign-in with another service: OAuth 2.0's authorization code flow with PKCE (RFC 6749 §4.1,
RFC 7636), and OpenID Connect on it, as pure decisions. `Lanes/Web/IO/SignIn.lean` performs them:
it draws the random bytes, keeps the pending sign-ins and calls the provider.

A sign-in begun is an `Entry` of `Pending`, under a random `state` and bound to the browser by a
random value in a cookie; it waits for the provider's callback for a while (`Settings.ttl_ms`),
and there are at most `Settings.maxPending`, the oldest dropped first. A callback is accepted only
for a state kept, from the browser it was begun in, before it expires (`Pending.callback_ok`), and
the state is gone after (`Pending.callback_removes`), so over any run no state is accepted more
often than it was issued (`Pending.accepted_le_issued`).

A provider is OpenID Connect (an ID token, checked by `IdToken.verify`) or OAuth 2.0 alone, whose
user is known by calling its API with the access token (`Source.userApi`). Endpoints are given
explicitly, as a discovery document gives them: none is fetched.
-/

@[expose] public section

namespace Lanes.OAuth

open Http

/-- A value never to be printed or logged: a client secret, a code, a token, a PKCE verifier.
`Repr` and `ToString` say only that it is one. -/
structure Secret where
  value : String
  deriving DecidableEq, Hashable

instance : Repr Secret := ⟨fun _ _ => "<secret>"⟩

instance : ToString Secret := ⟨fun _ => "<secret>"⟩

/-- How a provider says who signed in. -/
inductive Source where
  /-- OpenID Connect: an ID token from one of `issuers`, signed by a key of the JWK Set at the
  URL `jwks`. -/
  | idToken (issuers : List String) (jwks : String)
  /-- OAuth 2.0 alone: the access token is shown to each URL of `urls`, and `read` makes an
  identity of their JSON answers, in that order. -/
  | userApi (urls : List String) (read : List Json → Except String Identity)

structure Provider where
  /-- The name in its routes: `/sign-in/<name>` and `/sign-in/<name>/callback`. -/
  name : String
  /-- The authorization endpoint. -/
  authorize : String
  /-- The token endpoint. -/
  token : String
  scopes : List String
  source : Source
  /-- Parameters the authorization request also carries. -/
  extra : List (String × String) := []

/-- What the deployment registered with a provider. -/
structure Client where
  id : String
  secret : Secret
  /-- The redirect URI registered: the URL of the provider's callback route. -/
  redirect : String
  deriving Repr

/-- Every limit (rule 2.6). -/
structure Settings where
  /-- How long a sign-in begun waits for its callback. -/
  ttl_ms : Nat := 600000
  /-- Sign-ins waiting at once; beyond, the oldest is dropped. -/
  maxPending : Nat := 1024
  /-- How far a provider's clock may be from this one. -/
  skew_s : Nat := 60
  /-- A JWK Set is fetched again at most this often, however many tokens name keys it lacks. -/
  minRefresh_ms : Nat := 60000
  /-- Keys older than this are fetched again before they are used. -/
  maxAge_ms : Nat := 3600000
  deriving Repr

def b64 (bytes : ByteArray) : String := Base64.encode .rawUrl bytes

/-- The S256 challenge of a PKCE verifier (RFC 7636 §4.2). -/
def challenge (verifier : String) : String := b64 (Sha256.hash verifier.toUTF8)

/-- Fresh bytes for one sign-in from the operating system's random source, 32 of each. -/
structure Seed where
  state : ByteArray
  nonce : ByteArray
  verifier : ByteArray
  binding : ByteArray

/-- What a callback accepted gives: what the code is exchanged with and the ID token checked
against. -/
structure Grant where
  provider : String
  nonce : String
  verifier : Secret
  deriving DecidableEq, Repr, Hashable

structure Entry where
  state : String
  /-- The value of the browser's cookie. -/
  binding : String
  expires_ms : Nat
  grant : Grant
  deriving DecidableEq, Repr, Hashable

/-- The sign-ins begun and not yet called back, newest first. -/
structure Pending where
  entries : List Entry := []
  deriving DecidableEq, Repr, Hashable

inductive Refusal where
  | unknownProvider
  /-- No sign-in waits under the state: never issued, used already, or dropped. -/
  | unknownState
  /-- The state was issued to another browser. -/
  | otherBrowser
  /-- The state was issued for another provider's sign-in. -/
  | otherProvider
  | expired
  /-- The provider's answer is an error, such as the user's refusal. -/
  | denied (error : String)
  /-- The callback has no code or no state. -/
  | malformed
  /-- The token endpoint gave no token: its error code, or why its answer is none. -/
  | token (why : String)
  | idToken (why : IdToken.Refusal)
  | userApi (why : String)
  deriving DecidableEq, Repr

/-- Two values compared in a time that does not depend on where they differ. -/
def same (a b : String) : Bool := Bytes.same a.toUTF8 b.toUTF8

theorem same_iff (a b : String) : same a b = true ↔ a = b := by
  simp [same, Bytes.same_iff, String.toByteArray_inj]

namespace Pending

/-- A sign-in begun: kept first, with the others that have not expired, at most `limit`. -/
def begin (p : Pending) (limit now_ms : Nat) (e : Entry) : Pending :=
  ⟨(e :: p.entries.filter (now_ms < ·.expires_ms)).take limit⟩

theorem length_begin (p : Pending) (limit now_ms : Nat) (e : Entry) :
    (p.begin limit now_ms e).entries.length ≤ limit :=
  List.length_take_le ..

/-- The provider's callback, from the browser with the cookie `binding`, under `state`, on the
route of `provider`. Whatever the answer, no sign-in waits under the state after. -/
def callback (p : Pending) (now_ms : Nat) (provider binding state : String) :
    Pending × Except Refusal Grant :=
  match p.entries.find? (same ·.state state) with
  | none => (p, .error .unknownState)
  | some e =>
    let rest : Pending := ⟨p.entries.filter (!same ·.state state)⟩
    if !same e.binding binding then (rest, .error .otherBrowser)
    else if e.grant.provider != provider then (rest, .error .otherProvider)
    else if e.expires_ms ≤ now_ms then (rest, .error .expired)
    else (rest, .ok e.grant)

/-- A callback is accepted only for a sign-in begun under its state, in its browser, for its
provider, and not expired. -/
theorem callback_ok {p : Pending} {now_ms : Nat} {provider binding state : String} {g : Grant}
    (h : (p.callback now_ms provider binding state).2 = .ok g) :
    ∃ e ∈ p.entries, e.state = state ∧ e.binding = binding ∧ e.grant.provider = provider
      ∧ now_ms < e.expires_ms ∧ e.grant = g := by
  unfold callback at h
  split at h
  · cases h
  · rename_i e hf
    have hmem := List.mem_of_find?_eq_some hf
    have hs : same e.state state = true := List.find?_some (p := fun (x : Entry) => same x.state state) hf
    have hs := (same_iff _ _).mp hs
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    rename_i hb hp hx
    simp only [Bool.not_eq_true', Bool.not_eq_false, bne_iff_ne, ne_eq,
      Decidable.not_not] at hb hp hx
    cases h
    exact ⟨e, hmem, hs, (same_iff _ _).mp hb, hp, by omega, rfl⟩

/-- After a callback, no sign-in waits under its state. -/
theorem callback_removes (p : Pending) (now_ms : Nat) (provider binding state : String) :
    ∀ e ∈ (p.callback now_ms provider binding state).1.entries, e.state ≠ state := by
  intro e he
  unfold callback at he
  split at he
  · rename_i hf
    intro hs
    have := List.find?_eq_none.mp hf e he
    simp [hs, (same_iff state state).mpr rfl] at this
  · have hrest : ∀ e ∈ p.entries.filter (!same ·.state state), e.state ≠ state := by
      intro e he hs
      simp [List.mem_filter, hs, (same_iff state state).mpr rfl] at he
    split at he
    · exact hrest e he
    · split at he
      · exact hrest e he
      · split at he <;> exact hrest e he

theorem callback_sublist (p : Pending) (now_ms : Nat) (provider binding state : String) :
    (p.callback now_ms provider binding state).1.entries.Sublist p.entries := by
  unfold callback
  split
  · exact .refl _
  · split
    · exact List.filter_sublist
    · split
      · exact List.filter_sublist
      · split <;> exact List.filter_sublist

/-- What happens to the sign-ins: one begun, or a callback. -/
inductive Op where
  | begin (limit now_ms : Nat) (e : Entry)
  | callback (now_ms : Nat) (provider binding state : String)

def Op.issues (state : String) : Op → Bool
  | .begin _ _ e => e.state == state
  | .callback .. => false

/-- The sign-ins after `ops`, and the states of the callbacks accepted, in order. -/
def run (p : Pending) : List Op → Pending × List String
  | [] => (p, [])
  | .begin limit now_ms e :: ops => run (p.begin limit now_ms e) ops
  | .callback now_ms provider binding state :: ops =>
    let next := run (p.callback now_ms provider binding state).1 ops
    match (p.callback now_ms provider binding state).2 with
    | .ok _ => (next.1, state :: next.2)
    | .error _ => next

private theorem count_begin (p : Pending) (limit now_ms : Nat) (e : Entry) (s : String) :
    (p.begin limit now_ms e).entries.countP (·.state == s)
      ≤ p.entries.countP (·.state == s) + (if e.state == s then 1 else 0) := by
  simp only [begin]
  have h1 := (List.take_sublist limit (e :: p.entries.filter (now_ms < ·.expires_ms))).countP_le
    (p := (·.state == s))
  have h2 := (List.filter_sublist (p := (now_ms < ·.expires_ms)) (l := p.entries)).countP_le
    (p := (·.state == s))
  rw [List.countP_cons] at h1
  cases hb : (e.state == s) <;>
    simp only [hb, ite_true, Bool.false_eq_true, ite_false] at h1 ⊢ <;> omega

/-- Over any run from no sign-ins, no state is accepted more often than it was issued: a state
issued once is accepted at most once. -/
theorem accepted_le_issued (ops : List Op) (s : String) :
    (run {} ops).2.count s ≤ ops.countP (·.issues s) := by
  suffices h : ∀ (p : Pending),
      (run p ops).2.count s ≤ p.entries.countP (·.state == s) + ops.countP (·.issues s) by
    simpa using h {}
  induction ops with
  | nil => intro p; simp [run]
  | cons op ops ih =>
    intro p
    cases op with
    | begin limit now_ms e =>
      have h1 := ih (p.begin limit now_ms e)
      have h2 := count_begin p limit now_ms e s
      have hc : (Op.begin limit now_ms e :: ops).countP (·.issues s)
          = ops.countP (·.issues s) + if e.state == s then 1 else 0 := by
        simp [List.countP_cons, Op.issues]
      simp only [run]
      rw [hc]
      cases hb : (e.state == s) <;>
        simp only [hb, ite_true, Bool.false_eq_true, ite_false] at h2 ⊢ <;> omega
    | callback now_ms provider binding state =>
      have hq := ih (p.callback now_ms provider binding state).1
      have hsub := (callback_sublist p now_ms provider binding state).countP_le
        (p := (·.state == s))
      have hiss : (Op.callback now_ms provider binding state :: ops).countP (·.issues s)
          = ops.countP (·.issues s) := by
        simp [Op.issues]
      simp only [run]
      rw [hiss]
      cases hc : (p.callback now_ms provider binding state).2 with
      | error _ => simp only; omega
      | ok g =>
        simp only [List.count_cons]
        by_cases hs : state = s
        · subst hs
          obtain ⟨e, he, hes, -⟩ := callback_ok hc
          have hzero : (p.callback now_ms provider binding state).1.entries.countP
              (·.state == state) = 0 :=
            List.countP_eq_zero.mpr fun e' he' => by
              simpa using callback_removes p now_ms provider binding state e' he'
          have hpos : 0 < p.entries.countP (·.state == state) :=
            List.countP_pos_iff.mpr ⟨e, he, by simp [hes]⟩
          simp only [beq_self_eq_true, ite_true]
          omega
        · have : (state == s) = false := by simpa using hs
          simp only [this, Bool.false_eq_true, ite_false, Nat.add_zero]
          omega

end Pending

/-- The entry a seed makes. -/
def Seed.entry (seed : Seed) (provider : String) (expires_ms : Nat) : Entry :=
  { state := b64 seed.state, binding := b64 seed.binding, expires_ms,
    grant := { provider, nonce := b64 seed.nonce, verifier := ⟨b64 seed.verifier⟩ } }

/-- The URL the browser is sent to (RFC 6749 §4.1.1, RFC 7636 §4.3, OpenID Connect Core
§3.1.2.1); a nonce only for OpenID Connect. -/
def authorizeUrl (provider : Provider) (client : Client) (e : Entry) : String :=
  let nonce := match provider.source with
    | .idToken .. => [("nonce", e.grant.nonce)]
    | .userApi .. => []
  let params := [("response_type", "code"), ("client_id", client.id),
    ("redirect_uri", client.redirect), ("scope", " ".intercalate provider.scopes),
    ("state", e.state), ("code_challenge", challenge e.grant.verifier.value),
    ("code_challenge_method", "S256")] ++ nonce ++ provider.extra
  provider.authorize ++ (if provider.authorize.contains '?' then "&" else "?") ++ encodeForm params

/-- What a provider's discovery document (OpenID Connect Discovery 1.0 §3) says that sign-in
uses. Read from a copy kept with the deployment: none is fetched. -/
structure Discovery where
  issuer : String
  authorize : String
  token : String
  jwks : String
  /-- `id_token_signing_alg_values_supported`. -/
  algs : List String
  /-- `code_challenge_methods_supported`. -/
  challenges : List String
  deriving DecidableEq, Repr

def Discovery.read (text : String) : Option Discovery := do
  let j ← (Json.parse text).toOption
  let strings (name : String) : List String := match j.getObjVal? name with
    | .ok (.arr xs) => xs.toList.filterMap IdToken.string?
    | _ => []
  return { issuer := ← Jose.str? j "issuer", authorize := ← Jose.str? j "authorization_endpoint",
           token := ← Jose.str? j "token_endpoint", jwks := ← Jose.str? j "jwks_uri",
           algs := strings "id_token_signing_alg_values_supported",
           challenges := strings "code_challenge_methods_supported" }

/-- The OpenID Connect provider a discovery document describes. -/
def Discovery.provider (d : Discovery) (name : String) (scopes : List String := ["openid", "email"]) :
    Provider :=
  { name, authorize := d.authorize, token := d.token, scopes, source := .idToken [d.issuer] d.jwks }

/-- A sign-in begun now: the pending sign-ins with its entry, the URL to send the browser to,
and the value of the cookie that binds it to the browser. -/
def begin (settings : Settings) (provider : Provider) (client : Client) (p : Pending)
    (now_ms : Nat) (seed : Seed) : Pending × String × String :=
  let e := seed.entry provider.name (now_ms + settings.ttl_ms)
  (p.begin settings.maxPending now_ms e, authorizeUrl provider client e, e.binding)

/-- What the provider sent the browser back with (RFC 6749 §4.1.2, §4.1.2.1). -/
inductive Answer where
  | code (code : Secret) (state : String)
  | error (error : String) (state : Option String)
  | malformed

def Answer.state : Answer → Option String
  | .code _ state => some state
  | .error _ state => state
  | .malformed => none

def Answer.read (query : List (String × String)) : Answer :=
  let get (name : String) := (query.find? (·.1 == name)).map (·.2)
  match get "error", get "code", get "state" with
  | some e, _, state => .error e state
  | none, some c, some state => .code ⟨c⟩ state
  | none, _, _ => .malformed

/-- The form posted to the token endpoint (RFC 6749 §4.1.3, RFC 7636 §4.5), the client
authenticated by its secret in the body (`client_secret_post`). -/
def tokenForm (client : Client) (code verifier : Secret) : List (String × String) :=
  [("grant_type", "authorization_code"), ("code", code.value), ("redirect_uri", client.redirect),
    ("client_id", client.id), ("client_secret", client.secret.value),
    ("code_verifier", verifier.value)]

structure Tokens where
  access : Secret
  idToken : Option Secret := none
  deriving Repr

/-- The token endpoint's answer (RFC 6749 §5.1, §5.2): a bearer access token, and for OpenID
Connect an ID token; or the provider's error code. -/
def Tokens.read (status : Nat) (body : ByteArray) : Except Refusal Tokens :=
  match (String.fromUTF8? body).map Json.parse with
  | some (.ok j) =>
    match Jose.str? j "error", Jose.str? j "access_token", Jose.str? j "token_type" with
    | some e, _, _ => .error (.token e)
    | none, some access, some kind =>
      if status == 200 && kind.toLower == "bearer" then
        .ok { access := ⟨access⟩, idToken := (Jose.str? j "id_token").map (⟨·⟩) }
      else .error (.token "no bearer token")
    | none, _, _ => .error (.token "no access token")
  | _ => .error (.token "not JSON")

/-- What the token endpoint answered, or `none` if it did not. -/
def tokenAnswer : Option Response → Except Refusal Tokens
  | none => .error (.token "no answer")
  | some r => Tokens.read r.status r.body

/-- What a user API answered: JSON, with status 200. -/
def userAnswer : Option Response → Except Refusal Json
  | none => .error (.userApi "no answer")
  | some r =>
    if r.status != 200 then .error (.userApi s!"status {r.status}")
    else match (String.fromUTF8? r.body).map Json.parse with
      | some (.ok j) => .ok j
      | _ => .error (.userApi "not JSON")

/-- The keys a JWK Set's URL answered with, if it answered one. -/
def keysAnswer : Option Response → Option (List Jose.Jwk)
  | some r =>
    if r.status == 200 then (String.fromUTF8? r.body).bind fun text => (Jose.readKeys text).toOption
    else none
  | none => none

/-- A provider's keys, and when they were last fetched. -/
structure Keys where
  keys : List Jose.Jwk := []
  fetched_ms : Option Nat := none

inductive Lookup where
  | use (keys : List Jose.Jwk)
  | fetch

/-- Whether to check a token with the keys held or to fetch the set first: fetch when none was
fetched, or when the keys are old or lack the token's `kid`, but never sooner than
`minRefresh_ms` after the last fetch, so tokens naming unknown keys cannot make a server call the
provider more often. -/
def Keys.lookup (k : Keys) (settings : Settings) (now_ms : Nat) (kid : Option String) : Lookup :=
  match k.fetched_ms with
  | none => .fetch
  | some t =>
    if now_ms < t + settings.maxAge_ms && kid.all (fun id => k.keys.any (·.kid == some id)) then
      .use k.keys
    else if t + settings.minRefresh_ms ≤ now_ms then .fetch
    else .use k.keys

/-- After a fetch at `now_ms`: the keys it gave, or those held if it gave none. -/
def Keys.fetched (k : Keys) (now_ms : Nat) (got : Option (List Jose.Jwk)) : Keys :=
  { keys := got.getD k.keys, fetched_ms := some now_ms }

theorem Keys.lookup_fetch {k : Keys} {settings : Settings} {now_ms : Nat} {kid : Option String}
    (h : k.lookup settings now_ms kid = .fetch) :
    ∀ t, k.fetched_ms = some t → t + settings.minRefresh_ms ≤ now_ms := by
  intro t ht
  simp only [lookup, ht] at h
  split at h
  · cases h
  · split at h
    · assumption
    · cases h

/-- Once fetched, the set is not fetched again within `minRefresh_ms`, whatever tokens come. -/
theorem Keys.no_fetch_within (k : Keys) (settings : Settings) (t : Nat)
    (got : Option (List Jose.Jwk)) (now_ms : Nat) (kid : Option String)
    (h : now_ms < t + settings.minRefresh_ms) :
    (k.fetched t got).lookup settings now_ms kid ≠ .fetch := fun hf => by
  have := Keys.lookup_fetch hf t rfl
  omega

/-- The routes of sign-in: `/<prefix>/<provider>` begins, `/<prefix>/<provider>/callback` is
the callback. -/
inductive Route where
  | begin (provider : String)
  | callback (provider : String)
  | other
  deriving DecidableEq, Repr

def route (pathPrefix : String) (r : Request) : Route :=
  if r.method != .get then .other
  else match r.path with
    | [p, name] => if p == pathPrefix then .begin name else .other
    | [p, name, "callback"] => if p == pathPrefix then .callback name else .other
    | _ => .other

/-- The headers that carry an identity into the system. A client's own are dropped where a
request arrives (`strip`), so only the sign-in can have written them. -/
def identityHeaders : List String :=
  ["x-lanes-identity-issuer", "x-lanes-identity-subject", "x-lanes-identity-email",
    "x-lanes-identity-email-verified"]

def strip (r : Request) : Request :=
  { r with headers := r.headers.filter (·.1 ∉ identityHeaders) }

/-- The request with the identity, without its query, which held the code. -/
def withIdentity (r : Request) (id : Identity) : Request :=
  { r with query := [], headers := r.headers ++ [("x-lanes-identity-issuer", id.issuer),
      ("x-lanes-identity-subject", id.subject)]
      ++ (id.email.map fun e => [("x-lanes-identity-email", e)]).getD []
      ++ [("x-lanes-identity-email-verified", if id.emailVerified then "true" else "false")] }

/-- The identity the sign-in verified for this request. -/
def identity? (r : Request) : Option Identity := do
  let issuer ← r.header? "x-lanes-identity-issuer"
  let subject ← r.header? "x-lanes-identity-subject"
  let verified ← r.header? "x-lanes-identity-email-verified"
  return { issuer, subject, email := r.header? "x-lanes-identity-email",
           emailVerified := verified == "true" }

private theorem find?_strip (r : Request) {name : String} (h : name ∈ identityHeaders) :
    (strip r).headers.find? (·.1 == name) = none := by
  simp only [strip, List.find?_eq_none, List.mem_filter, beq_iff_eq, decide_eq_true_eq]
  intro x hx heq
  exact hx.2 (heq ▸ h)

theorem identity?_strip (r : Request) : identity? (strip r) = none := by
  simp [identity?, Request.header?, find?_strip r (name := "x-lanes-identity-issuer")
    (by simp [identityHeaders])]

/-- What the sign-in writes into a request it has stripped, the system reads back. -/
theorem identity?_withIdentity (r : Request) (id : Identity) :
    identity? (withIdentity (strip r) id) = some id := by
  have hs := fun name (h : name ∈ identityHeaders) => find?_strip r h
  obtain ⟨issuer, subject, email, verified⟩ := id
  cases email <;> cases verified <;>
    simp [identity?, withIdentity, Request.header?, List.find?_append,
      hs "x-lanes-identity-issuer" (by simp [identityHeaders]),
      hs "x-lanes-identity-subject" (by simp [identityHeaders]),
      hs "x-lanes-identity-email" (by simp [identityHeaders]),
      hs "x-lanes-identity-email-verified" (by simp [identityHeaders])]

/-- The redirect that begins a sign-in, with the cookie that binds it to the browser: sent back
on the provider's redirect, a top-level navigation, so `SameSite=Lax`, and only to the sign-in's
own routes. -/
def beginResponse (pathPrefix cookie : String) (secure : Bool) (settings : Settings)
    (url binding : String) : Response :=
  (Response.redirect url 302).setCookie
    { name := cookie, value := binding, path := "/" ++ pathPrefix,
      maxAge_s := some (settings.ttl_ms / 1000), secure, sameSite := .lax }

def Refusal.describe : Refusal → String
  | .unknownProvider => "unknown provider"
  | .unknownState => "no sign-in waits for this answer"
  | .otherBrowser => "the sign-in was begun in another browser"
  | .otherProvider => "the sign-in was begun with another provider"
  | .expired => "the sign-in took too long"
  | .denied error => s!"the provider said {error}"
  | .malformed => "the provider's answer has no code"
  | .token why => s!"no token: {why}"
  | .idToken why => s!"the ID token is refused: {repr why}"
  | .userApi why => s!"the provider's user API: {why}"

def refusedResponse (why : Refusal) : Response :=
  .text s!"sign-in refused: {why.describe}\n" 403

/-- Where an endpoint's URL calls: `https` or `http`, the host, the port, and the path and query
of the request to make. -/
structure Endpoint where
  https : Bool
  host : String
  port : UInt16
  path : List String
  query : List (String × String)
  deriving DecidableEq, Repr

def Endpoint.parse (url : String) : Option Endpoint := do
  let u ← Url.parse url
  let https ← match u.scheme with
    | some "https" => some true
    | some "http" => some false
    | _ => none
  let a ← u.authority
  unless a.userinfo.isNone && u.fragment.isNone do none
  let host ← match a.host with
    | .ip (.v4 n) => some (String.ofList (Ip.print4 n.val))
    | .ip (.v6 _) => none
    | .name s => if s.isEmpty || s.contains '%' then none else some s
  let port ← match a.port.filter (· != "") with
    | none => some (if https then 443 else 80)
    | some digits => digits.toNat?.filter (fun n => 0 < n && n < 65536) |>.map (·.toUInt16)
  let path ← ((u.path.splitOn "/").drop 1).mapM (percentDecode ·)
  let path := if path == [""] then [] else path
  return { https, host, port, path, query := (u.query.map parseForm).getD [] }

end Lanes.OAuth
