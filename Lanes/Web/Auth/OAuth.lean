/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Auth.IdToken
public import Lanes.Web.Auth.Token
public import Lanes.Proof.List.Fold
public import Lanes.Web.Http.Cookie
public import Lanes.Lib.Net.Url

/-!
Sign-in with another service: OAuth 2.0's authorization code flow with PKCE (RFC 6749 §4.1,
RFC 7636), and OpenID Connect on it, as pure decisions. `Lanes/Web/IO/SignIn.lean` performs them:
it draws the random bytes and the key, keeps the states used and calls the provider.

A sign-in begun is a `Ticket`, a random `state` with its provider and expiry, which the browser
keeps in a cookie under the server's tag: the server keeps nothing for it, so beginnings, however
many, crowd out no one. A callback is accepted only with the ticket of its browser's cookie, for
its state and provider, before it expires (`check_ok`); once its sign-in is done the state is
claimed (`Used.claim`), and over any run no state is accepted twice (`Used.accepted_once`). The
states claimed are kept until they expire, at most `Settings.maxUsed`; a full set drops the oldest
and refuses every ticket that expires no later than they do, never one that could be a replay.

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
  /-- States of accepted callbacks kept, against replays, until their tickets expire; beyond, the
  oldest are dropped and the sign-ins that expire no later than they do are refused. -/
  maxUsed : Nat := 16384
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

/-- What a callback accepted gives: what the code is exchanged with and the ID token checked
against. -/
structure Grant where
  provider : String
  nonce : String
  verifier : Secret
  deriving DecidableEq, Repr, Hashable

/-- A sign-in begun, which the browser keeps in its binding cookie under the server's tag
(`Ticket.toCookie`), so that the server keeps nothing for a sign-in until its callback is accepted.
The nonce and the PKCE verifier are tags of the state under the server's key (`Ticket.grant`):
neither is in the cookie, which the request carries into the system. -/
structure Ticket where
  provider : String
  state : String
  expires_ms : Nat
  deriving DecidableEq, Repr, Hashable

inductive Refusal where
  | unknownProvider
  /-- The browser holds no sign-in of the server's: none begun there, or begun before a restart. -/
  | unknownState
  /-- The state was issued to another browser. -/
  | otherBrowser
  /-- The state was issued for another provider's sign-in. -/
  | otherProvider
  | expired
  /-- A callback under the state was accepted already. -/
  | used
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

namespace Ticket

/-- The state is base64url, without `.`, so the fields read back apart. -/
def payload (t : Ticket) : String := t.state ++ "." ++ toString t.expires_ms ++ "." ++ t.provider

def read (payload : String) : Option Ticket :=
  match payload.splitOn "." with
  | state :: expires :: provider => do
    return { provider := ".".intercalate provider, state, expires_ms := ← expires.toNat? }
  | _ => none

/-- The binding cookie's value: a token that outlives its ticket by an hour, so that a callback
in that hour is told the ticket expired (`check`), and a later one that it is unknown. -/
def toCookie (key : Hmac.Key) (t : Ticket) : String :=
  Auth.sign (.of key) "sign-in" (t.expires_ms / 1000 + 3600) t.payload

/-- The ticket of a binding cookie, if the server's key tagged it and it has not expired at
`now_ms`. -/
def ofCookie (key : Hmac.Key) (now_ms : Nat) (cookie : String) : Option Ticket :=
  (Auth.verify (.of key) "sign-in" (now_ms / 1000) cookie).bind read

def derive (key : Hmac.Key) (purpose state : String) : String :=
  b64 (key.mac (Auth.message purpose state))

/-- The nonce and the PKCE verifier (43 characters, RFC 7636 §4.1) of the sign-in. -/
def grant (key : Hmac.Key) (t : Ticket) : Grant :=
  { provider := t.provider, nonce := derive key "sign-in nonce" t.state,
    verifier := ⟨derive key "sign-in verifier" t.state⟩ }

end Ticket

/-- The provider's callback for `state`, on the route of `provider`, from a browser whose binding
cookie is `cookie`: its ticket, if the server tagged it for this state, this provider, and it has
not expired. -/
def check (key : Hmac.Key) (now_ms : Nat) (provider : String) (cookie : Option String)
    (state : String) : Except Refusal Ticket :=
  match cookie.bind (Ticket.ofCookie key now_ms) with
  | none => .error .unknownState
  | some t =>
    if !same t.state state then .error .otherBrowser
    else if t.provider != provider then .error .otherProvider
    else if t.expires_ms ≤ now_ms then .error .expired
    else .ok t

/-- A callback is accepted only with a ticket that the server's key tagged and that this
request's cookie carries, for its state, on its provider's route, before its expiry. -/
theorem check_ok {key : Hmac.Key} {now_ms : Nat} {provider : String} {cookie : Option String}
    {state : String} {t : Ticket} (h : check key now_ms provider cookie state = .ok t) :
    (∃ c, cookie = some c ∧ Ticket.ofCookie key now_ms c = some t) ∧ t.state = state
      ∧ t.provider = provider ∧ now_ms < t.expires_ms := by
  unfold check at h
  split at h
  · cases h
  · rename_i t' hc
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    rename_i hs hp hx
    cases h
    simp only [Bool.not_eq_true', Bool.not_eq_false, bne_iff_ne, ne_eq, Decidable.not_not] at hs hp hx
    obtain ⟨c, rfl, hu⟩ := Option.bind_eq_some_iff.mp hc
    exact ⟨⟨c, rfl, hu⟩, (same_iff _ _).mp hs, hp, by omega⟩

/-- The states of the callbacks accepted, each kept until its ticket expires, so that none is
accepted twice: all the server keeps of sign-ins. -/
structure Used where
  /-- Tickets that expire at this time or before are refused: the latest time a claim was made
  at, or later once a full set dropped states. -/
  floor_ms : Nat := 0
  /-- Newest first, each with its ticket's expiry. -/
  states : List (String × Nat) := []
  deriving DecidableEq, Repr, Hashable

namespace Used

/-- A callback's ticket claimed, once its sign-in is done: refused if it has expired or its state
was claimed before, else kept. With `limit` states kept, the oldest are dropped and the floor
raised to their expiries: a replay of a dropped state is still refused, as are tickets that expire
no later, and a ticket newer than those dropped is accepted. -/
def claim (u : Used) (limit now_ms : Nat) (t : Ticket) : Used × Except Refusal Unit :=
  let floor := max u.floor_ms now_ms
  let live := u.states.filter (floor < ·.2)
  if t.expires_ms ≤ floor then (⟨floor, live⟩, .error .expired)
  else if live.any (same ·.1 t.state) then (⟨floor, live⟩, .error .used)
  else
    let raised := (live.drop (limit - 1)).foldr (fun e m => max e.2 m) floor
    let kept := (live.take (limit - 1)).filter (raised < ·.2)
    if t.expires_ms ≤ raised then (⟨raised, kept⟩, .error .expired)
    else (⟨raised, (t.state, t.expires_ms) :: kept⟩, .ok ())

theorem length_claim (u : Used) {limit : Nat} (now_ms : Nat) (t : Ticket) (hl : 0 < limit)
    (hu : u.states.length ≤ limit) : (u.claim limit now_ms t).1.states.length ≤ limit := by
  have hf := (List.filter_sublist (p := (max u.floor_ms now_ms < ·.2)) (l := u.states)).length_le
  unfold claim; dsimp only
  split
  · exact Nat.le_trans hf hu
  · split
    · exact Nat.le_trans hf hu
    · have hk := (List.filter_sublist (l := (u.states.filter (max u.floor_ms now_ms < ·.2)).take
        (limit - 1)) (p := (((u.states.filter (max u.floor_ms now_ms < ·.2)).drop (limit - 1)).foldr
          (fun e m => max e.2 m) (max u.floor_ms now_ms) < ·.2))).length_le
      have ht := List.length_take_le (limit - 1) (u.states.filter (max u.floor_ms now_ms < ·.2))
      split
      · simp only; omega
      · simp only [List.length_cons]; omega

/-- A ticket claimed has not expired. -/
theorem claim_ok {u : Used} {limit now_ms : Nat} {t : Ticket}
    (h : (u.claim limit now_ms t).2 = .ok ()) : now_ms < t.expires_ms := by
  unfold claim at h; dsimp only at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  rename_i hx
  have := le_foldr_max (fun (e : String × Nat) => e.2) (max u.floor_ms now_ms)
    ((u.states.filter (max u.floor_ms now_ms < ·.2)).drop (limit - 1))
  omega

/-- What the set knows of a state accepted with expiry `x`: kept, or refused by the floor. -/
def Holds (u : Used) (s : String) (x : Nat) : Prop := (s, x) ∈ u.states ∨ x ≤ u.floor_ms

private theorem holds_live {u : Used} {s : String} {x floor : Nat} (h : Holds u s x)
    (hf : u.floor_ms ≤ floor) : (s, x) ∈ u.states.filter (floor < ·.2) ∨ x ≤ floor := by
  rcases h with h | h
  · by_cases hx : floor < x
    · exact .inl (List.mem_filter.mpr ⟨h, by simpa using hx⟩)
    · exact .inr (by omega)
  · exact .inr (by omega)

private theorem holds_kept {live : List (String × Nat)} {s : String} {x floor k : Nat}
    (h : (s, x) ∈ live ∨ x ≤ floor) :
    (s, x) ∈ (live.take k).filter ((live.drop k).foldr (fun e m => max e.2 m) floor < ·.2)
      ∨ x ≤ (live.drop k).foldr (fun e m => max e.2 m) floor := by
  have h0 := le_foldr_max (fun (e : String × Nat) => e.2) floor (live.drop k)
  rcases h with h | h
  · rw [← List.take_append_drop k live] at h
    rcases List.mem_append.mp h with h | h
    · by_cases hx : (live.drop k).foldr (fun e m => max e.2 m) floor < x
      · exact .inl (List.mem_filter.mpr ⟨h, by simpa using hx⟩)
      · exact .inr (by omega)
    · exact .inr (le_foldr_max_of_mem (fun (e : String × Nat) => e.2) floor h)
  · exact .inr (by omega)

/-- What the set knows of a state, it knows after any claim. -/
theorem claim_holds {u : Used} {s : String} {x : Nat} (limit now_ms : Nat) (t : Ticket)
    (h : Holds u s x) : Holds (u.claim limit now_ms t).1 s x := by
  have hl := holds_live h (Nat.le_max_left u.floor_ms now_ms)
  have hk := holds_kept (k := limit - 1) hl
  unfold claim Holds; dsimp only
  split
  · exact hl
  · split
    · exact hl
    · split
      · exact hk
      · rcases hk with hk | hk
        · exact .inl (List.mem_cons_of_mem _ hk)
        · exact .inr hk

/-- A ticket claimed expires after every state of its own the set knew of, and is kept. -/
theorem claim_ok_holds {u : Used} {limit now_ms : Nat} {t : Ticket}
    (h : (u.claim limit now_ms t).2 = .ok ()) :
    (∀ x, Holds u t.state x → x < t.expires_ms)
      ∧ Holds (u.claim limit now_ms t).1 t.state t.expires_ms := by
  have h0 := le_foldr_max (fun (e : String × Nat) => e.2) (max u.floor_ms now_ms)
    ((u.states.filter (max u.floor_ms now_ms < ·.2)).drop (limit - 1))
  unfold claim at h ⊢; dsimp only at h ⊢
  split at h; · cases h
  rename_i hfresh
  split at h; · cases h
  rename_i hnew
  split at h; · cases h
  rename_i hraised
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases holds_live hx (Nat.le_max_left u.floor_ms now_ms) with hx | hx
    · exact absurd (List.any_eq_true.mpr ⟨_, hx, (same_iff _ _).mpr rfl⟩) hnew
    · omega
  · simp only [hfresh, hnew, hraised, ite_false, Holds, Bool.false_eq_true]
    exact .inl List.mem_cons_self

/-- The tickets accepted over a run of claims at the times given, in order. -/
def run (u : Used) (limit : Nat) : List (Nat × Ticket) → Used × List Ticket
  | [] => (u, [])
  | (now_ms, t) :: ops =>
    let next := run (u.claim limit now_ms t).1 limit ops
    match (u.claim limit now_ms t).2 with
    | .ok _ => (next.1, t :: next.2)
    | .error _ => next

private theorem run_lt {s : String} {x : Nat} (limit : Nat) :
    ∀ (ops : List (Nat × Ticket)) (u : Used), Holds u s x →
      ∀ b ∈ (run u limit ops).2, b.state = s → x < b.expires_ms
  | [], _, _ => by simp [run]
  | (now_ms, t) :: ops, u, h => by
    have ih := run_lt limit ops _ (claim_holds limit now_ms t h)
    simp only [run]
    cases hc : (u.claim limit now_ms t).2 with
    | error _ => exact ih
    | ok _ =>
      intro b hb hs
      rcases List.mem_cons.mp hb with rfl | hb
      · exact (claim_ok_holds hc).1 x (hs ▸ h)
      · exact ih b hb hs

private theorem run_sublist (limit : Nat) :
    ∀ (ops : List (Nat × Ticket)) (u : Used), (run u limit ops).2.Sublist (ops.map (·.2))
  | [], _ => by simp [run]
  | (now_ms, t) :: ops, u => by
    have ih := run_sublist limit ops (u.claim limit now_ms t).1
    simp only [run, List.map_cons]
    cases (u.claim limit now_ms t).2 with
    | error _ => exact ih.cons _
    | ok _ => exact ih.cons_cons _

/-- Over any run of claims, a state accepted again is accepted with a ticket that expires later.
The server tags one ticket for each random state, so each state is accepted at most once
(`accepted_once`). -/
theorem accepted_later (u : Used) (limit : Nat) :
    ∀ ops : List (Nat × Ticket),
      (run u limit ops).2.Pairwise (fun a b => a.state = b.state → a.expires_ms < b.expires_ms)
  | [] => by simp [run]
  | (now_ms, t) :: ops => by
    have ih := accepted_later (u.claim limit now_ms t).1 limit ops
    simp only [run]
    cases hc : (u.claim limit now_ms t).2 with
    | error _ => exact ih
    | ok _ =>
      refine List.Pairwise.cons (fun b hb hs => ?_) ih
      exact run_lt limit ops _ (claim_ok_holds hc).2 b hb hs.symm

/-- When the tickets presented for one state have one expiry, as those the server tags do, no
state is accepted twice. -/
theorem accepted_once (u : Used) (limit : Nat) (ops : List (Nat × Ticket))
    (h : ∀ a ∈ ops, ∀ b ∈ ops, a.2.state = b.2.state → a.2.expires_ms = b.2.expires_ms) :
    ((run u limit ops).2.map (·.state)).Nodup := by
  have hsub := run_sublist limit ops u
  refine List.pairwise_map.mpr ((accepted_later u limit ops).imp_of_mem fun {a b} ha hb hab hs => ?_)
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp (hsub.subset ha)
  obtain ⟨b', hb', rfl⟩ := List.mem_map.mp (hsub.subset hb)
  have := h a' ha' b' hb' hs
  have := hab hs
  omega

end Used

/-- The URL the browser is sent to (RFC 6749 §4.1.1, RFC 7636 §4.3, OpenID Connect Core
§3.1.2.1); a nonce only for OpenID Connect. -/
def authorizeUrl (provider : Provider) (client : Client) (state : String) (g : Grant) : String :=
  let nonce := match provider.source with
    | .idToken .. => [("nonce", g.nonce)]
    | .userApi .. => []
  let params := [("response_type", "code"), ("client_id", client.id),
    ("redirect_uri", client.redirect), ("scope", " ".intercalate provider.scopes),
    ("state", state), ("code_challenge", challenge g.verifier.value),
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

/-- A sign-in begun now under the random bytes `state`: the URL to send the browser to, and the
value of the cookie that binds it to the browser. -/
def begin (settings : Settings) (key : Hmac.Key) (provider : Provider) (client : Client)
    (now_ms : Nat) (state : ByteArray) : String × String :=
  let t : Ticket := { provider := provider.name, state := b64 state,
                      expires_ms := now_ms + settings.ttl_ms }
  (authorizeUrl provider client t.state (t.grant key), t.toCookie key)

/-- The issuers of one provider name the same users: an identity from any of them names the
first, so that a user has one key whichever the token named. -/
def Identity.under (issuers : List String) (id : Identity) : Identity :=
  match issuers with
  | first :: _ => if id.issuer ∈ issuers then { id with issuer := first } else id
  | [] => id

theorem Identity.under_cons {first : String} {rest : List String} {id : Identity}
    (h : id.issuer ∈ first :: rest) : Identity.under (first :: rest) id = { id with issuer := first } := by
  simp only [under, h, ite_true]

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
    "x-lanes-identity-email-verified", "x-lanes-identity-name"]

def strip (r : Request) : Request :=
  { r with headers := r.headers.filter (·.1 ∉ identityHeaders) }

/-- The request with the identity, without its query, which held the code. -/
def withIdentity (r : Request) (id : Identity) : Request :=
  { r with query := [], headers := r.headers ++ [("x-lanes-identity-issuer", id.issuer),
      ("x-lanes-identity-subject", id.subject)]
      ++ (id.email.map fun e => [("x-lanes-identity-email", e)]).getD []
      ++ [("x-lanes-identity-email-verified", if id.emailVerified then "true" else "false")]
      ++ (id.name.map fun n => [("x-lanes-identity-name", n.val)]).getD [] }

/-- The identity the sign-in verified for this request. -/
def identity? (r : Request) : Option Identity := do
  let issuer ← r.header? "x-lanes-identity-issuer"
  let subject ← r.header? "x-lanes-identity-subject"
  let verified ← r.header? "x-lanes-identity-email-verified"
  return { issuer, subject, email := r.header? "x-lanes-identity-email",
           emailVerified := verified == "true"
           name := (r.header? "x-lanes-identity-name").bind DisplayName.of? }

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
  obtain ⟨issuer, subject, email, verified, name⟩ := id
  cases email <;> cases verified <;> cases name <;>
    simp [identity?, withIdentity, Request.header?, List.find?_append, DisplayName.of?_val,
      hs "x-lanes-identity-issuer" (by simp [identityHeaders]),
      hs "x-lanes-identity-subject" (by simp [identityHeaders]),
      hs "x-lanes-identity-email" (by simp [identityHeaders]),
      hs "x-lanes-identity-email-verified" (by simp [identityHeaders]),
      hs "x-lanes-identity-name" (by simp [identityHeaders])]

/-- The redirect that begins a sign-in, with the cookie that binds it to the browser: sent back
on the provider's redirect, a top-level navigation, so `SameSite=Lax`; over HTTPS a `__Host-`
cookie (`hostCookie`), which no other site or subdomain can set. -/
def beginResponse (cookie : String) (secure : Bool) (settings : Settings) (url ticket : String) :
    Response :=
  (Response.redirect url 302).setCookie
    { name := hostCookie cookie secure, value := ticket, path := "/",
      maxAge_s := some (settings.ttl_ms / 1000), secure, sameSite := .lax }

def Refusal.describe : Refusal → String
  | .unknownProvider => "unknown provider"
  | .unknownState => "no sign-in waits for this answer"
  | .used => "the sign-in was used already"
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
