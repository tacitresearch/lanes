/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Auth.Jose

/-!
An OpenID Connect ID token (OpenID Connect Core §2, §3.1.3.7): a JWS whose claims say who signed
in, for which client, until when, and in answer to which request (its nonce). `verify` checks the
signature (`Jose.verify`), reads the claims and checks each; `verify_accepted` says that a token
it accepts is signed by a key of the set for an algorithm of the allow-list and that every check
of `Accepted` holds.
-/

@[expose] public section

namespace Lanes.OAuth

def DisplayName.maxChars : Nat := 64

/-- Not a control character (C0, DEL, C1), a line or paragraph separator, or a mark that
reorders the text around it (bidirectional embeddings, overrides and isolates). -/
def DisplayName.allowed (c : Char) : Bool :=
  let v := c.val
  !(v < 0x20 || (0x7f ≤ v && v < 0xa0) || v == 0x2028 || v == 0x2029
    || (0x202a ≤ v && v ≤ 0x202e) || (0x2066 ≤ v && v ≤ 0x2069))

def DisplayName.Valid (s : String) : Prop :=
  0 < s.length ∧ s.length ≤ DisplayName.maxChars ∧ s.all DisplayName.allowed = true

/-- A name to show for a user, as the provider gave it: text nobody checked, of at most
`maxChars` characters, none of them a control character. Show it as text, which `Html` escapes,
and never as markup, a URL or a header of a response. -/
structure DisplayName where
  val : String
  valid : DisplayName.Valid val
  deriving DecidableEq, Repr, Hashable

namespace DisplayName

instance (s : String) : Decidable (Valid s) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def of? (s : String) : Option DisplayName :=
  if h : Valid s then some ⟨s, h⟩ else none

/-- What a provider sends, made a name: its control characters dropped, blanks trimmed, cut to
`maxChars`; none when nothing is left. -/
def clean (raw : String) : Option DisplayName :=
  let kept := String.ofList (raw.toList.filter allowed)
  of? (String.ofList (kept.trimAscii.toString.toList.take maxChars))

theorem of?_val (n : DisplayName) : of? n.val = some n := by
  simp [of?, n.valid]

theorem length_le (n : DisplayName) : n.val.length ≤ maxChars := n.valid.2.1

end DisplayName

/-- Who signed in. A user is named by `issuer` and `subject` together, which do not change; the
email is the provider's, and `emailVerified` whether the provider says it checked the address.
`name` is what the provider calls the user, for display only: anyone may choose it. -/
structure Identity where
  issuer : String
  subject : String
  email : Option String := none
  emailVerified : Bool := false
  name : Option DisplayName := none
  deriving DecidableEq, Repr, Hashable

namespace IdToken

/-- The claims that are checked or used. Times are seconds since the epoch. -/
structure Claims where
  iss : String
  sub : String
  aud : List String
  azp : Option String := none
  exp : Nat
  nbf : Option Nat := none
  nonce : Option String := none
  email : Option String := none
  emailVerified : Bool := false
  /-- OpenID Connect's `name`, which the `profile` scope asks for. -/
  name : Option String := none
  deriving DecidableEq, Repr

def Claims.identity (c : Claims) : Identity :=
  { issuer := c.iss, subject := c.sub, email := c.email, emailVerified := c.emailVerified
    name := c.name.bind DisplayName.clean }

/-- What a token must say to be accepted now. -/
structure Expect where
  issuers : List String
  clientId : String
  nonce : String
  now_s : Nat
  /-- How far the provider's clock may be from this one, either way. -/
  skew_s : Nat

inductive Refusal where
  | jose (why : Jose.Refusal)
  /-- The payload is not JSON with the claims as their types, or `sub` is empty. -/
  | malformed
  | issuer
  | audience
  | authorizedParty
  | expired
  | notYetValid
  | nonce
  deriving DecidableEq, Repr

/-- A member that is absent, or of the type `read` reads. -/
def optional (j : Json) (name : String) (read : Json → Option α) : Option (Option α) :=
  match j.getObjVal? name with
  | .error _ => some none
  | .ok v => (read v).map some

def string? : Json → Option String
  | .str s => some s
  | _ => none

def nat? (j : Json) : Option Nat := j.getNat?.toOption

/-- `aud`: one string, or an array of strings. -/
def audience? : Json → Option (List String)
  | .str s => some [s]
  | .arr xs => xs.toList.mapM string?
  | _ => none

/-- `exp` and `nbf` must be whole seconds; `email_verified` a Boolean, `false` when absent;
`name` a string when present. -/
def Claims.read (payload : ByteArray) : Option Claims := do
  let j ← (String.fromUTF8? payload).bind fun text => (Json.parse text).toOption
  let iss ← (j.getObjVal? "iss").toOption.bind string?
  let sub ← (j.getObjVal? "sub").toOption.bind string?
  if sub.isEmpty then none
  let aud ← (j.getObjVal? "aud").toOption.bind audience?
  let exp ← (j.getObjVal? "exp").toOption.bind nat?
  let nbf ← optional j "nbf" nat?
  let azp ← optional j "azp" string?
  let nonce ← optional j "nonce" string?
  let email ← optional j "email" string?
  let verified ← optional j "email_verified" fun | .bool b => some b | _ => none
  let name ← optional j "name" string?
  return { iss, sub, aud, azp, exp, nbf, nonce, email, emailVerified := verified.getD false, name }

/-- Every check of OpenID Connect Core §3.1.3.7 that is about the claims (items 2 to 5, 9 and
11), and `nbf` as RFC 7519 §4.1.5 has it. A token for several audiences must name this client
its authorized party. -/
structure Accepted (x : Expect) (c : Claims) : Prop where
  issuer : c.iss ∈ x.issuers
  audience : x.clientId ∈ c.aud
  authorizedParty : c.azp = some x.clientId ∨ (c.azp = none ∧ c.aud = [x.clientId])
  unexpired : x.now_s < c.exp + x.skew_s
  started : ∀ nbf, c.nbf = some nbf → nbf ≤ x.now_s + x.skew_s
  nonce : c.nonce = some x.nonce

def check (x : Expect) (c : Claims) : Except Refusal Identity :=
  if c.iss ∉ x.issuers then .error .issuer
  else if x.clientId ∉ c.aud then .error .audience
  else if !(c.azp == some x.clientId || (c.azp == none && c.aud == [x.clientId])) then
    .error .authorizedParty
  else if c.exp + x.skew_s ≤ x.now_s then .error .expired
  else if c.nbf.any (x.now_s + x.skew_s < ·) then .error .notYetValid
  else if c.nonce != some x.nonce then .error .nonce
  else .ok c.identity

theorem check_ok_iff {x : Expect} {c : Claims} {id : Identity} :
    check x c = .ok id ↔ Accepted x c ∧ id = c.identity := by
  unfold check
  constructor
  · intro h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    cases h
    rename_i h1 h2 h3 h4 h5 h6
    simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, Option.any_eq_true, not_exists, not_and, bne_iff_ne, ne_eq,
      Decidable.not_not, decide_eq_true_eq] at h1 h2 h3 h4 h5 h6
    exact ⟨⟨h1, h2, h3.imp id id, by omega, fun n hn => by have := h5 n hn; omega, h6⟩, rfl⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6⟩, rfl⟩
    have h3' : (c.azp == some x.clientId || (c.azp == none && c.aud == [x.clientId])) = true := by
      rcases h3 with h | ⟨ha, hb⟩ <;> simp_all
    have h5' : (c.nbf.any (x.now_s + x.skew_s < ·)) = false := by
      cases hn : c.nbf with
      | none => rfl
      | some n => have := h5 n hn; simp; omega
    have h4' : ¬ c.exp + x.skew_s ≤ x.now_s := by omega
    simp only [h1, h2, h3', h5', h6, h4', not_true_eq_false, Bool.not_true, ite_false,
      bne_self_eq_false, Bool.false_eq_true]

/-- The identity a token signed by a key of `keys` gives, if every claim passes. -/
def verify (keys : List Jose.Jwk) (x : Expect) (token : String) : Except Refusal Identity :=
  match Jose.verify keys token with
  | .error why => .error (.jose why)
  | .ok c =>
    match Claims.read c.payload with
    | none => .error .malformed
    | some claims => check x claims

/-- An accepted token: its header names RS256 or ES256, a key of `keys` of that algorithm and of
its `kid` checks its signature, and every claim passes. -/
theorem verify_accepted {keys : List Jose.Jwk} {x : Expect} {token : String} {id : Identity}
    (h : verify keys x token = .ok id) :
    ∃ c claims, Jose.Compact.read token = .ok c
      ∧ (c.header.getObjVal? "alg" = .ok (.str "RS256")
        ∨ c.header.getObjVal? "alg" = .ok (.str "ES256"))
      ∧ (∃ k ∈ keys, k.fits c.alg ∧ (c.kid = none ∨ k.kid = c.kid)
        ∧ k.key.verifies c.signed c.signature)
      ∧ Claims.read c.payload = some claims ∧ Accepted x claims ∧ id = claims.identity := by
  unfold verify at h
  split at h
  · cases h
  · rename_i c hv
    split at h
    · cases h
    · rename_i claims hc
      obtain ⟨hr, halg, hk⟩ := Jose.verify_ok hv
      obtain ⟨ha, hid⟩ := check_ok_iff.mp h
      refine ⟨c, claims, hr, ?_, hk, hc, ha, hid⟩
      cases hcalg : c.alg <;> rw [hcalg] at halg <;> simp_all [Jose.Alg.name]

end IdToken

end Lanes.OAuth
