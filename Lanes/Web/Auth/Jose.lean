/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Crypto.Verify
public import Lanes.Lib.Encoding.Json
public import Lanes.Lib.Encoding.Base64

/-!
Signed JSON as an identity provider sends it: JWS in compact form (RFC 7515 §7.1) and the keys
of a JWK Set (RFC 7517), for the two algorithms of the allow-list, RS256 and ES256 (RFC 7518
§3.3, §3.4). The name in a token's header is read only through `Alg.parse?`, so `none`, the HMAC
algorithms and every other name are refused before any key is looked at, and a key checks only
the algorithm of its type (`Jwk.fits`): an RSA key is never taken for an HMAC secret.

`verify_ok` says what an accepted token is: a header that names RS256 or ES256, and a key of the
set, of that algorithm and of the header's `kid`, under which the signature checks.
-/

@[expose] public section

namespace Lanes.Jose

inductive Alg where
  | rs256
  | es256
  deriving DecidableEq, Repr, Hashable

def Alg.name : Alg → String
  | .rs256 => "RS256"
  | .es256 => "ES256"

/-- The allow-list. -/
def Alg.parse? (s : String) : Option Alg :=
  if s = "RS256" then some .rs256 else if s = "ES256" then some .es256 else none

theorem Alg.parse?_eq_some {s : String} {a : Alg} : parse? s = some a ↔ s = a.name := by
  cases a <;> by_cases h1 : s = "RS256" <;> by_cases h2 : s = "ES256" <;> simp_all [parse?, name]

/-- Why a token is refused. -/
inductive Refusal where
  /-- Not three parts of base64url, or a header that is not a JSON object with a name in `alg`. -/
  | malformed
  /-- An algorithm outside the allow-list, `none` and the HMAC ones among them. -/
  | alg (name : String)
  /-- An extension the header says must be understood (`crit`): none is. -/
  | critical
  /-- No key of the set is of the token's algorithm and `kid`. -/
  | unknownKey
  | signature
  deriving DecidableEq, Repr

structure Jwk where
  kid : Option String := none
  /-- The algorithm the set says the key is for, if it says. -/
  alg : Option Alg := none
  key : PublicKey

/-- Whether the key may check a signature made with `alg`: RS256 by an RSA key, ES256 by a P-256
key, and either only if the set names no other algorithm for it. -/
def Jwk.fits (k : Jwk) (alg : Alg) : Bool :=
  k.alg.all (· == alg) && match alg, k.key with
    | .rs256, .rsa .. => true
    | .es256, .p256 .. => true
    | _, _ => false

def str? (j : Json) (name : String) : Option String :=
  match j.getObjVal? name with
  | .ok (.str s) => some s
  | _ => none

/-- A member written in base64url without padding. -/
def bytes? (j : Json) (name : String) : Option ByteArray :=
  (str? j name).bind (Base64.decode .rawUrl)

/-- A key for signatures: RSA with `n` and `e`, or EC on P-256 with `x` and `y`, valid
(`PublicKey.valid`). Any other key is not read, since a set also holds keys for other uses. -/
def Jwk.read? (j : Json) : Option Jwk := do
  if (str? j "use").any (· != "sig") then none
  let alg ← match str? j "alg" with
    | none => some none
    | some name => (Alg.parse? name).map some
  let key ← match str? j "kty" with
    | some "RSA" => (bytes? j "n").bind fun n => (bytes? j "e").map (PublicKey.rsa n)
    | some "EC" =>
      if str? j "crv" == some "P-256" then
        (bytes? j "x").bind fun x => (bytes? j "y").map (PublicKey.p256 x)
      else none
    | _ => none
  if key.valid then return { kid := str? j "kid", alg, key } else none

/-- The keys of a JWK Set that `Jwk.read?` reads. -/
def readKeys (text : String) : Except Refusal (List Jwk) :=
  match Json.parse text with
  | .ok j =>
    match j.getObjVal? "keys" with
    | .ok (.arr keys) => .ok (keys.toList.filterMap Jwk.read?)
    | _ => .error .malformed
  | .error _ => .error .malformed

/-- A token in compact form, taken apart. -/
structure Compact where
  header : Json
  alg : Alg
  kid : Option String
  /-- What the signature is over: the first two parts, as sent, and the dot between. -/
  signed : ByteArray
  payload : ByteArray
  signature : ByteArray

/-- The algorithm and the key id a header names. -/
def readHeader (j : Json) : Except Refusal (Alg × Option String) :=
  match j, j.getObjVal? "crit", j.getObjVal? "alg", j.getObjVal? "kid" with
  | .obj _, .ok _, _, _ => .error .critical
  | .obj _, .error _, .ok (.str name), kid =>
    match Alg.parse? name, kid with
    | some a, .ok (.str k) => .ok (a, some k)
    | some a, .error _ => .ok (a, none)
    | some _, .ok _ => .error .malformed
    | none, _ => .error (.alg name)
  | _, _, _, _ => .error .malformed

theorem readHeader_alg {j : Json} {a : Alg} {kid : Option String}
    (h : readHeader j = .ok (a, kid)) : j.getObjVal? "alg" = .ok (.str a.name) := by
  unfold readHeader at h
  split at h <;> try cases h
  rename_i halg
  rw [halg]
  split at h <;> cases h <;> rename_i hp <;> rw [Alg.parse?_eq_some.mp hp]

def Compact.read (token : String) : Except Refusal Compact :=
  match token.splitOn "." with
  | [h, p, s] =>
    match Base64.decode .rawUrl h, Base64.decode .rawUrl p, Base64.decode .rawUrl s with
    | some hb, some pb, some sb =>
      match (String.fromUTF8? hb).map Json.parse with
      | some (.ok j) =>
        (readHeader j).map fun (alg, kid) =>
          { header := j, alg, kid, signed := (h ++ "." ++ p).toUTF8, payload := pb, signature := sb }
      | _ => .error .malformed
    | _, _, _ => .error .malformed
  | _ => .error .malformed

/-- A token's header names an algorithm of the allow-list, exactly. -/
theorem Compact.read_alg {token : String} {c : Compact} (h : Compact.read token = .ok c) :
    c.header.getObjVal? "alg" = .ok (.str c.alg.name) := by
  unfold Compact.read at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  rename_i j _
  cases hh : readHeader j with
  | error _ => rw [hh] at h; cases h
  | ok v =>
    rw [hh] at h
    cases h
    exact readHeader_alg hh

/-- The keys that may check the token: of its algorithm, and of its `kid` if it names one. -/
def candidates (keys : List Jwk) (c : Compact) : List Jwk :=
  keys.filter fun k => k.fits c.alg && (c.kid.isNone || k.kid == c.kid)

/-- The token, if a key of `keys` that may check it does. -/
def verify (keys : List Jwk) (token : String) : Except Refusal Compact := do
  let c ← Compact.read token
  let ks := candidates keys c
  if ks.isEmpty then throw .unknownKey
  if ks.any fun k => k.key.verifies c.signed c.signature then return c
  throw .signature

theorem verify_ok {keys : List Jwk} {token : String} {c : Compact}
    (h : verify keys token = .ok c) :
    Compact.read token = .ok c ∧ c.header.getObjVal? "alg" = .ok (.str c.alg.name)
      ∧ ∃ k ∈ keys, k.fits c.alg ∧ (c.kid = none ∨ k.kid = c.kid)
        ∧ k.key.verifies c.signed c.signature := by
  unfold verify at h
  cases hr : Compact.read token with
  | error _ => rw [hr] at h; cases h
  | ok c' =>
    simp only [hr, bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · rename_i hany
        cases h
        refine ⟨rfl, Compact.read_alg hr, ?_⟩
        obtain ⟨k, hk, hv⟩ := List.any_eq_true.mp hany
        simp only [candidates, List.mem_filter, Bool.and_eq_true, Bool.or_eq_true,
          Option.isNone_iff_eq_none, beq_iff_eq] at hk
        exact ⟨k, hk.1, hk.2.1, hk.2.2.imp id Eq.symm |>.imp id (fun h => h.symm), hv⟩
      · cases h

end Lanes.Jose
