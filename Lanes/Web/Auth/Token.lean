/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Crypto.Native
public import Lanes.Lib.Encoding.Digits

/-!
Signed tokens: a payload and its HMAC-SHA-256 tag under a server key, for a named purpose, so a
token made for one purpose (a session cookie) is no token for another (a form). The bridge of a
web application verifies a token where a request enters and hands the system what it carried,
never what the request body claims.

A token is `v1.<key id>.<expiry>.<tag>.<payload>`. The version says how to read the rest; the key
id picks the key it is checked with, so a key can be rotated while the tokens of the one before
are still accepted (`Keys.rotate`, `verify_rotate`); the expiry, in seconds since the Unix epoch,
is under the tag, and a token is refused from then on (`verify_expired`). A form token is
`v1.<key id>.<tag>`, bound to a session, and ends with it.

`verify_sign` proves a token reads back as its payload. That nobody without the key can make a
token is the assumption that HMAC-SHA-256 is a pseudorandom function (`TRUSTED.md`).
-/

@[expose] public section

namespace Lanes.Hmac

/-- A key of the server's, which has no `Repr` so that it is not printed. -/
structure Key where
  bytes : ByteArray

def Key.of (key : ByteArray) : Key := ⟨key⟩

def Key.mac (key : Key) (msg : ByteArray) : ByteArray := hmac key.bytes msg

theorem size_mac (key : Key) (msg : ByteArray) : (key.mac msg).size = 32 := size_hmac _ _

end Lanes.Hmac

namespace Lanes.Auth

/-- A key under the id the tokens it signs carry. -/
structure Signer where
  id : Nat
  key : Hmac.Key

/-- The keys of a deployment: `current` signs, and a token of any of them is checked with the
key its id names, the first of that id. -/
structure Keys where
  current : Signer
  previous : List Signer := []

namespace Keys

/-- One key, as id 0: for a key that is never rotated, such as one drawn at each start. -/
def of (key : Hmac.Key) : Keys := ⟨⟨0, key⟩, []⟩

def find? (keys : Keys) (id : Nat) : Option Hmac.Key :=
  ((keys.current :: keys.previous).find? (·.id == id)).map (·.key)

/-- `next` signs from now on; the keys before it still verify until they are dropped. -/
def rotate (keys : Keys) (next : Signer) : Keys := ⟨next, keys.current :: keys.previous⟩

theorem find?_current (keys : Keys) : keys.find? keys.current.id = some keys.current.key := by
  simp [find?]

/-- After a rotation to a new id, a key keeps its id. -/
theorem find?_rotate {keys : Keys} {next : Signer} {id : Nat} (h : next.id ≠ id) :
    (keys.rotate next).find? id = keys.find? id := by
  simp [find?, rotate, List.find?_cons, beq_iff_eq, h]

end Keys

/-- What a tag authenticates. `purpose` is a name the application fixes, without a zero byte, so
the zero byte after it keeps two purposes apart whatever the payloads (`message_inj`). -/
def message (purpose payload : String) : ByteArray :=
  purpose.toUTF8 ++ ⟨#[0]⟩ ++ payload.toUTF8

/-- The tag of `payload` for `purpose`: 64 hex digits. -/
def tag (key : Hmac.Key) (purpose payload : String) : String :=
  Bytes.hex (key.mac (message purpose payload))

/-- A number in decimal, with no leading zero. -/
def decimal (n : Nat) : String := String.ofList (Digits.toChars 10 n)

/-- What comes before a token's tag, and is under it: the version, the key's id and the second
the token expires at. -/
def head (id expires_s : Nat) : String := "v1." ++ decimal id ++ "." ++ decimal expires_s

def signWith (s : Signer) (purpose : String) (expires_s : Nat) (payload : String) : String :=
  head s.id expires_s ++ "." ++ tag s.key purpose (head s.id expires_s ++ "." ++ payload) ++ "."
    ++ payload

/-- A token of `payload` for `purpose`, under the current key, refused from `expires_s`. -/
def sign (keys : Keys) (purpose : String) (expires_s : Nat) (payload : String) : String :=
  signWith keys.current purpose expires_s payload

/-- The text before the first `.`, and the text after it. -/
def splitDot : List Char → Option (List Char × List Char)
  | [] => none
  | '.' :: b => some ([], b)
  | c :: rest => (splitDot rest).map fun (a, b) => (c :: a, b)

/-- The key id, expiry and payload a token names where `signWith` writes them. -/
def fields (token : String) : Option (Nat × Nat × String) :=
  match token.toList with
  | 'v' :: '1' :: '.' :: rest => do
    let (id, rest) ← splitDot rest
    let (expires, rest) ← splitDot rest
    let id ← Digits.ofChars? 10 id
    let expires_s ← Digits.ofChars? 10 expires
    match rest.drop 64 with
    | '.' :: payload => some (id, expires_s, String.ofList payload)
    | _ => none
  | _ => none

/-- The payload of a token, if it is what its key makes of it for `purpose` and has not expired
at `now_s`. The token is compared whole, in time that depends on its length only. -/
def verify (keys : Keys) (purpose : String) (now_s : Nat) (token : String) : Option String :=
  match fields token with
  | some (id, expires_s, payload) =>
    match keys.find? id with
    | some key =>
      if now_s < expires_s
          && Bytes.same (signWith ⟨id, key⟩ purpose expires_s payload).toUTF8 token.toUTF8 then
        some payload
      else none
    | none => none
  | none => none

theorem length_hex (bytes : ByteArray) : (Bytes.hex bytes).length = 2 * bytes.size := by
  simp only [Bytes.hex, String.length_ofList, List.length_flatMap, List.length_cons,
    List.length_nil]
  show _ = 2 * bytes.data.size
  simp [List.map_const', Nat.mul_comm]

theorem length_tag (key : Hmac.Key) (purpose payload : String) :
    (tag key purpose payload).length = 64 := by
  simp [tag, length_hex, Hmac.size_mac]

theorem splitDot_append {a b : List Char} (h : '.' ∉ a) : splitDot (a ++ '.' :: b) = some (a, b) := by
  induction a with
  | nil => rfl
  | cons c a ih =>
    have hc : c ≠ '.' := fun e => h (e ▸ List.mem_cons_self ..)
    rw [List.cons_append, splitDot.eq_3 c _ hc, ih (fun m => h (List.mem_cons_of_mem _ m))]
    rfl

theorem dot_not_mem_toChars (n : Nat) : '.' ∉ Digits.toChars 10 n := by
  intro h
  have := Digits.mem_toChars (by omega) (by omega) h
  simp [Digits.lower] at this

theorem toList_signWith (s : Signer) (purpose : String) (expires_s : Nat) (payload : String) :
    (signWith s purpose expires_s payload).toList
      = 'v' :: '1' :: '.' :: ((decimal s.id).toList ++ '.' :: ((decimal expires_s).toList
        ++ '.' :: ((tag s.key purpose (head s.id expires_s ++ "." ++ payload)).toList
          ++ '.' :: payload.toList))) := by
  simp [signWith, head]

theorem fields_signWith (s : Signer) (purpose : String) (expires_s : Nat) (payload : String) :
    fields (signWith s purpose expires_s payload) = some (s.id, expires_s, payload) := by
  have hlen : (tag s.key purpose (head s.id expires_s ++ "." ++ payload)).toList.length = 64 := by
    rw [String.length_toList]; exact length_tag ..
  simp only [fields, toList_signWith, decimal, String.toList_ofList,
    splitDot_append (dot_not_mem_toChars _), Digits.ofChars?_toChars (b := 10) (by omega) (by omega),
    List.drop_append_of_le_length (Nat.le_of_eq hlen.symm),
    List.drop_eq_nil_of_le (Nat.le_of_eq hlen), List.nil_append, String.ofList_toList,
    Option.bind_eq_bind, Option.bind_some]

/-- A token verifies, until it expires, under keys in which its key's id names its key. -/
theorem verify_signWith {keys : Keys} {s : Signer} (hk : keys.find? s.id = some s.key)
    (purpose : String) {now_s expires_s : Nat} (h : now_s < expires_s) (payload : String) :
    verify keys purpose now_s (signWith s purpose expires_s payload) = some payload := by
  simp [verify, fields_signWith, hk, h, (Bytes.same_iff _ _).mpr]

theorem verify_sign (keys : Keys) (purpose : String) {now_s expires_s : Nat} (h : now_s < expires_s)
    (payload : String) : verify keys purpose now_s (sign keys purpose expires_s payload) = some payload :=
  verify_signWith keys.find?_current purpose h payload

/-- A token signed before a rotation to a new id still verifies after it. -/
theorem verify_rotate (keys : Keys) {next : Signer} (hid : next.id ≠ keys.current.id)
    (purpose : String) {now_s expires_s : Nat} (h : now_s < expires_s) (payload : String) :
    verify (keys.rotate next) purpose now_s (sign keys purpose expires_s payload) = some payload :=
  verify_signWith (by rw [Keys.find?_rotate hid]; exact keys.find?_current) purpose h payload

/-- From its expiry on, a token is refused under any keys. -/
theorem verify_expired (keys : Keys) (s : Signer) (purpose : String) {now_s expires_s : Nat}
    (h : expires_s ≤ now_s) (payload : String) :
    verify keys purpose now_s (signWith s purpose expires_s payload) = none := by
  have : ¬ now_s < expires_s := by omega
  simp only [verify, fields_signWith]
  split <;> simp [this]

/-- The prefix of a form token, under its tag: the version and the key's id. -/
def formHead (id : Nat) : String := "v1." ++ decimal id

/-- The token a form carries for a session, so that a page on another site, which cannot read
the session's cookie, cannot make a request that passes as the user's. Its tag is that of
`formHead id ++ "." ++ session` for the purpose `form`, which is therefore no purpose for an
application to sign with. -/
def formTokenWith (s : Signer) (session : String) : String :=
  formHead s.id ++ "." ++ tag s.key "form" (formHead s.id ++ "." ++ session)

def formToken (keys : Keys) (session : String) : String := formTokenWith keys.current session

/-- The key id a form token names. -/
def formId (field : String) : Option Nat :=
  match field.toList with
  | 'v' :: '1' :: '.' :: rest => do
    let (id, _) ← splitDot rest
    Digits.ofChars? 10 id
  | _ => none

/-- Whether `field` is the form token of `session` under the key its id names, compared whole in
time that depends on its length only. -/
def checkForm (keys : Keys) (session field : String) : Bool :=
  match formId field >>= fun id => (keys.find? id).map (id, ·) with
  | some (id, key) => Bytes.same (formTokenWith ⟨id, key⟩ session).toUTF8 field.toUTF8
  | none => false

theorem formId_formTokenWith (s : Signer) (session : String) :
    formId (formTokenWith s session) = some s.id := by
  have : (formTokenWith s session).toList = 'v' :: '1' :: '.' :: ((decimal s.id).toList
      ++ '.' :: (tag s.key "form" (formHead s.id ++ "." ++ session)).toList) := by
    simp [formTokenWith, formHead]
  simp only [formId, this, decimal, String.toList_ofList, splitDot_append (dot_not_mem_toChars _),
    Option.bind_eq_bind, Option.bind_some, Digits.ofChars?_toChars (b := 10) (by omega) (by omega)]

theorem checkForm_formTokenWith {keys : Keys} {s : Signer} (hk : keys.find? s.id = some s.key)
    (session : String) : checkForm keys session (formTokenWith s session) = true := by
  simp [checkForm, formId_formTokenWith, hk, (Bytes.same_iff _ _).mpr]

theorem checkForm_formToken (keys : Keys) (session : String) :
    checkForm keys session (formToken keys session) = true :=
  checkForm_formTokenWith keys.find?_current session

end Lanes.Auth
