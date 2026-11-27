/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Crypto.Native

/-!
Signed tokens: a payload and its HMAC-SHA-256 tag under a server key, for a named purpose, so a
token made for one purpose (a session cookie) is no token for another (a form). The bridge of a
web application verifies a token where a request enters and hands the system what it carried,
never what the request body claims.

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

/-- What a tag authenticates. `purpose` is a name the application fixes, without a zero byte, so
the zero byte after it keeps two purposes apart whatever the payloads (`message_inj`). -/
def message (purpose payload : String) : ByteArray :=
  purpose.toUTF8 ++ ⟨#[0]⟩ ++ payload.toUTF8

/-- The tag of `payload` for `purpose`: 64 hex digits. -/
def tag (key : Hmac.Key) (purpose payload : String) : String :=
  Bytes.hex (key.mac (message purpose payload))

def sign (key : Hmac.Key) (purpose payload : String) : String :=
  tag key purpose payload ++ "." ++ payload

/-- The payload of a token, if its tag is the one `key` gives it for `purpose`. The tags are
compared in time that does not depend on where they differ. -/
def verify (key : Hmac.Key) (purpose token : String) : Option String :=
  let chars := token.toList
  match chars.drop 64 with
  | '.' :: rest =>
    let payload := String.ofList rest
    if Bytes.same (tag key purpose payload).toUTF8 (String.ofList (chars.take 64)).toUTF8 then
      some payload
    else none
  | _ => none

theorem length_hex (bytes : ByteArray) : (Bytes.hex bytes).length = 2 * bytes.size := by
  simp only [Bytes.hex, String.length_ofList, List.length_flatMap, List.length_cons,
    List.length_nil]
  show _ = 2 * bytes.data.size
  simp [List.map_const', Nat.mul_comm]

theorem length_tag (key : Hmac.Key) (purpose payload : String) :
    (tag key purpose payload).length = 64 := by
  simp [tag, length_hex, Hmac.size_mac]

theorem verify_sign (key : Hmac.Key) (purpose payload : String) :
    verify key purpose (sign key purpose payload) = some payload := by
  have hlen : (tag key purpose payload).toList.length = 64 := by
    rw [String.length_toList]; exact length_tag key purpose payload
  have hchars : (sign key purpose payload).toList
      = (tag key purpose payload).toList ++ '.' :: payload.toList := by
    simp [sign]
  simp only [verify, hchars, List.drop_append_of_le_length (Nat.le_of_eq hlen.symm),
    List.drop_eq_nil_of_le (Nat.le_of_eq hlen), List.nil_append, String.ofList_toList,
    List.take_append_of_le_length (Nat.le_of_eq hlen.symm),
    List.take_of_length_le (Nat.le_of_eq hlen), (Bytes.same_iff _ _).mpr rfl, ite_true]

/-- The token a form carries for a session, so that a page on another site, which cannot read
the session's cookie, cannot make a request that passes as the user's. It is the tag of `sign`
for the purpose `form`, which is therefore no purpose for an application to sign with. -/
def formToken (key : Hmac.Key) (session : String) : String :=
  tag key "form" session

def checkForm (key : Hmac.Key) (session field : String) : Bool :=
  Bytes.same (formToken key session).toUTF8 field.toUTF8

theorem checkForm_formToken (key : Hmac.Key) (session : String) :
    checkForm key session (formToken key session) = true :=
  (Bytes.same_iff _ _).mpr rfl

end Lanes.Auth
