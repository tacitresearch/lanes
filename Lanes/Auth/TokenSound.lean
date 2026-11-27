/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Auth.Token
public import Lanes.Data.Utf8

/-!
What signed tokens and form tokens accept, up to the one assumption `TRUSTED.md` makes of
HMAC-SHA-256: that nobody without the key finds two messages with one tag. `verify` accepts
exactly the tokens `sign` makes for its purpose (`verify_eq_some`); one made for another purpose
passes only if two different messages have one tag (`verify_sign_other`, through `message_inj`).
`checkForm` accepts exactly the form token of its session (`checkForm_iff`); another session's
passes only if two different messages have one tag (`checkForm_other`).
-/

@[expose] public section

namespace Lanes.Auth

private theorem toList_length_tag (key : Hmac.Key) (purpose payload : String) :
    (tag key purpose payload).toList.length = 64 := by
  rw [String.length_toList]; exact length_tag key purpose payload

private theorem eq_of_toByteArray {s t : String} (h : s.toByteArray = t.toByteArray) : s = t := by
  have := congrArg String.fromUTF8? h
  rw [fromUTF8?_toByteArray, fromUTF8?_toByteArray] at this
  exact Option.some.inj this

/-- `verify` accepts a token exactly when it is what `sign` makes of its payload, for that key and
purpose. -/
theorem verify_eq_some {key : Hmac.Key} {purpose token payload : String} :
    verify key purpose token = some payload ↔ token = sign key purpose payload := by
  constructor
  · intro h
    unfold verify at h
    dsimp only at h
    split at h
    · rename_i rest hdrop
      split at h
      · rename_i hsame
        cases h
        have htag := eq_of_toByteArray ((Bytes.same_iff _ _).mp hsame)
        apply String.toList_inj.mp
        rw [← List.take_append_drop 64 token.toList, hdrop]
        simp [sign, htag]
      · cases h
    · cases h
  · rintro rfl
    exact verify_sign key purpose payload

private theorem zero_not_mem {s : String} (h : '\x00' ∉ s.toList) : (0 : UInt8) ∉ s.toUTF8.data.toList := by
  intro hmem
  rw [String.toUTF8_eq_toByteArray, data_toList_toByteArray, List.mem_flatMap] at hmem
  obtain ⟨c, hc, hb⟩ := hmem
  have := utf8EncodeChar_ascii hb (by decide)
  have hc0 : c = '\x00' := Char.toNat_inj.mp (by rw [← this]; rfl)
  exact h (hc0 ▸ hc)

/-- Different purposes without a zero byte, or different payloads, make different messages. -/
theorem message_inj {purpose purpose' payload payload' : String} (hp : '\x00' ∉ purpose.toList)
    (hp' : '\x00' ∉ purpose'.toList) (h : message purpose payload = message purpose' payload') :
    purpose = purpose' ∧ payload = payload' := by
  have hdata := congrArg (fun b : ByteArray => b.data.toList) h
  simp only [message, ByteArray.data_append, Array.toList_append, List.append_assoc] at hdata
  have hstop : ∀ s : String, '\x00' ∉ s.toList → ∀ b ∈ s.toUTF8.data.toList, (b != 0) = true :=
    fun s hs b hb => bne_iff_ne.mpr fun e => zero_not_mem hs (e ▸ hb)
  have htake := congrArg (List.takeWhile (· != 0)) hdata
  have hdrop := congrArg (List.dropWhile (· != 0)) hdata
  rw [List.takeWhile_append_of_pos (hstop _ hp), List.takeWhile_append_of_pos (hstop _ hp')]
    at htake
  rw [List.dropWhile_append_of_pos (hstop _ hp), List.dropWhile_append_of_pos (hstop _ hp')]
    at hdrop
  simp only [List.takeWhile_cons,
    List.dropWhile_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    List.cons_append, List.nil_append, List.cons.injEq, true_and] at htake hdrop
  refine ⟨eq_of_toByteArray ?_, eq_of_toByteArray ?_⟩
  · exact ByteArray.ext (Array.ext' (by simpa [String.toUTF8_eq_toByteArray] using htake))
  · exact ByteArray.ext (Array.ext' (by simpa [String.toUTF8_eq_toByteArray] using hdrop))

private theorem sign_inj {key : Hmac.Key} {purpose purpose' payload payload' : String}
    (h : sign key purpose payload = sign key purpose' payload') :
    tag key purpose payload = tag key purpose' payload' ∧ payload = payload' := by
  have hl := congrArg String.toList h
  simp only [sign, String.toList_append] at hl
  have h₁ := congrArg (List.take 64) hl
  have h₂ := congrArg (List.drop 64) hl
  simp only [List.append_assoc, List.take_append_of_le_length (Nat.le_of_eq (toList_length_tag ..).symm),
    List.take_of_length_le (Nat.le_of_eq (toList_length_tag ..)),
    List.drop_append_of_le_length (Nat.le_of_eq (toList_length_tag ..).symm),
    List.drop_eq_nil_of_le (Nat.le_of_eq (toList_length_tag ..)), List.nil_append] at h₁ h₂
  simp only [show ".".toList = ['.'] from rfl, List.singleton_append, List.cons.injEq,
    true_and] at h₂
  exact ⟨String.toList_inj.mp h₁, String.toList_inj.mp h₂⟩

private theorem hex_inj {a b : ByteArray} (h : Bytes.hex a = Bytes.hex b) : a = b := by
  have := congrArg Bytes.unhex? h
  rw [Bytes.unhex?_hex, Bytes.unhex?_hex] at this
  exact Option.some.inj this

/-- A token signed for one purpose passes for another only if HMAC gives two different messages
one tag, which `TRUSTED.md` assumes nobody without the key can bring about. -/
theorem verify_sign_other {key : Hmac.Key} {purpose purpose' payload payload' : String}
    (hp : '\x00' ∉ purpose.toList) (hp' : '\x00' ∉ purpose'.toList) (hne : purpose ≠ purpose')
    (h : verify key purpose' (sign key purpose payload) = some payload') :
    payload' = payload ∧ message purpose payload ≠ message purpose' payload
      ∧ key.mac (message purpose payload) = key.mac (message purpose' payload) := by
  obtain ⟨htag, rfl⟩ := sign_inj (verify_eq_some.mp h)
  exact ⟨rfl, fun e => hne (message_inj hp hp' e).1, hex_inj htag⟩

/-- `checkForm` accepts exactly the form token of its session. -/
theorem checkForm_iff {key : Hmac.Key} {session field : String} :
    checkForm key session field = true ↔ field = formToken key session := by
  rw [checkForm, Bytes.same_iff]
  exact ⟨fun h => (eq_of_toByteArray h).symm, fun h => h ▸ rfl⟩

/-- The form token of one session passes for another only if HMAC gives two different messages
one tag. -/
theorem checkForm_other {key : Hmac.Key} {session session' : String} (hne : session ≠ session')
    (h : checkForm key session (formToken key session') = true) :
    message "form" session ≠ message "form" session'
      ∧ key.mac (message "form" session) = key.mac (message "form" session') := by
  have htag := checkForm_iff.mp h
  refine ⟨fun e => hne (message_inj (by decide) (by decide) e).2, hex_inj htag.symm⟩

end Lanes.Auth
