/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Auth.Token
public import Lanes.Proof.Utf8

/-!
What signed tokens and form tokens accept, up to the one assumption `TRUSTED.md` makes of
HMAC-SHA-256: that nobody without the key finds two messages with one tag. `verify` accepts
exactly the tokens `signWith` makes, before their expiry, with a key the keys name by its id
(`verify_eq_some`); one made for another purpose passes only if two different messages have one
tag (`verify_sign_other`, through `message_inj`). `checkForm` accepts exactly the form tokens of
its session under such a key (`checkForm_iff`); another session's passes only if two different
messages have one tag (`checkForm_other`).
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

/-- `verify` accepts a token exactly when it is what `signWith` makes of its payload, for that
purpose, with a key the keys name by its id, and it has not expired. -/
theorem verify_eq_some {keys : Keys} {purpose : String} {now_s : Nat} {token payload : String} :
    verify keys purpose now_s token = some payload
      ↔ ∃ id key expires_s, keys.find? id = some key ∧ now_s < expires_s
        ∧ token = signWith ⟨id, key⟩ purpose expires_s payload := by
  constructor
  · intro h
    unfold verify at h
    split at h
    · rename_i id expires_s payload' _
      split at h
      · rename_i key hk
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          exact ⟨id, key, expires_s, hk, hc.1, (eq_of_toByteArray ((Bytes.same_iff _ _).mp hc.2)).symm⟩
        · cases h
      · cases h
    · cases h
  · rintro ⟨id, key, expires_s, hk, hlt, rfl⟩
    exact verify_signWith (s := ⟨id, key⟩) hk purpose hlt payload

/-- Two tokens are one only with one key id, expiry and payload. -/
theorem signWith_inj {s s' : Signer} {purpose purpose' : String} {e e' : Nat} {p p' : String}
    (h : signWith s purpose e p = signWith s' purpose' e' p') : s.id = s'.id ∧ e = e' ∧ p = p' := by
  have := congrArg fields h
  rw [fields_signWith, fields_signWith] at this
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this

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

private theorem tag_of_signWith {s s' : Signer} {purpose purpose' : String} {e : Nat} {p : String}
    (hid : s.id = s'.id) (h : signWith s purpose e p = signWith s' purpose' e p) :
    tag s.key purpose (head s.id e ++ "." ++ p) = tag s'.key purpose' (head s'.id e ++ "." ++ p) := by
  have hl := congrArg String.toList h
  rw [toList_signWith, toList_signWith, hid] at hl
  simp only [List.cons.injEq, List.append_cancel_left_eq, true_and] at hl
  have := List.append_cancel_right hl
  rw [hid]
  exact String.toList_inj.mp this

private theorem hex_inj {a b : ByteArray} (h : Bytes.hex a = Bytes.hex b) : a = b := by
  have := congrArg Bytes.unhex? h
  rw [Bytes.unhex?_hex, Bytes.unhex?_hex] at this
  exact Option.some.inj this

/-- A token signed for one purpose passes for another only if HMAC gives two different messages
one tag, which `TRUSTED.md` assumes nobody without the key can bring about. -/
theorem verify_sign_other {keys : Keys} {s : Signer} (hk : keys.find? s.id = some s.key)
    {purpose purpose' payload payload' : String} {now_s expires_s : Nat}
    (hp : '\x00' ∉ purpose.toList) (hp' : '\x00' ∉ purpose'.toList) (hne : purpose ≠ purpose')
    (h : verify keys purpose' now_s (signWith s purpose expires_s payload) = some payload') :
    payload' = payload
      ∧ message purpose (head s.id expires_s ++ "." ++ payload)
        ≠ message purpose' (head s.id expires_s ++ "." ++ payload)
      ∧ s.key.mac (message purpose (head s.id expires_s ++ "." ++ payload))
        = s.key.mac (message purpose' (head s.id expires_s ++ "." ++ payload)) := by
  obtain ⟨id, key, e, hk', _, heq⟩ := verify_eq_some.mp h
  obtain ⟨hid, rfl, rfl⟩ := signWith_inj heq
  have hkey : key = s.key := by
    simp only at hid
    rw [← hid, hk] at hk'
    exact (Option.some.inj hk').symm
  subst hkey
  have htag := tag_of_signWith (s' := ⟨id, s.key⟩) hid heq
  simp only [tag] at htag hid
  rw [← hid] at htag
  exact ⟨rfl, fun e => hne (message_inj hp hp' e).1, hex_inj htag⟩

/-- A key id and the rest of a form token read apart. -/
private theorem formTokenWith_inj {s s' : Signer} {session session' : String}
    (h : formTokenWith s session = formTokenWith s' session') :
    s.id = s'.id ∧ tag s.key "form" (formHead s.id ++ "." ++ session)
      = tag s'.key "form" (formHead s'.id ++ "." ++ session') := by
  have hid : s.id = s'.id := by
    have := congrArg formId h
    rw [formId_formTokenWith, formId_formTokenWith] at this
    exact Option.some.inj this
  refine ⟨hid, ?_⟩
  have hl := congrArg String.toList h
  simp only [formTokenWith, String.toList_append, hid, List.append_assoc,
    List.append_cancel_left_eq] at hl
  rw [hid]
  exact String.toList_inj.mp hl

/-- `checkForm` accepts exactly the form tokens of its session under a key the keys name by its
id. -/
theorem checkForm_iff {keys : Keys} {session field : String} :
    checkForm keys session field = true
      ↔ ∃ id key, keys.find? id = some key ∧ field = formTokenWith ⟨id, key⟩ session := by
  constructor
  · intro h
    unfold checkForm at h
    split at h
    · rename_i id key hf
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff,
        Prod.mk.injEq] at hf
      obtain ⟨id', _, key', hk, rfl, rfl⟩ := hf
      exact ⟨id', key', hk, (eq_of_toByteArray ((Bytes.same_iff _ _).mp h)).symm⟩
    · cases h
  · rintro ⟨id, key, hk, rfl⟩
    exact checkForm_formTokenWith (s := ⟨id, key⟩) hk session

/-- The form token of one session passes for another only if HMAC gives two different messages
one tag. -/
theorem checkForm_other {keys : Keys} {s : Signer} (hk : keys.find? s.id = some s.key)
    {session session' : String} (hne : session ≠ session')
    (h : checkForm keys session (formTokenWith s session') = true) :
    message "form" (formHead s.id ++ "." ++ session) ≠ message "form" (formHead s.id ++ "." ++ session')
      ∧ s.key.mac (message "form" (formHead s.id ++ "." ++ session))
        = s.key.mac (message "form" (formHead s.id ++ "." ++ session')) := by
  obtain ⟨id, key, hk', heq⟩ := checkForm_iff.mp h
  obtain ⟨hid, htag⟩ := formTokenWith_inj heq
  have hkey : key = s.key := by
    simp only at hid
    rw [← hid, hk] at hk'
    exact (Option.some.inj hk').symm
  subst hkey
  simp only [tag] at htag hid
  rw [← hid] at htag
  refine ⟨fun e => hne ?_, hex_inj htag.symm⟩
  have := (message_inj (by decide) (by decide) e).2
  have hl := congrArg String.toList this
  simp only [String.toList_append, List.append_cancel_left_eq] at hl
  exact String.toList_inj.mp hl

end Lanes.Auth
