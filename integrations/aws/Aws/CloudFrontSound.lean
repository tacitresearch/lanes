/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Aws.CloudFront
import Lanes.Lib.Encoding.Json.PrinterSound

/-!
What CloudFront checks a link against: the canned policy signed is byte for byte the one AWS
documents for the URL and the time (`cannedPolicy_eq`), which CloudFront builds again to check
the signature; CloudFront's base64 reads back (`decode_encode`); and every parameter and cookie
needs no escaping, so every cookie is set (`cookies_valid`).
-/

namespace Aws.CloudFront

open Lanes

theorem swap_swap (c : Char) : swap (swap c) = c := by
  unfold swap
  repeat' split
  all_goals simp_all

theorem decode_encode (bytes : ByteArray) : decode (encode bytes) = some bytes := by
  have : (Base64.encode .std bytes).toList.map (swap ∘ swap) = (Base64.encode .std bytes).toList := by
    simp [Function.comp_def, swap_swap]
  simp [decode, encode, List.map_map, this, Base64.decode_encode]

theorem urlSafe_swap_char : ∀ v : Fin 64, urlSafe (swap (Base64.Alphabet.std.char v)) = true := by
  decide

theorem urlSafe_of_mem_encode {bytes : ByteArray} {c : Char} (h : c ∈ (encode bytes).toList) :
    urlSafe c = true := by
  simp only [encode, String.toList_ofList, List.mem_map] at h
  obtain ⟨d, hd, rfl⟩ := h
  rcases Base64.allowed_of_mem_encode .std bytes hd with ⟨v, rfl⟩ | ⟨_, rfl⟩
  · exact urlSafe_swap_char v
  · decide

theorem eq_iff_val (c d : Char) : c = d ↔ c.val.toNat = d.val.toNat :=
  ⟨fun h => h ▸ rfl, fun h => Char.ext (UInt32.toNat_inj.mp h)⟩

theorem cookieOctet_of_urlSafe {c : Char} (h : urlSafe c = true) : Http.cookieOctet c = true := by
  simp only [urlSafe, Char.isAlphanum, Char.isAlpha, Char.isUpper, Char.isLower, Char.isDigit,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, UInt32.le_iff_toNat_le,
    eq_iff_val] at h
  simp only [Http.cookieOctet, Http.visible, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq, UInt32.le_iff_toNat_le, eq_iff_val]
  simp at h ⊢
  omega

theorem needsEscape_of_resourceChar {c : Char} (h : resourceChar c = true) :
    Json.needsEscape c = false := by
  simp only [resourceChar, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, _⟩, h2⟩, h3⟩ := h
  simp only [Json.needsEscape, Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
  refine ⟨⟨h2, h3⟩, ?_⟩
  simp only [Char.le_def, UInt32.le_iff_toNat_le] at h1
  intro hc
  rw [UInt32.lt_iff_toNat_lt] at hc
  simp at h1 hc
  omega

theorem compress_resource (r : Resource) :
    (Json.str r.val).compress.toList = '"' :: r.val.toList ++ ['"'] := by
  have h : ∀ c ∈ r.val.toList, Json.needsEscape c = false := fun c hc =>
    needsEscape_of_resourceChar (List.all_eq_true.mp r.property.2 c hc)
  simp [Json.compress, Json.compressTo, Json.renderString_toList, Json.flatMap_escapeChar h]

theorem compress_nat (e : Nat) : (Json.num (e : JsonNumber)).compress.toList = (toString e).toList := by
  simp [Json.compress, Json.compressTo, JsonNumber.toString, JsonNumber.fromNat, JsonNumber.fromInt]
  show (Int.ofNat e).repr.toList = _
  simp [Int.repr, Nat.repr]

theorem escapeChar_plain {c : Char} (h : Json.needsEscape c = false) :
    (Json.escapeChar "" c).toList = [c] := Json.escapeChar_of_not_needsEscape h

theorem cannedPolicy_eq (r : Resource) (e : Nat) :
    cannedPolicy r e = "{\"Statement\":[{\"Resource\":\"" ++ r.val
      ++ "\",\"Condition\":{\"DateLessThan\":{\"AWS:EpochTime\":" ++ toString e ++ "}}}]}" := by
  apply String.ext
  simp [cannedPolicy, Policy.text, Policy.document, Policy.conditions, epoch, Json.compress_obj,
    Json.compress_arr, Json.renderString_toList, compress_resource, compress_nat]
  simp [escapeChar_plain, Json.needsEscape]

theorem urlSafe_toString (e : Nat) : (toString e).toList.all urlSafe = true := by
  rw [List.all_eq_true]
  intro c hc
  have hd := Json.isDigit_of_mem_toDigits (n := e) (by simpa [Nat.repr] using hc)
  simp only [urlSafe, Char.isAlphanum, Char.isDigit, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  exact .inl (.inl (.inl (.inr ⟨hd.1, hd.2⟩)))

theorem urlSafe_encode (bytes : ByteArray) : (encode bytes).toList.all urlSafe = true :=
  List.all_eq_true.mpr fun _ hc => urlSafe_of_mem_encode hc

theorem urlSafe_keyId (k : KeyId) : k.val.toList.all urlSafe = true := by
  rw [List.all_eq_true]
  intro c hc
  have := List.all_eq_true.mp k.property.2 c hc
  simp only [Bool.and_eq_true] at this
  simp [urlSafe, this.1]

/-- Every parameter of a link is named by a token after `CloudFront-` and valued in letters,
digits, `-`, `_` and `~`, which neither a URL nor a cookie escapes. -/
theorem fields_safe (keyId : KeyId) (digest : Digest) (g : Grant) (signature : ByteArray) :
    ∀ kv ∈ fields keyId digest g signature,
      Http.token ("CloudFront-" ++ kv.1) = true ∧ kv.2.toList.all urlSafe = true := by
  intro kv hkv
  simp only [fields, List.cons_append, List.mem_cons, List.mem_append] at hkv
  rcases hkv with h | h | h | h
  · cases g <;> simp only at h <;> subst h
    · exact ⟨by dsimp only; decide, urlSafe_toString _⟩
    · exact ⟨by dsimp only; decide, urlSafe_encode _⟩
  · subst h; exact ⟨by dsimp only; decide, urlSafe_encode _⟩
  · subst h; exact ⟨by dsimp only; decide, urlSafe_keyId _⟩
  · split at h <;> simp at h
    subst h; exact ⟨by decide, by decide⟩

/-- Every cookie of a grant is valid, so `Response.setCookie` sets each one. -/
theorem cookies_valid (keyId : KeyId) (digest : Digest) (g : Grant) (signature : ByteArray)
    {path : String} (hpath : path.toList.all Http.cookieOctet = true) :
    ∀ c ∈ cookies (fields keyId digest g signature) path, c.valid = true := by
  intro c hc
  simp only [cookies, List.mem_map] at hc
  obtain ⟨kv, hkv, rfl⟩ := hc
  obtain ⟨hname, hvalue⟩ := fields_safe keyId digest g signature kv hkv
  simp only [Http.Cookie.valid, hname, hpath, Bool.true_and, Bool.and_true]
  exact List.all_eq_true.mpr fun c hc => cookieOctet_of_urlSafe (List.all_eq_true.mp hvalue c hc)

end Aws.CloudFront
