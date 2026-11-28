/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Services.S3.Post
public import Lanes.Lib.Encoding.Json.ParserSound
public import Lanes.Lib.Encoding.Json.BasicSound
public import Lanes.Proof.Utf8

/-!
The policy a form carries says what was asked: its base64 is well formed, it holds JSON within
the reader's limits, and it reads back as exactly the conditions given, in order, and the expiry
given (`Post.form_policy`, `Post.expiration_parse`). What S3 admits under such a policy is a
file whose size is within the range, posted before the expiry (`Post.admitted_bounded`).
-/

@[expose] public section

namespace Lanes.S3.Post

open Http SigV4

theorem field?_dollar (f : String) : field? ("$" ++ f) = some f := by
  simp [field?]

theorem read?_json (c : Condition) : Condition.read? c.json.normalize = some c := by
  cases c with
  | eq field value =>
    simp [Condition.json, Json.normalize, Json.mkObj, Json.sortFields, Json.dedupFields,
      Condition.read?]
  | startsWith field p => simp [Condition.json, Json.normalize, Condition.read?, field?_dollar]
  | length min max => simp [Condition.json, Json.normalize, Condition.read?]

theorem mapM_read? (l : List Condition) :
    l.mapM (Condition.read? ∘ fun c => c.json.normalize) = some l := by
  induction l with
  | nil => rfl
  | cons c rest ih => simp [read?_json, ih]

theorem depth_json (c : Condition) : c.json.depth ≤ 1 := by
  cases c <;> simp [Condition.json, Json.depth]

theorem depth_conditions (l : List Condition) :
    (l.map Condition.json).foldl (fun d (e : Json) => max d e.depth) 0 ≤ 1 := by
  suffices ∀ acc, acc ≤ 1 → (l.map Condition.json).foldl (fun d (e : Json) => max d e.depth) acc ≤ 1
    from this 0 (by omega)
  induction l with
  | nil => simp
  | cons c rest ih =>
    intro acc h
    simp only [List.map_cons, List.foldl_cons]
    exact ih _ (Nat.max_le.mpr ⟨h, depth_json c⟩)

theorem depth_document (d : Document) : d.json.depth ≤ 128 := by
  have := depth_conditions d.conditions
  simp [Document.json, Json.depth]
  omega

/-- What `Json.parse` takes of a condition's numbers. -/
def Condition.Small : Condition → Prop
  | .length min max => min ≤ maxObject_bytes ∧ max ≤ maxObject_bytes
  | _ => True

theorem digits_num (n : Nat) (h : n ≤ maxObject_bytes) : (Json.num n).digits ≤ 1000 := by
  simp only [Json.digits, JsonNumber.digits]
  have := (Nat.length_toDigits_le_iff (b := 10) (n := n) (k := 10) (by decide) (by decide)).mpr
    (Nat.lt_of_le_of_lt h (by decide))
  have : (Nat.toDigits 10 (JsonNumber.fromNat n).mantissa.natAbs).length ≤ 10 := by
    simpa [JsonNumber.fromNat, JsonNumber.fromInt] using this
  simp [JsonNumber.fromNat, JsonNumber.fromInt] at this ⊢
  omega

theorem digits_json (c : Condition) (h : c.Small) : c.json.digits ≤ 1000 := by
  cases c with
  | eq => simp [Condition.json, Json.digits]
  | startsWith => simp [Condition.json, Json.digits]
  | length min max =>
    simp only [Condition.Small] at h
    have h1 := digits_num min h.1
    have h2 := digits_num max h.2
    simp only [Json.digits] at h1 h2
    simp [Condition.json, Json.digits]
    omega

theorem digits_conditions (l : List Condition) (h : ∀ c ∈ l, c.Small) :
    (l.map Condition.json).foldl (fun d (e : Json) => max d e.digits) 0 ≤ 1000 := by
  suffices ∀ acc, acc ≤ 1000 →
      (l.map Condition.json).foldl (fun d (e : Json) => max d e.digits) acc ≤ 1000
    from this 0 (by omega)
  induction l with
  | nil => simp
  | cons c rest ih =>
    intro acc hacc
    simp only [List.map_cons, List.foldl_cons]
    exact ih (fun c hc => h c (by simp [hc])) _
      (Nat.max_le.mpr ⟨hacc, digits_json c (h c (by simp))⟩)

theorem digits_document (d : Document) (h : ∀ c ∈ d.conditions, c.Small) :
    d.json.digits ≤ 1000 := by
  have := digits_conditions d.conditions h
  simp [Document.json, Json.digits]
  omega

theorem read?_normalize (d : Document) : Document.read? d.json.normalize = some d := by
  have hc : d.json.normalize.getObjVal? "conditions" =
      .ok (.arr ((d.conditions.map fun c => c.json.normalize).toArray)) := by
    rw [Document.json, Json.normalize]
    exact Json.getObjVal?_mkObj.mpr (by simp [Json.normalize])
  have he : d.json.normalize.getObjVal? "expiration" = .ok (.str d.expiration) := by
    rw [Document.json, Json.normalize]
    exact Json.getObjVal?_mkObj.mpr (by simp [Json.normalize])
  simp [Document.read?, hc, he, bind, Except.bind, Json.getArr?, Json.getStr?, Except.toOption,
    mapM_read?]

/-- A policy decodes, as S3 decodes it, to the document it was written from: well-formed base64
of JSON within the reader's limits. -/
theorem decode?_encode (d : Document) (h : ∀ c ∈ d.conditions, c.Small) :
    decode? d.encode = some d := by
  have hp : Json.parse (Json.compress d.json) = .ok d.json.normalize :=
    Json.parse_compress _ (depth_document d) (digits_document d h)
  have hu : String.fromUTF8? (Json.compress d.json).toUTF8 = some (Json.compress d.json) :=
    fromUTF8?_toByteArray _
  simp only [decode?, Document.encode, Base64.decode_encode, Option.bind_eq_bind,
    Option.bind_some, hu, hp]
  simp [Except.toOption, read?_normalize]

theorem small_conditions (b : Bucket) (creds : Credentials) (t : Civil.DateTime) (p : Policy) :
    ∀ c ∈ conditions b creds t p, c.Small := by
  have hmax : p.length.max ≤ maxObject_bytes := p.length.bounded
  have hmin : p.length.min ≤ maxObject_bytes := Nat.le_trans p.length.ordered hmax
  intro c hc
  cases c with
  | length a b =>
    cases hk : p.key <;> simp [conditions, eqs, hk, KeyRule.condition] at hc <;>
      (obtain ⟨rfl, rfl⟩ := hc; exact ⟨hmin, hmax⟩)
  | _ => trivial

/-- The policy of a form reads back, as S3 reads it, as exactly the conditions `conditions`
gives, in order, and the expiration `expiration` gives. -/
theorem form_policy (b : Bucket) (creds : Credentials) (t : Civil.DateTime) (p : Policy) :
    decode? (form b creds t p).policy = some (document b creds t p) :=
  decode?_encode _ (small_conditions b creds t p)

/-- The expiry of a policy reads back as `expiry` seconds after its signing, which its type keeps
within seven days. -/
theorem expiration_parse (t : Civil.DateTime) (expiry : Expiry)
    (h : TimeFormat.InRange (Civil.DateTime.ofUnix (t.toUnix + expiry.val)).date) :
    ∃ ts, TimeFormat.parseRfc3339 (expiration t expiry) = some ts ∧
      ts.toUnix = t.toUnix + expiry.val := by
  let ts : TimeFormat.Timestamp := ⟨.ofUnix (t.toUnix + expiry.val), 0, ⟨0, by decide⟩⟩
  refine ⟨ts, TimeFormat.parseRfc3339_print (t := ts) ?_, ?_⟩
  · simp [TimeFormat.printRfc3339?, h, ts, expiration]
  · simp [ts, TimeFormat.Timestamp.toUnix, Civil.toUnix_ofUnix]

/-- What S3 admits meets every condition of the policy. -/
theorem check_holds {d : Document} {bucket : String} {fields : List (String × String)}
    {size : Nat} {now_s : Int} (h : check d bucket fields size now_s = .ok ()) :
    ∀ c ∈ d.conditions, c.holds (("bucket", bucket) :: fields) size = true := by
  intro c hc
  simp only [check] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · next hfind => simpa using List.find?_eq_none.mp hfind c hc
    · cases h

theorem check_expires {d : Document} {bucket : String} {fields : List (String × String)}
    {size : Nat} {now_s : Int} (h : check d bucket fields size now_s = .ok ()) :
    ∃ ts, TimeFormat.parseRfc3339 d.expiration = some ts ∧ now_s < ts.toUnix := by
  simp only [check] at h
  split at h
  · cases h
  · next ts hts =>
    split at h
    · next hnow => exact ⟨ts, hts, hnow⟩
    · cases h

/-- A file S3 admits under the policy of a form has a size within the policy's range and is
posted before the policy expires, at most seven days after it was signed. -/
theorem admitted_bounded (b : Bucket) (creds : Credentials) (t : Civil.DateTime) (p : Policy)
    {d : Document} {fields : List (String × String)} {size : Nat} {now_s : Int}
    (hd : decode? (form b creds t p).policy = some d)
    (hrange : TimeFormat.InRange (Civil.DateTime.ofUnix (t.toUnix + p.expiry.val)).date)
    (h : check d b.name fields size now_s = .ok ()) :
    p.length.min ≤ size ∧ size ≤ p.length.max ∧ now_s < t.toUnix + p.expiry.val := by
  rw [form_policy] at hd
  cases hd
  have hl := check_holds h (.length p.length.min p.length.max) (by simp [document, conditions])
  simp only [Condition.holds, Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨ts, hts, hnow⟩ := check_expires h
  obtain ⟨ts', hts', hu⟩ := expiration_parse t p.expiry hrange
  simp only [document] at hts
  rw [hts'] at hts
  cases hts
  exact ⟨hl.1, hl.2, hu ▸ hnow⟩

end Lanes.S3.Post
