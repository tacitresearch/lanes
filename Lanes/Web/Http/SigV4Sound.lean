/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.SigV4

/-!
What the canonical request of Signature Version 4 is, proved of `Lanes.SigV4` for every input.

An escape is letters, digits, `-._~` and `%XX` in capitals only (`SigV4.encode_chunks`), and
unescaping gives back what was escaped, a path of segments, slashes and all
(`SigV4.decodePath_canonicalPath`). The canonical query holds the parameters given, sorted by
escaped name and then value (`SigV4.sortQuery_perm`, `SigV4.sortQuery_sorted`). The signed
headers are in lowercase, strictly in order, so each once, and are the names of the canonical
headers, one for each name given (`SigV4.canonicalHeaders_sorted`, `canonicalHeaders_lower`,
`mem_canonicalHeaders`). And the target the client writes for a signed request is the
canonical path and query that were signed (`SigV4.target_sign`).
-/

@[expose] public section

namespace Lanes.SigV4

open Http

/-! ## Escapes -/

def upperHex (c : Char) : Bool := ('0' ≤ c && c ≤ '9') || ('A' ≤ c && c ≤ 'F')

def unreservedChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z')
    || c == '-' || c == '.' || c == '_' || c == '~'

/-- One unreserved character, or `%` and two hex digits in capitals. -/
def chunk : List Char → Bool
  | [c] => unreservedChar c
  | ['%', a, b] => upperHex a && upperHex b
  | _ => false

private theorem chunk_byte : ∀ b : UInt8, chunk (percentEncodeByte b) = true := by
  decide

/-- An escape is unreserved characters and `%XX` in capitals, and nothing else. -/
theorem encode_chunks (s : String) :
    ∃ chunks : List (List Char), (encode s).toList = chunks.flatten ∧ ∀ c ∈ chunks, chunk c := by
  refine ⟨s.toUTF8.data.toList.map percentEncodeByte, ?_, ?_⟩
  · simp [encode, percentEncode, List.flatMap]
  · intro c mem
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp mem
    exact chunk_byte b

private theorem slash_not_mem_encode (s : String) : '/' ∉ (encode s).toList := by
  have : ∀ b : UInt8, '/' ∉ percentEncodeByte b := by decide
  simp only [encode, percentEncode, String.toList_ofList, List.mem_flatMap, not_exists, not_and]
  exact fun b _ => this b

/-- The path a canonical path escapes, without its first slash. -/
def decodePath (canonical : String) : Option String :=
  match canonical.toList with
  | '/' :: rest =>
    ((rest.splitOn '/').mapM fun segment => percentDecode (String.ofList segment)).map
      ("/".intercalate ·)
  | _ => none

private theorem mapM_decode (segs : List String) :
    (segs.map fun s => (encode s).toList).mapM (fun segment => percentDecode (String.ofList segment))
      = some segs := by
  induction segs with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.map_cons, List.mapM_cons, String.ofList_toList, encode,
      percentDecode_percentEncode]
    simp only [encode] at ih
    simp [ih]

/-- An object key escaped segment by segment, slashes kept, reads back as itself. -/
theorem decodePath_canonicalPath (path : String) :
    decodePath (canonicalPath (segments path)) = some path := by
  have hne : segments path ≠ [] := by simp [segments, List.splitOn_ne_nil]
  have hsplit : (['/'].intercalate ((segments path).map fun s => (encode s).toList)).splitOn '/'
      = (segments path).map fun s => (encode s).toList := by
    apply List.splitOn_intercalate
    · intro l hl
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp hl
      exact slash_not_mem_encode s
    · simpa using hne
  have hjoin : "/".intercalate (segments path) = path := by
    rw [← String.toList_inj, String.toList_intercalate]
    simp [segments, List.map_map, Function.comp_def, List.intercalate_splitOn]
  simp only [decodePath, canonicalPath, String.toList_append, String.toList_intercalate]
  simp only [show "/".toList = ['/'] from rfl, List.cons_append, List.nil_append, hsplit,
    List.map_map, Function.comp_def]
  rw [mapM_decode]
  simp [hjoin]

/-! ## The canonical query -/

private theorem pairLe_trans (a b c : String × String) :
    pairLe a b = true → pairLe b c = true → pairLe a c = true := by
  simp only [pairLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
  rintro (h1 | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩)
  · exact .inl (Std.lt_trans h1 h2)
  · exact .inl (h2 ▸ h1)
  · exact .inl (h1 ▸ h2)
  · exact .inr ⟨h1.trans h2, Std.le_trans h1' h2'⟩

private theorem pairLe_total (a b : String × String) : (pairLe a b || pairLe b a) = true := by
  simp only [pairLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
  by_cases h : a.1 < b.1
  · exact .inl (.inl h)
  · by_cases h' : b.1 < a.1
    · exact .inr (.inl h')
    · have heq : a.1 = b.1 := Std.le_antisymm (Std.not_lt.mp h') (Std.not_lt.mp h)
      rcases (Std.le_total : a.2 ≤ b.2 ∨ b.2 ≤ a.2) with h2 | h2
      · exact .inl (.inr ⟨heq, h2⟩)
      · exact .inr (.inr ⟨heq.symm, h2⟩)

/-- The canonical query has exactly the parameters given. -/
theorem sortQuery_perm (query : List (String × String)) : (sortQuery query).Perm query :=
  List.mergeSort_perm _ _

/-- Sorted by escaped name, then by escaped value. -/
theorem sortQuery_sorted (query : List (String × String)) :
    ((sortQuery query).map encodePair).Pairwise fun a b => pairLe a b = true := by
  rw [List.pairwise_map]
  exact List.pairwise_mergeSort (fun a b c => pairLe_trans (encodePair a) (encodePair b) (encodePair c))
    (fun a b => pairLe_total (encodePair a) (encodePair b)) _

theorem sortQuery_sortQuery (query : List (String × String)) :
    sortQuery (sortQuery query) = sortQuery query := by
  apply List.mergeSort_of_pairwise
  have := sortQuery_sorted query
  rwa [List.pairwise_map] at this

theorem canonicalQuery_sortQuery (query : List (String × String)) :
    canonicalQuery (sortQuery query) = canonicalQuery query := by
  simp only [canonicalQuery, sortQuery_sortQuery]

/-! ## The signed headers -/

private theorem lt_of_not_lt_ne {a b : String} (h : ¬ a < b) (hne : a ≠ b) : b < a := by
  rcases (Std.le_total : a ≤ b ∨ b ≤ a) with h' | h'
  · exact absurd (Std.le_antisymm h' (Std.not_lt.mp h)) hne
  · exact Std.lt_of_le_of_ne h' (Ne.symm hne)

private theorem mem_insertHeader {l : List (String × String)} {h : String × String} {x : String}
    (hx : x ∈ (insertHeader l h).map (·.1)) : x ∈ l.map (·.1) ∨ x = h.1 := by
  induction l with
  | nil => simp_all [insertHeader]
  | cons p rest ih =>
    obtain ⟨n, v⟩ := p
    obtain ⟨m, w⟩ := h
    simp only [insertHeader] at hx
    split at hx
    · simp at hx
      rcases hx with rfl | rfl | hx
      · exact .inr rfl
      · simp
      · simp [hx]
    · split at hx
      · simp at hx
        rcases hx with rfl | hx
        · simp
        · simp [hx]
      · simp only [List.map_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp
        · rcases ih hx with h | h
          · simp [h]
          · exact .inr h

private theorem insertHeader_mem {l : List (String × String)} {h : String × String} {x : String}
    (hx : x ∈ l.map (·.1) ∨ x = h.1) : x ∈ (insertHeader l h).map (·.1) := by
  induction l with
  | nil => simp_all [insertHeader]
  | cons p rest ih =>
    obtain ⟨n, v⟩ := p
    obtain ⟨m, w⟩ := h
    simp only [insertHeader]
    split
    · simp only [List.map_cons, List.mem_cons] at hx ⊢
      rcases hx with (h | h) | h <;> simp [h]
    · split
      · next heq =>
        simp only [List.map_cons, List.mem_cons] at hx ⊢
        rcases hx with (h | h) | h
        · exact .inl h
        · exact .inr h
        · exact .inl (h.trans heq)
      · simp only [List.map_cons, List.mem_cons] at hx ⊢
        rcases hx with (h | h) | h
        · exact .inl h
        · exact .inr (ih (.inl h))
        · exact .inr (ih (.inr h))

private theorem insertHeader_sorted {l : List (String × String)} (h : String × String)
    (hl : (l.map (·.1)).Pairwise (· < ·)) : ((insertHeader l h).map (·.1)).Pairwise (· < ·) := by
  induction l with
  | nil => simp [insertHeader]
  | cons p rest ih =>
    obtain ⟨n, v⟩ := p
    obtain ⟨m, w⟩ := h
    simp only [List.map_cons, List.pairwise_cons] at hl
    simp only [insertHeader]
    split
    · next hlt =>
      simp only [List.map_cons, List.pairwise_cons, List.mem_cons]
      refine ⟨?_, hl.1, hl.2⟩
      rintro x (rfl | hx)
      · exact hlt
      · exact Std.lt_trans hlt (hl.1 x hx)
    · split
      · simpa using hl
      · next hnlt hne =>
        simp only [List.map_cons, List.pairwise_cons]
        refine ⟨?_, ih hl.2⟩
        intro x hx
        rcases mem_insertHeader hx with hx | rfl
        · exact hl.1 x hx
        · exact lt_of_not_lt_ne hnlt hne

private theorem foldl_insert_sorted (headers acc : List (String × String))
    (hacc : (acc.map (·.1)).Pairwise (· < ·)) :
    ((headers.foldl (fun acc (n, v) => insertHeader acc (n.toLower, trimValue v)) acc).map
      (·.1)).Pairwise (· < ·) := by
  induction headers generalizing acc with
  | nil => exact hacc
  | cons h rest ih => exact ih _ (insertHeader_sorted _ hacc)

/-- The signed headers are strictly in order: sorted, and each name once. -/
theorem canonicalHeaders_sorted (headers : List (String × String)) :
    ((canonicalHeaders headers).map (·.1)).Pairwise (· < ·) :=
  foldl_insert_sorted headers [] (by simp)

private theorem mem_foldl_insert (headers acc : List (String × String)) (x : String) :
    x ∈ (headers.foldl (fun acc (n, v) => insertHeader acc (n.toLower, trimValue v)) acc).map
      (·.1) ↔ x ∈ acc.map (·.1) ∨ ∃ h ∈ headers, h.1.toLower = x := by
  induction headers generalizing acc with
  | nil => simp
  | cons h rest ih =>
    simp only [List.foldl_cons, ih, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (hx | hx)
      · rcases mem_insertHeader hx with hx | hx
        · exact .inl hx
        · exact .inr (.inl hx.symm)
      · exact .inr (.inr hx)
    · rintro (hx | hx | hx)
      · exact .inl (insertHeader_mem (.inl hx))
      · exact .inl (insertHeader_mem (.inr hx.symm))
      · exact .inr hx

/-- A name is signed exactly when a header of that name, in lowercase, is given. -/
theorem mem_canonicalHeaders (headers : List (String × String)) (x : String) :
    x ∈ (canonicalHeaders headers).map (·.1) ↔ ∃ h ∈ headers, h.1.toLower = x := by
  simp [canonicalHeaders, mem_foldl_insert]

private theorem isUpper_toLower (c : Char) : c.toLower.isUpper = false := by
  unfold Char.toLower
  split
  · next h =>
    simp only [Char.isUpper, decide_eq_false_iff_not]
    have h' : c.val ≥ 65 ∧ c.val ≤ 90 := h
    show ¬(c.val + (97 - 65) ≥ 65 ∧ c.val + (97 - 65) ≤ 90)
    rintro ⟨h1, h2⟩
    obtain ⟨h3, h4⟩ := h'
    simp only [ge_iff_le, UInt32.le_iff_toNat_le, UInt32.toNat_add] at h1 h2 h3 h4
    have : (97 - 65 : UInt32).toNat = 32 := rfl
    have hc := c.val.toNat_lt
    have h65 : (65 : UInt32).toNat = 65 := rfl
    have h90 : (90 : UInt32).toNat = 90 := rfl
    simp only [this, h65, h90] at h1 h2 h3 h4
    omega
  · next h =>
    simp only [Char.isUpper, decide_eq_false_iff_not]
    exact h

/-- No signed header has a capital letter. -/
theorem canonicalHeaders_lower (headers : List (String × String)) :
    ∀ x ∈ (canonicalHeaders headers).map (·.1), ∀ c ∈ x.toList, c.isUpper = false := by
  intro x hx c hc
  obtain ⟨h, -, rfl⟩ := (mem_canonicalHeaders headers x).mp hx
  simp only [String.toLower, String.toList_map, List.mem_map] at hc
  obtain ⟨d, -, rfl⟩ := hc
  exact isUpper_toLower d

/-! ## What is signed is what is sent -/

private theorem sortQuery_eq_nil {query : List (String × String)} :
    sortQuery query = [] ↔ query = [] := by
  constructor
  · intro h
    have := (sortQuery_perm query).length_eq
    simp only [h, List.length_nil] at this
    exact List.length_eq_zero_iff.mp this.symm
  · rintro rfl
    simp [sortQuery]

/-- The target the client writes for a signed request is the canonical path and query. -/
theorem target_sign (creds : Credentials) (t : Civil.DateTime) (scope : Scope)
    (host verb payloadHash : String) (r : Request) :
    (sign creds t scope host verb payloadHash r).target
      = canonicalPath r.path ++ (if r.query = [] then "" else "?" ++ canonicalQuery r.query) := by
  simp only [sign, Request.target, canonicalPath, canonicalQuery, encode, encodePair,
    String.append_assoc]
  congr 2
  by_cases h : r.query = []
  · simp [h, sortQuery]
  · have : sortQuery r.query ≠ [] := fun h' => h (sortQuery_eq_nil.mp h')
    simp [h, this]

end Lanes.SigV4
