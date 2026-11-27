/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.Sse
public import Lanes.Web.Http.WireSound
public import Lanes.Web.Http.ReadRequestSound

/-!
The client's reader of Server-Sent Events (`Sse.parse`) reads back what the server writes: the
events of a stream, in order, each once, whatever comments to keep it open are between them
(`Sse.parse_written`), for events that are `valid`; and an event made from a system's answer is
valid (`Sse.Event.ofResponse_valid`).
-/

@[expose] public section

namespace Lanes.Http.Sse

/-! Lines -/

theorem splitLf_cons {c : Char} (hc : c ≠ '\n') (rest line : List Char) :
    splitLf (c :: rest) line = splitLf rest (c :: line) := by
  simp [splitLf]

theorem splitLf_line : ∀ {l : List Char}, '\n' ∉ l → ∀ (acc rest : List Char),
    splitLf (l ++ '\n' :: rest) acc = (acc.reverse ++ l) :: splitLf rest []
  | [], _, acc, rest => by simp [splitLf]
  | c :: l, h, acc, rest => by
    have hc : c ≠ '\n' := fun e => h (e ▸ List.mem_cons_self)
    have hl : '\n' ∉ l := fun m => h (List.mem_cons_of_mem _ m)
    rw [List.cons_append, splitLf_cons hc, splitLf_line hl (c :: acc) rest]
    simp

theorem splitLf_lines : ∀ {ls : List (List Char)}, (∀ l ∈ ls, '\n' ∉ l) → ∀ rest,
    splitLf (ls.flatMap (· ++ ['\n']) ++ rest) [] = ls ++ splitLf rest []
  | [], _, rest => by simp
  | l :: ls, h, rest => by
    have := splitLf_line (h l List.mem_cons_self) [] (ls.flatMap (· ++ ['\n']) ++ rest)
    simp only [List.flatMap_cons, List.append_assoc, List.cons_append, List.nil_append] at this ⊢
    rw [this, splitLf_lines (fun l' m => h l' (List.mem_cons_of_mem _ m)) rest]
    simp

/-! A reader folds the lines of a block, and dispatches at its blank line -/

theorem lines_append : ∀ (ls : List (List Char)) (r : Reader) (rest : List (List Char)),
    (∀ l ∈ ls, l ≠ []) → Reader.lines r (ls ++ rest) = Reader.lines (ls.foldl Reader.field r) rest
  | [], r, rest, _ => rfl
  | l :: ls, r, rest, h => by
    have hl : l ≠ [] := h l List.mem_cons_self
    rw [List.cons_append, List.foldl_cons, ← lines_append ls (r.field l) rest
      (fun l' m => h l' (List.mem_cons_of_mem _ m))]
    cases l with
    | nil => exact absurd rfl hl
    | cons c l => rfl

theorem field_data (r : Reader) (v : List Char) :
    r.field ("data: ".toList ++ v)
      = { r with data := if r.hasData then r.data ++ '\n' :: v else v, hasData := true } := by
  simp [Reader.field]

theorem field_event (r : Reader) (v : List Char) :
    r.field ("event: ".toList ++ v) = { r with event := some (String.ofList v) } := by
  simp [Reader.field]

theorem field_id (r : Reader) (v : List Char) (h : '\x00' ∉ v) :
    r.field ("id: ".toList ++ v) = { r with id := some (String.ofList v) } := by
  simp [Reader.field, h]

theorem field_retry (r : Reader) (n : Nat) (h : n < 10 ^ 18) :
    r.field ("retry: ".toList ++ (toString n).toList) = { r with retry := some n } := by
  have e : decimal? n.repr = some n := decimal?_toString h
  simp [Reader.field, ← Nat.toString_eq_ofList_toDigits, e]

/-! What the server writes of an event is read back as the event -/

theorem pieces_ne_nil (sep : Char) : ∀ l : List Char, pieces sep l ≠ []
  | [] => by simp [pieces]
  | c :: rest => by
    unfold pieces
    split <;> simp

theorem pieces_cons (sep : Char) (c : Char) (rest : List Char) :
    ∃ p ps, pieces sep rest = p :: ps ∧ pieces sep (c :: rest)
      = if c = sep then [] :: p :: ps else (c :: p) :: ps := by
  cases h : pieces sep rest with
  | nil => exact absurd h (pieces_ne_nil sep rest)
  | cons p ps => exact ⟨p, ps, rfl, by simp [pieces, h]⟩

theorem intercalate_cons_head (sep c : Char) (p : List Char) (ps : List (List Char)) :
    [sep].intercalate ((c :: p) :: ps) = c :: [sep].intercalate (p :: ps) := by
  cases ps <;> simp [List.intercalate_cons_cons]

theorem intercalate_pieces (sep : Char) : ∀ l : List Char, [sep].intercalate (pieces sep l) = l
  | [] => rfl
  | c :: rest => by
    have ih := intercalate_pieces sep rest
    obtain ⟨p, ps, hp, hc⟩ := pieces_cons sep c rest
    rw [hp] at ih
    rw [hc]
    split
    · rename_i e
      rw [List.intercalate_cons_cons, ih, e]
      simp
    · rw [intercalate_cons_head, ih]

theorem mem_pieces (sep : Char) : ∀ {l p : List Char}, p ∈ pieces sep l → sep ∉ p
  | [], p, h => by simp [pieces] at h; subst h; simp
  | c :: rest, p, h => by
    obtain ⟨q, qs, hq, hc⟩ := pieces_cons sep c rest
    rw [hc] at h
    split at h
    · simp only [List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · exact mem_pieces sep (by rw [hq]; exact List.mem_cons.mpr h)
    · rename_i hne
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · simp only [List.mem_cons, not_or]
        exact ⟨fun e => hne e.symm, mem_pieces sep (by rw [hq]; exact List.mem_cons_self)⟩
      · exact mem_pieces sep (by rw [hq]; exact List.mem_cons_of_mem _ h)

theorem fold_more : ∀ (qs : List (List Char)) (r : Reader), r.hasData = true →
    (qs.map ("data: ".toList ++ ·)).foldl Reader.field r
      = { r with data := r.data ++ qs.flatMap ('\n' :: ·) }
  | [], r, _ => by simp
  | q :: qs, r, hr => by
    simp only [List.map_cons, List.foldl_cons, field_data, hr, ite_true]
    rw [fold_more qs _ rfl]
    simp [List.append_assoc]

theorem intercalate_flatMap (p : List Char) : ∀ qs : List (List Char),
    ['\n'].intercalate (p :: qs) = p ++ qs.flatMap ('\n' :: ·)
  | [] => by simp
  | q :: qs => by
    rw [List.intercalate_cons_cons, intercalate_flatMap q qs]
    simp

/-- Folding the data lines of an event into a reader that has no data yet gives the data. -/
theorem fold_data (p : List Char) (qs : List (List Char)) (r : Reader) (hr : r.hasData = false) :
    ((p :: qs).map ("data: ".toList ++ ·)).foldl Reader.field r
      = { r with data := ['\n'].intercalate (p :: qs), hasData := true } := by
  simp only [List.map_cons, List.foldl_cons, field_data, hr, Bool.false_eq_true, ite_false]
  rw [fold_more qs _ rfl, intercalate_flatMap]

theorem valid_iff {e : Event} : e.valid = true ↔
    (∀ n, e.event = some n → '\n' ∉ n.toList ∧ '\r' ∉ n.toList)
      ∧ (∀ i, e.id = some i → '\n' ∉ i.toList ∧ '\r' ∉ i.toList ∧ '\x00' ∉ i.toList)
      ∧ '\r' ∉ e.data.toList ∧ (∀ n, e.retry = some n → n < 10 ^ 18) := by
  cases hE : e.event <;> cases hI : e.id <;> cases hR : e.retry <;>
    simp [Event.valid, hE, hI, hR, and_assoc]

/-- A reader that has read the lines of a valid event holds the event. -/
theorem fold_lines (e : Event) (h : e.valid = true) :
    e.lines.foldl Reader.field {}
      = { data := e.data.toList, hasData := true, event := e.event, id := e.id, retry := e.retry } := by
  obtain ⟨hev, hid, -, hretry⟩ := valid_iff.mp h
  obtain ⟨p, qs, hp⟩ : ∃ p qs, pieces '\n' e.data.toList = p :: qs := by
    cases hq : pieces '\n' e.data.toList with
    | nil => exact absurd hq (pieces_ne_nil _ _)
    | cons p qs => exact ⟨p, qs, rfl⟩
  have hdata : ['\n'].intercalate (p :: qs) = e.data.toList := by
    rw [← hp, intercalate_pieces]
  unfold Event.lines
  rw [List.foldl_append, List.foldl_append, List.foldl_append, hp]
  cases hE : e.event <;> cases hI : e.id <;> cases hR : e.retry
  all_goals simp only [Option.map_none, Option.map_some, Option.toList_none, Option.toList_some,
    List.foldl_nil, List.foldl_cons, field_event]
  all_goals (try rw [field_id _ _ (hid _ hI).2.2])
  all_goals (try rw [field_retry _ _ (hretry _ hR)])
  all_goals rw [fold_data _ _ _ rfl, hdata]
  all_goals simp [String.ofList_toList]

theorem lines_ok (e : Event) (h : e.valid = true) : ∀ l ∈ e.lines, '\n' ∉ l ∧ l ≠ [] := by
  obtain ⟨hev, hid, -, -⟩ := valid_iff.mp h
  intro l hl
  unfold Event.lines at hl
  simp only [List.mem_append, List.mem_map, Option.mem_toList,
    Option.map_eq_some_iff] at hl
  rcases hl with ((⟨n, hn, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨n, -, rfl⟩) | ⟨p, hp, rfl⟩
  · exact ⟨by simpa using (hev n hn).1, by simp⟩
  · exact ⟨by simpa using (hid i hi).1, by simp⟩
  · refine ⟨?_, by simp⟩
    simp only [List.mem_append, not_or]
    refine ⟨by decide, fun m => ?_⟩
    rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at m
    have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) m
    revert this
    decide
  · exact ⟨by simpa using mem_pieces '\n' hp, by simp⟩

/-- A reader at the start of a block reads a valid event's lines and its blank line as the
event. -/
theorem lines_event (e : Event) (h : e.valid = true) (rest : List (List Char)) :
    Reader.lines {} (e.lines ++ [] :: rest) = e :: Reader.lines {} rest := by
  rw [lines_append _ _ _ fun l hl => (lines_ok e h l hl).2, fold_lines e h]
  simp [Reader.lines, String.ofList_toList]

/-- What a stream writes: events, and comments (`none`) between them that keep it open. -/
def written : List (Option Event) → List Char
  | [] => []
  | some e :: rest => e.chars ++ written rest
  | none :: rest => ":\n\n".toList ++ written rest

/-- The client's reader reads the events of a stream back as they were written, in order, each
once, whatever comments are between them. -/
theorem parse_written : ∀ (xs : List (Option Event)), (∀ e ∈ xs.filterMap id, e.valid = true) →
    parse (written xs) = xs.filterMap id
  | [], _ => by simp [parse, written, splitLf, Reader.lines]
  | some e :: rest, h => by
    have he : e.valid = true := h e (by simp)
    have ih := parse_written rest fun e' m => h e' (by simp [m])
    unfold parse at ih ⊢
    have hchars : e.chars ++ written rest
        = (e.lines ++ [[]]).flatMap (· ++ ['\n']) ++ written rest := by
      simp [Event.chars]
    rw [written, hchars, splitLf_lines (fun l hl => ?_)]
    · rw [List.append_assoc, List.singleton_append, lines_event e he, ih]
      simp
    · simp only [List.mem_append, List.mem_singleton] at hl
      rcases hl with hl | rfl
      · exact (lines_ok e he l hl).1
      · simp
  | none :: rest, h => by
    have ih := parse_written rest fun e' m => h e' (by simp [m])
    unfold parse at ih ⊢
    have hchars : ":\n\n".toList ++ written rest
        = [[':'], []].flatMap (· ++ ['\n']) ++ written rest := rfl
    rw [written, hchars, splitLf_lines (by decide)]
    simp [Reader.lines, Reader.field, ih]


theorem lf_noCR (l : List Char) : '\r' ∉ Event.lf l := by
  fun_induction Event.lf l <;> simp_all [eq_comm]

theorem oneLine_ok (s : String) :
    '\n' ∉ (Event.oneLine s).toList ∧ '\r' ∉ (Event.oneLine s).toList
      ∧ '\x00' ∉ (Event.oneLine s).toList := by
  simp [Event.oneLine, String.toList_ofList]

/-- An event a system gives as its answer to a pull is one the client reads back as it is. -/
theorem Event.ofResponse_valid (r : Response) : (Event.ofResponse r).valid = true := by
  refine valid_iff.mpr ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    simp only [Event.ofResponse, Option.map_eq_some_iff] at hn
    obtain ⟨v, -, rfl⟩ := hn
    exact ⟨(oneLine_ok v).1, (oneLine_ok v).2.1⟩
  · intro i hi
    simp only [Event.ofResponse, Option.map_eq_some_iff] at hi
    obtain ⟨v, -, rfl⟩ := hi
    exact oneLine_ok v
  · simp only [Event.ofResponse, String.toList_ofList]
    exact lf_noCR _
  · intro n hn
    simp only [Event.ofResponse, Option.bind_eq_some_iff, Option.filter_eq_some_iff] at hn
    obtain ⟨v, -, -, h⟩ := hn
    simpa using h

end Lanes.Http.Sse
