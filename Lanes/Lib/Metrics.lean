/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Metrics

Counters, gauges and histograms as values, and the text a Prometheus server scrapes: the text
exposition format, version 0.0.4. Nothing here is shared or mutable. An adapter keeps the values
where it likes and renders them when it is asked.

A value is a natural number written with `Family.scale` decimal places, so a latency kept in
microseconds is written in seconds with no floating point. A histogram keeps, for each bound, how
many observations were at or below it, which is what the format writes. So its buckets count
exactly the observations at or below their bounds (`Histogram.observeAll_eq`), they never go
down (`Histogram.buckets_pairwise`), and the last, `+Inf`, is its count
(`Histogram.buckets_getLast`). Label values and help text are escaped as the format says, and a
reader of the format reads them back as written (`readLabelValue_escapeLabel`,
`readHelp_escapeHelp`), so neither can end its quotes or its line early. Names are made valid
(`valid_sanitize`), and a valid one is left as it is (`sanitize_of_valid`).
-/

@[expose] public section

namespace Lanes.Metrics

/-! ## Histograms -/

/-- For each bound in `bounds`, how many observations were at or below it; how many there were;
and their sum. -/
structure Histogram (bounds : List Nat) where
  below : List Nat := bounds.map fun _ => 0
  count : Nat := 0
  sum : Nat := 0
  deriving DecidableEq, Repr

namespace Histogram

variable {bounds : List Nat}

/-- Add one to each count whose bound is at least `v`. -/
def bump (v : Nat) : List Nat → List Nat → List Nat
  | b :: bs, c :: cs => (if v ≤ b then c + 1 else c) :: bump v bs cs
  | _, _ => []

def observe (v : Nat) (h : Histogram bounds) : Histogram bounds :=
  { below := bump v bounds h.below, count := h.count + 1, sum := h.sum + v }

def observeAll (bounds : List Nat) (vs : List Nat) : Histogram bounds :=
  vs.foldl (fun h v => h.observe v) {}

/-- The cumulative counts the format writes, one per bound and then `+Inf`. -/
def buckets (h : Histogram bounds) : List Nat :=
  h.below ++ [h.count]

theorem bump_map (v : Nat) (f : Nat → Nat) : ∀ bs : List Nat,
    bump v bs (bs.map f) = bs.map fun b => f b + if v ≤ b then 1 else 0
  | [] => rfl
  | b :: bs => by
    simp only [List.map_cons, bump, bump_map v f bs, List.cons.injEq, and_true]
    split <;> omega

theorem observe_observeAll (bounds vs : List Nat) (v : Nat) :
    (observeAll bounds vs).observe v = observeAll bounds (vs ++ [v]) := by
  simp [observeAll, List.foldl_append]

theorem foldl_observe (bounds : List Nat) : ∀ (vs : List Nat) (f : Nat → Nat) (count sum : Nat),
    vs.foldl (fun h v => h.observe v) ({ below := bounds.map f, count, sum } : Histogram bounds) =
      { below := bounds.map (fun b => f b + vs.countP (· ≤ b)), count := count + vs.length
        sum := sum + vs.sum }
  | [], f, count, sum => by simp
  | v :: vs, f, count, sum => by
    rw [List.foldl_cons, observe, bump_map, foldl_observe bounds vs]
    simp only [List.countP_cons, List.length_cons, List.sum_cons, Histogram.mk.injEq]
    refine ⟨List.map_congr_left fun b _ => ?_, by omega, by omega⟩
    simp only [decide_eq_true_eq]
    split <;> omega

/-- A histogram is its observations: each bound's count is the observations at or below it. -/
theorem observeAll_eq (bounds vs : List Nat) :
    observeAll bounds vs =
      { below := bounds.map (fun b => vs.countP (· ≤ b)), count := vs.length, sum := vs.sum } := by
  simpa [observeAll] using foldl_observe bounds vs (fun _ => 0) 0 0

/-- With ascending bounds, the buckets never go down: each counts what the one before counts. -/
theorem buckets_pairwise {bounds : List Nat} (vs : List Nat) (sorted : bounds.Pairwise (· ≤ ·)) :
    (observeAll bounds vs).buckets.Pairwise (· ≤ ·) := by
  rw [observeAll_eq, buckets, List.pairwise_append, List.pairwise_map]
  refine ⟨sorted.imp fun h => List.countP_mono_left fun x _ hx => ?_, by simp, ?_⟩
  · simp only [decide_eq_true_eq] at hx ⊢; omega
  · simp only [List.mem_map, List.mem_singleton]
    rintro _ ⟨b, _, rfl⟩ _ rfl
    exact List.countP_le_length

/-- The last bucket, `+Inf`, is the count. -/
theorem buckets_getLast (h : Histogram bounds) : h.buckets.getLast? = some h.count := by
  simp [buckets]

end Histogram

/-! ## Escaping -/

def escapeLabelChar (c : Char) : List Char :=
  if c = '\\' then ['\\', '\\'] else if c = '"' then ['\\', '"']
  else if c = '\n' then ['\\', 'n'] else [c]

/-- A label value as the format writes it between quotes. -/
def escapeLabel (s : String) : String :=
  String.ofList (s.toList.flatMap escapeLabelChar)

def escapeHelpChar (c : Char) : List Char :=
  if c = '\\' then ['\\', '\\'] else if c = '\n' then ['\\', 'n'] else [c]

/-- Help text as the format writes it, to the end of its line. -/
def escapeHelp (s : String) : String :=
  String.ofList (s.toList.flatMap escapeHelpChar)

/-- How a reader of the format takes a label value after its opening quote: the value, and what
follows its closing quote. A raw line feed, or a backslash before anything but a backslash, a
quote or `n`, is not a label value. -/
def readLabelValue : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
    if c = '"' then some ([], rest)
    else if c = '\n' then none
    else if c = '\\' then
      match rest with
      | d :: rest =>
        if d = '\\' ∨ d = '"' then (readLabelValue rest).map fun (v, r) => (d :: v, r)
        else if d = 'n' then (readLabelValue rest).map fun (v, r) => ('\n' :: v, r)
        else none
      | [] => none
    else (readLabelValue rest).map fun (v, r) => (c :: v, r)

/-- How a reader of the format takes help text, which runs to the end of its line. -/
def readHelp : List Char → Option (List Char)
  | [] => some []
  | c :: rest =>
    if c = '\n' then none
    else if c = '\\' then
      match rest with
      | d :: rest =>
        if d = '\\' then (readHelp rest).map ('\\' :: ·)
        else if d = 'n' then (readHelp rest).map ('\n' :: ·)
        else none
      | [] => none
    else (readHelp rest).map (c :: ·)

theorem readLabelValue_escape (rest : List Char) : ∀ cs : List Char,
    readLabelValue (cs.flatMap escapeLabelChar ++ '"' :: rest) = some (cs, rest)
  | [] => by rw [readLabelValue.eq_def]; simp
  | c :: cs => by
    have ih := readLabelValue_escape rest cs
    simp only [List.flatMap_cons, escapeLabelChar]
    by_cases h1 : c = '\\'
    · subst h1; simp [readLabelValue, ih]
    by_cases h2 : c = '"'
    · subst h2; simp [readLabelValue, ih]
    by_cases h3 : c = '\n'
    · subst h3; simp [readLabelValue, ih]
    rw [readLabelValue.eq_def]
    simp [h1, h2, h3, ih]

/-- A reader reads an escaped label value back as it was, and its closing quote where it was
written: what follows is untouched. -/
theorem readLabelValue_escapeLabel (s : String) (rest : List Char) :
    readLabelValue ((escapeLabel s).toList ++ '"' :: rest) = some (s.toList, rest) := by
  simpa [escapeLabel] using readLabelValue_escape rest s.toList

theorem readHelp_escape : ∀ cs : List Char, readHelp (cs.flatMap escapeHelpChar) = some cs
  | [] => rfl
  | c :: cs => by
    have ih := readHelp_escape cs
    simp only [List.flatMap_cons, escapeHelpChar]
    by_cases h1 : c = '\\'
    · subst h1; simp [readHelp, ih]
    by_cases h3 : c = '\n'
    · subst h3; simp [readHelp, ih]
    rw [readHelp.eq_def]
    simp [h1, h3, ih]

/-- A reader reads escaped help text back as it was. -/
theorem readHelp_escapeHelp (s : String) : readHelp (escapeHelp s).toList = some s.toList := by
  simpa [escapeHelp] using readHelp_escape s.toList

theorem not_mem_escapeLabelChar (c : Char) : '\n' ∉ escapeLabelChar c := by
  unfold escapeLabelChar
  repeat' split
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals first | decide | exact fun e => ‹¬c = '\n'› e.symm

theorem not_mem_escapeHelpChar (c : Char) : '\n' ∉ escapeHelpChar c := by
  unfold escapeHelpChar
  repeat' split
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals first | decide | exact fun e => ‹¬c = '\n'› e.symm

/-- An escaped label value has no line feed, so it cannot end its line. -/
theorem newline_not_mem_escapeLabel (s : String) : '\n' ∉ (escapeLabel s).toList := by
  simpa [escapeLabel] using fun c _ => not_mem_escapeLabelChar c

/-- Nor has escaped help text. -/
theorem newline_not_mem_escapeHelp (s : String) : '\n' ∉ (escapeHelp s).toList := by
  simpa [escapeHelp] using fun c _ => not_mem_escapeHelpChar c

/-! ## Names -/

/-- A letter, `_`, or, after the first character, a digit: `[a-zA-Z_][a-zA-Z0-9_]*`, which the
format allows for both metric and label names. -/
def nameChar (first : Bool) (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_' || (!first && '0' ≤ c && c ≤ '9')

def validChars : List Char → Bool
  | [] => false
  | c :: cs => nameChar true c && cs.all (nameChar false)

def valid (s : String) : Bool :=
  validChars s.toList

def sanitizeChars (cs : List Char) : List Char :=
  let cs := cs.map fun c => if nameChar false c then c else '_'
  match cs with
  | c :: _ => if nameChar true c then cs else '_' :: cs
  | [] => ['_']

/-- Each character the format does not allow in a name is `_`, and a name that would start with
a digit, or be empty, starts with `_`. -/
def sanitize (s : String) : String :=
  String.ofList (sanitizeChars s.toList)

theorem nameChar_of_first {c : Char} (h : nameChar true c = true) : nameChar false c = true := by
  simp only [nameChar, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with ((h | h) | h) | h
  · exact .inl (.inl (.inl h))
  · exact .inl (.inl (.inr h))
  · exact .inl (.inr h)
  · simp at h

theorem valid_sanitize (s : String) : valid (sanitize s) = true := by
  have all : ∀ c ∈ s.toList.map (fun c => if nameChar false c then c else '_'),
      nameChar false c = true := by
    simp only [List.mem_map]
    rintro _ ⟨c, _, rfl⟩
    split <;> simp_all [nameChar]
  simp only [valid, sanitize, String.toList_ofList, sanitizeChars]
  generalize s.toList.map (fun c => if nameChar false c then c else '_') = ms at all ⊢
  match ms, all with
  | [], _ => simp [validChars, nameChar]
  | c :: cs, all =>
    simp only
    split
    · simp only [validChars, Bool.and_eq_true, List.all_eq_true]
      exact ⟨‹_›, fun x hx => all x (List.mem_cons_of_mem c hx)⟩
    · simp only [validChars, Bool.and_eq_true, List.all_eq_true]
      exact ⟨by decide, all⟩

theorem sanitize_of_valid {s : String} (h : valid s = true) : sanitize s = s := by
  simp only [valid] at h
  simp only [sanitize, sanitizeChars]
  match hs : s.toList, h with
  | c :: cs, h =>
    simp only [validChars, Bool.and_eq_true, List.all_eq_true] at h
    have : (c :: cs).map (fun c => if nameChar false c then c else '_') = c :: cs := by
      conv => rhs; rw [← List.map_id (c :: cs)]
      refine List.map_congr_left fun x hx => ?_
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [nameChar_of_first h.1]
      · simp [h.2 x hx]
    rw [this]
    simp [h.1, ← hs]

/-! ## Rendering -/

abbrev Labels := List (String × String)

def trimZeros (cs : List Char) : List Char :=
  (cs.reverse.dropWhile (· == '0')).reverse

/-- `n` with `scale` decimal places, without trailing zeros: `decimal 3 2500` is `2.5`. -/
def decimal (scale n : Nat) : String :=
  let unit := 10 ^ scale
  let digits := Nat.toDigits 10 (n % unit)
  let frac := trimZeros (List.replicate (scale - digits.length) '0' ++ digits)
  if scale = 0 || frac.isEmpty then toString (n / unit)
  else toString (n / unit) ++ "." ++ String.ofList frac

def decimalInt (scale : Nat) (v : Int) : String :=
  if v < 0 then "-" ++ decimal scale v.natAbs else decimal scale v.toNat

inductive Series where
  | counter (samples : List (Labels × Nat))
  | gauge (samples : List (Labels × Int))
  | histogram (bounds : List Nat) (samples : List (Labels × Histogram bounds))

def Series.kind : Series → String
  | .counter _ => "counter"
  | .gauge _ => "gauge"
  | .histogram _ _ => "histogram"

/-- A metric: its name, its help text and its series, one per set of labels. Values and bounds
are written with `scale` decimal places. -/
structure Family where
  name : String
  help : String
  scale : Nat := 0
  series : Series

def renderLabels (ls : Labels) : String :=
  if ls.isEmpty then ""
  else "{" ++ ",".intercalate (ls.map fun (k, v) => sanitize k ++ "=\"" ++ escapeLabel v ++ "\"")
    ++ "}"

def sample (name : String) (ls : Labels) (value : String) : String :=
  name ++ renderLabels ls ++ " " ++ value ++ "\n"

def renderHistogram (name : String) (scale : Nat) {bounds : List Nat} (ls : Labels)
    (h : Histogram bounds) : String :=
  String.join ((bounds.zip h.below).map fun (b, n) =>
      sample (name ++ "_bucket") (ls ++ [("le", decimal scale b)]) (toString n))
    ++ sample (name ++ "_bucket") (ls ++ [("le", "+Inf")]) (toString h.count)
    ++ sample (name ++ "_sum") ls (decimal scale h.sum)
    ++ sample (name ++ "_count") ls (toString h.count)

def Family.render (f : Family) : String :=
  let name := sanitize f.name
  let body := match f.series with
    | .counter samples =>
      String.join (samples.map fun (ls, n) => sample name ls (decimal f.scale n))
    | .gauge samples =>
      String.join (samples.map fun (ls, v) => sample name ls (decimalInt f.scale v))
    | .histogram _ samples =>
      String.join (samples.map fun (ls, h) => renderHistogram name f.scale ls h)
  "# HELP " ++ name ++ " " ++ escapeHelp f.help ++ "\n# TYPE " ++ name ++ " " ++ f.series.kind
    ++ "\n" ++ body

/-- The text exposition format, version 0.0.4. -/
def render (families : List Family) : String :=
  String.join (families.map Family.render)

/-- The `Content-Type` of `render`'s text. -/
def contentType : String :=
  "text/plain; version=0.0.4; charset=utf-8"

end Lanes.Metrics
