/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Http.Url

/-!
Media types as RFC 9110 §8.3.1 writes them: `type/subtype`, then parameters, each a name and a
value that is a token or a quoted string (§5.6.2, §5.6.4, §5.6.6). The type, the subtype and the
parameters' names are case-insensitive and kept in lowercase; values keep their case. A name
may occur once (RFC 6838 §4.3). `format` writes a value back (`parse_format`), and
`parse_format_eq` is case-insensitivity: two media types that differ only in the case of their
type, subtype and names read the same.

The text is a field value, which has no whitespace at either end (RFC 9110 §5.5).
-/

@[expose] public section

namespace Lanes

structure MediaType where
  type : String
  subtype : String
  params : List (String × String) := []
  deriving DecidableEq, Repr

namespace MediaType

def isTchar (c : Char) : Bool :=
  Url.isAlpha c || Url.isDigit c || "!#$%&'*+-.^_`|~".toList.contains c

def isWs (c : Char) : Bool := c == ' ' || c == '\t'

/-- What a quoted string holds without a backslash: anything but controls, `"` and `\`. -/
def isQdtext (c : Char) : Bool :=
  c == '\t' || c == ' ' || c == '!' || ('#' ≤ c && c ≤ '[') || (']' ≤ c && c ≤ '~') || 0x80 ≤ c.toNat

/-- What a quoted string can hold at all: anything but controls other than tab. -/
def isQuotable (c : Char) : Bool := c == '\t' || (' ' ≤ c && c ≤ '~') || 0x80 ≤ c.toNat

def token : List Char → List Char × List Char
  | c :: rest => if isTchar c then (c :: (token rest).1, (token rest).2) else ([], c :: rest)
  | [] => ([], [])

def skipWs : List Char → List Char
  | c :: rest => if isWs c then skipWs rest else c :: rest
  | [] => []

/-- A quoted string after its opening quote: its text, and what follows the closing quote. -/
def quoted : List Char → Option (List Char × List Char)
  | '"' :: rest => some ([], rest)
  | '\\' :: c :: rest =>
    if isQuotable c then (quoted rest).map fun (v, r) => (c :: v, r) else none
  | c :: rest => if isQdtext c then (quoted rest).map fun (v, r) => (c :: v, r) else none
  | [] => none

def value : List Char → Option (List Char × List Char)
  | '"' :: rest => quoted rest
  | cs => if (token cs).1 = [] then none else some (token cs)

theorem length_skipWs_le (cs : List Char) : (skipWs cs).length ≤ cs.length := by
  induction cs with
  | nil => simp [skipWs]
  | cons c rest ih =>
    simp only [skipWs]
    split
    · simp; omega
    · simp

theorem length_token_le (cs : List Char) : (token cs).2.length ≤ cs.length := by
  induction cs with
  | nil => simp [token]
  | cons c rest ih =>
    simp only [token]
    split
    · simp; omega
    · simp

theorem length_quoted_le (cs : List Char) : ∀ {v r : List Char}, quoted cs = some (v, r) →
    r.length < cs.length := by
  fun_induction quoted cs <;> intro v r h
  · simp at h; simp [← h.2]
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨v', r'⟩, hq, he⟩ := h
    simp only [Prod.mk.injEq] at he
    rw [← he.2]
    simp only [List.length_cons]
    have := (by assumption : ∀ {v r : List Char}, quoted _ = some (v, r) → r.length < _) hq
    omega
  · simp at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨v', r'⟩, hq, he⟩ := h
    simp only [Prod.mk.injEq] at he
    rw [← he.2]
    simp only [List.length_cons]
    have := (by assumption : ∀ {v r : List Char}, quoted _ = some (v, r) → r.length < _) hq
    omega
  · simp at h
  · simp at h

theorem length_value_le {cs v r : List Char} (h : value cs = some (v, r)) : r.length ≤ cs.length := by
  unfold value at h
  split at h
  · have := length_quoted_le _ h; simp; omega
  · split at h
    · cases h
    · simp only [Option.some.injEq] at h
      have := length_token_le cs
      rw [h] at this
      exact this

/-- Parameters, each after `;` and optional whitespace; an empty one is skipped (`a/b;;c=d`). -/
def parseParams (cs : List Char) : Option (List (List Char × List Char)) :=
  if cs = [] then some []
  else
    match _h : skipWs cs with
    | ';' :: r =>
      match _ht : token (skipWs r) with
      | ([], _) => parseParams (skipWs r)
      | (name, '=' :: r') =>
        match _hv : value r' with
        | some (v, r'') => (parseParams r'').map ((name, v) :: ·)
        | none => none
      | _ => none
    | _ => none
termination_by cs.length
decreasing_by
  all_goals
    have h1 := length_skipWs_le cs
    have h2 := length_skipWs_le r
    rw [_h] at h1
    simp only [List.length_cons] at h1
  · omega
  · have h3 := length_token_le (skipWs r)
    rw [_ht] at h3
    have h4 := length_value_le _hv
    simp only [List.length_cons] at h3
    omega

def parseRaw (cs : List Char) : Option MediaType :=
  match token cs with
  | (t, '/' :: r) =>
    (parseParams (token r).2).map fun ps =>
      { type := String.ofList (Url.lower t), subtype := String.ofList (Url.lower (token r).1),
        params := ps.map fun (n, v) => (String.ofList (Url.lower n), String.ofList v) }
  | _ => none

def isToken (s : String) : Bool := !s.isEmpty && s.toList.all isTchar

def names (m : MediaType) : List String := m.params.map fun (n, _) => String.ofList (Url.lower n.toList)

/-- What `format` writes so that `parse` reads it: tokens, values a quoted string can hold, and
each name once in whatever case. -/
def valid (m : MediaType) : Bool :=
  isToken m.type && isToken m.subtype
    && m.params.all (fun (n, v) => isToken n && v.toList.all isQuotable) && m.names.Nodup

/-- The type, the subtype and the names in lowercase, which is how `parse` keeps them. -/
def lower (m : MediaType) : MediaType where
  type := String.ofList (Url.lower m.type.toList)
  subtype := String.ofList (Url.lower m.subtype.toList)
  params := m.params.map fun (n, v) => (String.ofList (Url.lower n.toList), v)

def parse (s : String) : Option MediaType :=
  (parseRaw s.toList).filter fun m => m.valid && m.lower == m

def quote (v : List Char) : List Char :=
  '"' :: v.flatMap (fun c => if c == '"' || c == '\\' then ['\\', c] else [c]) ++ ['"']

/-- A value as a token if it is one, else as a quoted string. -/
def valueChars (v : String) : List Char := if isToken v then v.toList else quote v.toList

def chars (m : MediaType) : List Char :=
  m.type.toList ++ '/' :: m.subtype.toList
    ++ m.params.flatMap fun (n, v) => ';' :: ' ' :: n.toList ++ '=' :: valueChars v

def format (m : MediaType) : String := String.ofList m.chars

end MediaType

end Lanes
