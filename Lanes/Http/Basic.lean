/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.Codec

/-!
# HTTP requests and responses as data

Plain data types for an HTTP exchange. Application logic, specs and tests use these and never
touch a socket or `Std.Http`: the server adapter (`Lanes.Env.Http`) converts at the edge. That
keeps handlers pure and keeps the young `Std.Http` API behind one thin wrapper.
-/

@[expose] public section

namespace Lanes.Http

/-- The request methods an application sees. The adapter answers `HEAD` as `GET` without the
body and refuses the rest with `405`. -/
inductive Method where
  | get | post | put | patch | delete
  deriving DecidableEq, Repr, Hashable

/-- Bodies print as text when they are UTF-8 and as a byte count otherwise. Low priority, so a
`Repr ByteArray` instance from elsewhere wins. -/
instance (priority := low) reprBody : Repr ByteArray where
  reprPrec b _ :=
    match String.fromUTF8? b with
    | some s => repr s
    | none => s!"<{b.size} bytes>"

structure Request where
  method : Method
  /-- The path as decoded segments: `/todos/42` is `["todos", "42"]`. -/
  path : List String
  /-- The query parameters, decoded, in order. A parameter without a value has value `""`. -/
  query : List (String × String) := []
  /-- The headers, with lowercase names, in order. -/
  headers : List (String × String) := []
  body : ByteArray := .empty
  deriving DecidableEq, Repr, Hashable

def Method.codec : Codec Method :=
  Codec.sum% Method { get, post, put, patch, delete }

/-- How a request is written to a journal. -/
def Request.codec : Codec Request :=
  let fields := Codec.list (Codec.pair Codec.string Codec.string)
  Codec.struct% Request { method := Method.codec, path := Codec.list Codec.string,
    query := fields, headers := fields, body := Codec.bytes }

structure Response where
  status : Nat := 200
  /-- `Content-Length` and `Date` are added by the server. -/
  headers : List (String × String) := []
  body : ByteArray := .empty
  deriving DecidableEq, Repr, Hashable, Inhabited

def hexValue? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def percentDecodeBytes (plusIsSpace : Bool) : List Char → Option (List UInt8)
  | [] => some []
  | '%' :: hi :: lo :: rest => do
    let h ← hexValue? hi
    let l ← hexValue? lo
    let rest ← percentDecodeBytes plusIsSpace rest
    return UInt8.ofNat (h * 16 + l) :: rest
  | '%' :: _ => none
  | c :: rest => do
    let rest ← percentDecodeBytes plusIsSpace rest
    return (if c == '+' && plusIsSpace then " " else c.toString).toUTF8.data.toList ++ rest

/-- `none` if an escape is malformed or the result is not UTF-8. -/
def percentDecode (s : String) (plusIsSpace : Bool := false) : Option String := do
  let bytes ← percentDecodeBytes plusIsSpace s.toList
  String.fromUTF8? (ByteArray.mk bytes.toArray)

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

/-- Letters, digits and `-._~`: the bytes RFC 3986 lets a URL carry unescaped everywhere. -/
def unreserved (b : UInt8) : Bool :=
  (48 ≤ b && b ≤ 57) || (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122)
    || b == 45 || b == 46 || b == 95 || b == 126

def percentEncodeByte (b : UInt8) : List Char :=
  if unreserved b then [Char.ofNat b.toNat]
  else ['%', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

def percentEncode (s : String) : String :=
  String.ofList (s.toUTF8.data.toList.flatMap percentEncodeByte)

private theorem hexValue?_hexDigit : ∀ n, n < 16 → hexValue? (hexDigit n) = some n := by decide

private theorem unreserved_plain : ∀ b : UInt8, unreserved b →
    Char.ofNat b.toNat ≠ '%' ∧ Char.ofNat b.toNat ≠ '+' ∧ (Char.ofNat b.toNat).utf8Size = 1
      ∧ (Char.ofNat b.toNat).val.toUInt8 = b := by decide

private theorem ofNat_nibbles :
    ∀ b : UInt8, UInt8.ofNat (b.toNat / 16) * 16 + UInt8.ofNat (b.toNat % 16) = b := by decide

private theorem percentDecodeBytes_encodeByte (plusIsSpace : Bool) (b : UInt8) (cs : List Char) :
    percentDecodeBytes plusIsSpace (percentEncodeByte b ++ cs)
      = (percentDecodeBytes plusIsSpace cs).map (b :: ·) := by
  unfold percentEncodeByte
  split
  · rename_i h
    obtain ⟨h1, h2, h3, h4⟩ := unreserved_plain b h
    rw [List.singleton_append, percentDecodeBytes]
    · simp [h2, Char.toString, String.toByteArray_singleton, List.utf8Encode_singleton,
        String.utf8EncodeChar_eq_singleton h3, h4]
      cases percentDecodeBytes plusIsSpace cs <;> simp
    · intro hi lo rest h _; exact h1 h
    · intro h; exact h1 h
  · have h16 : b.toNat / 16 < 16 := by have := b.toNat_lt; omega
    simp [percentDecodeBytes, hexValue?_hexDigit _ h16,
      hexValue?_hexDigit _ (Nat.mod_lt _ (by decide : 16 > 0)), ofNat_nibbles]
    cases percentDecodeBytes plusIsSpace cs <;> simp

private theorem percentDecodeBytes_encode (plusIsSpace : Bool) (bs : List UInt8) :
    percentDecodeBytes plusIsSpace (bs.flatMap percentEncodeByte) = some bs := by
  induction bs with
  | nil => simp [percentDecodeBytes]
  | cons b bs ih => simp [List.flatMap_cons, percentDecodeBytes_encodeByte, ih]

/-- Decoding reads back what was encoded, with `+` read as a space or not: an encoding has no `+`. -/
theorem percentDecode_percentEncode (s : String) (plusIsSpace : Bool := false) :
    percentDecode (percentEncode s) plusIsSpace = some s := by
  simp [percentDecode, percentEncode, percentDecodeBytes_encode, String.fromUTF8?, s.isValidUTF8,
    String.fromUTF8]

private theorem percentEncodeByte_plain :
    ∀ b : UInt8, ∀ c ∈ percentEncodeByte b, c ≠ '&' ∧ c ≠ '=' ∧ c ≠ ';' := by decide

/-- An encoding has no `&`, `=` or `;`, so it cannot end a field of a form or a cookie. -/
theorem percentEncode_plain (s : String) :
    ∀ c ∈ (percentEncode s).toList, c ≠ '&' ∧ c ≠ '=' ∧ c ≠ ';' := by
  intro c hc
  simp only [percentEncode, String.toList_ofList, List.mem_flatMap] at hc
  obtain ⟨b, -, hb⟩ := hc
  exact percentEncodeByte_plain b c hb

/-- The fields of a form body: its pieces between `&`, each a key and a value split at the first
`=`, or a key alone, percent-decoded with `+` as a space. Pairs that do not decode are dropped. -/
def parseForm (s : String) : List (String × String) :=
  (s.toList.splitOn '&').filterMap fun pair =>
    if pair.isEmpty then none
    else
      match pair.splitOn '=' with
      | [key] => (percentDecode (String.ofList key) true).map (·, "")
      | key :: value => do
        let key ← percentDecode (String.ofList key) true
        let value ← percentDecode (String.ofList (['='].intercalate value)) true
        return (key, value)
      | [] => none

/-- A form as a body: each key and value percent-encoded, joined by `=`, and the fields by `&`. -/
def encodeForm (fields : List (String × String)) : String :=
  "&".intercalate (fields.map fun (key, value) => percentEncode key ++ "=" ++ percentEncode value)

private theorem splitOn_field (key value : String) :
    ((percentEncode key).toList ++ '=' :: (percentEncode value).toList).splitOn '='
      = [(percentEncode key).toList, (percentEncode value).toList] := by
  have := List.splitOn_intercalate (ls := [(percentEncode key).toList, (percentEncode value).toList])
    '=' (by
      intro l hl hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact (percentEncode_plain key '=' hmem).2.1 rfl
      · exact (percentEncode_plain value '=' hmem).2.1 rfl) (by simp)
  simpa [List.intercalate] using this

/-- `parseForm` reads back every form `encodeForm` writes, whatever its keys and values hold. -/
theorem parseForm_encodeForm (fields : List (String × String)) :
    parseForm (encodeForm fields) = fields := by
  cases fields with
  | nil => simp [parseForm, encodeForm]
  | cons field more =>
    have hparts : ∀ l ∈ (field :: more).map (fun (kv : String × String) =>
        (percentEncode kv.1 ++ "=" ++ percentEncode kv.2).toList), '&' ∉ l := by
      intro l hl hmem
      obtain ⟨⟨k, v⟩, -, rfl⟩ := List.mem_map.mp hl
      simp only [String.toList_append, List.mem_append] at hmem
      rcases hmem with (h | h) | h
      · exact (percentEncode_plain k '&' h).1 rfl
      · simp at h
      · exact (percentEncode_plain v '&' h).1 rfl
    have hsplit := List.splitOn_intercalate '&' hparts (by simp)
    simp only [parseForm, encodeForm, String.toList_intercalate, List.map_map]
    rw [show ("&".toList) = ['&'] from rfl]
    simp only [Function.comp_def] at hsplit ⊢
    rw [hsplit, List.filterMap_map]
    generalize field :: more = fields
    induction fields with
    | nil => rfl
    | cons kv fields ih =>
      simp only [List.filterMap_cons] at ih ⊢
      simp only [Function.comp_apply] at ih ⊢
      simp [splitOn_field, String.ofList_toList, percentDecode_percentEncode] at ih ⊢
      exact ih

namespace Request

def param? (r : Request) (key : String) : Option String :=
  (r.query.find? (·.1 == key)).map (·.2)

/-- `name` must be lowercase. -/
def header? (r : Request) (name : String) : Option String :=
  (r.headers.find? (·.1 == name)).map (·.2)

def text? (r : Request) : Option String :=
  String.fromUTF8? r.body

def form (r : Request) : List (String × String) :=
  match r.text? with
  | some s => parseForm s
  | none => []

def field? (r : Request) (key : String) : Option String :=
  (r.form.find? (·.1 == key)).map (·.2)

private theorem find?_lookup (pairs : List (String × String)) (key : String) :
    (pairs.find? (·.1 == key)).map (·.2) = pairs.lookup key := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
    by_cases h : pair.1 = key
    · simp [List.lookup, h]
    · have : (key == pair.1) = false := by simp [Ne.symm h]
      simp [List.lookup, h, this, ih]

/-- The value of the first parameter named `key`. -/
theorem param?_eq_lookup (r : Request) (key : String) : r.param? key = r.query.lookup key :=
  find?_lookup ..

/-- The value of the first header named `name`. -/
theorem header?_eq_lookup (r : Request) (name : String) : r.header? name = r.headers.lookup name :=
  find?_lookup ..

/-- The value of the first field of the form named `key`. -/
theorem field?_eq_lookup (r : Request) (key : String) : r.field? key = r.form.lookup key :=
  find?_lookup ..

/-- A request whose body is a form `encodeForm` wrote carries its fields. -/
theorem form_encodeForm {r : Request} {fields : List (String × String)}
    (h : r.body = (encodeForm fields).toUTF8) : r.form = fields := by
  simp only [form, text?, h, String.toUTF8_eq_toByteArray, String.fromUTF8?,
    (encodeForm fields).isValidUTF8, String.fromUTF8, dite_true]
  exact parseForm_encodeForm fields

end Request

namespace Response

def ofText (contentType : String) (body : String) (status : Nat := 200) : Response where
  status
  headers := [("content-type", contentType)]
  body := body.toUTF8

def text (body : String) (status : Nat := 200) : Response :=
  ofText "text/plain; charset=utf-8" body status

/-- The body must already be escaped HTML; build it with `Lanes.Html`. -/
def html (body : String) (status : Nat := 200) : Response :=
  ofText "text/html; charset=utf-8" body status

/-- The body must already be serialized JSON. -/
def json (body : String) (status : Nat := 200) : Response :=
  ofText "application/json" body status

def empty (status : Nat := 204) : Response where
  status

def redirect (location : String) (status : Nat := 303) : Response where
  status
  headers := [("location", location)]

def withHeader (r : Response) (name value : String) : Response :=
  { r with headers := r.headers ++ [(name, value)] }

end Response

end Lanes.Http
