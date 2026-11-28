/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std
public import Lanes.Lib.Net.Percent
public import Lanes.Lib.Mime.Multipart

/-!
# HTTP requests and responses as data

Plain data types for an HTTP exchange. Application logic, specs and tests use these and never
touch a socket: the server reads them from bytes and writes them as bytes at the edge
(`Lanes.Web.Http.Conn`, `Lanes.Web.IO.Server`), which keeps handlers pure.
-/

@[expose] public section

namespace Lanes.Http

/-- The request methods an application sees. The server answers `HEAD` as `GET` without the
body and refuses the rest with `501`. -/
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

/-- A request as the server has read it, already parsed: a system sees this, never bytes
(rule 2.2). -/
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

/-- A response as data, which the server writes. -/
structure Response where
  status : Nat := 200
  /-- `Content-Length` is added by the server, and `Connection: close` when it closes after. -/
  headers : List (String × String) := []
  body : ByteArray := .empty
  deriving DecidableEq, Repr, Hashable, Inhabited

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

/-- The boundary of a `multipart/form-data` body. -/
def boundary? (r : Request) : Option String := do
  let m ← (r.header? "content-type").bind MediaType.parse
  if m.type == "multipart" && m.subtype == "form-data" then m.params.lookup "boundary" else none

/-- The parts of a `multipart/form-data` body, within `limits`. -/
def parts (r : Request) (limits : Multipart.Limits := {}) :
    Except Multipart.Error (List Multipart.Part) :=
  match r.boundary? with
  | some b => Multipart.parse limits b r.body
  | none => .error .malformed

/-- The text fields of a form: of a `multipart/form-data` body, its parts that are no file
(`Multipart.fields`); of any other, `application/x-www-form-urlencoded` (`parseForm`). -/
def form (r : Request) : List (String × String) :=
  match r.boundary? with
  | some _ =>
    match r.parts with
    | .ok parts => Multipart.fields parts
    | .error _ => []
  | none =>
    match r.text? with
    | some s => parseForm s
    | none => []

/-- The file a `multipart/form-data` form sent under `name`. -/
def file? (r : Request) (name : String) : Option Multipart.Part :=
  match r.parts with
  | .ok parts => Multipart.file? parts name
  | .error _ => none

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

/-- A request whose body is a form `encodeForm` wrote, and which is not multipart, carries its
fields. -/
theorem form_encodeForm {r : Request} {fields : List (String × String)}
    (h : r.body = (encodeForm fields).toUTF8) (hb : r.boundary? = none) : r.form = fields := by
  simp only [form, hb, text?, h, String.toUTF8_eq_toByteArray, String.fromUTF8?,
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
