/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# HTTP requests and responses as data

Plain data types for an HTTP exchange. Application logic, specs and tests use these and never
touch a socket or `Std.Http`: the server adapter (`Lanes.Env.Http`) converts at the edge. That
keeps handlers pure and keeps the young `Std.Http` API behind one thin wrapper.
-/

@[expose] public section

namespace Lanes.Http

/-- The request methods an application can handle. Others are refused by the adapter. -/
inductive Method where
  | get | head | post | put | patch | delete | options
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
    return (if c == '+' && plusIsSpace then " " else c.toString).toUTF8.toList ++ rest

/-- `none` if an escape is malformed or the result is not UTF-8. -/
def percentDecode (s : String) (plusIsSpace : Bool := false) : Option String := do
  let bytes ← percentDecodeBytes plusIsSpace s.toList
  String.fromUTF8? (ByteArray.mk bytes.toArray)

/-- Pairs that do not decode are dropped. -/
def parseForm (s : String) : List (String × String) :=
  (s.splitOn "&").filterMap fun pair =>
    if pair.isEmpty then none
    else
      match pair.splitOn "=" with
      | [key] => (percentDecode key true).map (·, "")
      | key :: value => do
        let key ← percentDecode key true
        let value ← percentDecode ("=".intercalate value) true
        return (key, value)
      | [] => none

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
