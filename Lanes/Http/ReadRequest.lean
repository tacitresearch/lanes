/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Http.Wire

/-!
The reader of the requests a server receives, as a pure function of the bytes received so far,
by the strict profile of `docs/decisions/new-the-server-reads-requests-by-a-strict-profile.md`:
it needs more, or it has a request and where it ends, or it refuses with a status, and an
answer once given stays as more bytes arrive. Every limit is a field of `Request.Limits`. What it
is proved to do is in `Lanes.Http.ReadRequestSound`.
-/

@[expose] public section

namespace Lanes.Http

inductive Refusal where
  | badRequest
  | contentTooLarge
  | uriTooLong
  | fieldsTooLarge
  | notImplemented
  | versionNotSupported
  deriving DecidableEq, Repr

def Refusal.status : Refusal → Nat
  | .badRequest => 400
  | .contentTooLarge => 413
  | .uriTooLong => 414
  | .fieldsTooLarge => 431
  | .notImplemented => 501
  | .versionNotSupported => 505

/-- What a reader makes of the bytes from where it starts: it needs more, it refuses them, or it
has read a value that ends just before `stop`. -/
inductive Parsed (α : Type) where
  | more
  | refuse (why : Refusal)
  | done (value : α) (stop : Nat)
  deriving DecidableEq, Repr

/-- Whether the bytes from `i` on start with `pattern`. -/
def matchAt (bytes : ByteArray) : List UInt8 → Nat → Bool
  | [], _ => true
  | b :: rest, i => bytes[i]? == some b && matchAt bytes rest (i + 1)

/-- The first index from `pos` on where `pattern` starts and ends by `stop`. -/
def find (bytes : ByteArray) (pattern : List UInt8) (pos stop : Nat) : Option Nat :=
  if pos + pattern.length ≤ min stop bytes.size then
    if matchAt bytes pattern pos then some pos else find bytes pattern (pos + 1) stop
  else none
termination_by stop + 1 - pos

/-- The parts of `chars` between the `sep`s. -/
def pieces (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: rest =>
    let parts := pieces sep rest
    if c = sep then [] :: parts else (c :: parts.headD []) :: parts.tail

namespace Request

structure Limits where
  /-- Bytes of the request line, its CRLF left out; a longer one is refused with `414`. -/
  line_max : Nat := 8192
  /-- Bytes of the head, its blank line included; a longer one is refused with `431`. -/
  head_max : Nat := 16384
  /-- More fields are refused with `431`. -/
  fields_max : Nat := 100
  /-- Bytes of the body; a larger one is refused with `413`. -/
  body_max : Nat := 1048576
  /-- Chunks of a chunked body, the last one left out; more are refused with `413`. -/
  chunks_max : Nat := 4096
  deriving Repr

inductive Version where
  | http10
  | http11
  deriving DecidableEq, Repr

inductive Framing where
  | length (bytes : Nat)
  | chunked
  deriving DecidableEq, Repr

structure Head where
  method : Method
  /-- The method was `HEAD`: answered as `GET`, without the body. -/
  headOnly : Bool
  path : List String
  query : List (String × String)
  version : Version
  /-- In order, names in lowercase and values without the blanks around them. -/
  fields : List (String × String)
  framing : Framing
  deriving DecidableEq, Repr

/-- A request as the server hands it on. -/
structure Incoming where
  request : Request
  headOnly : Bool
  /-- The connection ends after the response. -/
  close : Bool
  deriving DecidableEq, Repr

/-- The elements of a list-valued field (RFC 9110, 5.6.1), in lowercase. -/
def elements (values : List String) : List String :=
  values.flatMap fun value => (pieces ',' value.toList).map fun e => (String.ofList (trimOws e)).toLower

def version? : List Char → Except Refusal Version
  | ['H', 'T', 'T', 'P', '/', '1', '.', '1'] => .ok .http11
  | ['H', 'T', 'T', 'P', '/', '1', '.', '0'] => .ok .http10
  | ['H', 'T', 'T', 'P', '/', major, '.', minor] =>
    if major.isDigit && minor.isDigit then .error .versionNotSupported else .error .badRequest
  | _ => .error .badRequest

/-- The method, and whether it was `HEAD`. -/
def method? (chars : List Char) : Except Refusal (Method × Bool) :=
  match String.ofList chars with
  | "GET" => .ok (.get, false)
  | "HEAD" => .ok (.get, true)
  | "POST" => .ok (.post, false)
  | "PUT" => .ok (.put, false)
  | "PATCH" => .ok (.patch, false)
  | "DELETE" => .ok (.delete, false)
  | name => if token name then .error .notImplemented else .error .badRequest

/-- What RFC 3986 lets a path or a query hold besides `/` and `?`; `%` starts an escape. -/
def pchar (c : Char) : Bool :=
  c.isAlphanum || "-._~!$&'()*+,;=:@%".toList.contains c

def targetChar (c : Char) : Bool :=
  pchar c || c == '/' || c == '?'

def hostChar (c : Char) : Bool :=
  c.isAlphanum || "-._~!$&'()*+,;=:[]%".toList.contains c

def segments? (path : List Char) : Option (List String) :=
  if path.isEmpty then some [] else (pieces '/' path).mapM fun s => percentDecode (String.ofList s)

def queryPart? (chars : List Char) : Option String :=
  percentDecode (String.ofList (chars.map fun c => if c = '+' then ' ' else c))

def pair? (chars : List Char) : Option (String × String) := do
  let key ← queryPart? (chars.takeWhile (· != '='))
  let value ← queryPart? ((chars.dropWhile (· != '=')).drop 1)
  return (key, value)

def query? (chars : List Char) : Option (List (String × String)) :=
  if chars.isEmpty then some [] else (pieces '&' chars).mapM pair?

/-- The path and the query of a target in origin form. -/
def target? : List Char → Except Refusal (List String × List (String × String))
  | '/' :: rest =>
    if rest.all targetChar then
      match segments? (rest.takeWhile (· != '?')), query? ((rest.dropWhile (· != '?')).drop 1) with
      | some path, some query => .ok (path, query)
      | _, _ => .error .badRequest
    else .error .badRequest
  | _ => .error .badRequest

def fieldLine? (line : List Char) : Except Refusal (String × String) :=
  match headerLine? line with
  | some field => .ok field
  | none => .error .badRequest

def host? (version : Version) (fields : List (String × String)) : Except Refusal Unit :=
  match (fields.filter (·.1 == "host")).map (·.2), version with
  | [host], _ => if host != "" && host.toList.all hostChar then .ok () else .error .badRequest
  | [], .http10 => .ok ()
  | _, _ => .error .badRequest

/-- Whether a field that says where the body ends has a tab in its line. RFC 9110 lets a tab
stand for a blank there, and some parsers do not, which is how `chunked` with a tab after it is
used to smuggle a request (TE.TE). -/
def tabbedFraming (fieldLines : List (List Char)) : Bool :=
  fieldLines.any fun line =>
    ["content-length", "transfer-encoding"].contains
        (String.ofList (line.takeWhile (· != ':'))).toLower
      && line.contains '\t'

/-- Where the body ends (RFC 9112, 6.3), from the head alone. -/
def framing? (limits : Limits) (version : Version) (fields : List (String × String)) :
    Except Refusal Framing :=
  let codings := (fields.filter (·.1 == "transfer-encoding")).map (·.2)
  let lengths := (fields.filter (·.1 == "content-length")).map (·.2)
  match codings, lengths with
  | [], [] => .ok (.length 0)
  | [], [length] =>
    match decimal? length with
    | some n => if limits.body_max < n then .error .contentTooLarge else .ok (.length n)
    | none => .error .badRequest
  | [coding], [] =>
    if version == .http11 && coding.toLower == "chunked" then .ok .chunked
    else if version == .http11 && (elements [coding]).getLast? == some "chunked"
        && (elements [coding]).count "chunked" == 1 then .error .notImplemented
    else .error .badRequest
  | _, _ => .error .badRequest

/-- The head given as its lines, the request line first. -/
def parseHead (limits : Limits) : List (List Char) → Except Refusal Head
  | [] => .error .badRequest
  | line :: fieldLines =>
    match pieces ' ' line with
    | [method, target, version] => do
      let version ← version? version
      let (method, headOnly) ← method? method
      if limits.fields_max < fieldLines.length then throw .fieldsTooLarge
      let fields ← fieldLines.mapM fieldLine?
      host? version fields
      if tabbedFraming fieldLines then throw .badRequest
      let framing ← framing? limits version fields
      let (path, query) ← target? target
      return { method, headOnly, path, query, version, fields, framing }
    | _ => .error .badRequest

/-- The head that starts at `pos`, and where its body starts. A request line that has no CRLF
within `line_max + 2` bytes, or a head with no blank line within `head_max` bytes, is refused as
soon as that many bytes are there. -/
def readHead (limits : Limits) (bytes : ByteArray) (pos : Nat) : Parsed Head :=
  match find bytes [13, 10] pos (pos + limits.line_max + 2) with
  | none => if pos + limits.line_max + 2 ≤ bytes.size then .refuse .uriTooLong else .more
  | some lineEnd =>
    match find bytes [13, 10, 13, 10] lineEnd (pos + limits.head_max) with
    | none => if pos + limits.head_max ≤ bytes.size then .refuse .fieldsTooLarge else .more
    | some blank =>
      match String.fromUTF8? (bytes.extract pos blank) with
      | none => .refuse .badRequest
      | some text =>
        match parseHead limits (splitLines text.toList [] []) with
        | .error why => .refuse why
        | .ok head => .done head (blank + 4)

/-- The size of the chunk whose size line starts at `pos`, and where its data starts: one to
sixteen hex digits and a CRLF, nothing else. -/
def chunkSize (bytes : ByteArray) (pos : Nat) : Parsed Nat :=
  let (size, digitsEnd) := hex bytes chunkSizeDigits_max pos 0
  if digitsEnd = pos then
    if pos < bytes.size then .refuse .badRequest else .more
  else
    match crlf bytes digitsEnd with
    | .more => .more
    | .done none => .refuse .badRequest
    | .done (some start) => .done size start

/-- The chunked body from `pos` on, after `body`. `fuel` is the number of chunks left, the last
one included. -/
def chunks (limits : Limits) (bytes : ByteArray) : (fuel pos : Nat) → (body : ByteArray) →
    Parsed ByteArray
  | 0, _, _ => .refuse .contentTooLarge
  | fuel + 1, pos, body =>
    match chunkSize bytes pos with
    | .more => .more
    | .refuse why => .refuse why
    | .done size start =>
      if size = 0 then
        match crlf bytes start with
        | .more => .more
        | .done none => .refuse .badRequest
        | .done (some stop) => .done body stop
      else if limits.body_max < body.size + size then .refuse .contentTooLarge
      else
        match crlf bytes (start + size) with
        | .more => .more
        | .done none => .refuse .badRequest
        | .done (some next) =>
          chunks limits bytes fuel next (body ++ bytes.extract start (start + size))

def Head.close (head : Head) : Bool :=
  head.version == .http10
    || head.fields.any fun (name, value) => name == "connection" && (elements [value]).contains "close"

def Head.expectsContinue (head : Head) : Bool :=
  head.fields.any fun (name, value) => name == "expect" && value.toLower == "100-continue"

def Head.incoming (head : Head) (body : ByteArray) : Incoming where
  request := { method := head.method, path := head.path, query := head.query
               headers := head.fields, body }
  headOnly := head.headOnly
  close := head.close

/-- The request that starts at `pos`, read by the profile. -/
def read (limits : Limits) (bytes : ByteArray) (pos : Nat) : Parsed Incoming :=
  match readHead limits bytes pos with
  | .more => .more
  | .refuse why => .refuse why
  | .done head start =>
    match head.framing with
    | .length n =>
      if start + n ≤ bytes.size then
        .done (head.incoming (bytes.extract start (start + n))) (start + n)
      else .more
    | .chunked =>
      match chunks limits bytes (limits.chunks_max + 1) start .empty with
      | .more => .more
      | .refuse why => .refuse why
      | .done body stop => .done (head.incoming body) stop

end Request

end Lanes.Http
