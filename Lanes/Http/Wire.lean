/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Http.Basic

/-!
HTTP/1.1 on the wire, as pure functions: a request as the bytes a client sends, and the bytes a
server answers with as a response. The client adapter (`Lanes.Env.HttpClient`) only moves these
bytes over a socket.

The parser reads one response whose connection the server closes afterwards, which is what the
writer asks for with `Connection: close`. It is total, never reads outside the bytes it is
given, and answers `none` to anything it does not understand.
-/

@[expose] public section

namespace Lanes.Http

/-- The bytes of a request to `host`. The path and query are escaped; a header whose name or
value contains a line break is left out, so a value built from data cannot add headers. -/
def Request.wire (r : Request) (host : String) : ByteArray :=
  let method := match r.method with
    | .get => "GET" | .post => "POST" | .put => "PUT" | .patch => "PATCH" | .delete => "DELETE"
  let path := "/" ++ "/".intercalate (r.path.map percentEncode)
  let query := if r.query.isEmpty then ""
    else "?" ++ "&".intercalate (r.query.map fun (k, v) => percentEncode k ++ "=" ++ percentEncode v)
  let clean := fun (s : String) => !s.any fun c => c == '\r' || c == '\n'
  let headers := r.headers.filter fun (name, value) =>
    clean name && clean value && !["host", "content-length", "connection"].contains name.toLower
  let lines := [s!"{method} {path}{query} HTTP/1.1", s!"Host: {host}", "Connection: close",
      s!"Content-Length: {r.body.size}"] ++ headers.map fun (name, value) => s!"{name}: {value}"
  ("\r\n".intercalate lines ++ "\r\n\r\n").toUTF8 ++ r.body

/-- Where the blank line that ends the head is: the index just after `\r\n\r\n`. -/
def headEnd (bytes : ByteArray) : Option Nat :=
  (List.range (bytes.size - 3)).find? (fun i =>
    bytes[i]? == some 13 && bytes[i + 1]? == some 10 && bytes[i + 2]? == some 13
      && bytes[i + 3]? == some 10)
    |>.map (· + 4)

/-- A chunked body, decoded. `fuel` bounds the number of chunks. -/
def dechunk (bytes : ByteArray) : (fuel : Nat) → (pos : Nat) → (acc : ByteArray) →
    Option ByteArray
  | 0, _, _ => none
  | fuel + 1, pos, acc =>
    let lineEnd := (List.range (bytes.size - pos - 1)).find? fun i =>
      bytes[pos + i]? == some 13 && bytes[pos + i + 1]? == some 10
    match lineEnd with
    | none => none
    | some len =>
      let line := (String.fromUTF8? (bytes.extract pos (pos + len))).getD ""
      let digits := (line.splitOn ";").headD "" |>.trimAscii.toString
      let size := digits.toList.foldl (init := some 0) fun acc c =>
        acc.bind fun n => (hexValue? c).map (n * 16 + ·)
      match size with
      | none => none
      | some 0 => if digits.isEmpty then none else some acc
      | some size =>
        let start := pos + len + 2
        if start + size + 2 ≤ bytes.size then
          dechunk bytes fuel (start + size + 2) (acc ++ bytes.extract start (start + size))
        else none

def Response.parse (bytes : ByteArray) : Option Response := do
  let bodyStart ← headEnd bytes
  let head ← String.fromUTF8? (bytes.extract 0 (bodyStart - 4))
  let lines := head.splitOn "\r\n"
  let status ← match (lines.headD "").splitOn " " with
    | version :: code :: _ => if version.startsWith "HTTP/1." then code.toNat? else none
    | _ => none
  let headers := lines.drop 1 |>.filterMap fun line =>
    match line.splitOn ":" with
    | name :: value =>
      some (name.trimAscii.toString.toLower, (":".intercalate value).trimAscii.toString)
    | [] => none
  let rest := bytes.extract bodyStart bytes.size
  let chunked := headers.any fun (name, value) =>
    name == "transfer-encoding" && value.toLower == "chunked"
  let body ← if chunked then dechunk rest (rest.size + 1) 0 .empty
    else match (headers.find? (·.1 == "content-length")).bind (·.2.toNat?) with
      | some length => if length ≤ rest.size then some (rest.extract 0 length) else none
      | none => some rest
  return { status, headers, body }

end Lanes.Http
