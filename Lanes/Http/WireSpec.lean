/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Http.Wire

/-!
Writers of HTTP responses, as a server sends them. They are what the theorems about the reader
are stated against (`Lanes.Http.WireSound`): the reader reads back what these write. No adapter
runs them, so they are not trusted code; they are the specification.
-/

@[expose] public section

namespace Lanes.Http

namespace Response

/-- Whether the reader gives this header back as it is written, its name in lowercase: its
name is a token and frames nothing, and its value has no control character but tab and no blank
at either end. -/
def kept (field : String × String) : Bool :=
  token field.1 && field.1.toLower != "content-length" && field.1.toLower != "transfer-encoding"
    && field.2.toList.all plain && !(field.2.toList.head?.any ows)
    && !(field.2.toList.getLast?.any ows)

/-- The headers as the reader gives them back. -/
def lowered (headers : List (String × String)) : List (String × String) :=
  headers.map fun (name, value) => (name.toLower, value)

/-- Whether the writer can send this response so that the reader reads it back: a final status
of three digits, no body where the status allows none, a length of at most eighteen digits,
and headers the reader keeps. -/
def writable (r : Response) : Bool :=
  200 ≤ r.status && r.status < 1000 && (r.body.size == 0 || !(r.status == 204 || r.status == 304))
    && r.body.size < 10 ^ 18 && r.headers.all kept

/-- The head of `r`, with the writer's `own` header lines before its headers, ended by its blank
line. An interim (`1xx`) response is its head alone, with no lines of the writer's own. -/
def headWire (r : Response) (own : List String) : ByteArray :=
  ("\r\n".intercalate (("HTTP/1.1 " ++ toString r.status ++ " ") :: own
    ++ r.headers.map fun (name, value) => name ++ ": " ++ value) ++ "\r\n\r\n").toUTF8

/-- The bytes of `r` as a server sends it, framed by its length. -/
def wire (r : Response) : ByteArray :=
  r.headWire ["Content-Length: " ++ toString r.body.size] ++ r.body

def chunk (data : ByteArray) : ByteArray :=
  (String.ofList (Nat.toDigits 16 data.size) ++ "\r\n").toUTF8 ++ data ++ "\r\n".toUTF8

/-- The bytes of `r` with its body sent as `chunks`, which must make it up; `r.body` itself is
not read. -/
def wireChunked (r : Response) (chunks : List ByteArray) : ByteArray :=
  r.headWire ["Transfer-Encoding: chunked"] ++ chunks.foldl (· ++ chunk ·) .empty
    ++ "0\r\n\r\n".toUTF8

/-- Whether this is an interim (`1xx`) response the reader skips, with headers it keeps. -/
def interim (r : Response) : Bool :=
  100 ≤ r.status && r.status < 200 && r.headers.all kept

/-- The bytes of `r`, framed by its length, after the heads of the interim responses
`interims`. -/
def wireAfter (interims : List Response) (r : Response) : ByteArray :=
  interims.foldl (· ++ ·.headWire []) .empty ++ r.wire

/-- The bytes of `r` with nothing to say where it ends but the end of the connection. -/
def wireToEnd (r : Response) : ByteArray :=
  r.headWire [] ++ r.body

end Response

end Lanes.Http
