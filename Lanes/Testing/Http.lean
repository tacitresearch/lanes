/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes

/-!
What a test over HTTP keeps writing: a server of a handler on a local port, a request a
connection, for a fake of another service; and reading what came back, a page's text, a header,
a cookie it sets, the text between two markers with HTML's escapes undone.
-/

@[expose] public section

namespace Lanes.Testing

open Lanes.Http Std Std.Async

/-- A server of `handler` on `127.0.0.1` and a port the system chose: each connection is read
until one request is whole, answered, and closed. A request the reader refuses closes it. -/
def listen (handler : Request → IO Response) (backlog : UInt32 := 64) :
    Async (TCP.Socket.Server × UInt16) := do
  let server ← TCP.Socket.Server.mk
  server.bind (.v4 ⟨.ofParts 127 0 0 1, 0⟩)
  server.listen backlog
  let port := (← server.getSockName).port
  background do
    try
      repeat
        let client ← server.accept
        background do
          try
            let mut got := ByteArray.empty
            repeat
              let some bytes ← client.recv? 65536 | break
              got := got ++ bytes
              match Request.read {} got 0 with
              | .done incoming _ =>
                client.send (Response.wire (← handler incoming.request))
                break
              | .more => pure ()
              | .refuse _ => break
          catch _ => pure ()
          client.close
    catch _ => pure ()
  return (server, port)

def json (body : String) (status : Nat := 200) : Response :=
  Response.ofText "application/json" body status

/-- The body as text; empty when there is no response or it is not UTF-8. -/
def text (r : Option Response) : String :=
  (r.bind fun r => String.fromUTF8? r.body).getD ""

/-- Whether the body holds `part`. -/
def shows (r : Option Response) (part : String) : Bool :=
  ((text r).splitOn part).length > 1

/-- The status, `0` when there is no response. -/
def status (r : Option Response) : Nat := (r.map (·.status)).getD 0

def location (r : Option Response) : String := (r.bind (·.headers.lookup "location")).getD ""

/-- What HTML's escapes stand for, `&amp;` last. -/
def unescape (s : String) : String :=
  ((((s.replace "&quot;" "\"").replace "&#39;" "'").replace "&lt;" "<").replace "&gt;" ">").replace
    "&amp;" "&"

/-- The text after the first `start` in the body, up to the next `stop`, unescaped. -/
def between (r : Option Response) (start stop : String) : Option String := do
  let rest ← ((text r).splitOn start)[1]?
  return unescape ((rest.splitOn stop).headD "")

/-- The value of the hidden field `name` a page's form carries. -/
def field (r : Option Response) (name : String) : Option String :=
  between r s!"name=\"{name}\" value=\"" "\""

/-- The value a `set-cookie` of the response gives `name`. -/
def setCookie (r : Option Response) (name : String) : Option String := do
  let header ← ((← r).headers.filter (·.1 == "set-cookie")).find? (·.2.startsWith (name ++ "="))
  return ((header.2.drop (name.length + 1)).takeWhile (· != ';')).toString

/-- The query of a URL, decoded. -/
def queryOf (url : String) : List (String × String) :=
  ((Url.parse url).bind (·.query)).map parseForm |>.getD []

/-- A path as a list of segments: `/v/3` is `["v", "3"]`. -/
def segments (path : String) : List String := (path.splitOn "/").filter (· != "")

end Lanes.Testing
