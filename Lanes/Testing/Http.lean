/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes

/-!
What a test over HTTP keeps writing: a server of a handler on a local port, a request a
connection, for a fake of another service; and reading what came back, a page's text, a header,
a cookie it sets, the text between two markers with HTML's escapes undone, a page's tags and the
form it carries.
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

/-- The character an entity's name between `&` and `;` stands for: the five `Lanes.Html` writes
and numeric references. -/
def entity? (name : String) : Option Char :=
  match name with
  | "amp" => some '&'
  | "lt" => some '<'
  | "gt" => some '>'
  | "quot" => some '"'
  | "apos" => some '\''
  | _ =>
    let hexDigit? (c : Char) : Option Nat :=
      if c.isDigit then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c.toLower && c.toLower ≤ 'f' then some (c.toLower.toNat - 'a'.toNat + 10)
      else none
    let code : Option Nat := match name.toList with
      | '#' :: 'x' :: hex@(_ :: _) | '#' :: 'X' :: hex@(_ :: _) =>
        hex.foldlM (init := 0) fun n c => (hexDigit? c).map (n * 16 + ·)
      | '#' :: decimal@(_ :: _) => (String.ofList decimal).toNat?
      | _ => none
    (code.filter Nat.isValidChar).map Char.ofNat

/-- What HTML's escapes stand for, read once from the left, so `&amp;lt;` is `&lt;`. An `&` that
starts no entity stays. -/
def unescape (s : String) : String :=
  match s.splitOn "&" with
  | [] => ""
  | first :: pieces => first ++ String.join (pieces.map fun piece =>
    match piece.splitOn ";" with
    | name :: rest@(_ :: _) =>
      match entity? name with
      | some c => c.toString ++ ";".intercalate rest
      | none => "&" ++ piece
    | _ => "&" ++ piece)

/-- The text after the first `start` in the body, up to the next `stop`, unescaped. -/
def between (r : Option Response) (start stop : String) : Option String := do
  let rest ← ((text r).splitOn start)[1]?
  return unescape ((rest.splitOn stop).headD "")

/-- The value of the hidden field `name` a page's form carries. -/
def field (r : Option Response) (name : String) : Option String :=
  between r s!"name=\"{name}\" value=\"" "\""

/-- A tag as `tags` reads it: its name lowercased, `/form` for an end tag, and its attributes, each
name lowercased and each value unquoted and unescaped. -/
structure Tag where
  name : String
  attrs : List (String × String)
  deriving DecidableEq, Repr

def Tag.attr? (t : Tag) (name : String) : Option String := t.attrs.lookup name

/-- Where `tags` is in the text: between tags, in a tag's name, between its attributes, in an
attribute's name, after one before an `=`, before a value, or in a value quoted or bare. -/
inductive Tag.Lexing where
  | text
  | name (rev : List Char)
  | between
  | attr (rev : List Char)
  | named (attr : String)
  | equals (attr : String)
  | quoted (quote : Char) (attr : String) (rev : List Char)
  | bare (attr : String) (rev : List Char)

/-- The tags read so far, newest first; the tag being read, its name and attributes newest
first; and where in the text the next character is. -/
structure Tag.Lexer where
  done : List Tag := []
  tag : String := ""
  attrs : List (String × String) := []
  at_ : Tag.Lexing := .text

def Tag.nameChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == ':' || c == '.'

def Tag.lower (rev : List Char) : String := String.ofList (rev.reverse.map Char.toLower)

def Tag.Lexer.close (l : Tag.Lexer) (attrs : List (String × String)) : Tag.Lexer :=
  { done := ⟨l.tag, attrs.reverse⟩ :: l.done, at_ := .text }

def Tag.Lexer.step (l : Tag.Lexer) (c : Char) : Tag.Lexer :=
  match l.at_ with
  | .text => if c == '<' then { l with at_ := .name [] } else l
  | .name rev =>
    if Tag.nameChar c || (rev.isEmpty && c == '/') then { l with at_ := .name (c :: rev) }
    else if rev.isEmpty then { l with at_ := .text }
    else
      let l := { l with tag := Tag.lower rev, attrs := [] }
      if c == '>' then l.close [] else { l with at_ := .between }
  | .between =>
    if c == '>' then l.close l.attrs
    else if Tag.nameChar c then { l with at_ := .attr [c] } else l
  | .attr rev =>
    if Tag.nameChar c then { l with at_ := .attr (c :: rev) }
    else if c == '=' then { l with at_ := .equals (Tag.lower rev) }
    else if c == '>' then l.close ((Tag.lower rev, "") :: l.attrs)
    else { l with at_ := .named (Tag.lower rev) }
  | .named a =>
    if c == '=' then { l with at_ := .equals a }
    else if c == '>' then l.close ((a, "") :: l.attrs)
    else if Tag.nameChar c then { l with attrs := (a, "") :: l.attrs, at_ := .attr [c] }
    else l
  | .equals a =>
    if c == '"' || c == '\'' then { l with at_ := .quoted c a [] }
    else if c == '>' then l.close ((a, "") :: l.attrs)
    else if c.isWhitespace then l
    else { l with at_ := .bare a [c] }
  | .quoted q a rev =>
    if c == q then { l with attrs := (a, unescape (String.ofList rev.reverse)) :: l.attrs,
                            at_ := .between }
    else { l with at_ := .quoted q a (c :: rev) }
  | .bare a rev =>
    let value := unescape (String.ofList rev.reverse)
    if c == '>' then l.close ((a, value) :: l.attrs)
    else if c.isWhitespace then { l with attrs := (a, value) :: l.attrs, at_ := .between }
    else { l with at_ := .bare a (c :: rev) }

/-- The tags of an HTML text, in order, with their attributes: what a test reads a page's markup
with, as a browser would, not by searching its text. Comments and the text of scripts are not
told apart from markup. -/
def tags (html : String) : List Tag :=
  (html.toList.foldl Tag.Lexer.step {}).done.reverse

/-- What a form posts to, and its hidden fields, in order. -/
structure Form where
  action : String
  fields : List (String × String)
  deriving DecidableEq, Repr

/-- The form of the page whose `id` is `id`: its `action` and the `name` and `value` of each
hidden `input` in it. Attributes may come in any order, quoted either way, and escaped as
`Lanes.Html` writes them. -/
def form? (page : Option Response) (id : String) : Option Form := do
  let rest := (tags (text page)).dropWhile fun t => !(t.name == "form" && t.attr? "id" == some id)
  let start ← rest.head?
  let inside := (rest.drop 1).takeWhile (·.name != "/form")
  return { action := (start.attr? "action").getD ""
           fields := inside.filterMap fun t => do
             guard (t.name == "input" && (t.attr? "type").map (·.toLower) == some "hidden")
             return (← t.attr? "name", (t.attr? "value").getD "") }

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
