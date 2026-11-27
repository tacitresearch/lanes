/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std

/-!
The part of XML 1.0 that S3's answers use, read into a tree: elements, whose attributes are
skipped, text with the five named entities and character references, the declaration, comments
and processing instructions, which are skipped. A document type, `CDATA`, a reference to any
other entity, an element nested deeper than `maxDepth`, an end tag that does not match, and
anything after the root are refused, so nothing in a document is expanded or fetched. Every
function is total; the size of what it reads is the HTTP client's limit.
-/

@[expose] public section

namespace Lanes.S3.Xml

inductive Node where
  | element (name : String) (children : List Node)
  | text (s : String)
  deriving Repr, Inhabited

inductive Token where
  | start (name : String)
  | stop (name : String)
  | text (s : String)
  deriving DecidableEq, Repr

def nameChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == '.' || c == ':'

def space (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- The rest after the first `stop`, if there is one. -/
def after (stop : List Char) : List Char → Option (List Char)
  | [] => none
  | c :: rest => if stop.isPrefixOf (c :: rest) then some ((c :: rest).drop stop.length)
    else after stop rest

/-- The attributes of a start tag, skipped: whether the tag closes itself, and the rest after it. -/
def skipAttributes (quote : Option Char) : List Char → Option (Bool × List Char)
  | [] => none
  | c :: rest =>
    match quote with
    | some q => if c == q then skipAttributes none rest else skipAttributes (some q) rest
    | none =>
      if c == '"' || c == '\'' then skipAttributes (some c) rest
      else if c == '>' then some (false, rest)
      else if c == '/' then match rest with
        | '>' :: rest => some (true, rest)
        | _ => none
      else if c == '<' || c == '&' then none
      else skipAttributes none rest

def hexValue? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55) else none

/-- The code point a character reference names, decimal or after `x` in hex. -/
def codePoint? : List Char → Option Nat
  | 'x' :: hex =>
    if hex.isEmpty || hex.length > 6 then none
    else hex.foldlM (fun n c => (16 * n + ·) <$> hexValue? c) 0
  | digits =>
    if digits.isEmpty || digits.length > 7 || !digits.all Char.isDigit then none
    else some (digits.foldl (fun n c => 10 * n + (c.toNat - 48)) 0)

def charRef? (digits : List Char) : Option Char :=
  (codePoint? digits).bind fun n => if n == 0 || !n.isValidChar then none else some (Char.ofNat n)

def entity? (name : List Char) : Option Char :=
  match name with
  | ['l', 't'] => some '<'
  | ['g', 't'] => some '>'
  | ['a', 'm', 'p'] => some '&'
  | ['q', 'u', 'o', 't'] => some '"'
  | ['a', 'p', 'o', 's'] => some '\''
  | '#' :: digits => charRef? digits
  | _ => none

/-- Text with its references replaced; `none` for a reference that is not one, or a `<`. -/
def unescape : (fuel : Nat) → List Char → Option (List Char)
  | 0, _ => none
  | _, [] => some []
  | fuel + 1, '&' :: rest => do
    let (name, tail) := rest.span (· != ';')
    let tail ← tail.tail?
    let c ← if name.length ≤ 10 then entity? name else none
    return c :: (← unescape fuel tail)
  | _, '<' :: _ => none
  | fuel + 1, c :: rest => (c :: ·) <$> unescape fuel rest

/-- `s` as XML text: `&`, `<`, `>`, `"` and `'` as entities. -/
def escape (s : String) : String :=
  String.join (s.toList.map fun
    | '&' => "&amp;" | '<' => "&lt;" | '>' => "&gt;" | '"' => "&quot;" | '\'' => "&apos;"
    | c => c.toString)

/-- The tokens of a document; `fuel` bounds the steps, one per token or skipped part. -/
def tokens : (fuel : Nat) → List Char → List Token → Option (List Token)
  | 0, _, _ => none
  | _, [], acc => some acc.reverse
  | fuel + 1, '<' :: '?' :: rest, acc => do tokens fuel (← after ['?', '>'] rest) acc
  | fuel + 1, '<' :: '!' :: '-' :: '-' :: rest, acc => do tokens fuel (← after ['-', '-', '>'] rest) acc
  | _, '<' :: '!' :: _, _ => none
  | fuel + 1, '<' :: '/' :: rest, acc =>
    let (name, tail) := rest.span nameChar
    match tail.dropWhile space with
    | '>' :: tail => if name.isEmpty then none else tokens fuel tail (.stop (String.ofList name) :: acc)
    | _ => none
  | fuel + 1, '<' :: rest, acc => do
    let (name, tail) := rest.span nameChar
    unless !name.isEmpty && tail.head?.any (fun c => space c || c == '>' || c == '/') do none
    let (closed, tail) ← skipAttributes none tail
    let name := String.ofList name
    tokens fuel tail ((if closed then [.stop name, .start name] else [.start name]) ++ acc)
  | fuel + 1, chars, acc => do
    let (text, tail) := chars.span (· != '<')
    let text ← unescape (text.length + 1) text
    tokens fuel tail (.text (String.ofList text) :: acc)

/-- The elements open, innermost first, each with its children so far in reverse. -/
abbrev Stack := List (String × List Node)

def push (maxDepth : Nat) (stack : Stack) : Token → Option Stack
  | .start name => if stack.length < maxDepth then some ((name, []) :: stack) else none
  | .text s => match stack with
    | (name, children) :: rest => some ((name, .text s :: children) :: rest)
    | [] => if s.all space then some [] else none
  | .stop name => match stack with
    | (open_, children) :: (parent, siblings) :: rest =>
      if open_ == name then some ((parent, .element name children.reverse :: siblings) :: rest)
      else none
    | _ => none

/-- The root element of a document, if it is one this reader understands. -/
def parse (input : String) (maxDepth : Nat := 16) : Option Node := do
  let chars := input.toList
  let ts ← tokens (chars.length + 1) chars []
  -- The root's parent is a sentinel with no name; text around the root is blanks only.
  let stack ← ts.foldlM (push (maxDepth + 1)) [("", [])]
  match stack with
  | [("", children)] =>
    match children.filter (fun | .text s => !s.all space | _ => true) with
    | [root@(.element _ _)] => some root
    | _ => none
  | _ => none

namespace Node

def name : Node → String
  | .element name _ => name
  | .text _ => ""

def children : Node → List Node
  | .element _ cs => cs
  | .text _ => []

/-- The text directly inside an element. -/
def content (n : Node) : String :=
  String.join (n.children.filterMap fun | .text s => some s | _ => none)

def all (n : Node) (name : String) : List Node := n.children.filter (·.name == name)

def child? (n : Node) (name : String) : Option Node := (n.all name).head?

def text? (n : Node) (name : String) : Option String := (n.child? name).map content

end Node

end Lanes.S3.Xml
