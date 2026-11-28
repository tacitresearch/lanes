/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Html.Basic
public import Lanes.Web.Html.Unescape

/-!
HTML from users, such as a comment or a profile, made safe to show: `sanitize` reads it as a
browser's tokenizer does, keeps the elements and attributes a `Policy` allows, and returns an
`Html` value, which `render` writes again with every text and value escaped. Text is kept, with
its character references decoded; an element the policy does not allow is left out and its
content kept, but for those whose content is code or another language (`dropped`), which go
whole. Comments, doctypes and processing instructions go.

What a browser reads from the result has only the policy's elements and attributes, and every
URL attribute holds a URL `Html.safeUrl` passes and whose scheme the policy allows
(`Html.sanitize_safe`, in `Lanes/Web/Html/SanitizeSound.lean`). Whatever a policy says, no
element of `dropped` is kept, nor an event handler (`on…`), `style` or `srcset`.

The elements are nested as the input nests them: an end tag closes the elements opened after
its own, and one with no element open is ignored. A browser may still move an element (a `p`
inside a `p`, the rows of a table), but it cannot add one.
-/

@[expose] public section

namespace Lanes.Html

namespace Sanitize

/-- Elements left out with all they hold: code, styles, frames, forms' raw text, and the foreign
content of SVG and MathML, which the HTML parser reads by other rules. -/
def dropped : List String :=
  ["script", "style", "template", "iframe", "frame", "frameset", "object", "embed", "applet",
    "noscript", "noembed", "noframes", "xmp", "plaintext", "textarea", "title", "svg", "math",
    "select", "option", "head", "base", "link", "meta"]

/-- Elements whose content the tokenizer reads as text up to their end tag. -/
def rawText : List String :=
  ["script", "style", "xmp", "iframe", "noembed", "noframes", "noscript", "textarea", "title"]

/-- Attributes that hold a URL a browser may follow or load. -/
def urlAttributes : List String := urlAttrs ++ ["cite", "poster", "background", "longdesc"]

def nameChar (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '-' || c == ':'

/-- A name kept as written: lowercase letters, digits, `-` and `:`, starting with a letter. -/
def nameOk (n : String) : Bool :=
  n.toList.all nameChar && n.toList.head?.any fun c => 'a' ≤ c && c ≤ 'z'

def forbiddenAttr (n : String) : Bool := n.startsWith "on" || n == "style" || n == "srcset"

def isUrlAttr (n : String) : Bool := urlAttributes.contains n.toLower

/-- The scheme of a URL as `safeUrl` finds it, in lowercase; `none` for a relative URL. -/
def scheme? (url : String) : Option String :=
  let visible := url.toList.filter (!urlBlank ·)
  let s := visible.takeWhile fun c => c != ':' && c != '/' && c != '?' && c != '#'
  if (visible.drop s.length).head? == some ':' then some (String.ofList (s.map Char.toLower)) else none

end Sanitize

structure Policy where
  /-- The elements kept, each with the attributes it may keep. -/
  tags : List (String × List String)
  /-- Attributes any kept element may keep. -/
  globalAttrs : List String := ["title", "lang", "dir"]
  /-- The schemes a URL attribute may have; a relative URL is always kept. `safeUrl` allows only
  some (`allowedSchemes`), so another is never kept. -/
  schemes : List String := ["http", "https", "mailto"]
  /-- Elements nested deeper are left out, their content kept. -/
  maxDepth : Nat := 64

namespace Policy

open Sanitize

def keepsTag (p : Policy) (tag : String) : Bool :=
  nameOk tag && !dropped.contains tag && p.tags.any (·.1 == tag)

def urlOk (p : Policy) (url : String) : Bool :=
  safeUrl url == url && (scheme? url).all p.schemes.contains

def keepsAttr (p : Policy) (tag : String) (a : Attr) : Bool :=
  nameOk a.name && !forbiddenAttr a.name
    && (p.globalAttrs.contains a.name || p.tags.any fun (t, as) => t == tag && as.contains a.name)
    && (!isUrlAttr a.name || a.value.any p.urlOk)

/-- Formatting, links, lists, quotes, code, headings, tables and images: what a comment or a
post written in Markdown becomes. -/
def basic : Policy where
  tags :=
    [("a", ["href"]), ("abbr", []), ("b", []), ("blockquote", ["cite"]), ("br", []), ("code", []),
      ("dd", []), ("del", []), ("div", []), ("dl", []), ("dt", []), ("em", []), ("h1", []),
      ("h2", []), ("h3", []), ("h4", []), ("h5", []), ("h6", []), ("hr", []), ("i", []),
      ("img", ["src", "alt", "width", "height"]), ("ins", []), ("kbd", []), ("li", []),
      ("mark", []), ("ol", ["start"]), ("p", []), ("pre", []), ("q", ["cite"]), ("s", []),
      ("small", []), ("span", []), ("strong", []), ("sub", []), ("sup", []), ("table", []),
      ("tbody", []), ("td", ["colspan", "rowspan"]), ("tfoot", []), ("th", ["colspan", "rowspan"]),
      ("thead", []), ("tr", []), ("u", []), ("ul", [])]

/-- Text with no markup: every element is left out, its text kept. -/
def textOnly : Policy where
  tags := []
  globalAttrs := []

end Policy

/-! ### Reading -/

namespace Sanitize

inductive Piece where
  | text (s : String)
  | start (tag : String) (attrs : List Attr)
  | finish (tag : String)
  deriving Repr

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'

def isAlpha (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

def lowerAscii (c : Char) : Char := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

def lowerName (cs : List Char) : String := String.ofList (cs.map lowerAscii)

/-- What a value or a name runs to, and the rest. -/
def span (stop : Char → Bool) (cs : List Char) : List Char × List Char :=
  (cs.takeWhile (!stop ·), cs.dropWhile (!stop ·))

/-- An attribute's value after `=` and blanks, and the rest; `none` at the end of the text. -/
def value (cs : List Char) : Option (String × List Char) :=
  match cs with
  | '"' :: rest =>
    let (v, r) := span (· == '"') rest
    if r.isEmpty then none else some (unescape (String.ofList v) true, r.drop 1)
  | '\'' :: rest =>
    let (v, r) := span (· == '\'') rest
    if r.isEmpty then none else some (unescape (String.ofList v) true, r.drop 1)
  | _ =>
    let (v, r) := span (fun c => isWs c || c == '>') cs
    some (unescape (String.ofList v) true, r)

/-- The attributes of a start tag up to its `>`, the first of two of one name kept, and the rest;
`none` at the end of the text, where a browser drops the tag. Each round reads a character. -/
def attrs : Nat → List Char → List Attr → Option (List Attr × List Char)
  | 0, _, _ => none
  | fuel + 1, cs, acc =>
    match cs.dropWhile fun c => isWs c || c == '/' with
    | [] => none
    | '>' :: rest => some (acc.reverse, rest)
    | c :: rest =>
      let (n, r) := span (fun c => isWs c || c == '/' || c == '>' || c == '=') rest
      let name := lowerName (c :: n)
      let add (a : Attr) := if acc.any (·.name == name) then acc else a :: acc
      match r.dropWhile isWs with
      | '=' :: r' =>
        match value (r'.dropWhile isWs) with
        | some (v, r'') => attrs fuel r'' (add ⟨name, some v⟩)
        | none => none
      | r' => attrs fuel r' (add ⟨name, none⟩)

/-- The text up to the end tag `</tag` of an element of raw text, and what follows it. -/
def rawUntil (tag : String) : List Char → List Char → List Char × List Char
  | [], acc => (acc.reverse, [])
  | '<' :: '/' :: rest, acc =>
    let n := tag.length
    let name := rest.take n
    let after := rest.drop n
    if lowerName name == tag && (after.head?.all fun c => isWs c || c == '/' || c == '>') then
      (acc.reverse, '<' :: '/' :: rest)
    else rawUntil tag ('/' :: rest) ('<' :: acc)
  | c :: rest, acc => rawUntil tag rest (c :: acc)

/-- What follows the first `-->`, or nothing. -/
def afterComment : List Char → List Char
  | '-' :: '-' :: '>' :: rest => rest
  | _ :: rest => afterComment rest
  | [] => []

def tagName (cs : List Char) : String × List Char :=
  let (n, r) := span (fun c => isWs c || c == '/' || c == '>') cs
  (lowerName n, r)

/-- The pieces of a text, newest first. Each round reads at least a character. -/
def pieces : Nat → List Char → List Piece → List Piece
  | 0, _, acc => acc
  | _, [], acc => acc
  | fuel + 1, cs, acc =>
    match cs with
    | '<' :: '!' :: '-' :: '-' :: rest =>
      let rest := match rest with
        | '>' :: r => r
        | '-' :: '>' :: r => r
        | _ => afterComment rest
      pieces fuel rest acc
    | '<' :: '/' :: c :: rest =>
      if isAlpha c then
        let (name, r) := tagName (c :: rest)
        pieces fuel ((r.dropWhile (· != '>')).drop 1) (.finish name :: acc)
      else if c == '>' then pieces fuel rest acc
      else pieces fuel ((rest.dropWhile (· != '>')).drop 1) acc
    | '<' :: '!' :: rest | '<' :: '?' :: rest => pieces fuel ((rest.dropWhile (· != '>')).drop 1) acc
    | '<' :: c :: rest =>
      if isAlpha c then
        let (name, r) := tagName (c :: rest)
        match attrs (r.length + 1) r [] with
        | none => acc
        | some (as, r') =>
          let acc := .start name as :: acc
          if name == "plaintext" then .text (String.ofList r') :: acc
          else if rawText.contains name then
            let (body, r'') := rawUntil name r' []
            pieces fuel r'' (.text (String.ofList body) :: acc)
          else pieces fuel r' acc
      else pieces fuel (c :: rest) (.text "<" :: acc)
    | ['<'] => .text "<" :: acc
    | _ =>
      let (t, r) := span (· == '<') cs
      pieces fuel r (.text (unescape (String.ofList t)) :: acc)

/-! ### Building -/

structure Open where
  tag : String
  attrs : List Attr
  /-- Newest first. -/
  children : List Html

structure Builder where
  /-- Innermost first. -/
  stack : List Open := []
  /-- Newest first. -/
  top : List Html := []
  /-- An element of `dropped` being skipped, and how many of its name are open. -/
  skip : Option (String × Nat) := none

def Builder.add (b : Builder) (h : Html) : Builder :=
  match b.stack with
  | o :: rest => { b with stack := { o with children := h :: o.children } :: rest }
  | [] => { b with top := h :: b.top }

def Builder.closeOne (b : Builder) : Builder :=
  match b.stack with
  | o :: rest => ({ b with stack := rest } : Builder).add (.element o.tag o.attrs o.children.reverse)
  | [] => b

def Builder.closeTo (b : Builder) : Nat → Builder
  | 0 => b
  | n + 1 => (b.closeOne).closeTo n

def Builder.piece (p : Policy) (b : Builder) : Piece → Builder
  | .text s =>
    if b.skip.isSome then b else b.add (.text s)
  | .start tag as =>
    match b.skip with
    | some (name, n) => if tag == name then { b with skip := some (name, n + 1) } else b
    | none =>
      if dropped.contains tag then
        if voidTags.contains tag then b else { b with skip := some (tag, 1) }
      else if p.keepsTag tag && b.stack.length < p.maxDepth then
        if voidTags.contains tag then b.add (.element tag as [])
        else { b with stack := ⟨tag, as, []⟩ :: b.stack }
      else b
  | .finish tag =>
    match b.skip with
    | some (name, n) =>
      if tag == name then { b with skip := if n ≤ 1 then none else some (name, n - 1) } else b
    | none =>
      match b.stack.findIdx? (·.tag == tag) with
      | some i => b.closeTo (i + 1)
      | none => b

/-- Only what the policy allows, whatever the tree holds. -/
def prune (p : Policy) : Html → Html
  | .text s => .text s
  | .element tag as children =>
    if p.keepsTag tag then .element tag (as.filter (p.keepsAttr tag)) (pruneAll p children)
    else .fragment (pruneAll p children)
  | .fragment children => .fragment (pruneAll p children)
where
  pruneAll (p : Policy) : List Html → List Html
    | [] => []
    | h :: hs => prune p h :: pruneAll p hs

end Sanitize

open Sanitize in
/-- `html`, written by a user, as the elements and attributes of `p`. -/
def sanitize (p : Policy) (html : String) : Html :=
  let ps := (pieces (html.length + 1) html.toList []).reverse
  let b := ps.foldl (Builder.piece p) {}
  let b := b.closeTo b.stack.length
  prune p (.fragment b.top.reverse)

end Lanes.Html
