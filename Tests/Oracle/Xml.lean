/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic
import Lanes.Services.S3

/-! `Lanes.S3.Xml.parse` against Go's `encoding/xml`: what each accepts, and the tree. -/

namespace Tests.Oracle.Xml

open Lanes Lanes.S3

/-- An element's content with adjacent texts joined, as `oracles/go/xml` writes it. -/
def joined : List Json → List Json
  | .str a :: .str b :: rest => joined (.str (a ++ b) :: rest)
  | j :: rest => j :: joined rest
  | [] => []
termination_by l => l.length

def canonical : Xml.Node → Json
  | .text s => .str s
  | .element name children =>
    Json.mkObj [("name", (name : Json)),
      ("content", .arr (joined (children.attach.map fun ⟨c, _⟩ => canonical c)).toArray)]
termination_by n => n
decreasing_by
  simp only [Xml.Node.element.sizeOf_spec]
  have := List.sizeOf_lt_of_mem ‹_›
  omega

def answerWith (maxDepth : Nat) (input : ByteArray) : Answer :=
  (String.fromUTF8? input).bind (Xml.parse · maxDepth) |>.map canonical

def answer (c : Case) : Answer := answerWith 16 c.input

/-! ## Cases -/

/-- What S3 writes, and, one time in twenty, what it does not. -/
def mostly (good bad : List String) : Gen String := do
  if ← Gen.chance 5 then Gen.pick bad else Gen.pick good

def names : Gen String :=
  mostly ["a", "B", "ListBucketResult", "Key", "s3:Key", "a.b", "_c", "x-y", "Contents"]
    ["é", "1a", "-a", "a::b"]

def texts : Gen String :=
  mostly ["x", " ", "photos%2F2006%2Fa+b.jpg", "&quot;fba9dede&quot;", "&lt;&#65;&#x42;&amp;&apos;&gt;",
      "a\r\nb", "\r", "é ሴ 😀", "\t\n", "&#x10FFFF;", "&#x0000041;", ">", "2009-10-12T17:50:30.000Z"]
    ["&#0;", "&#1;", "&#xD800;", "&#xFFFE;", "&e;", "&#65", "a]]>b", "\x01", "\uFFFE", "&amp"]

def attributes : Gen String :=
  mostly ["", "", "", " xmlns=\"http://s3.amazonaws.com/doc/2006-03-01/\"", " a='1'", " a=\"x>y\"",
      " a=\"&amp;\"", " a='1' b=\"2\"", " xmlns:s3=\"http://s3.amazonaws.com/doc/2006-03-01/\""]
    [" a", " a=1", " a=\"<\"", " a=\"&e;\"", " a='1'b='2'"]

def misc : Gen String :=
  mostly ["<!-- a comment -->", "<?p x?>"] ["<![CDATA[<x>&]]>", "<!-- a -- b -->", "<??>", "<!--->"]

def element : Nat → Gen String
  | 0 => do return s!"<{← names}/>"
  | fuel + 1 => do
    let name ← names
    let attrs ← attributes
    if ← Gen.chance 15 then return s!"<{name}{attrs}/>"
    let items ← Gen.list (← Gen.below 4) do
      match ← Gen.below 6 with
      | 0 | 1 => texts
      | 2 => misc
      | _ => element fuel
    let close ← if ← Gen.chance 2 then names else pure name
    return s!"<{name}{attrs}>{String.join items}</{close}{← Gen.pick ["", "", " "]}>"

def prologs : Gen String :=
  mostly ["", "", "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n", "<!-- before -->\n", "\n  "]
    ["<?xml version=\"1.1\"?>", "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>",
      "<!DOCTYPE a [<!ENTITY e \"x\">]>", "x", "\uFEFF"]

def deep (n : Nat) : String :=
  String.join (List.replicate n "<a>") ++ "x" ++ String.join (List.replicate n "</a>")

def alphabet : List Char := "<>/?!-&;#x\"'= \t\r\naAbB:._01é[]".toList

def case : Gen Case := do
  let s ← match ← Gen.below 10 with
    | 0 => Gen.text alphabet 16
    | 1 => do pure (deep (14 + (← Gen.below 6)))
    | 2 | 3 => do Gen.mutate alphabet ((← prologs) ++ (← element 3))
    | _ => do pure ((← prologs) ++ (← element 3) ++ (← Gen.pick ["", "\n", " ", "<!-- after -->", "<a/>"]))
  if ← Gen.chance 2 then
    return ⟨"parse", ⟨s.toUTF8.data.push ((← Gen.pick [0x80, 0xff, 0xc3]) : Nat).toUInt8⟩⟩
  return text s "parse"

def edges : List Case :=
  ["", " ", "<a/>", "<a></a>", "<a>x</a>", "<a><b/>x<c>y</c>z</a>", "<a>&lt;&#65;&#x42;&amp;</a>",
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<a/>\n", "<a>x<!-- c -->y</a>", "<a/><b/>", "x<a/>",
    "<a></b>", "<a>", "<a>\r\n</a>", "<a>&#13;</a>", "<a><![CDATA[x]]></a>",
    "<!DOCTYPE a><a/>", "<a b>x</a>", "<s3:Key>k</s3:Key>", deep 16, deep 17,
    "<ListBucketResult xmlns=\"http://s3.amazonaws.com/doc/2006-03-01/\"><Name>b</Name></ListBucketResult>"].map
    (text · "parse")

/-! ## Where ours departs from Go -/

/-- `<!` that starts neither a comment nor CDATA: a document type, or another declaration. -/
def declarationAt : List Char → Bool
  | '<' :: '!' :: rest => !("--".toList.isPrefixOf rest) && !("[CDATA[".toList.isPrefixOf rest)
  | _ => false

/-- The text without its declarations, each to its `>` outside quotes and nested `<…>`. -/
def withoutDeclarations : (fuel : Nat) → List Char → List Char
  | 0, cs => cs
  | fuel + 1, cs@(c :: rest) =>
    if declarationAt cs then
      -- As Go reads one: the character after `<!` is taken as it is, then nested `<…>` and
      -- quotes are skipped to a `>` at depth 0.
      let rec skip : Nat → Nat → Option Char → List Char → List Char
        | 0, _, _, cs => cs
        | _, _, _, [] => []
        | n + 1, depth, some q, c :: rest => skip n depth (if c == q then none else some q) rest
        | n + 1, depth, none, c :: rest =>
          if c == '"' || c == '\'' then skip n depth (some c) rest
          else if c == '<' then skip n (depth + 1) none rest
          else if c == '>' then (if depth == 0 then rest else skip n (depth - 1) none rest)
          else skip n depth none rest
      withoutDeclarations fuel (skip cs.length 0 none (cs.drop 3))
    else c :: withoutDeclarations fuel rest
  | _, [] => []

/-- The text with each CDATA section written as text, escaped. -/
def withoutCdata : (fuel : Nat) → List Char → List Char
  | 0, cs => cs
  | fuel + 1, cs@(c :: rest) =>
    if "<![CDATA[".toList.isPrefixOf cs then
      let body := cs.drop 9
      match Xml.after "]]>".toList body with
      | some tail =>
        let inner := body.take (body.length - tail.length - 3)
        (Xml.escape (String.ofList inner)).toList ++ withoutCdata fuel tail
      | none => cs
    else c :: withoutCdata fuel rest
  | _, [] => []

/-- The text with each character reference to a surrogate written `&#xFFFD;`. -/
def surrogatesReplaced (cs : List Char) : List Char :=
  go cs.length cs
where
  go : Nat → List Char → List Char
    | 0, cs => cs
    | fuel + 1, '&' :: '#' :: rest =>
      let (digits, tail) := rest.span (· != ';')
      match Xml.codePoint? digits, tail with
      | some n, ';' :: tail =>
        if 0xD800 ≤ n && n < 0xE000 then "&#xFFFD;".toList ++ go fuel tail
        else '&' :: '#' :: digits ++ ';' :: go fuel tail
      | _, _ => '&' :: '#' :: go fuel rest
    | fuel + 1, c :: rest => c :: go fuel rest
    | _, [] => []

/-- The text as Go reads it, written as ours reads it: without declarations, CDATA as text, a
reference to a surrogate as one to U+FFFD. -/
def asGoReads (cs : List Char) : List Char :=
  surrogatesReplaced (withoutCdata cs.length (withoutDeclarations cs.length cs))

/-- Ours, without its limit on depth, on the text as Go reads it, if that is not the text. -/
def oursAsGoReads (c : Case) : Option Answer :=
  (String.fromUTF8? c.input).bind fun s =>
    let t := String.ofList (asGoReads s.toList)
    if t == s then none else some (answerWith 10000 t.toUTF8)

/-- Go reads a document type and CDATA. Ours refuses both, so that nothing in a document is
expanded and every text is read one way. Without them, written as text, ours answers as Go. -/
def declarations (c : Case) (go : Answer) : Bool :=
  (answer c).isNone && go.isSome && (String.fromUTF8? c.input).any (fun s =>
    let cs := s.toList
    withoutCdata cs.length (withoutDeclarations cs.length cs) != cs) && oursAsGoReads c == some go

/-- Go reads a reference to a surrogate, which XML 1.0's `Char` does not hold, as U+FFFD; ours
refuses it. With U+FFFD written instead, ours answers as Go. -/
def surrogate (c : Case) (go : Answer) : Bool :=
  (answer c).isNone && go.isSome &&
    (String.fromUTF8? c.input).any (fun s => surrogatesReplaced s.toList != s.toList)
    && oursAsGoReads c == some go

/-- Ours refuses an element nested deeper than `maxDepth`, 16; Go has no limit. -/
def deeper (c : Case) (go : Answer) : Bool :=
  (answer c).isNone && answerWith 10000 c.input == go

def space (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r' || c == '\n'

def nameStart (c : Char) : Bool := c.isAlpha || c == '_' || c == ':' || c.toNat > 127

/-- A reference in an attribute's value: one of the five, or a character's. -/
def reference (name : List Char) : Bool :=
  (Xml.entity? name).isSome && (name.length ≤ 10)

/-- XML 1.0's attributes of a start tag, up to its `>` or `/>`: `true` when well formed. -/
def attributesOk : (fuel : Nat) → List Char → Bool
  | 0, _ => false
  | fuel + 1, cs =>
    let rest := cs.dropWhile space
    match rest with
    | '>' :: _ | '/' :: '>' :: _ => true
    | c :: _ =>
      cs.head?.any space && nameStart c &&
        let (name, afterName) := rest.span Xml.nameChar
        -- Go reads an attribute's name as a QName too: one colon at most.
        name.count ':' ≤ 1 &&
        match afterName.dropWhile space with
        | '=' :: v =>
          match v.dropWhile space with
          | q :: body =>
            if q != '"' && q != '\'' then false
            else
              let (value, tail) := body.span (· != q)
              let refsOk := (value.splitOn '&').drop 1 |>.all fun piece =>
                let (name, semi) := piece.span (· != ';')
                !semi.isEmpty && reference name
              !value.contains '<' && refsOk && !tail.isEmpty && attributesOk fuel (tail.drop 1)
          | [] => false
        | _ => false
    | [] => false

/-- Whether some start tag's attributes are not as XML 1.0 writes them. -/
def badAttributes : List Char → Bool
  | '<' :: c :: rest =>
    if nameStart c then
      let (_, afterName) := rest.span Xml.nameChar
      !attributesOk afterName.length afterName || badAttributes rest
    else badAttributes (c :: rest)
  | _ :: rest => badAttributes rest
  | [] => false

/-- Ours skips a start tag's attributes, which S3 writes only as namespaces, without reading
them; Go refuses one that is not well formed. -/
def skipsAttributes (c : Case) (go : Answer) : Bool :=
  (answer c).isSome && go.isNone && (String.fromUTF8? c.input).any (badAttributes ·.toList)

/-- What follows each `<` or `</`, to a blank, `>` or `/`. -/
def tagNames : List Char → List (List Char)
  | '<' :: rest =>
    ((rest.dropWhile (· == '/')).takeWhile fun c => !space c && c != '>' && c != '/')
      :: tagNames rest
  | _ :: rest => tagNames rest
  | [] => []

/-- Ours reads names of ASCII letters, digits and `-_.:`, which S3's are; Go reads names in
any script. -/
def nonAsciiName (c : Case) (go : Answer) : Bool :=
  (answer c).isNone && go.isSome && (String.fromUTF8? c.input).any fun s =>
    (tagNames s.toList).any (·.any (·.toNat > 127))

/-- Go checks the declaration's version and encoding; ours skips it, and reads UTF-8. -/
def declaration (c : Case) (go : Answer) : Bool :=
  (answer c).isSome && go.isNone && (String.fromUTF8? c.input).any fun s =>
    (s.splitOn "<?xml").length > 1

/-- Go reads a name as XML Namespaces' QName, with one colon at most; ours as XML 1.0's names,
and keeps it whole. -/
def colons (c : Case) (go : Answer) : Bool :=
  (answer c).isSome && go.isNone && (String.fromUTF8? c.input).any fun s =>
    (tagNames s.toList).any fun n => n.count ':' > 1

def package : Package where
  name := "xml"
  edges := edges
  case := case
  answer := answer
  known c go :=
    if declarations c go then some "Go reads a document type and CDATA; ours refuses both"
    else if deeper c go then some "nested deeper than ours reads (16)"
    else if skipsAttributes c go then some "ours skips attributes without reading them"
    else if nonAsciiName c go then some "Go reads names in any script; ours reads ASCII names"
    else if declaration c go then some "Go checks the XML declaration; ours skips it"
    else if colons c go then some "Go reads a name with one colon at most; ours with any"
    else if surrogate c go then some "Go reads a reference to a surrogate as U+FFFD; ours refuses it"
    else none

end Tests.Oracle.Xml
