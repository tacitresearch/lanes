/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic
import Lanes.Web.Html.Sanitize

/-!
`Html.unescape` against the WHATWG standard's examples and Go's `html.UnescapeString`;
`Html.sanitize` against attacks written by hand.
-/

namespace Tests.Oracle.Html

open Lanes Lanes.Html

def basic (s : String) : String := (sanitize Policy.basic s).render

def unescapeTests : List (String × Bool) :=
  [ ("html: named references, the longest first, old names without ;",
      unescape "&amp;&lt;&gt;&quot;&apos;&nbsp;&Aacute;&CounterClockwiseContourIntegral;"
          == "&<>\"' Á∳"
        && unescape "&notit; &notin; &amp &ampx &AMP" == "¬it; ∉ & &x &"
        && unescape "&NotEqualTilde;" == "≂̸" && unescape "&nosuch; &; & &#" == "&nosuch; &; & &#"),
    ("html: numeric references, in decimal and hexadecimal, with or without ;",
      unescape "&#65;&#x42;&#X43&#0068;&#x1F600;" == "ABCD😀"
        && unescape "&#0;&#xD800;&#x110000;&#99999999999999;" == "����"
        && unescape "&#128;&#x9F;&#x81;" == "€Ÿ\u0081" && unescape "&#x;&#;&#xg" == "&#x;&#;&#xg"),
    ("html: in an attribute, an old name without ; before = or a letter is kept",
      unescape "?a=1&copy=2&amp;b&lt" true == "?a=1&copy=2&b<"
        && unescape "&ampx &amp=" true == "&ampx &amp=" && unescape "&amp;x" true == "&x") ]

def sanitizeTests : List (String × Bool) :=
  [ ("sanitize: scripts, handlers and styles go, text stays",
      basic "<p onclick=\"x()\">Hi <b>there</b><script>alert(1)</script></p>" == "<p>Hi <b>there</b></p>"
        && basic "<img src=x onerror=alert(1)>" == "<img src=\"x\">"
        && basic "<style>p{}</style><div style=\"x\">t</div>" == "<div>t</div>"
        && basic "<SCRIPT SRC=//x.example/a.js></SCRIPT>ok" == "ok"),
    ("sanitize: URLs of other schemes go, however they are spelled",
      ["javascript:alert(1)", " JaVa&#x09;script:alert(1)", "&#106;avascript:x", "java\nscript:x",
        "data:text/html,x", "vbscript:x", "JAVASCRIPT&colon;x"].all fun u =>
          basic s!"<a href=\"{u}\">x</a>" == "<a>x</a>"),
    ("sanitize: relative URLs and the policy's schemes stay",
      basic "<a href=\"/a?b=1&amp;c=2\">x</a>" == "<a href=\"/a?b=1&amp;c=2\">x</a>"
        && basic "<a href='https://example.com/'>x</a>" == "<a href=\"https://example.com/\">x</a>"
        && basic "<a href=\"tel:1\">x</a>" == "<a>x</a>"
        && (sanitize { Policy.basic with schemes := ["tel"] } "<a href=\"tel:1\">x</a>").render
          == "<a href=\"tel:1\">x</a>"),
    ("sanitize: foreign content and frames go whole",
      basic "<svg><g/onload=alert(2)//<p>x</svg>after" == "after"
        && basic "<math><mi xlink:href=\"javascript:x\">m</mi></math>a" == "a"
        && basic "<iframe src=\"javascript:x\"><b>in</b></iframe>b" == "b"
        && basic "<noscript><p title=\"</noscript><img src=x onerror=alert(1)>\"></noscript>c"
          == "<img src=\"x\">&quot;&gt;c"),
    ("sanitize: elements not allowed are left out, their text kept",
      basic "<unknown x=1>keep</unknown> <font color=red>f</font>" == "keep f"
        && (sanitize Policy.textOnly "<b>bold</b> &amp; <i>it</i>").render == "bold &amp; it"),
    ("sanitize: comments and doctypes go; text is escaped again",
      basic "<!-- <script>x</script> --><!DOCTYPE html>a < b &lt; c" == "a &lt; b &lt; c"
        && basic "<!--><b>x</b>" == "<b>x</b>" && basic "<b>x</b><!-- unclosed" == "<b>x</b>"),
    ("sanitize: end tags close what they open, unclosed elements are closed",
      basic "<b><i>x</b>y</i>" == "<b><i>x</i></b>y" && basic "<div><span>open" == "<div><span>open</span></div>"
        && basic "</p>stray" == "stray"),
    ("sanitize: attribute values keep their text, escaped",
      basic "<p title='a\"b' lang=en>q</p>" == "<p title=\"a&quot;b\" lang=\"en\">q</p>"
        && basic "<p title=\"x\" title=\"y\">q</p>" == "<p title=\"x\">q</p>"
        && basic "<p title=\"&lt;script&gt;\">q</p>" == "<p title=\"&lt;script&gt;\">q</p>"),
    ("sanitize: a tag cut off at the end goes",
      basic "a<b title=\"x" == "a" && basic "a<b" == "a"),
    ("sanitize: elements nested past the policy's depth are left out, their text kept",
      (sanitize { Policy.basic with maxDepth := 2 } "<div><div><div>x</div></div></div>").render
        == "<div><div>x</div></div>") ]

def alphabet : List Char := "<>/=\"' ab&#;x!-".toList

def fragments : List String :=
  ["<p>", "</p>", "<b>", "</b>", "<a href=\"", "javascript:", "https://e.com/", "\">", "<script>",
    "</script>", "<!--", "-->", "&amp;", "&lt;", "<img src=x onerror=", "<svg>", "</svg>", " title=",
    "<style>", "</style>", "<textarea>", "</textarea>", "<div", ">"]

def htmlGen : Gen String := do
  let parts ← Gen.list (← Gen.below 10) do
    if ← Gen.chance 60 then Gen.pick fragments else Gen.text alphabet 4
  return String.join parts

/-- What `sanitize` writes, sanitized again, is written the same: the reader reads the writer's
output as the tree it wrote. -/
def stableTests : List (String × Bool) :=
  let inputs := Gen.run 7 (Gen.list 2000 htmlGen)
  [("sanitize: what sanitize writes sanitizes to itself, on generated inputs",
    inputs.all fun s => basic (basic s) == basic s)]

def tests : List (String × Bool) := unescapeTests ++ sanitizeTests ++ stableTests

def answer (c : Case) : Answer :=
  match c.op, String.fromUTF8? c.input with
  | "unescape", some s => some (.str (unescape s))
  | _, _ => none

/-- A decimal reference of one digit without `;`, such as `&#8x`. -/
def oneDigit : List Char → Bool
  | '&' :: '#' :: d :: rest =>
    (d.isDigit && (rest.head?.all fun c => !c.isDigit && c != ';')) || oneDigit (d :: rest)
  | _ :: rest => oneDigit rest
  | [] => false

/-- Go reads `&#x;` and `&#X;`, which have no digit, as U+FFFD, keeps a decimal reference of
one digit without `;` as written, and leaves `&nLt;` and `&nGt;` out of its table (their
characters are longer than their names, which its decoder in place cannot hold); the standard
and browsers do none of these. -/
def known (c : Case) (_ : Answer) : Option String :=
  match String.fromUTF8? c.input with
  | some s =>
    if (s.splitOn "&#x;").length > 1 || (s.splitOn "&#X;").length > 1 then
      some "Go reads &#x; with no digit as U+FFFD"
    else if oneDigit s.toList then some "Go keeps a decimal reference of one digit without ;"
    else if (s.splitOn "&nLt;").length > 1 || (s.splitOn "&nGt;").length > 1 then
      some "Go's table leaves out nLt; and nGt;"
    else none
  | none => none

def refAlphabet : List Char := "&#;xX0123456789aAbfFgnotilmpq ".toList

def case : Gen Case := do
  let parts ← Gen.list (← Gen.below 6) do
    match ← Gen.below 6 with
    | 0 => Gen.pick ["&amp", "&lt;", "&notin", "&noti", "&Aacute", "&CounterClockwiseContourIntegral;",
        "&NotEqualTilde;", "&nbsp", "&#x", "&#", "&#X1F600;", "&#128;", "&#xD800;", "&#0;"]
    | _ => Gen.text refAlphabet 5
  return text (String.join parts) "unescape"

/-- Every name of the table, followed by a letter. -/
def tableEdges : List Case :=
  (entityTable.splitOn "\n").map fun line => text ("&" ++ (line.splitOn " ").headD "" ++ "z") "unescape"

def package : Package where
  name := "html"
  edges := ["&amp;", "&amp", "&notit;", "&#x;", "&#;", "&#65", "&#x110000;", "&#99999999999;", "&#128;",
    "&CounterClockwiseContourIntegral;", "&ampx", "&&amp;"].map (text · "unescape") ++ tableEdges
  case
  answer
  known
  recorded := 3000

end Tests.Oracle.Html
