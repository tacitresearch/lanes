/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# HTML as a value

`Html` is an inductive type, so a view is a pure function into data: it can be tested, compared
and reasoned about. Text can only enter a page through `Html.text`, which is escaped when the
page is rendered. `String` and `Html` are different types, so unescaped text cannot be spliced
into markup by accident.
-/

@[expose] public section

namespace Lanes

/-- A value of `none` renders as a bare name, such as `disabled`. -/
structure Html.Attr where
  name : String
  value : Option String := none
  deriving DecidableEq, Repr, Hashable

inductive Html where
  /-- It is escaped when rendered. -/
  | text (s : String)
  | element (tag : String) (attrs : List Html.Attr) (children : List Html)
  | fragment (children : List Html)
  deriving Repr

namespace Html

def empty : Html := .fragment []

instance : Inhabited Html := ⟨empty⟩

def escapeChar : Char → List Char
  | '&' => ['&', 'a', 'm', 'p', ';']
  | '<' => ['&', 'l', 't', ';']
  | '>' => ['&', 'g', 't', ';']
  | '"' => ['&', 'q', 'u', 'o', 't', ';']
  | '\'' => ['&', '#', '3', '9', ';']
  | c => [c]

/-- Escape text for use as HTML text or inside a quoted attribute value. This is the only way
text enters rendered markup. -/
def escape (s : String) : String :=
  String.ofList (s.toList.flatMap escapeChar)

theorem escapeChar_safe {c d : Char} (h : d ∈ escapeChar c) :
    d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"' ∧ d ≠ '\'' := by
  unfold escapeChar at h
  split at h
  all_goals try (simp only [List.mem_cons, List.not_mem_nil, or_false] at h;
                 rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  all_goals try (simp only [List.mem_cons, List.not_mem_nil, or_false] at h;
                 rcases h with rfl | rfl | rfl | rfl | rfl <;> decide)
  all_goals try (simp only [List.mem_cons, List.not_mem_nil, or_false] at h;
                 rcases h with rfl | rfl | rfl | rfl <;> decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  subst h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro heq; subst heq; simp_all)

/--
Escaped text contains none of `<`, `>`, `"` and `'`. Whatever the input, it stays text: it
cannot become markup and cannot break out of an attribute value.
-/
theorem escape_safe (s : String) {d : Char} (h : d ∈ (escape s).toList) :
    d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"' ∧ d ≠ '\'' := by
  simp only [escape, String.toList_ofList, List.mem_flatMap] at h
  obtain ⟨c, _, hc⟩ := h
  exact escapeChar_safe hc

/-- Keep only the characters allowed in a tag or attribute name. Names come from templates, but
a name built at run time must not be able to inject markup either. -/
def safeName (name : String) : String :=
  String.ofList (name.toList.filter fun c => c.isAlphanum || c == '-' || c == '_' || c == ':')

def voidTags : List String :=
  ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track",
   "wbr"]

def urlAttrs : List String :=
  ["href", "src", "action", "formaction", "xlink:href"]

def blockedUrl : String := "about:invalid#blocked"

/--
A URL that is safe to put in a URL attribute: `url` itself if it is relative or its scheme is
`http`, `https`, `mailto` or `tel`, and `blockedUrl` otherwise. This keeps `javascript:` and
`data:` URLs built from user data out of links and forms. Browsers ignore spaces and control
characters in a scheme, so they are ignored here too.
-/
def safeUrl (url : String) : String :=
  let visible := url.toList.filter fun c => c.val > 0x20
  let scheme := visible.takeWhile fun c => c != ':' && c != '/' && c != '?' && c != '#'
  if (visible.drop scheme.length).head? == some ':' then
    if ["http", "https", "mailto", "tel"].contains (String.ofList (scheme.map Char.toLower)) then url
    else blockedUrl
  else url

def Attr.render (a : Attr) : String :=
  let name := safeName a.name
  match a.value with
  | some v => s!" {name}=\"{escape (if urlAttrs.contains name.toLower then safeUrl v else v)}\""
  | none => s!" {name}"

mutual

def render : Html → String
  | .text s => escape s
  | .element tag attrs children =>
    let tag := safeName tag
    let attrs := String.join (attrs.map Attr.render)
    if voidTags.contains tag then s!"<{tag}{attrs}>"
    else s!"<{tag}{attrs}>{renderAll children}</{tag}>"
  | .fragment children => renderAll children

def renderAll : List Html → String
  | [] => ""
  | node :: nodes => render node ++ renderAll nodes

end

def document (page : Html) : String :=
  "<!DOCTYPE html>" ++ page.render

end Html

/-- What may be written as `{value}` in a template's children. -/
class ToHtml (α : Type) where
  toHtml : α → Html

instance : ToHtml Html := ⟨id⟩
instance : ToHtml String := ⟨.text⟩
instance : ToHtml Nat := ⟨fun n => .text (toString n)⟩
instance : ToHtml Int := ⟨fun n => .text (toString n)⟩
instance {α : Type} [ToHtml α] : ToHtml (List α) := ⟨fun l => .fragment (l.map ToHtml.toHtml)⟩
instance {α : Type} [ToHtml α] : ToHtml (Array α) := ⟨fun l => .fragment (l.toList.map ToHtml.toHtml)⟩
instance {α : Type} [ToHtml α] : ToHtml (Option α) where
  toHtml
    | some a => ToHtml.toHtml a
    | none => .empty

/-- What may be written as `name={value}` in a template's attributes. -/
class ToAttr (α : Type) where
  /-- The attributes for a name and a value: usually one, none for a `false` flag. -/
  toAttr : String → α → List Html.Attr

instance : ToAttr String := ⟨fun name v => [⟨name, some v⟩]⟩
instance : ToAttr Nat := ⟨fun name v => [⟨name, some (toString v)⟩]⟩
instance : ToAttr Int := ⟨fun name v => [⟨name, some (toString v)⟩]⟩
instance : ToAttr Bool := ⟨fun name v => if v then [⟨name, none⟩] else []⟩
instance {α : Type} [ToAttr α] : ToAttr (Option α) where
  toAttr name
    | some v => ToAttr.toAttr name v
    | none => []

end Lanes
