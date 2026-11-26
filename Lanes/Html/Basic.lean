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

## Main definitions

- `Html`: text, elements and fragments.
- `Html.render`: the markup as a string.
- `Html.escape`: the one escaping function.
- `ToHtml`, `ToAttr`: what may appear as a child or as an attribute value in a template.

## Main statements

- `Html.escape_safe`: escaped text contains none of `<`, `>`, `"` and `'`, so it cannot open or
  close a tag or leave an attribute value.
-/

@[expose] public section

namespace Lanes

/-- An attribute of an element. A value of `none` renders as a bare name, such as `disabled`. -/
structure Html.Attr where
  /-- The attribute name. -/
  name : String
  /-- The attribute value, or `none` for a boolean attribute. -/
  value : Option String := none
  deriving DecidableEq, Repr, Hashable

/-- An HTML document fragment. -/
inductive Html where
  /-- Text. It is escaped when rendered. -/
  | text (s : String)
  /-- An element with attributes and children. -/
  | element (tag : String) (attrs : List Html.Attr) (children : List Html)
  /-- A sequence of nodes with no element around them. -/
  | fragment (children : List Html)
  deriving Repr

namespace Html

/-- The empty fragment. -/
def empty : Html := .fragment []

instance : Inhabited Html := ⟨empty⟩

/-- How one character is written in HTML text and attribute values. -/
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

/-- No character produced by escaping can open or close a tag or end a quoted attribute. -/
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

/-- Elements that have no content and no closing tag. -/
def voidTags : List String :=
  ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track",
   "wbr"]

/-- Render one attribute, with a leading space. -/
def Attr.render (a : Attr) : String :=
  match a.value with
  | some v => s!" {safeName a.name}=\"{escape v}\""
  | none => s!" {safeName a.name}"

mutual

/-- The markup of a node. -/
def render : Html → String
  | .text s => escape s
  | .element tag attrs children =>
    let tag := safeName tag
    let attrs := String.join (attrs.map Attr.render)
    if voidTags.contains tag then s!"<{tag}{attrs}>"
    else s!"<{tag}{attrs}>{renderAll children}</{tag}>"
  | .fragment children => renderAll children

/-- The markup of a list of nodes. -/
def renderAll : List Html → String
  | [] => ""
  | node :: nodes => render node ++ renderAll nodes

end

/-- A complete HTML document: the doctype followed by the markup. -/
def document (page : Html) : String :=
  "<!DOCTYPE html>" ++ page.render

end Html

/-- What may be written as `{value}` in a template's children. -/
class ToHtml (α : Type) where
  /-- The node for a value. -/
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
/-- A boolean attribute is present when `true` and absent when `false`. -/
instance : ToAttr Bool := ⟨fun name v => if v then [⟨name, none⟩] else []⟩
instance {α : Type} [ToAttr α] : ToAttr (Option α) where
  toAttr name
    | some v => ToAttr.toAttr name v
    | none => []

end Lanes
