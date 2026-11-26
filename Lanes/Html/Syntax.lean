/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Html.Basic

/-!
# Template syntax

HTML written inside Lean, checked by the Lean compiler. The syntax is scoped: a view file turns
it on with `open scoped Lanes.Html`, and code elsewhere is not affected by it.

The syntax is a macro, so there is no generate step and no second language server: errors point
at the template line, and hover and go-to-definition work inside templates.

- A lowercase tag is an element. An uppercase tag is a component, that is a Lean function
  returning `Html`: attributes become named arguments and children become the `children`
  argument.
- Text is a string literal: `<p>"Hello"</p>`. It is escaped when rendered.
- `{term}` splices a Lean term as a child (any `ToHtml` type) or as an attribute value (any
  `ToAttr` type). A `Bool` attribute value adds or omits the attribute.
- `{term}` among the attributes splices a `List Html.Attr`, such as the `Hx` vocabulary gives.
- `<>…</>` is a fragment: several nodes with no element around them.
- Attribute names may contain hyphens (`hx-post`, `data-id`) and may be Lean keywords (`class`,
  `for`, `open`).
- A tag name follows its `<` with no space. With a space, `a < b` is a comparison as usual.
- `<script>` and `<style>` take no children: browsers do not decode escaped text inside them, so
  inline code would arrive broken. Load scripts and styles with `src` and `<link>`.
-/

public section

namespace Lanes.Html

open Lean

declare_syntax_cat lanesAttr
declare_syntax_cat lanesChild
declare_syntax_cat lanesElem

scoped syntax sepBy1(rawIdent, "-") "=" str : lanesAttr
scoped syntax sepBy1(rawIdent, "-") "=" "{" term "}" : lanesAttr
scoped syntax sepBy1(rawIdent, "-") : lanesAttr
scoped syntax "{" term "}" : lanesAttr
/-- `<tag attrs/>`. No space is allowed between `<` and the tag name: that is what tells a tag
from a comparison such as `count < limit`. -/
scoped syntax "<" noWs rawIdent lanesAttr* "/>" : lanesElem
scoped syntax "<" noWs rawIdent lanesAttr* ">" lanesChild* "</" rawIdent ">" : lanesElem
scoped syntax "<>" lanesChild* "</>" : lanesElem
scoped syntax str : lanesChild
scoped syntax "{" term "}" : lanesChild
scoped syntax lanesElem : lanesChild
scoped syntax:max lanesElem : term

private meta def attrName (parts : Array Syntax) : String :=
  "-".intercalate (parts.toList.map fun p => p.getId.toString)

private meta def expandAttr : Syntax → MacroM (TSyntax `term)
  | `(lanesAttr| $[$parts]-* = $v:str) =>
    `(Lanes.ToAttr.toAttr $(quote (attrName parts)) ($v : String))
  | `(lanesAttr| $[$parts]-* = { $v }) => `(Lanes.ToAttr.toAttr $(quote (attrName parts)) $v)
  | `(lanesAttr| $[$parts]-*) => `(Lanes.ToAttr.toAttr $(quote (attrName parts)) true)
  | `(lanesAttr| { $attrs }) => `(($attrs : List Lanes.Html.Attr))
  | _ => Macro.throwUnsupported

private meta def applyArg (f : TSyntax `term) : Syntax → MacroM (TSyntax `term)
  | `(lanesAttr| $name:ident = $v:str) => `($f ($name := $v))
  | `(lanesAttr| $name:ident = { $v }) => `($f ($name := $v))
  | `(lanesAttr| $name:ident) => `($f ($name := true))
  | stx => Macro.throwErrorAt stx "a component argument needs a plain name, without hyphens or braces"

private meta def expandChild : Syntax → MacroM (TSyntax `term)
  | `(lanesChild| $s:str) => `(Lanes.Html.text $s)
  | `(lanesChild| { $t }) => `(Lanes.ToHtml.toHtml $t)
  | `(lanesChild| $e:lanesElem) => `($e:lanesElem)
  | _ => Macro.throwUnsupported

private meta def isComponent (tag : Syntax) : Bool :=
  match tag.getId.toString.toList with
  | c :: _ => c.isUpper
  | [] => false

private meta def expandElem : Syntax → MacroM (TSyntax `term)
  | `(lanesElem| <> $children* </>) => do
    let children ← children.mapM (expandChild ·.raw)
    `(Lanes.Html.fragment [$children,*])
  | `(lanesElem| <$tag $attrs* />) => do
    if isComponent tag then
      attrs.foldlM (fun f a => applyArg f a.raw) (⟨tag.raw⟩ : TSyntax `term)
    else
      let attrs ← attrs.mapM (expandAttr ·.raw)
      `(Lanes.Html.element $(quote tag.getId.toString) (List.flatten [$attrs,*]) [])
  | `(lanesElem| <$tag $attrs* > $children* </ $close >) => do
    if tag.getId != close.getId then
      Macro.throwErrorAt close s!"expected </{tag.getId}> to close <{tag.getId}>"
    if (tag.getId == `script || tag.getId == `style) && !children.isEmpty then
      Macro.throwErrorAt tag s!"<{tag.getId}> takes no children here: text inside it is not \
        decoded by browsers, so inline code would arrive broken. Load it from a file instead."
    let children ← children.mapM (expandChild ·.raw)
    if isComponent tag then
      let f ← attrs.foldlM (fun f a => applyArg f a.raw) (⟨tag.raw⟩ : TSyntax `term)
      `($f (children := [$children,*]))
    else
      let attrs ← attrs.mapM (expandAttr ·.raw)
      `(Lanes.Html.element $(quote tag.getId.toString) (List.flatten [$attrs,*]) [$children,*])
  | _ => Macro.throwUnsupported

macro_rules
  | `($e:lanesElem) => expandElem e

end Lanes.Html
