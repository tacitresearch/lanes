/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Html.Basic

/-!
What a browser reads from a rendered page. `lex` is the HTML tokenizer in the states a page of
Lanes passes through: text with character references, start tags with double-quoted attribute
values, and end tags; anything else breaks it. `lex_render` proves that it reads every page
`render` writes, and reads it as the tree says (`tokens`): each character of a text as that
character, each attribute with the value it was given, through `safeUrl` for a URL attribute,
and each element with its tag. So text from anywhere stays text: it cannot open or close an
element, or end an attribute's value.

A browser also lowercases names, keeps the first of two attributes of one name, reads a carriage
return as a newline, and reads what is inside `title`, `textarea`, `noscript` and the other
elements of raw text as text, so an element inside one of them arrives as text.

`safeUrl_scheme` proves that the scheme a browser reads from what `safeUrl` returns, however it
treats blanks and controls, is one of `allowedSchemes`, or `about` for `blockedUrl`.
-/

@[expose] public section

namespace Lanes.Html

inductive Token where
  | char (c : Char)
  | start (tag : String) (attrs : List (String × Option String))
  | finish (tag : String)
  deriving DecidableEq, Repr

/-- The attribute as a browser reads it from `Attr.render`. -/
def Attr.token (a : Attr) : List (String × Option String) :=
  let name := safeName a.name
  if name.isEmpty then [] else [(name, a.value.map (Attr.shown name))]

mutual

def tokens : Html → List Token
  | .text s => s.toList.map .char
  | .element tag attrs children =>
    let tag := safeName tag
    let start := Token.start tag (attrs.flatMap Attr.token)
    if !isTagName tag then tokensAll children
    else if voidTags.contains tag.toLower then [start]
    else if rawTextTags.contains tag.toLower then [start, .finish tag]
    else start :: tokensAll children ++ [.finish tag]
  | .fragment children => tokensAll children

def tokensAll : List Html → List Token
  | [] => []
  | node :: nodes => tokens node ++ tokensAll nodes

end

/-- The character a reference names, for the five `escape` writes. -/
def charRef : List Char → Option Char
  | ['a', 'm', 'p'] => some '&'
  | ['l', 't'] => some '<'
  | ['g', 't'] => some '>'
  | ['q', 'u', 'o', 't'] => some '"'
  | ['#', '3', '9'] => some '\''
  | _ => none

inductive Lexer.Mode where
  | data
  | charRef (name : List Char)
  | tagOpen
  | tagName (name : List Char)
  | beforeAttr (tag : String) (attrs : List (String × Option String))
  | attrName (tag : String) (attrs : List (String × Option String)) (name : List Char)
  | beforeValue (tag : String) (attrs : List (String × Option String)) (name : String)
  | value (tag : String) (attrs : List (String × Option String)) (name : String)
      (value : List Char)
  | valueRef (tag : String) (attrs : List (String × Option String)) (name : String)
      (value ref : List Char)
  | afterValue (tag : String) (attrs : List (String × Option String))
  | endTagOpen
  | endTagName (name : List Char)
  | broken

structure Lexer where
  mode : Lexer.Mode
  out : List Token

def Lexer.step (l : Lexer) (c : Char) : Lexer :=
  match l.mode with
  | .data =>
    if c = '<' then ⟨.tagOpen, l.out⟩
    else if c = '&' then ⟨.charRef [], l.out⟩
    else ⟨.data, l.out ++ [.char c]⟩
  | .charRef name =>
    if c = ';' then
      match Html.charRef name with
      | some d => ⟨.data, l.out ++ [.char d]⟩
      | none => ⟨.broken, l.out⟩
    else ⟨.charRef (name ++ [c]), l.out⟩
  | .tagOpen =>
    if c.isAlpha then ⟨.tagName [c], l.out⟩
    else if c = '/' then ⟨.endTagOpen, l.out⟩
    else ⟨.broken, l.out⟩
  | .tagName name =>
    if nameChar c then ⟨.tagName (name ++ [c]), l.out⟩
    else if c = ' ' then ⟨.beforeAttr (String.ofList name) [], l.out⟩
    else if c = '>' then ⟨.data, l.out ++ [.start (String.ofList name) []]⟩
    else ⟨.broken, l.out⟩
  | .beforeAttr tag attrs =>
    if nameChar c then ⟨.attrName tag attrs [c], l.out⟩
    else if c = '>' then ⟨.data, l.out ++ [.start tag attrs]⟩
    else ⟨.broken, l.out⟩
  | .attrName tag attrs name =>
    if nameChar c then ⟨.attrName tag attrs (name ++ [c]), l.out⟩
    else if c = '=' then ⟨.beforeValue tag attrs (String.ofList name), l.out⟩
    else if c = ' ' then ⟨.beforeAttr tag (attrs ++ [(String.ofList name, none)]), l.out⟩
    else if c = '>' then ⟨.data, l.out ++ [.start tag (attrs ++ [(String.ofList name, none)])]⟩
    else ⟨.broken, l.out⟩
  | .beforeValue tag attrs name =>
    if c = '"' then ⟨.value tag attrs name [], l.out⟩ else ⟨.broken, l.out⟩
  | .value tag attrs name value =>
    if c = '"' then ⟨.afterValue tag (attrs ++ [(name, some (String.ofList value))]), l.out⟩
    else if c = '&' then ⟨.valueRef tag attrs name value [], l.out⟩
    else ⟨.value tag attrs name (value ++ [c]), l.out⟩
  | .valueRef tag attrs name value ref =>
    if c = ';' then
      match Html.charRef ref with
      | some d => ⟨.value tag attrs name (value ++ [d]), l.out⟩
      | none => ⟨.broken, l.out⟩
    else ⟨.valueRef tag attrs name value (ref ++ [c]), l.out⟩
  | .afterValue tag attrs =>
    if c = ' ' then ⟨.beforeAttr tag attrs, l.out⟩
    else if c = '>' then ⟨.data, l.out ++ [.start tag attrs]⟩
    else ⟨.broken, l.out⟩
  | .endTagOpen =>
    if c.isAlpha then ⟨.endTagName [c], l.out⟩ else ⟨.broken, l.out⟩
  | .endTagName name =>
    if nameChar c then ⟨.endTagName (name ++ [c]), l.out⟩
    else if c = '>' then ⟨.data, l.out ++ [.finish (String.ofList name)]⟩
    else ⟨.broken, l.out⟩
  | .broken => ⟨.broken, l.out⟩

/-- The tokens a browser reads from `page`, or `none` if `page` leaves the states `Lexer.step`
knows or ends inside a tag or a reference. -/
def lex (page : String) : Option (List Token) :=
  match page.toList.foldl Lexer.step ⟨.data, []⟩ with
  | ⟨.data, out⟩ => some out
  | _ => none

private theorem foldl_escapeChar (c : Char) (out : List Token) :
    (escapeChar c).foldl Lexer.step ⟨.data, out⟩ = ⟨.data, out ++ [.char c]⟩ := by
  unfold escapeChar
  split <;> simp_all [Lexer.step, charRef]

private theorem foldl_escapeChar_value (c : Char) {tag attrs name value out} :
    (escapeChar c).foldl Lexer.step ⟨.value tag attrs name value, out⟩
      = ⟨.value tag attrs name (value ++ [c]), out⟩ := by
  unfold escapeChar
  split <;> simp_all [Lexer.step, charRef]

private theorem foldl_escape (s : String) (out : List Token) :
    (escape s).toList.foldl Lexer.step ⟨.data, out⟩ = ⟨.data, out ++ s.toList.map .char⟩ := by
  rw [escape, String.toList_ofList]
  generalize s.toList = cs
  induction cs generalizing out with
  | nil => simp
  | cons c cs ih => simp [List.flatMap_cons, List.foldl_append, foldl_escapeChar, ih]

private theorem foldl_escape_value (s : String) {tag attrs name value out} :
    (escape s).toList.foldl Lexer.step ⟨.value tag attrs name value, out⟩
      = ⟨.value tag attrs name (value ++ s.toList), out⟩ := by
  rw [escape, String.toList_ofList]
  generalize s.toList = cs
  induction cs generalizing value with
  | nil => simp
  | cons c cs ih => simp [List.flatMap_cons, List.foldl_append, foldl_escapeChar_value, ih]

theorem nameChar_safe {c : Char} (h : nameChar c) :
    c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'' ∧ c ≠ '=' ∧ c ≠ '/' ∧ c ≠ ' ' ∧ c ≠ '&' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rintro rfl; exact absurd h (by decide))

/-- A tag or attribute name holds only letters, digits, `-`, `_` and `:`, so it cannot end a tag,
start a value or carry markup. -/
theorem mem_safeName {name : String} {c : Char} (h : c ∈ (safeName name).toList) : nameChar c := by
  simp only [safeName, String.toList_ofList, List.mem_filter] at h
  exact h.2

private theorem foldl_tagName {cs : List Char} (h : ∀ c ∈ cs, nameChar c) {name out} :
    cs.foldl Lexer.step ⟨.tagName name, out⟩ = ⟨.tagName (name ++ cs), out⟩ := by
  induction cs generalizing name with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [show Lexer.step ⟨.tagName name, out⟩ c = ⟨.tagName (name ++ [c]), out⟩ by
      simp [Lexer.step, h c (by simp)], ih fun d hd => h d (by simp [hd])]
    simp

private theorem foldl_attrName {cs : List Char} (h : ∀ c ∈ cs, nameChar c) {tag attrs name out} :
    cs.foldl Lexer.step ⟨.attrName tag attrs name, out⟩ = ⟨.attrName tag attrs (name ++ cs), out⟩ := by
  induction cs generalizing name with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [show Lexer.step ⟨.attrName tag attrs name, out⟩ c = ⟨.attrName tag attrs (name ++ [c]), out⟩
      by simp [Lexer.step, h c (by simp)], ih fun d hd => h d (by simp [hd])]
    simp

private theorem foldl_endTagName {cs : List Char} (h : ∀ c ∈ cs, nameChar c) {name out} :
    cs.foldl Lexer.step ⟨.endTagName name, out⟩ = ⟨.endTagName (name ++ cs), out⟩ := by
  induction cs generalizing name with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [show Lexer.step ⟨.endTagName name, out⟩ c = ⟨.endTagName (name ++ [c]), out⟩ by
      simp [Lexer.step, h c (by simp)], ih fun d hd => h d (by simp [hd])]
    simp

/-- Where a start tag can end or take another attribute, with the tag and attributes it has. -/
private def inTag? : Lexer.Mode → Option (String × List (String × Option String))
  | .tagName name => some (String.ofList name, [])
  | .attrName tag attrs name => some (tag, attrs ++ [(String.ofList name, none)])
  | .afterValue tag attrs => some (tag, attrs)
  | _ => none

private theorem step_space {m : Lexer.Mode} {tag attrs out} (h : inTag? m = some (tag, attrs)) :
    Lexer.step ⟨m, out⟩ ' ' = ⟨.beforeAttr tag attrs, out⟩ := by
  cases m <;> simp_all [inTag?, Lexer.step, nameChar]

private theorem step_close {m : Lexer.Mode} {tag attrs out} (h : inTag? m = some (tag, attrs)) :
    Lexer.step ⟨m, out⟩ '>' = ⟨.data, out ++ [.start tag attrs]⟩ := by
  cases m <;> simp_all [inTag?, Lexer.step, nameChar]

private theorem safeName_cons {name : String} (h : safeName name ≠ "") :
    ∃ c cs, (safeName name).toList = c :: cs ∧ nameChar c ∧ ∀ d ∈ cs, nameChar d := by
  cases hs : (safeName name).toList with
  | nil => exact absurd (String.toList_eq_nil_iff.mp hs) h
  | cons c cs =>
    have hmem := fun d (hd : d ∈ c :: cs) => mem_safeName (hs ▸ hd)
    exact ⟨c, cs, rfl, hmem c (by simp), fun d hd => hmem d (by simp [hd])⟩

private theorem foldl_attr (a : Attr) {m : Lexer.Mode} {tag attrs out}
    (h : inTag? m = some (tag, attrs)) :
    ∃ m', inTag? m' = some (tag, attrs ++ a.token)
      ∧ a.render.toList.foldl Lexer.step ⟨m, out⟩ = ⟨m', out⟩ := by
  unfold Attr.render Attr.token
  by_cases hn : safeName a.name = ""
  · exact ⟨m, by simp [hn, h], by simp [hn]⟩
  obtain ⟨c, cs, hcs, hc, hcs'⟩ := safeName_cons hn
  have hname : String.ofList (c :: cs) = safeName a.name := by
    rw [← hcs, String.ofList_toList]
  have hpre : (safeName a.name).toList.foldl Lexer.step (" ".toList.foldl Lexer.step ⟨m, out⟩)
      = ⟨.attrName tag attrs (c :: cs), out⟩ := by
    rw [show " ".toList = [' '] from rfl, List.foldl_cons, List.foldl_nil, step_space h, hcs,
      List.foldl_cons]
    simp [Lexer.step, hc, foldl_attrName hcs']
  have hn' : (safeName a.name).isEmpty = false := by simpa using hn
  simp only [hn', Bool.false_eq_true, ↓reduceIte]
  cases a.value with
  | none =>
    refine ⟨.attrName tag attrs (c :: cs), by simp [inTag?, hname], ?_⟩
    rw [String.toList_append, List.foldl_append, hpre]
  | some v =>
    refine ⟨.afterValue tag (attrs ++ [(safeName a.name, some (Attr.shown (safeName a.name) v))]),
      by simp [inTag?], ?_⟩
    simp only [String.toList_append, List.foldl_append]
    rw [hpre]
    simp [Lexer.step, nameChar, foldl_escape_value, hname]

private theorem foldl_attrs (as : List Attr) {m : Lexer.Mode} {tag attrs out}
    (h : inTag? m = some (tag, attrs)) :
    ∃ m', inTag? m' = some (tag, attrs ++ as.flatMap Attr.token)
      ∧ (String.join (as.map Attr.render)).toList.foldl Lexer.step ⟨m, out⟩ = ⟨m', out⟩ := by
  induction as generalizing m attrs with
  | nil => exact ⟨m, by simp [h], by simp⟩
  | cons a as ih =>
    obtain ⟨m₁, h₁, e₁⟩ := foldl_attr a (out := out) h
    obtain ⟨m₂, h₂, e₂⟩ := ih h₁
    refine ⟨m₂, by simpa using h₂, ?_⟩
    simp only [String.toList_join, List.map_cons, List.flatMap_cons, List.foldl_append] at e₂ ⊢
    rw [e₁, e₂]

private theorem isTagName_cons {name : String} (h : isTagName (safeName name)) :
    ∃ c cs, (safeName name).toList = c :: cs ∧ c.isAlpha ∧ ∀ d ∈ cs, nameChar d := by
  cases hs : (safeName name).toList with
  | nil => simp [isTagName, hs] at h
  | cons c cs =>
    simp only [isTagName, hs, List.head?_cons, Option.any_some] at h
    exact ⟨c, cs, rfl, h, fun d hd => mem_safeName (hs ▸ List.mem_cons_of_mem c hd)⟩

private theorem foldl_start {tag : String} (as : List Attr) (h : isTagName (safeName tag)) (out) :
    (startTag (safeName tag) (String.join (as.map Attr.render))).toList.foldl Lexer.step
        ⟨.data, out⟩
      = ⟨.data, out ++ [.start (safeName tag) (as.flatMap Attr.token)]⟩ := by
  obtain ⟨c, cs, hcs, hc, hcs'⟩ := isTagName_cons h
  have hname : String.ofList (c :: cs) = safeName tag := by rw [← hcs, String.ofList_toList]
  have hin : inTag? (.tagName (c :: cs)) = some (safeName tag, []) := by simp [inTag?, hname]
  obtain ⟨m, hm, e⟩ := foldl_attrs as (out := out) hin
  have hopen : (safeName tag).toList.foldl Lexer.step ("<".toList.foldl Lexer.step ⟨.data, out⟩)
      = ⟨.tagName (c :: cs), out⟩ := by
    simp [hcs, Lexer.step, hc, foldl_tagName hcs']
  simp only [startTag, String.toList_append, List.foldl_append]
  rw [hopen, e]
  simp [step_close hm]

private theorem foldl_finish {tag : String} (h : isTagName (safeName tag)) (out) :
    (endTag (safeName tag)).toList.foldl Lexer.step ⟨.data, out⟩
      = ⟨.data, out ++ [.finish (safeName tag)]⟩ := by
  obtain ⟨c, cs, hcs, hc, hcs'⟩ := isTagName_cons h
  have hname : String.ofList (c :: cs) = safeName tag := by rw [← hcs, String.ofList_toList]
  simp only [endTag, String.toList_append, List.foldl_append, hcs]
  simp [Lexer.step, hc, foldl_endTagName hcs', nameChar, hname]

mutual

private theorem foldl_render : ∀ (page : Html) (out : List Token),
    page.render.toList.foldl Lexer.step ⟨.data, out⟩ = ⟨.data, out ++ page.tokens⟩
  | .text s, out => by simp [render, tokens, foldl_escape]
  | .element tag attrs children, out => by
    by_cases ht : isTagName (safeName tag)
    · have start := foldl_start attrs ht
      have finish := foldl_finish ht
      rw [render, tokens]
      simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      split
      · exact start out
      split
      · rw [String.toList_append, List.foldl_append, start, finish]
        simp
      · rw [String.toList_append, List.foldl_append, String.toList_append, List.foldl_append,
          start, foldl_renderAll children, finish]
        simp
    · simp [render, tokens, ht, foldl_renderAll children]
  | .fragment children, out => by simp [render, tokens, foldl_renderAll children]

private theorem foldl_renderAll : ∀ (pages : List Html) (out : List Token),
    (renderAll pages).toList.foldl Lexer.step ⟨.data, out⟩ = ⟨.data, out ++ tokensAll pages⟩
  | [], out => by simp [renderAll, tokensAll]
  | page :: pages, out => by
    simp [renderAll, tokensAll, List.foldl_append, foldl_render page, foldl_renderAll pages]

end

/-- A browser reads every page `render` writes as the tree it was rendered from. -/
theorem lex_render (page : Html) : lex page.render = some page.tokens := by
  simp [lex, foldl_render page []]

private theorem isAlpha_toLower (c : Char) : c.toLower.isAlpha = c.isAlpha := by
  unfold Char.toLower
  split
  · rename_i h
    simp only [Char.isAlpha, Char.isUpper, Char.isLower, ge_iff_le] at h ⊢
    simp only [UInt32.le_iff_toNat_le] at h ⊢
    simp [UInt32.toNat_add] at h ⊢
    rw [Nat.mod_eq_of_lt (by omega)]
    have h₁ : 97 ≤ c.toNat + 32 ∧ c.toNat + 32 ≤ 122 := by omega
    simp [h₁, h.1, h.2]
  · rfl

private theorem isTagName_toLower (name : String) : isTagName name.toLower = isTagName name := by
  simp only [isTagName, String.toLower, String.toList_map, List.head?_map]
  cases name.toList.head? <;> simp [isAlpha_toLower]

/-- A void element renders as its start tag, whatever children it is given. -/
theorem render_void {tag : String} (h : voidTags.contains (safeName tag).toLower)
    (attrs : List Attr) (children : List Html) :
    render (.element tag attrs children) = startTag (safeName tag) (String.join (attrs.map Attr.render)) := by
  have hvoid : ∀ t ∈ voidTags, isTagName t := by decide
  have ht : isTagName (safeName tag) := by
    rw [← isTagName_toLower]
    exact hvoid _ (List.contains_iff_mem.mp h)
  simp [render, ht, List.contains_iff_mem.mp h]

def schemeChar (c : Char) : Bool :=
  c.isAlphanum || c == '+' || c == '-' || c == '.'

/-- The scheme a browser reads from the characters of a URL, lowercased: what comes before the
first `:`, if it is a letter and then letters, digits, `+`, `-` and `.`, as in the URL
standard's scheme state. Otherwise the URL is relative and has none. -/
def scheme? (url : List Char) : Option String :=
  match url, url.dropWhile schemeChar with
  | c :: _, ':' :: _ =>
    if c.isAlpha then some (String.ofList ((url.takeWhile schemeChar).map Char.toLower)) else none
  | _, _ => none

private theorem schemeChar_plain {c : Char} (h : schemeChar c) :
    urlBlank c = false ∧ c ≠ ':' ∧ c ≠ '/' ∧ c ≠ '?' ∧ c ≠ '#' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [schemeChar, Char.isAlphanum, Char.isAlpha, Char.isUpper, Char.isLower,
      Char.isDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rcases h with ((((h | h) | h) | h) | h) | h
    all_goals first
      | (subst h; decide)
      | (simp only [urlBlank, decide_eq_false_iff_not, ge_iff_le, UInt32.le_iff_toNat_le] at h ⊢
         simp at h ⊢
         omega)
  all_goals (rintro rfl; exact absurd h (by decide))

private theorem scheme?_some {view : List Char} {scheme : String} (h : scheme? view = some scheme) :
    ∃ pre rest, view = pre ++ ':' :: rest ∧ (∀ c ∈ pre, schemeChar c)
      ∧ scheme = String.ofList (pre.map Char.toLower) := by
  unfold scheme? at h
  split at h
  · rename_i c cs rest hdrop
    split at h
    · refine ⟨(c :: cs).takeWhile schemeChar, rest, ?_, fun d hd => List.all_eq_true.mp List.all_takeWhile d hd, ?_⟩
      · rw [← hdrop, List.takeWhile_append_dropWhile]
      · exact (Option.some.inj h).symm
    · simp at h
  · simp at h

private theorem filter_scheme {pre rest : List Char} (h : ∀ c ∈ pre, schemeChar c) :
    (pre ++ ':' :: rest).filter (!urlBlank ·) = pre ++ ':' :: rest.filter (!urlBlank ·) := by
  rw [List.filter_append, List.filter_eq_self.mpr fun c hc => by simp [(schemeChar_plain (h c hc)).1]]
  simp [urlBlank]

private theorem safeUrl_of_scheme {url : String} {pre rest : List Char}
    (h : url.toList.filter (!urlBlank ·) = pre ++ ':' :: rest) (hpre : ∀ c ∈ pre, schemeChar c) :
    safeUrl url = if allowedSchemes.contains (String.ofList (pre.map Char.toLower)) then url
      else blockedUrl := by
  have hstop : ∀ c ∈ pre, (c != ':' && c != '/' && c != '?' && c != '#') = true := fun c hc => by
    have := schemeChar_plain (hpre c hc)
    simp [this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2]
  simp [safeUrl, h, List.takeWhile_append_of_pos hstop]

theorem safeUrl_eq (url : String) : safeUrl url = url ∨ safeUrl url = blockedUrl := by
  unfold safeUrl
  dsimp only
  split
  · split
    · exact .inl rfl
    · exact .inr rfl
  · exact .inl rfl

private theorem pre_blocked {pre rest : List Char} (hpre : ∀ c ∈ pre, schemeChar c)
    (h : blockedUrl.toList.filter (!urlBlank ·) = pre ++ ':' :: rest) : pre = "about".toList := by
  have hstop : ∀ c ∈ pre, (c != ':') = true := fun c hc => by
    simp [(schemeChar_plain (hpre c hc)).2.1]
  have := congrArg (List.takeWhile (· != ':')) h
  rw [List.takeWhile_append_of_pos hstop] at this
  simp only [List.takeWhile_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    List.append_nil] at this
  rw [← this]
  decide

/-- Whatever scheme a browser reads from the URL `safeUrl` returns, whichever blanks and controls
it ignores, is one of `allowedSchemes`, or `about` when the URL was blocked: never `javascript`,
`data` or `vbscript`, in any case or spacing. -/
theorem safeUrl_scheme (url : String) {view : List Char} {scheme : String}
    (hview : view.filter (!urlBlank ·) = (safeUrl url).toList.filter (!urlBlank ·))
    (hscheme : scheme? view = some scheme) :
    scheme ∈ allowedSchemes ∨ (safeUrl url = blockedUrl ∧ scheme = "about") := by
  obtain ⟨pre, rest, rfl, hpre, rfl⟩ := scheme?_some hscheme
  rw [filter_scheme hpre] at hview
  have about : safeUrl url = blockedUrl → String.ofList (pre.map Char.toLower) = "about" := by
    intro hb
    rw [hb] at hview
    rw [pre_blocked hpre hview.symm]
    decide
  rcases safeUrl_eq url with hu | hb
  · rw [hu] at hview
    rw [safeUrl_of_scheme hview.symm hpre] at hu
    split at hu
    · exact .inl (List.elem_iff.mp (by assumption))
    · exact .inr ⟨hu ▸ rfl, about (hu ▸ rfl)⟩
  · exact .inr ⟨hb, about hb⟩

end Lanes.Html
