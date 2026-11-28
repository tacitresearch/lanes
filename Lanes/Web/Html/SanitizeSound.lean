/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Html.Sanitize
public import Lanes.Web.Html.BasicSound

/-!
What `Html.sanitize` is proved to do: a browser reads what `render` writes of its result
(`Html.lex_sanitize`), and every element it reads is one the policy keeps, with only attributes
the policy keeps for it, a URL attribute's value being a URL that `safeUrl` passes and whose scheme
the policy allows (`Html.sanitize_safe`). The proof is about `Sanitize.prune`, the last step,
so it holds whatever the tokenizer and the builder before it do.
-/

@[expose] public section

namespace Lanes.Html

open Sanitize

/-- What a browser may read from a sanitized page. -/
def Safe (p : Policy) : Token → Prop
  | .start tag attrs => p.keepsTag tag ∧ ∀ a ∈ attrs, p.keepsAttr tag ⟨a.1, a.2⟩
  | _ => True

theorem safeName_of_nameOk {n : String} (h : nameOk n) : safeName n = n := by
  simp only [nameOk, Bool.and_eq_true, List.all_eq_true] at h
  have : n.toList.filter Html.nameChar = n.toList := by
    rw [List.filter_eq_self]
    intro c hc
    have := h.1 c hc
    simp only [Sanitize.nameChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    simp only [Html.nameChar, Bool.or_eq_true, beq_iff_eq]
    rcases this with ((⟨h1, h2⟩ | ⟨h1, h2⟩) | h3) | h4
    · left; left; left
      simp only [Char.isAlphanum, Char.isAlpha, Char.isLower, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq]
      exact .inl (.inr ⟨h1, h2⟩)
    · left; left; left
      simp only [Char.isAlphanum, Char.isDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact .inr ⟨h1, h2⟩
    · left; left; right; simpa using h3
    · right; simpa using h4
  rw [safeName, this, String.ofList_toList]

theorem nameOk_ne_empty {n : String} (h : nameOk n) : n ≠ "" := by
  rintro rfl
  simp [nameOk] at h

theorem keepsTag_nameOk {p : Policy} {tag : String} (h : p.keepsTag tag) : nameOk tag := by
  simp only [Policy.keepsTag, Bool.and_eq_true] at h
  exact h.1.1

/-- A kept attribute reads as it is: its name is a name, and a URL attribute's value is one
`safeUrl` leaves alone. -/
theorem token_of_keepsAttr {p : Policy} {tag : String} {a : Attr} (h : p.keepsAttr tag a) :
    Attr.token a = [(a.name, a.value)] := by
  simp only [Policy.keepsAttr, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hn, _⟩, _⟩, hu⟩ := h
  have hs := safeName_of_nameOk hn
  simp only [Attr.token, hs, nameOk_ne_empty hn, String.isEmpty_iff, ite_false]
  congr
  cases hv : a.value with
  | none => rfl
  | some v =>
    simp only [Option.map_some, Option.some.injEq, Attr.shown]
    split
    · rename_i hc
      have hurl : isUrlAttr a.name = true := by
        simp only [isUrlAttr, urlAttributes, List.contains_append, Bool.or_eq_true]
        exact .inl hc
      rcases hu with hu | hu
      · simp [hurl] at hu
      · rw [hv] at hu
        simp only [Option.any_some, Policy.urlOk, Bool.and_eq_true, beq_iff_eq] at hu
        exact hu.1
    · rfl

theorem start_safe {p : Policy} {tag : String} {as : List Attr} (ht : p.keepsTag tag) :
    Safe p (.start (safeName tag) ((as.filter (p.keepsAttr tag)).flatMap Attr.token)) := by
  rw [safeName_of_nameOk (keepsTag_nameOk ht)]
  refine ⟨ht, ?_⟩
  intro a ha
  simp only [List.mem_flatMap, List.mem_filter] at ha
  obtain ⟨b, ⟨_, hb⟩, hab⟩ := ha
  rw [token_of_keepsAttr hb, List.mem_singleton] at hab
  subst hab
  exact hb

mutual

theorem prune_safe (p : Policy) : ∀ (h : Html), ∀ t ∈ (prune p h).tokens, Safe p t
  | .text s => by
    intro t ht
    simp only [prune, tokens, List.mem_map] at ht
    obtain ⟨_, _, rfl⟩ := ht
    trivial
  | .element tag as children => by
    intro t ht
    have hc := pruneAll_safe p children
    unfold prune at ht
    split at ht
    · rename_i hk
      simp only [tokens] at ht
      split at ht
      · exact hc t ht
      split at ht
      · simp only [List.mem_singleton] at ht
        subst ht
        exact start_safe hk
      split at ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact start_safe hk
        · trivial
      · simp only [List.cons_append, List.mem_cons, List.mem_append,
          List.not_mem_nil, or_false] at ht
        rcases ht with rfl | ht | rfl
        · exact start_safe hk
        · exact hc t ht
        · trivial
    · simp only [tokens] at ht
      exact hc t ht
  | .fragment children => by
    intro t ht
    simp only [prune, tokens] at ht
    exact pruneAll_safe p children t ht

theorem pruneAll_safe (p : Policy) : ∀ (hs : List Html), ∀ t ∈ tokensAll (prune.pruneAll p hs), Safe p t
  | [] => by intro t ht; simp [prune.pruneAll, tokensAll] at ht
  | h :: hs => by
    intro t ht
    simp only [prune.pruneAll, tokensAll, List.mem_append] at ht
    rcases ht with ht | ht
    · exact prune_safe p h t ht
    · exact pruneAll_safe p hs t ht

end

/-- Every element a browser reads from a sanitized page is one the policy keeps, with only the
attributes it keeps for it; a URL attribute holds a URL `safeUrl` passes, of a scheme the policy
allows. -/
theorem sanitize_safe (p : Policy) (html : String) : ∀ t ∈ (sanitize p html).tokens, Safe p t :=
  prune_safe p _

/-- A browser reads a sanitized page as its tree. -/
theorem lex_sanitize (p : Policy) (html : String) :
    lex (sanitize p html).render = some (sanitize p html).tokens :=
  lex_render _

end Lanes.Html
