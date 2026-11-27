/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Html.Htmx
public import Lanes.Web.Http.RouteSound

/-!
What htmx does with the attributes of `Hx`. The request it makes from `Hx.request route a`, with
the method the attribute names and the URL it holds, is matched by `route` with `a`
(`Hx.request_match?`). An event name keeps only what a name needs (`Hx.mem_eventName`), so a
rendered trigger has no `[`, which htmx would run as JavaScript, and no `,`, which would start
another trigger (`Hx.render_plain`); and an `HX-Trigger` header from `Response.trigger` has no
`{`, which htmx would read as JSON.
-/

@[expose] public section

namespace Lanes.Hx

open Lanes.Http

theorem methodAttr_inj {m m' : Method} (h : methodAttr m = methodAttr m') : m = m' := by
  cases m <;> cases m' <;> simp_all [methodAttr]

/-- The request htmx makes from `Hx.request route a` is matched by `route`, with `a`. -/
theorem request_match? {α : Type} (route : Route α) (a : α) {name url : String}
    (h : ⟨name, some url⟩ ∈ request route a) {req : Request} (hmethod : methodAttr req.method = name)
    (htarget : Request.target? url.toList = .ok (req.path, req.query)) :
    route.match? req = some a := by
  simp only [request, List.mem_singleton, Html.Attr.mk.injEq, Option.some.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact route.match?_target a (methodAttr_inj hmethod) htarget

theorem mem_eventName {name : String} {c : Char} (h : c ∈ (eventName name).toList) :
    c.isAlphanum ∨ c = '-' ∨ c = '_' ∨ c = ':' ∨ c = '.' := by
  simp only [eventName, String.toList_ofList, List.mem_filter, Bool.or_eq_true, beq_iff_eq] at h
  rcases h.2 with (((h | h) | h) | h) | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr h)))

/-- A character that cannot open a filter, a list of triggers or JSON in htmx. -/
private def quiet (c : Char) : Prop :=
  c ≠ '[' ∧ c ≠ ',' ∧ c ≠ '{'

private theorem quiet_of_alphanum {c : Char} (h : c.isAlphanum) : quiet c := by
  refine ⟨?_, ?_, ?_⟩ <;> (rintro rfl; exact absurd h (by decide))

/-- An event name holds no `[`, `,` or `{`. -/
theorem eventName_plain (name : String) :
    ∀ c ∈ (eventName name).toList, c ≠ '[' ∧ c ≠ ',' ∧ c ≠ '{' := by
  intro c hc
  rcases mem_eventName hc with h | rfl | rfl | rfl | rfl
  · exact quiet_of_alphanum h
  all_goals decide

/-- A rendered trigger holds no `[`, `,` or `{`. -/
theorem render_plain : ∀ (t : Trigger), ∀ c ∈ t.render.toList, c ≠ '[' ∧ c ≠ ',' ∧ c ≠ '{'
  | .load | .click | .change | .submit | .revealed => by
    simp only [Trigger.render]; decide
  | .event name => eventName_plain name
  | .every seconds => by
    intro c hc
    simp only [Trigger.render, String.toList_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · revert c; decide
    · have hdigit : c.isDigit := by
        rw [show toString (max 1 seconds) = (max 1 seconds).repr from rfl, Nat.toList_repr] at hc
        exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
      exact quiet_of_alphanum (by simp [Char.isAlphanum, hdigit])
    · revert c; decide
  | .fromBody inner => by
    intro c hc
    simp only [Trigger.render, String.toList_append, List.mem_append] at hc
    rcases hc with hc | hc
    · exact render_plain inner c hc
    · revert c; decide

end Lanes.Hx
