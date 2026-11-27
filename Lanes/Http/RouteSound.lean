/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Http.Route
public import Lanes.Http.ReadRequestSound

/-!
A link reaches the handler of its route. The server reads a link's target back to the segments
the route printed (`Route.link_target`), so a request for it with the route's method is matched by
the route with the value the link was printed from (`Route.match?_target`), and `dispatch` hands it
to that route's handler unless a handler before it answers (`dispatch_link`).
-/

@[expose] public section

namespace Lanes.Http

variable {α β : Type}

theorem Slug.ofString?_text (s : Slug) : Slug.ofString? s.text = some s := by
  simp [Slug.ofString?, s.clean]

/-- A slug is any text that `Segment.Clean` admits, and reads back as that text. -/
theorem Slug.ofString?_eq_some {text : String} {s : Slug} :
    Slug.ofString? text = some s ↔ s.text = text := by
  constructor
  · intro h
    unfold Slug.ofString? at h
    split at h
    · cases h; rfl
    · simp at h
  · rintro rfl
    exact Slug.ofString?_text s

namespace Route

/-- The server reads a route's link as the path the route printed, with no query. -/
theorem link_target (r : Route α) (a : α) :
    Request.target? (r.link a).toList = .ok (r.path.print a, []) := by
  have hpath : r.path.print a ≠ [""] := fun h =>
    (r.path.clean a "" (by simp [h])).1 rfl
  have := Request.target?_target { method := r.method, path := r.path.print a } hpath
  simpa [Request.target, link] using this

/-- A request for a route's link, with the route's method, is matched by the route, with the
value the link was printed from. -/
theorem match?_target (r : Route α) (a : α) {request : Request} (hmethod : request.method = r.method)
    (htarget : Request.target? (r.link a).toList = .ok (request.path, request.query)) :
    r.match? request = some a := by
  rw [link_target] at htarget
  have hpath : request.path = r.path.print a := by
    simp only [Except.ok.injEq, Prod.mk.injEq] at htarget
    exact htarget.1.symm
  exact match?_link r a request hmethod hpath

end Route

/-- `dispatch` answers with the first handler that answers. -/
theorem dispatch_eq_some {handlers : List (Request → Option β)} {request : Request} {b : β} :
    dispatch handlers request = some b
      ↔ ∃ pre handler post, handlers = pre ++ handler :: post ∧ handler request = some b
        ∧ ∀ g ∈ pre, g request = none :=
  List.findSome?_eq_some_iff

theorem dispatch_eq_none {handlers : List (Request → Option β)} {request : Request} :
    dispatch handlers request = none ↔ ∀ g ∈ handlers, g request = none :=
  List.findSome?_eq_none_iff

/-- A request made from a route's link reaches that route's handler, with the value the link was
printed from, unless a handler before it answers. -/
theorem dispatch_link (r : Route α) (f : α → Request → β) (a : α)
    {pre post : List (Request → Option β)} {request : Request} (hmethod : request.method = r.method)
    (htarget : Request.target? (r.link a).toList = .ok (request.path, request.query))
    (hpre : ∀ g ∈ pre, g request = none) :
    dispatch (pre ++ r.handle f :: post) request = some (f a request) :=
  dispatch_eq_some.mpr ⟨pre, r.handle f, post, rfl,
    by simp [Route.handle, r.match?_target a hmethod htarget], hpre⟩

end Lanes.Http
