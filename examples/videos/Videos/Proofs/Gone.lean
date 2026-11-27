/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Proofs.Run

/-!
# A deleted video is never served again

A delete answered leaves no video with that id (`Site.gone_delete`), no input or start gives one
that id again (`Site.Gone.grows`), and what an output shows is a video of the site
(`Site.shows_handle`). So after a delete is answered, no output of any later input or start
shows the video (`Site.deleted_never_served`), however the store answers the delete: late,
refused, `unknown`, never, or after a crash. Links to the store handed out before the delete
are the store's: they last until they expire, or until the delete reaches the store (README).
-/

set_option linter.unusedSectionVars false

namespace Videos

open Lanes

namespace Site

variable (config : Config)

/-- `v` was a video's id, and is no video's now. -/
def Gone (s : Site) (v : VideoId) : Prop := v < s.next ∧ ∀ w ∈ s.videos, w.id ≠ v

theorem Gone.grows {s s' : Site} {v : VideoId} (h : Gone s v) (hg : Grows s s') : Gone s' v := by
  refine ⟨Nat.lt_of_lt_of_le h.1 hg.1, fun w hw heq => ?_⟩
  rcases hg.2 w hw with ⟨w', hw', hid⟩ | ⟨hid, _⟩
  · exact h.2 w' hw' (hid.trans heq)
  · rw [← heq, hid] at h
    exact Nat.lt_irrefl _ h.1

theorem Gone.not_shown {s : Site} {v : VideoId} {o : Out} (h : Gone s v) (ho : s.Shows o) :
    ∀ c ∈ o.cards, c.id ≠ v := by
  intro c hc
  obtain ⟨w, hw, rfl, -⟩ := ho c hc
  exact h.2 w hw

theorem shows_step (s : Site) (e : Turn) : ∀ o ∈ (s.step config e).2, s.Shows o := by
  cases e with
  | inl i => exact shows_handle config s i
  | inr _ => exact shows_recover config s

/-- A video gone stays gone through any turns, and none of their outputs shows it. -/
theorem Gone.run {s : Site} {v : VideoId} (h : Gone s v) (es : List Turn) :
    Gone (s.run config es).1 v ∧ ∀ o ∈ (s.run config es).2, ∀ c ∈ o.cards, c.id ≠ v := by
  induction es generalizing s with
  | nil => exact ⟨h, by simp [run_nil]⟩
  | cons e es ih =>
    obtain ⟨hgone, hshown⟩ := ih (h.grows (grows_step config s e))
    rw [run_cons]
    refine ⟨hgone, fun o ho => ?_⟩
    rcases List.mem_append.mp ho with ho | ho
    · exact h.not_shown (shows_step config s e o ho)
    · exact hshown o ho

/-- A delete answered `deleted` leaves the video gone. -/
theorem gone_delete {s : Site} (hfresh : Fresh s) {req : ReqId} {m : Member} {session : Sid}
    {v v' : VideoId} {r : ReqId} {viewer : Viewer}
    (h : Out.reply r viewer (.deleted v) ∈ (s.handle config (.request (.delete req m session v'))).2) :
    Gone (s.handle config (.request (.delete req m session v'))).1 v := by
  simp only [handle, request, withSession, owned] at h ⊢
  by_cases hl : s.live m session = true
  · cases hfind : s.find? v' with
    | none => simp [hl, hfind, answer] at h
    | some video =>
      by_cases ho : video.owner = m
      · simp only [hl, hfind, ho, ite_true, delete, pushDeleting] at h ⊢
        have hv : v = video.id := by
          simp only [List.mem_append, answer, List.mem_singleton, Out.reply.injEq,
            Reply.deleted.injEq, List.mem_map, reduceCtorEq, and_false, exists_false,
            or_false] at h
          rcases h with h | h
          · split at h
            · simp at h
            · simp at h
          · exact h.2.2
        subst hv
        exact ⟨hfresh video (find?_mem hfind), fun w hw heq => by
          simpa [heq] using (List.mem_filter.mp hw).2⟩
      · simp [hl, hfind, ho, answer] at h
  · simp [hl, answer] at h

/-- A deleted video is never served again: once a delete is answered, no output of any later
input or start of the actor shows the video, whatever the store answers to its delete, and
whenever. -/
theorem deleted_never_served (es₁ es₂ : List Turn) {req : ReqId} {m : Member} {session : Sid}
    {v v' : VideoId} {r : ReqId} {viewer : Viewer}
    (h : Out.reply r viewer (.deleted v) ∈
      (((Site.run config {} es₁).1).handle config (.request (.delete req m session v'))).2) :
    ∀ o ∈ ((((Site.run config {} es₁).1).handle config
        (.request (.delete req m session v'))).1.run config es₂).2, ∀ c ∈ o.cards, c.id ≠ v :=
  ((gone_delete config (fresh_init.run config es₁) h).run config es₂).2

end Site

end Videos
