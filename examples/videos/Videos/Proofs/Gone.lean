/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Proofs.Run

/-!
# A deleted video is never served again

A delete answered leaves no video with that id in its owner's site (`Site.gone_delete`), no
input or start gives one that id again (`Site.Gone.grows`), and what a read shows is a video of
the sites it reads (`Site.shows_read`). So after a delete is answered, no read at any later
boundary shows the video, whatever other members' sites it reads, which hold none of the
owner's videos (`Site.deleted_never_served`, and `Videos.owned` for the members' actors),
however the store answers the delete: late, refused, `unknown`, never, or after a crash. No
output of an input shows a video at all (`Site.quiet_handle`). Links to the store handed out
before the delete are the store's: they last until they expire, or until the delete reaches the
store (README).

With the site split into an actor per member, the delete is one step of the owner's actor, and a
read sees the owner's site at a boundary between entries (`Lanes.Batch.run_peeks`), so the video
leaves the feed, its channel and its watch page at one boundary: the one after the delete's
entry.
-/

set_option linter.unusedSectionVars false

namespace Videos

open Lanes

namespace Site

variable (config : Config)

/-- `v` was a video's id, and is no video's now. -/
def Gone (s : Site) (v : VideoId) : Prop := v.n < s.next ∧ ∀ w ∈ s.videos, w.id ≠ v

theorem Gone.grows {s s' : Site} {v : VideoId} (h : Gone s v) (hg : Grows s s') : Gone s' v := by
  refine ⟨Nat.lt_of_lt_of_le h.1 hg.1, fun w hw heq => ?_⟩
  rcases hg.2 w hw with ⟨w', hw', hid⟩ | ⟨hid, _⟩
  · exact h.2 w' hw' (hid.trans heq)
  · rw [← heq] at h
    exact Nat.lt_irrefl _ (hid ▸ h.1)

theorem Gone.not_shown {s : Site} {v : VideoId} {life : Auth.Lifetime} {at_s : Nat} {o : Out}
    (h : Gone s v) (ho : s.Shows life at_s o) :
    ∀ c ∈ o.cards, c.id ≠ v := by
  intro c hc
  obtain ⟨w, hw, rfl, -⟩ := ho c hc
  exact h.2 w hw

theorem shows_step (s : Site) (e : Turn) : ∀ o ∈ (s.step config e).2, ∃ t, s.Shows config.lifetime t o := by
  cases e with
  | inl i => exact fun o ho => ⟨_, shows_handle config s i o ho⟩
  | inr _ => exact fun o ho => ⟨0, shows_recover config s 0 o ho⟩

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
    · obtain ⟨_, hs⟩ := shows_step config s e o ho
      exact h.not_shown hs
    · exact hshown o ho

/-- A delete answered `deleted` leaves the video gone. -/
theorem gone_delete {s : Site} (hfresh : Fresh s) {req : ReqId} {m : Member} {session : Sid}
    {at_s : Nat} {v v' : VideoId} {r : ReqId} {viewer : Viewer}
    (h : Out.reply r viewer (.deleted v) ∈
      (s.handle config (.request (.delete req m session v') at_s)).2) :
    Gone (s.handle config (.request (.delete req m session v') at_s)).1 v := by
  simp only [handle, request, withSession, owned] at h ⊢
  by_cases hl : s.accepts config.lifetime at_s m session = true
  · cases hfind : s.find? v' with
    | none => simp [hl, hfind, answer] at h
    | some video =>
      by_cases ho : video.owner = m
      · simp only [hl, hfind, ho, ite_true, delete] at h ⊢
        have hv : v = video.id := by
          simp only [List.mem_append, answer, List.mem_singleton, Out.reply.injEq,
            Reply.deleted.injEq] at h
          rcases h with (((h | h) | h) | h) | h
          · unfold waiterOf at h
            split at h <;> simp [answer] at h
          · exact h.2.2
          · simp [schedule] at h
          · unfold unexpire at h
            split at h <;> simp at h
          · unfold unstart at h
            split at h <;> simp at h
        subst hv
        exact ⟨hfresh video (find?_mem hfind), fun w hw heq => by
          simpa [heq] using (List.mem_filter.mp hw).2⟩
      · simp [hl, hfind, ho, answer] at h
  · simp [hl, answer] at h

/-- A read of the sites of members, where the site of `v`'s owner has no video with id `v`, does
not show it. -/
theorem read_not_shown {sites : List (Member × Site)} {v : VideoId}
    (h : ∀ p ∈ sites, p.1 = v.owner → ∀ w ∈ p.2.videos, w.id ≠ v) (r : Read) (at_s : Nat) :
    ∀ o ∈ (union sites).read config r at_s, ∀ c ∈ o.cards, c.id ≠ v := by
  intro o ho c hc heq
  obtain ⟨w, hw, rfl, -⟩ := shows_read config _ r at_s o ho c hc
  obtain ⟨⟨m, t⟩, ht, hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨hw, hown⟩ := List.mem_filter.mp hw
  simp only [beq_iff_eq] at hown
  have heq' : w.id = v := heq
  exact h _ ht (by rw [← hown, heq']) w hw heq'

/-- A deleted video is never served again: once a delete is answered, no output of any later
input or start of the owner's actor shows the video, and no read after it shows it, whatever
other members' sites it reads, whatever the store answers to its delete, and whenever. -/
theorem deleted_never_served (es₁ es₂ : List Turn) {req : ReqId} {m : Member} {session : Sid}
    {at_s : Nat} {v v' : VideoId} {r : ReqId} {viewer : Viewer}
    (h : Out.reply r viewer (.deleted v) ∈
      (((Site.run config {} es₁).1).handle config (.request (.delete req m session v') at_s)).2) :
    (∀ o ∈ ((((Site.run config {} es₁).1).handle config
        (.request (.delete req m session v') at_s)).1.run config es₂).2, ∀ c ∈ o.cards, c.id ≠ v)
      ∧ ∀ (others : List (Member × Site)), (∀ p ∈ others, p.1 ≠ v.owner) → ∀ (rd : Read) (t : Nat),
        ∀ o ∈ (union ((v.owner, ((((Site.run config {} es₁).1).handle config
          (.request (.delete req m session v') at_s)).1.run config es₂).1) :: others)).read config rd t,
          ∀ c ∈ o.cards, c.id ≠ v := by
  have hgone := (gone_delete config (fresh_init.run config es₁) h).run config es₂
  refine ⟨hgone.2, fun others hothers rd t => read_not_shown config (fun p hp howner => ?_) rd t⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hgone.1.2
  · exact absurd howner (hothers p hp)

end Site

end Videos
