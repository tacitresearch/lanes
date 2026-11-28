/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Proofs.Members
import Videos.Proofs.Confirmed

/-!
# A like counts each member once

A video's likes are the members who like it, held by its owner's actor, and its count is how
many they are (`Site.card`). A like is let in by the liker's actor and taken by the owner's, as a
visit. No input or start makes a member appear twice (`Site.likedOnce_handle`), so in every
reachable state of the system, under every environment model, each video's count in every
member's site is the number of distinct members who like it (`likes_distinct`,
`count_distinct`). Liking again changes nothing, and taking a like back takes out the one there
is.
-/

set_option linter.unusedSectionVars false

namespace Videos

open Lanes

theorem eraseDups_of_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List α}, l.Nodup → l.eraseDups = l
  | [], _ => rfl
  | a :: as, h => by
    obtain ⟨ha, has⟩ := List.nodup_cons.mp h
    have hf : as.filter (fun b => !b == a) = as :=
      List.filter_eq_self.mpr fun b hb => by
        have : b ≠ a := fun e => ha (e ▸ hb)
        simpa using this
    rw [List.eraseDups_cons, hf, eraseDups_of_nodup has]

/-- No video's likes name a member twice. -/
def Site.LikedOnce (s : Site) : Prop := ∀ w ∈ s.videos, w.likes.Nodup

namespace Site

variable (config : Config)

theorem likedOnce_setVideo {s : Site} {x : Video} (h : s.LikedOnce) (hx : x.likes.Nodup) :
    (s.setVideo x).LikedOnce := by
  intro w hw
  simp only [setVideo, List.mem_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  split
  · exact hx
  · exact h w' hw'

theorem nodup_like {likes : List Member} (h : likes.Nodup) (m : Member) (on : Bool) :
    (if on then (if likes.contains m then likes else m :: likes) else likes.erase m).Nodup := by
  split
  · split
    · exact h
    · next hm => exact List.nodup_cons.mpr ⟨by simpa using hm, h⟩
  · exact h.erase m

theorem likedOnce_settle {s : Site} (h : s.LikedOnce) (r : Report) : (s.settle r).LikedOnce := by
  intro w hw
  simp only [settle, List.mem_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  unfold Report.move
  split
  · split
    · exact h w' hw'
    · exact h w' hw'
  · exact h w' hw'

theorem likedOnce_request {s : Site} (h : s.LikedOnce) (c : Command) (at_s : Nat) :
    (s.request config c at_s).1.LikedOnce := by
  let P : Site × List Out → Prop := fun r => r.1.LikedOnce
  have same : ∀ l, P (s, l) := fun _ => h
  have videos {s' : Site} (hv : s'.videos = s.videos) : s'.LikedOnce := fun w hw => h w (hv ▸ hw)
  cases c with
  | signIn req who name => exact videos rfl
  | signOut req m session => exact withSession_cases (P := P) same fun _ => videos rfl
  | create req m session title about visibility media =>
    refine withSession_cases (P := P) same fun _ => ?_
    show (s.create config _ _ m title about visibility media at_s).1.LikedOnce
    unfold create
    split
    · exact h
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact List.nodup_nil
      · exact h w hw
  | uploaded req m session v =>
    refine withSession_cases (P := P) same fun viewer => owned_cases (P := P) same fun w hw => ?_
    show (s.uploaded config req viewer at_s w).1.LikedOnce
    unfold uploaded
    split
    · unfold check
      dsimp only
      split
      · exact likedOnce_setVideo h (h w hw)
      · exact likedOnce_setVideo (x := { w with status := .checking req }) h (h w hw)
    · exact h
  | like req m session v on => exact withSession_cases (P := P) same fun _ => h
  | comment req m session v body => exact withSession_cases (P := P) same fun _ => h
  | uncomment req m session v c => exact withSession_cases (P := P) same fun _ => h
  | delete req m session v =>
    exact withSession_cases (P := P) same fun _ => owned_cases (P := P) same fun _ _ =>
      fun x hx => h x (List.mem_filter.mp hx).1
  | retry req m session v =>
    refine withSession_cases (P := P) same fun viewer => owned_cases (P := P) same fun w hw => ?_
    show (s.retry config req viewer w).1.LikedOnce
    unfold retry
    split
    · exact likedOnce_setVideo h (h w hw)
    · exact h
  | report req r signature =>
    show (s.report config req r signature).1.LikedOnce
    unfold report
    split
    · exact likedOnce_settle h r
    · exact h

theorem likedOnce_visit {s : Site} (h : s.LikedOnce) (v : Visit) : (s.visit config v).1.LikedOnce := by
  let P : Site × List Out → Prop := fun r => r.1.LikedOnce
  have same : ∀ l, P (s, l) := fun _ => h
  cases v with
  | like req viewer m v on =>
    exact seen_cases (P := P) same fun w hw => likedOnce_setVideo h (nodup_like (h w hw) m on)
  | comment req viewer m name v body =>
    refine seen_cases (P := P) same fun w hw => ?_
    show (s.comment config req viewer m name w body).1.LikedOnce
    unfold comment
    split
    · exact h
    · exact likedOnce_setVideo
        (x := { w with comments := w.comments ++ [{ id := s.nextComment, author := m, name, body }] })
        h (h w hw)
  | uncomment req viewer m v c =>
    refine seen_cases (P := P) same fun w hw => ?_
    show (s.uncomment req viewer m w c).1.LikedOnce
    unfold uncomment
    split
    · exact likedOnce_setVideo h (h w hw)
    · exact h

theorem likedOnce_unconfirmed {s : Site} (h : s.LikedOnce) {video : Video} (hv : video ∈ s.videos)
    (req : ReqId) (r : Reply) : (s.unconfirmed video req r).1.LikedOnce := by
  unfold unconfirmed
  split
  · exact likedOnce_setVideo h (h video hv)
  · exact h

theorem likedOnce_job {s : Site} (h : s.LikedOnce) (key : Key) (o : Outcome) :
    (s.job config key o).1.LikedOnce := by
  let P : Site × List Out → Prop := fun r => r.1.LikedOnce
  have same : ∀ l, P (s, l) := fun _ => h
  have found {w : Video} (hw : w ∈ s.videos) (size : Nat) : P (s.found config w size) :=
    likedOnce_setVideo h (h w hw)
  cases key with
  | check v req =>
    refine awaiting_cases (P := P) same fun w hw _ _ => ?_
    show (s.checked config w req o).1.LikedOnce
    unfold checked
    split
    · exact found hw _
    · exact likedOnce_unconfirmed h hw req _
    · split
      · exact found hw _
      · exact likedOnce_unconfirmed h hw req _
    all_goals first
      | exact likedOnce_unconfirmed h hw req _
      | exact h
  | expire v =>
    refine awaiting_cases (P := P) same fun w hw _ _ => ?_
    show (s.expired config w o).1.LikedOnce
    unfold expired
    split
    · exact found hw _
    · exact fun x hx => h x (List.mem_filter.mp hx).1
    · exact h
  | transcode r =>
    show (if o.givenUp then s.settle (.failed r) else s, ([] : List Out)).1.LikedOnce
    split
    · exact likedOnce_settle h _
    · exact h
  | delete v => exact h

theorem likedOnce_handle {s : Site} (h : s.LikedOnce) (i : Input) : (s.handle config i).1.LikedOnce := by
  cases i with
  | request c at_s => exact likedOnce_request config h c at_s
  | job key o => exact likedOnce_job config h key o
  | noticed _ => exact h
  | visit v => exact likedOnce_visit config h v

theorem likedOnce_recover {s : Site} (h : s.LikedOnce) : s.recover.1.LikedOnce := by
  intro w hw
  simp only [Site.recover, List.mem_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  split
  · exact h w' hw'
  · exact h w' hw'

end Site

/-- A like counts each member once: in every reachable state of the system, under every
environment model, no video's likes in any member's site name a member twice. -/
theorem likes_distinct (config : Config) (env : EnvModel fullSig) (m : Member) :
    (system config).Invariant env fun c => (c.state (.inr m) : Site).LikedOnce :=
  members_invariant (P := Site.LikedOnce) config (fun _ h => by simp at h)
    (fun _ i h => Site.likedOnce_handle config h i) (fun _ h => Site.likedOnce_recover h) env m
/-- So the count a video shows is the number of distinct members who like it. -/
theorem count_distinct {s : Site} (h : s.LikedOnce) {w : Video} (hw : w ∈ s.videos) :
    (s.card w).likes = w.likes.eraseDups.length := by
  simp [Site.card, eraseDups_of_nodup (h w hw)]

end Videos
