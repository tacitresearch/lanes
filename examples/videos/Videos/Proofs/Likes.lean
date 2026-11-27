/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.System
import Videos.Proofs.Confirmed

/-!
# A like counts each member once

A video's likes are the members who like it, and its count is how many they are
(`Site.card`). No input or start makes a member appear twice (`Site.likedOnce_handle`), so in
every reachable state of the system, under every environment model, each video's count is the
number of distinct members who like it (`likes_distinct`, `count_distinct`). Liking again
changes nothing, and taking a like back takes out the one there is.
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

theorem likedOnce_request {s : Site} (h : s.LikedOnce) (c : Command) :
    (s.request config c).1.LikedOnce := by
  let P : Site × List Out → Prop := fun r => r.1.LikedOnce
  have same : ∀ l, P (s, l) := fun _ => h
  have videos {s' : Site} (hv : s'.videos = s.videos) : s'.LikedOnce := fun w hw => h w (hv ▸ hw)
  cases c with
  | signIn req issuer subject name =>
    show (s.signIn config req issuer subject name).1.LikedOnce
    unfold signIn
    dsimp only
    split
    · exact videos rfl
    · split
      · exact h
      · exact videos rfl
  | signOut req m session => exact withSession_cases (P := P) same fun _ => videos rfl
  | create req m session title about visibility media at_s =>
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
    show (s.uploaded config req viewer w).1.LikedOnce
    unfold uploaded
    split
    · exact h
    · unfold check
      dsimp only
      split
      · exact likedOnce_setVideo h (h w hw)
      · exact likedOnce_setVideo (x := { w with status := .checking s.nextCall req }) h (h w hw)
  | watch req viewer v at_s =>
    show (s.watch req _ v at_s).1.LikedOnce
    rw [watch_fst]
    exact h
  | like req m session v on =>
    exact withSession_cases (P := P) same fun _ => seen_cases (P := P) same fun w hw =>
      likedOnce_setVideo h (nodup_like (h w hw) m on)
  | comment req m session v body =>
    refine withSession_cases (P := P) same fun viewer => seen_cases (P := P) same fun w hw => ?_
    show (s.comment config req viewer m w body).1.LikedOnce
    unfold comment
    split
    · exact h
    · exact likedOnce_setVideo
        (x := { w with comments := w.comments ++ [{ id := s.nextComment, author := m, body }] })
        h (h w hw)
  | uncomment req m session v c =>
    refine withSession_cases (P := P) same fun viewer => seen_cases (P := P) same fun w hw => ?_
    show (s.uncomment req viewer m w c).1.LikedOnce
    unfold uncomment
    split
    · exact likedOnce_setVideo h (h w hw)
    · exact h
  | delete req m session v =>
    exact withSession_cases (P := P) same fun _ => owned_cases (P := P) same fun _ _ =>
      fun x hx => h x (List.mem_filter.mp hx).1
  | feed => exact h
  | channel req viewer whose =>
    show (s.channel req _ whose).1.LikedOnce
    rw [channel_fst]
    exact h

theorem likedOnce_stored {s : Site} (h : s.LikedOnce) (call : Nat) (reply : Rpc.Reply StoreAnswer) :
    (s.stored config call reply).1.LikedOnce := by
  unfold stored
  split
  · next video hfind =>
    have hv := h video (List.mem_of_find?_eq_some hfind)
    split
    · unfold checked
      split
      · exact likedOnce_setVideo h hv
      · exact likedOnce_setVideo h hv
      · split
        · exact likedOnce_setVideo h hv
        · exact likedOnce_setVideo h hv
      · exact likedOnce_setVideo h hv
    · exact h
  · split
    · unfold deleteAnswered
      split
      · exact h
      · exact h
      · split
        · exact h
        · exact h
    · exact h

theorem likedOnce_handle {s : Site} (h : s.LikedOnce) (i : Input) : (s.handle config i).1.LikedOnce := by
  cases i with
  | request c => exact likedOnce_request config h c
  | store call reply => exact likedOnce_stored config h call reply

theorem likedOnce_recover {s : Site} (h : s.LikedOnce) : (s.recover config).1.LikedOnce := by
  intro w hw
  simp only [Site.recover, List.mem_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  split
  · exact h w' hw'
  · exact h w' hw'

end Site

/-- In every state the site's actor can reach, no video's likes name a member twice. -/
theorem likedOnce (config : Config) : (site config).Invariant Site.LikedOnce :=
  Actor.Inductive.invariant
    { init := fun _ h => by simp [site] at h
      step := fun s i h => by
        simpa [site] using Site.likedOnce_handle config h i
      recover := fun s h => by
        simpa [site] using Site.likedOnce_recover config h }

/-- A like counts each member once: in every reachable state of the system, under every
environment model, no video's likes name a member twice. -/
theorem likes_distinct (config : Config) (env : EnvModel sig) :
    (system config).Invariant env fun c => (c.state ()).LikedOnce :=
  System.invariant_of_actor (system config) () (likedOnce config) env

/-- So the count a video shows is the number of distinct members who like it. -/
theorem count_distinct {s : Site} (h : s.LikedOnce) {w : Video} (hw : w ∈ s.videos) :
    (s.card w).likes = w.likes.eraseDups.length := by
  simp [Site.card, eraseDups_of_nodup (h w hw)]

end Videos
