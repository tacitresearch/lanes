/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Proofs.Shows

/-!
# Runs of the spec, and what keeps a video's id

A run is a sequence of inputs and starts of the actor, from any site: each input one call of
`Site.handle`, each start one of `Site.recover`, as the actor does them (`Videos.site`). Of
every input and start: the next id only grows, and every video after is one that was there
before, under its id, or the new one with the id `next` had (`Site.grows_handle`).
-/

set_option linter.unusedSectionVars false

namespace Videos

open Lanes

/-- An input, or a start of the actor. -/
abbrev Turn := Input ⊕ Unit

namespace Site

variable (config : Config)

def step (s : Site) : Turn → Site × List Out
  | .inl i => s.handle config i
  | .inr () => s.recover config

/-- The site after the turns, and every output they gave, in order. -/
def run (s : Site) : List Turn → Site × List Out
  | [] => (s, [])
  | e :: es => ((s.step config e).1.run es).1 |> fun s' =>
    (s', (s.step config e).2 ++ ((s.step config e).1.run es).2)

theorem run_nil (s : Site) : s.run config [] = (s, []) := rfl

theorem run_cons (s : Site) (e : Turn) (es : List Turn) :
    s.run config (e :: es) =
      (((s.step config e).1.run config es).1,
        (s.step config e).2 ++ ((s.step config e).1.run config es).2) := rfl

theorem run_append (s : Site) (a b : List Turn) :
    s.run config (a ++ b) =
      (((s.run config a).1.run config b).1, (s.run config a).2 ++ ((s.run config a).1.run config b).2) := by
  induction a generalizing s with
  | nil => simp [run_nil]
  | cons e a ih => simp [run_cons, ih]

theorem run_concat (s : Site) (es : List Turn) (e : Turn) :
    s.run config (es ++ [e]) =
      (((s.run config es).1.step config e).1,
        (s.run config es).2 ++ ((s.run config es).1.step config e).2) := by
  rw [run_append]
  simp [run_cons, run_nil]

/-! ## Ids -/

/-- The next id has not shrunk, and every video is one there before, under its id, or the new
one with the id `next` had. -/
def Grows (s s' : Site) : Prop :=
  s.next ≤ s'.next ∧ ∀ w ∈ s'.videos, (∃ w' ∈ s.videos, w'.id = w.id) ∨ (w.id = s.next ∧ s.next < s'.next)

theorem grows_refl (s : Site) : Grows s s :=
  ⟨Nat.le_refl _, fun w hw => .inl ⟨w, hw, rfl⟩⟩

theorem grows_videos {s s' : Site} (hnext : s'.next = s.next) (hv : s'.videos = s.videos) :
    Grows s s' :=
  ⟨Nat.le_of_eq hnext.symm, fun w hw => .inl ⟨w, hv ▸ hw, rfl⟩⟩

theorem grows_setVideo {s : Site} {x : Video} (hx : ∃ w ∈ s.videos, w.id = x.id) :
    Grows s (s.setVideo x) := by
  refine ⟨Nat.le_refl _, fun w hw => ?_⟩
  simp only [setVideo, List.mem_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  split
  · next h => exact .inl (by simpa using hx)
  · exact .inl ⟨w', hw', rfl⟩

theorem grows_filter (s : Site) (p : Video → Bool) :
    Grows s { s with videos := s.videos.filter p } :=
  ⟨Nat.le_refl _, fun w hw => .inl ⟨w, (List.mem_filter.mp hw).1, rfl⟩⟩

theorem find?_mem {s : Site} {v : VideoId} {w : Video} (h : s.find? v = some w) : w ∈ s.videos :=
  List.mem_of_find?_eq_some h

theorem grows_withSession {s : Site} {life : Auth.Lifetime} {at_s : Nat} {req : ReqId}
    {m : Member} {session : Sid}
    {f : Viewer → Site × List Out} (hf : ∀ v, Grows s (f v).1) :
    Grows s (s.withSession life at_s req m session f).1 := by
  unfold withSession
  split
  · exact hf _
  · exact grows_refl s

theorem grows_owned {s : Site} {req : ReqId} {viewer : Viewer} {m : Member} {v : VideoId}
    {f : Video → Site × List Out} (hf : ∀ w ∈ s.videos, Grows s (f w).1) :
    Grows s (s.owned req viewer m v f).1 := by
  unfold owned
  split
  · split
    · next hfind _ => exact hf _ (find?_mem hfind)
    · exact grows_refl s
  · exact grows_refl s

theorem grows_seen {s : Site} {req : ReqId} {viewer : Viewer} {m : Member} {v : VideoId}
    {f : Video → Site × List Out} (hf : ∀ w ∈ s.videos, Grows s (f w).1) :
    Grows s (s.seen req viewer m v f).1 := by
  unfold seen
  split
  · split
    · next hfind _ => exact hf _ (find?_mem hfind)
    · exact grows_refl s
  · exact grows_refl s

theorem grows_check (s : Site) (req : ReqId) (viewer : Viewer) {video : Video}
    (hv : video ∈ s.videos) : Grows s (s.check config req viewer video).1 := by
  unfold check
  dsimp only
  split
  · exact grows_setVideo ⟨video, hv, rfl⟩
  · have h := grows_setVideo (s := s) (x := { video with status := .checking s.nextCall req })
      ⟨video, hv, rfl⟩
    exact ⟨h.1, h.2⟩

theorem watch_fst (s : Site) (req : ReqId) (viewer : Viewer) (v : VideoId) (at_s : Nat) :
    (s.watch req viewer v at_s).1 = s := by
  unfold watch
  dsimp only
  split
  · split <;> rfl
  · rfl

theorem channel_fst (s : Site) (req : ReqId) (viewer : Viewer) (whose : Member) :
    (s.channel req viewer whose).1 = s := by
  unfold channel
  dsimp only
  split <;> rfl

theorem grows_request (s : Site) (c : Command) (at_s : Nat) :
    Grows s (s.request config c at_s).1 := by
  cases c with
  | signIn req issuer subject name =>
    show Grows s (s.signIn config req issuer subject name at_s).1
    unfold signIn
    dsimp only
    split
    · exact grows_videos rfl rfl
    · split
      · exact grows_refl s
      · exact grows_videos rfl rfl
  | signOut req m session =>
    show Grows s (s.withSession config.lifetime at_s req m session _).1
    exact grows_withSession fun _ => grows_videos rfl rfl
  | create req m session title about visibility media =>
    refine grows_withSession fun _ => ?_
    unfold create
    split
    · exact grows_refl s
    · refine ⟨Nat.le_succ _, fun w hw => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact .inr ⟨rfl, Nat.lt_succ_self _⟩
      · exact .inl ⟨w, hw, rfl⟩
  | uploaded req m session v =>
    refine grows_withSession fun _ => grows_owned fun w hw => ?_
    unfold uploaded
    split
    · exact grows_refl s
    · exact grows_check config s req _ hw
  | watch req viewer v =>
    show Grows s (s.watch req _ v at_s).1
    rw [watch_fst]
    exact grows_refl s
  | like req m session v on =>
    exact grows_withSession fun _ => grows_seen fun w hw => grows_setVideo ⟨w, hw, rfl⟩
  | comment req m session v body =>
    refine grows_withSession fun _ => grows_seen fun w hw => ?_
    unfold comment
    split
    · exact grows_refl s
    · have h := grows_setVideo (s := s)
        (x := { w with comments := w.comments ++ [{ id := s.nextComment, author := m, body }] })
        ⟨w, hw, rfl⟩
      exact ⟨h.1, h.2⟩
  | uncomment req m session v c =>
    refine grows_withSession fun _ => grows_seen fun w hw => ?_
    unfold uncomment
    split
    · exact grows_setVideo ⟨w, hw, rfl⟩
    · exact grows_refl s
  | delete req m session v =>
    refine grows_withSession fun _ => grows_owned fun w _ => ?_
    have h := grows_filter s (·.id != w.id)
    exact ⟨h.1, h.2⟩
  | feed => exact grows_refl s
  | channel req viewer whose =>
    show Grows s (s.channel req _ whose).1
    rw [channel_fst]
    exact grows_refl s

theorem grows_stored (s : Site) (call : Nat) (reply : Rpc.Reply StoreAnswer) :
    Grows s (s.stored config call reply).1 := by
  unfold stored
  split
  · next video hfind =>
    have hv := List.mem_of_find?_eq_some hfind
    split
    · unfold checked
      split
      · exact grows_setVideo ⟨video, hv, rfl⟩
      · exact grows_setVideo ⟨video, hv, rfl⟩
      · split
        · exact grows_setVideo ⟨video, hv, rfl⟩
        · exact grows_setVideo ⟨video, hv, rfl⟩
      · exact grows_setVideo ⟨video, hv, rfl⟩
    · exact grows_refl s
  · split
    · unfold deleteAnswered
      split
      · exact grows_videos rfl rfl
      · exact grows_videos rfl rfl
      · split
        · exact grows_videos rfl rfl
        · exact grows_videos rfl rfl
    · exact grows_refl s

theorem grows_handle (s : Site) (i : Input) : Grows s (s.handle config i).1 := by
  cases i with
  | request c at_s => exact grows_request config s c at_s
  | store call reply => exact grows_stored config s call reply

theorem grows_recover (s : Site) : Grows s (s.recover config).1 := by
  refine ⟨Nat.le_refl _, fun w hw => ?_⟩
  simp only [Site.recover, List.mem_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  split <;> exact .inl ⟨w', hw', rfl⟩

theorem grows_step (s : Site) (e : Turn) : Grows s (s.step config e).1 := by
  cases e with
  | inl i => exact grows_handle config s i
  | inr _ => exact grows_recover config s

/-- Every video's id is below the next one, so no video made later has it. -/
def Fresh (s : Site) : Prop := ∀ w ∈ s.videos, w.id < s.next

theorem fresh_init : Fresh {} := by simp [Fresh]

theorem Fresh.grows {s s' : Site} (h : Fresh s) (hg : Grows s s') : Fresh s' := by
  intro w hw
  rcases hg.2 w hw with ⟨w', hw', hid⟩ | ⟨hid, hlt⟩
  · exact hid ▸ Nat.lt_of_lt_of_le (h w' hw') hg.1
  · rw [hid]; exact hlt

theorem Fresh.run {s : Site} (h : Fresh s) (es : List Turn) : Fresh (s.run config es).1 := by
  induction es generalizing s with
  | nil => exact h
  | cons e es ih => exact ih (h.grows (grows_step config s e))

end Site

end Videos
