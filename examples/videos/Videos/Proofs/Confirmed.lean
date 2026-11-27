/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Proofs.Gone

/-!
# A video is shown only once the store confirmed its upload

In every run from the empty site, an output that shows a video comes after an input in which the
scheduler said that a job asking the store whether the video's object is there (a `HEAD`, by
the job's key: `Key.op`) succeeded with `found` (`Site.listed_confirmed`). The scheduler says a
job succeeded with an answer only in the step that takes that answer to one of the job's
attempts (`Schedule.succeeded_replied`), and every attempt is that job's call to the store
(`Videos.Web.storeCall`). The browser's word is not enough, and a check the store did not
answer in time is not taken as found: the two seeded bugs of `Config` (`trustBrowser`,
`readyOnTimeout`) are exactly what the theorem assumes off, and the checker finds each
(`Videos.Check`).

The proof keeps, beside each ready video, the evidence for its status (`Evident`).
-/

set_option linter.unusedSectionVars false

namespace Videos

open Lanes

/-- The scheduler said, in one of the turns, that the job of `key` succeeded: the store answered
`found`. -/
def Found (es : List Turn) (key : Key) : Prop :=
  ∃ size, (Sum.inl (Input.job key (.succeeded (.found size))) : Turn) ∈ es

/-- The evidence for a ready video: a job that asks the store about its object succeeded with
`found`. -/
def Evident (es : List Turn) (w : Video) : Prop :=
  w.status.isReady = true → ∃ key, key.op = .head w.id ∧ Found es key

def Confirmed (es : List Turn) (s : Site) : Prop :=
  ∀ w ∈ s.videos, Evident es w

/-- The configuration without the seeded bugs. -/
structure Config.Honest (config : Config) : Prop where
  trustBrowser : config.trustBrowser = false
  readyOnTimeout : config.readyOnTimeout = false

theorem Evident.mono {es es' : List Turn} {w : Video} (h : Evident es w) : Evident (es ++ es') w :=
  fun hr => by
    obtain ⟨key, hop, size, hf⟩ := h hr
    exact ⟨key, hop, size, List.mem_append_left _ hf⟩

theorem Evident.unready {es : List Turn} {w : Video} (h : w.status.isReady = false) :
    Evident es w :=
  fun hr => by simp [h] at hr

theorem Evident.same {es : List Turn} {w x : Video} (h : Evident es w)
    (hid : x.id = w.id) (hst : x.status = w.status) : Evident es x := by
  intro hr
  rw [hid]
  exact h (hst ▸ hr)

namespace Site

variable (config : Config)

theorem confirmed_setVideo {es : List Turn} {s : Site} {x : Video}
    (h : Confirmed es s) (hx : Evident es x) : Confirmed es (s.setVideo x) := by
  intro w hw
  simp only [setVideo, List.mem_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  split
  · exact hx
  · exact h w' hw'

theorem confirmed_filter {es : List Turn} {s : Site} (h : Confirmed es s) (p : Video → Bool) :
    Confirmed es { s with videos := s.videos.filter p } :=
  fun w hw => h w (List.mem_filter.mp hw).1

theorem withSession_cases {s : Site} {life : Auth.Lifetime} {at_s : Nat} {req : ReqId}
    {m : Member} {session : Sid} {f : Viewer → Site × List Out} {P : Site × List Out → Prop}
    (hs : ∀ l, P (s, l)) (hf : ∀ v, P (f v)) : P (s.withSession life at_s req m session f) := by
  unfold withSession
  split
  · exact hf _
  · exact hs _

theorem owned_cases {s : Site} {req : ReqId} {viewer : Viewer} {m : Member} {v : VideoId}
    {f : Video → Site × List Out} {P : Site × List Out → Prop} (hs : ∀ l, P (s, l))
    (hf : ∀ w ∈ s.videos, P (f w)) : P (s.owned req viewer m v f) := by
  unfold owned
  split
  · split
    · next hfind _ => exact hf _ (find?_mem hfind)
    · exact hs _
  · exact hs _

theorem seen_cases {s : Site} {req : ReqId} {viewer : Viewer} {m : Member} {v : VideoId}
    {f : Video → Site × List Out} {P : Site × List Out → Prop} (hs : ∀ l, P (s, l))
    (hf : ∀ w ∈ s.videos, P (f w)) : P (s.seen req viewer m v f) := by
  unfold seen
  split
  · split
    · next hfind _ => exact hf _ (find?_mem hfind)
    · exact hs _
  · exact hs _

theorem unready_cases {s : Site} {v : VideoId} {f : Video → Site × List Out}
    {P : Site × List Out → Prop} (hs : ∀ l, P (s, l))
    (hf : ∀ w ∈ s.videos, w.id = v → P (f w)) : P (s.unready v f) := by
  unfold unready
  split
  · next video hfind =>
    split
    · exact hs _
    · have hid : video.id = v := by simpa using List.find?_some hfind
      exact hf _ (find?_mem hfind) hid
  · exact hs _

variable {config}

/-- What one input or start must keep, for the turns `es` before it with the turn added. -/
abbrev Keeps (es : List Turn) (r : Site × List Out) : Prop := Confirmed es r.1

theorem keeps_request (hc : config.Honest) {es : List Turn} {s : Site} (h : Confirmed es s)
    (c : Command) (at_s : Nat) : Keeps es (s.request config c at_s) := by
  have same : ∀ l, Keeps es (s, l) := fun _ => h
  have videos {s' : Site} (hv : s'.videos = s.videos) : Confirmed es s' := fun w hw => h w (hv ▸ hw)
  cases c with
  | signIn req issuer subject name =>
    show Keeps es (s.signIn config req issuer subject name at_s)
    unfold signIn
    dsimp only
    split
    · exact videos rfl
    · split
      · exact h
      · exact videos rfl
  | signOut req m session =>
    exact withSession_cases same fun _ => videos rfl
  | create req m session title about visibility media =>
    refine withSession_cases same fun _ => ?_
    unfold create
    split
    · exact h
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Evident.unready rfl
      · exact h w hw
  | uploaded req m session v =>
    refine withSession_cases same fun viewer => owned_cases same fun w hw => ?_
    unfold uploaded
    split
    · exact h
    · unfold check
      dsimp only
      simp only [hc.trustBrowser, Bool.false_eq_true, ↓reduceIte]
      exact confirmed_setVideo h (Evident.unready rfl)
  | watch req viewer v =>
    show Keeps es (s.watch req (s.viewer config.lifetime at_s viewer) v at_s)
    rw [Keeps, watch_fst]
    exact h
  | like req m session v on =>
    exact withSession_cases same fun _ => seen_cases same fun w hw =>
      confirmed_setVideo h ((h w hw).same rfl rfl)
  | comment req m session v body =>
    refine withSession_cases same fun _ => seen_cases same fun w hw => ?_
    unfold comment
    split
    · exact h
    · exact confirmed_setVideo h ((h w hw).same rfl rfl)
  | uncomment req m session v c =>
    refine withSession_cases same fun _ => seen_cases same fun w hw => ?_
    unfold uncomment
    split
    · exact confirmed_setVideo h ((h w hw).same rfl rfl)
    · exact h
  | delete req m session v =>
    exact withSession_cases same fun _ => owned_cases same fun w _ => confirmed_filter h _
  | feed req viewer before => exact h
  | channel req viewer whose =>
    show Keeps es (s.channel req (s.viewer config.lifetime at_s viewer) whose)
    rw [Keeps, channel_fst]
    exact h

theorem keeps_unconfirmed {es : List Turn} {s : Site} (h : Confirmed es s) (video : Video)
    (req : ReqId) (r : Reply) : Keeps es (s.unconfirmed video req r) := by
  unfold unconfirmed
  split
  · exact confirmed_setVideo h (Evident.unready rfl)
  · exact h

theorem keeps_job (hc : config.Honest) {es : List Turn} {s : Site} (h : Confirmed es s)
    (key : Key) (o : Outcome) (hin : (Sum.inl (Input.job key o) : Turn) ∈ es) :
    Keeps es (s.job config key o) := by
  have same : ∀ l, Keeps es (s, l) := fun _ => h
  have found {w : Video} (hid : key.op = .head w.id) (size : Nat)
      (ho : o = .succeeded (.found size)) : Keeps es (s.found config w size) :=
    confirmed_setVideo h fun _ => ⟨key, hid, size, ho ▸ hin⟩
  cases key with
  | check v req =>
    refine unready_cases same fun w _ hid => ?_
    have hop : (Key.check v req).op = .head w.id := by simp [Key.op, hid]
    unfold checked
    split
    · next size => exact found hop size rfl
    · exact keeps_unconfirmed h w req _
    · simp only [hc.readyOnTimeout, Bool.false_eq_true, ↓reduceIte]
      exact keeps_unconfirmed h w req _
    all_goals first
      | exact keeps_unconfirmed h w req _
      | exact h
  | expire v =>
    refine unready_cases same fun w _ hid => ?_
    have hop : (Key.expire v).op = .head w.id := by simp [Key.op, hid]
    unfold expired
    split
    · next size => exact found hop size rfl
    · exact confirmed_filter h _
    · exact h
  | delete v => exact h

theorem keeps_recover {es : List Turn} {s : Site} (h : Confirmed es s) : Keeps es s.recover := by
  intro w hw
  simp only [Site.recover, List.mem_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  split
  · exact Evident.unready rfl
  · exact h w' hw'

theorem confirmed_step (hc : config.Honest) {es : List Turn} {s : Site}
    (h : Confirmed es s) (e : Turn) : Confirmed (es ++ [e]) (s.step config e).1 := by
  have h' : Confirmed (es ++ [e]) s := fun w hw => (h w hw).mono
  cases e with
  | inl i =>
    cases i with
    | request c at_s => exact keeps_request hc h' c at_s
    | job key o => exact keeps_job hc h' key o (by simp)
    | noticed _ => exact h'
  | inr _ => exact keeps_recover h'

theorem confirmed_run_from (hc : config.Honest) (es : List Turn) {es₀ : List Turn} {s : Site}
    (h : Confirmed es₀ s) : Confirmed (es₀ ++ es) (s.run config es).1 := by
  induction es generalizing es₀ s with
  | nil => simpa [run_nil] using h
  | cons e es ih =>
    have := ih (confirmed_step hc h e)
    rw [run_cons]
    simpa using this

theorem confirmed_run (hc : config.Honest) (es : List Turn) :
    Confirmed es (Site.run config {} es).1 := by
  simpa using confirmed_run_from hc es (es₀ := []) (s := {}) (by simp [Confirmed])

variable (config)

/-- A video is shown only once the store confirmed its upload: in every run from the empty
site, an output that shows a video comes after an input in which the scheduler said that a job
asking the store whether the video's object is there succeeded with `found`. -/
theorem listed_confirmed (hc : config.Honest) (es : List Turn) (e : Turn) :
    ∀ o ∈ ((Site.run config {} es).1.step config e).2, ∀ c ∈ o.cards,
      ∃ key, key.op = .head c.id ∧ Found es key := by
  intro o ho c hc'
  obtain ⟨_, hshows⟩ := shows_step config _ e o ho
  obtain ⟨w, hw, rfl, hready, -⟩ := hshows c hc'
  exact confirmed_run hc es w hw hready

end Site

end Videos
