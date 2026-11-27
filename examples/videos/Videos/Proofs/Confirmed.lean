/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Proofs.Gone

/-!
# A video is shown only once the store confirmed its upload

In every run from the empty site, an output that shows a video comes after an output that asked
the store under some call whether the video's object is there, and after an input in which the
store answered that call `found` (`Site.listed_confirmed`). The browser's word is not enough,
and a check the store did not answer in time is not taken as found: the two seeded bugs of
`Config` (`trustBrowser`, `readyOnTimeout`) are exactly what the theorem assumes off, and the
checker finds each (`Videos.Check`).

The proof keeps, beside each video, the evidence for its status (`Evident`): a check out was
asked of the store; a ready video was asked about and found.
-/

set_option linter.unusedSectionVars false

namespace Videos

open Lanes

/-- The site asked the store, under `call`, whether the object of video `v` is there. -/
def Asked (outs : List Out) (call : Nat) (v : VideoId) : Prop :=
  ∃ deadline, Out.store ⟨call, deadline, .head v⟩ ∈ outs

/-- The store answered `call`: the object is there. -/
def Found (es : List Turn) (call : Nat) : Prop :=
  ∃ size, (Sum.inl (Input.store call (.answer (.found size))) : Turn) ∈ es

/-- The evidence for a video's status: a check out was asked of the store, and a ready video
was asked about, under a call the store answered `found`. -/
def Evident (es : List Turn) (outs : List Out) (w : Video) : Prop :=
  (∀ c r, w.status = .checking c r → Asked outs c w.id) ∧
    (w.status.isReady = true → ∃ call, Asked outs call w.id ∧ Found es call)

def Confirmed (es : List Turn) (outs : List Out) (s : Site) : Prop :=
  ∀ w ∈ s.videos, Evident es outs w

/-- The configuration without the seeded bugs. -/
structure Config.Honest (config : Config) : Prop where
  trustBrowser : config.trustBrowser = false
  readyOnTimeout : config.readyOnTimeout = false

theorem Evident.mono {es es' : List Turn} {outs outs' : List Out} {w : Video}
    (h : Evident es outs w) : Evident (es ++ es') (outs ++ outs') w := by
  refine ⟨fun c r hc => ?_, fun hr => ?_⟩
  · obtain ⟨d, hd⟩ := h.1 c r hc
    exact ⟨d, List.mem_append_left _ hd⟩
  · obtain ⟨call, ⟨d, hd⟩, ⟨size, hf⟩⟩ := h.2 hr
    exact ⟨call, ⟨d, List.mem_append_left _ hd⟩, ⟨size, List.mem_append_left _ hf⟩⟩

theorem Evident.pending {es : List Turn} {outs : List Out} {w : Video} (h : w.status = .pending) :
    Evident es outs w := by
  refine ⟨fun c r hc => ?_, fun hr => ?_⟩
  · rw [h] at hc; cases hc
  · rw [h] at hr; cases hr

theorem Evident.same {es : List Turn} {outs : List Out} {w x : Video} (h : Evident es outs w)
    (hid : x.id = w.id) (hst : x.status = w.status) : Evident es outs x := by
  refine ⟨fun c r hc => ?_, fun hr => ?_⟩
  · rw [hid]; exact h.1 c r (hst ▸ hc)
  · rw [hid]; exact h.2 (hst ▸ hr)

namespace Site

variable (config : Config)

theorem confirmed_setVideo {es : List Turn} {outs : List Out} {s : Site} {x : Video}
    (h : Confirmed es outs s) (hx : Evident es outs x) : Confirmed es outs (s.setVideo x) := by
  intro w hw
  simp only [setVideo, List.mem_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  split
  · exact hx
  · exact h w' hw'

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

variable {config}

/-- What one input or start must keep, for the histories `es` before it with the event added. -/
abbrev Keeps (es : List Turn) (outs : List Out) (r : Site × List Out) : Prop :=
  Confirmed es (outs ++ r.2) r.1

theorem keeps_same {es : List Turn} {outs : List Out} {s : Site} (h : Confirmed es outs s)
    (l : List Out) : Keeps es outs (s, l) :=
  fun w hw => by simpa using (h w hw).mono (es' := []) (outs' := l)

theorem keeps_request (hc : config.Honest) {es : List Turn} {outs : List Out} {s : Site}
    (h : Confirmed es outs s) (c : Command) (at_s : Nat) :
    Keeps es outs (s.request config c at_s) := by
  have same := keeps_same h
  have mono {l : List Out} : Confirmed es (outs ++ l) s := fun w hw => by
    simpa using (h w hw).mono (es' := []) (outs' := l)
  cases c with
  | signIn req issuer subject name =>
    show Keeps es outs (s.signIn config req issuer subject name at_s)
    unfold signIn
    dsimp only
    split
    · exact fun w hw => mono w hw
    · split
      · exact same _
      · exact fun w hw => mono w hw
  | signOut req m session =>
    exact withSession_cases same fun _ => fun w hw => mono w hw
  | create req m session title about visibility media =>
    refine withSession_cases same fun _ => ?_
    unfold create
    split
    · exact same _
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Evident.pending rfl
      · exact mono w hw
  | uploaded req m session v =>
    refine withSession_cases same fun viewer => owned_cases same fun w hw => ?_
    unfold uploaded
    split
    · exact same _
    · unfold check
      dsimp only
      simp only [hc.trustBrowser, Bool.false_eq_true, ↓reduceIte]
      refine confirmed_setVideo mono ⟨fun c r hst => ?_, fun hr => ?_⟩
      · cases hst
        exact ⟨config.store_ms, List.mem_append_right _ (List.mem_append_right _ (by simp))⟩
      · cases hr
  | watch req viewer v =>
    show Keeps es outs (s.watch req (s.viewer config.lifetime at_s viewer) v at_s)
    intro w hw
    rw [watch_fst] at hw
    exact mono w hw
  | like req m session v on =>
    exact withSession_cases same fun _ => seen_cases same fun w hw =>
      confirmed_setVideo mono ((mono w hw).same rfl rfl)
  | comment req m session v body =>
    refine withSession_cases same fun _ => seen_cases same fun w hw => ?_
    unfold comment
    split
    · exact same _
    · exact confirmed_setVideo mono ((mono w hw).same rfl rfl)
  | uncomment req m session v c =>
    refine withSession_cases same fun _ => seen_cases same fun w hw => ?_
    unfold uncomment
    split
    · exact confirmed_setVideo mono ((mono w hw).same rfl rfl)
    · exact same _
  | delete req m session v =>
    exact withSession_cases same fun _ => owned_cases same fun w _ =>
      fun x hx => mono x (List.mem_filter.mp hx).1
  | feed req viewer before => exact same _
  | channel req viewer whose =>
    show Keeps es outs (s.channel req (s.viewer config.lifetime at_s viewer) whose)
    intro w hw
    rw [channel_fst] at hw
    exact mono w hw

theorem keeps_stored (hc : config.Honest) {es : List Turn} {outs : List Out} {s : Site}
    (h : Confirmed es outs s) (call : Nat) (reply : Rpc.Reply StoreAnswer)
    (hin : (Sum.inl (Input.store call reply) : Turn) ∈ es) :
    Keeps es outs (s.stored config call reply) := by
  have same := keeps_same h
  have mono {l : List Out} : Confirmed es (outs ++ l) s := fun w hw => by
    simpa using (h w hw).mono (es' := []) (outs' := l)
  unfold stored
  split
  · next video hfind =>
    have hv := List.mem_of_find?_eq_some hfind
    have hchk := List.find?_some hfind
    split
    · next c waiter hst =>
      have hc' : c = call := by simpa [isChecking, hst] using hchk
      subst hc'
      unfold checked
      split
      · next size =>
        refine confirmed_setVideo mono ⟨fun c r hst' => (by cases hst'), fun _ => ?_⟩
        obtain ⟨d, hd⟩ := (h video hv).1 c waiter hst
        exact ⟨c, ⟨d, List.mem_append_left _ hd⟩, size, hin⟩
      · exact confirmed_setVideo mono (Evident.pending rfl)
      · simp only [hc.readyOnTimeout, Bool.false_eq_true, ↓reduceIte]
        exact confirmed_setVideo mono (Evident.pending rfl)
      · exact confirmed_setVideo mono (Evident.pending rfl)
    · exact same _
  · split
    · unfold deleteAnswered
      split
      · exact fun w hw => mono w hw
      · exact fun w hw => mono w hw
      · split
        · exact fun w hw => mono w hw
        · exact fun w hw => mono w hw
    · exact same _

theorem keeps_recover {es : List Turn} {outs : List Out} {s : Site} (h : Confirmed es outs s) :
    Keeps es outs (s.recover config) := by
  intro w hw
  simp only [Site.recover, List.mem_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  have e := (h w' hw').mono (es' := []) (outs' := (s.recover config).2)
  simp only [List.append_nil] at e
  split
  · exact Evident.pending rfl
  · exact e

theorem confirmed_step (hc : config.Honest) {es : List Turn} {outs : List Out} {s : Site}
    (h : Confirmed es outs s) (e : Turn) :
    Confirmed (es ++ [e]) (outs ++ (s.step config e).2) (s.step config e).1 := by
  have h' : Confirmed (es ++ [e]) outs s := fun w hw => by
    simpa using (h w hw).mono (es' := [e]) (outs' := [])
  cases e with
  | inl i =>
    cases i with
    | request c at_s => exact keeps_request hc h' c at_s
    | store call reply => exact keeps_stored hc h' call reply (by simp)
  | inr _ => exact keeps_recover h'

theorem confirmed_run_from (hc : config.Honest) (es : List Turn) {es₀ : List Turn}
    {outs₀ : List Out} {s : Site} (h : Confirmed es₀ outs₀ s) :
    Confirmed (es₀ ++ es) (outs₀ ++ (s.run config es).2) (s.run config es).1 := by
  induction es generalizing es₀ outs₀ s with
  | nil => simpa [run_nil] using h
  | cons e es ih =>
    have := ih (confirmed_step hc h e)
    rw [run_cons]
    simpa using this

theorem confirmed_run (hc : config.Honest) (es : List Turn) :
    Confirmed es (Site.run config {} es).2 (Site.run config {} es).1 := by
  simpa using confirmed_run_from hc es (es₀ := []) (outs₀ := []) (s := {}) (by simp [Confirmed])

variable (config)

/-- A video is shown only once the store confirmed its upload: in every run from the empty
site, an output that shows a video comes after an output that asked the store, under some call,
whether the video's object is there, and after the store's answer to that call: `found`. -/
theorem listed_confirmed (hc : config.Honest) (es : List Turn) (e : Turn) :
    ∀ o ∈ ((Site.run config {} es).1.step config e).2, ∀ c ∈ o.cards,
      ∃ call, Asked (Site.run config {} es).2 call c.id ∧ Found es call := by
  intro o ho c hc'
  obtain ⟨_, hshows⟩ := shows_step config _ e o ho
  obtain ⟨w, hw, rfl, hready, -⟩ := hshows c hc'
  exact (confirmed_run hc es w hw).2 hready

end Site

end Videos
