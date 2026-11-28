/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Proofs.Gone

/-!
# A video is shown only once the store confirmed its upload and the worker its transcode

Of every read over the sites of members, each the site of a run from the empty site: a video it
shows is in a site whose run has an input in which the scheduler said that a job asking the
store whether the video's upload is there (a `HEAD`, by the job's key: `Key.op`) succeeded with
`found` (`Site.listed_confirmed`), and a report of the worker that a round of the video's
transcode is done, whose signature is the worker's (`Site.listed_transcoded`). A read at a
boundary sees each member's site as the member's actor's run left it. The scheduler says a job succeeded with an answer only in the step
that takes that answer to one of the job's attempts (`Schedule.succeeded_replied`), and every
attempt is that job's call (`Videos.Web.storeCall`). The browser's word is not enough, a check
the store did not answer in time is not taken as found, and a report not signed with the
worker's key changes nothing: the three seeded bugs of `Config` (`trustBrowser`,
`readyOnTimeout`, `trustUnsigned`) are exactly what the theorems assume off, and the checker
finds each (`Videos.Check`).

A report changes only the video its round names (`Site.report_names`).

The proof keeps, beside each video, the evidence for its status (`Evident`).
-/

set_option linter.unusedSectionVars false

namespace Videos

open Lanes

/-- The scheduler said, in one of the turns, that the job of `key` succeeded: the store answered
`found`. -/
def Found (es : List Turn) (key : Key) : Prop :=
  ∃ size, (Sum.inl (Input.job key (.succeeded (.found size))) : Turn) ∈ es

/-- The worker reported, in one of the turns, that a round of video `v`'s transcode is done, with
a signature that checks under the worker's key. -/
def Transcoded (config : Config) (es : List Turn) (v : VideoId) : Prop :=
  ∃ req round signature at_s, round.video = v ∧
    (Sum.inl (Input.request (.report req (.done round) signature) at_s) : Turn) ∈ es ∧
    (Report.done round).signed config.workerKey signature = true

/-- The evidence for a video's status: once its upload is confirmed, a job that asks the store
about its upload succeeded with `found`; once it is ready, the worker said, signed, it is done. -/
def Evident (config : Config) (es : List Turn) (w : Video) : Prop :=
  (w.status.awaiting = false → ∃ key, key.op = .head w.id ∧ Found es key) ∧
    (w.status.isReady = true → Transcoded config es w.id)

def Confirmed (config : Config) (es : List Turn) (s : Site) : Prop :=
  ∀ w ∈ s.videos, Evident config es w

/-- The configuration without the seeded bugs. -/
structure Config.Honest (config : Config) : Prop where
  trustBrowser : config.trustBrowser = false
  readyOnTimeout : config.readyOnTimeout = false
  trustUnsigned : config.trustUnsigned = false

theorem Status.awaiting_of_isReady {st : Status} (h : st.isReady = true) : st.awaiting = false := by
  cases st <;> simp_all [Status.isReady, Status.awaiting]

variable {config : Config}

theorem Evident.mono {es es' : List Turn} {w : Video} (h : Evident config es w) :
    Evident config (es ++ es') w :=
  ⟨fun ha => by
    obtain ⟨key, hop, size, hf⟩ := h.1 ha
    exact ⟨key, hop, size, List.mem_append_left _ hf⟩,
   fun hr => by
    obtain ⟨req, round, sig, at_s, hv, hin, hs⟩ := h.2 hr
    exact ⟨req, round, sig, at_s, hv, List.mem_append_left _ hin, hs⟩⟩

theorem Evident.awaiting {es : List Turn} {w : Video} (h : w.status.awaiting = true) :
    Evident config es w :=
  ⟨fun ha => by simp [h] at ha, fun hr => by simp [Status.awaiting_of_isReady hr] at h⟩

theorem Evident.same {es : List Turn} {w x : Video} (h : Evident config es w)
    (hid : x.id = w.id) (hst : x.status = w.status) : Evident config es x := by
  rw [Evident, hid, hst]
  exact h

/-- A video whose upload was confirmed, moved to a status not ready. -/
theorem Evident.stays {es : List Turn} {w x : Video} (h : Evident config es w)
    (hid : x.id = w.id) (hw : w.status.awaiting = false) (hx : x.status.isReady = false) :
    Evident config es x :=
  ⟨fun _ => hid ▸ h.1 hw, fun hr => by simp [hx] at hr⟩

namespace Site

theorem confirmed_setVideo {es : List Turn} {s : Site} {x : Video}
    (h : Confirmed config es s) (hx : Evident config es x) : Confirmed config es (s.setVideo x) := by
  intro w hw
  simp only [setVideo, List.mem_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  split
  · exact hx
  · exact h w' hw'

theorem confirmed_filter {es : List Turn} {s : Site} (h : Confirmed config es s) (p : Video → Bool) :
    Confirmed config es { s with videos := s.videos.filter p } :=
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

theorem awaiting_cases {s : Site} {v : VideoId} {f : Video → Site × List Out}
    {P : Site × List Out → Prop} (hs : ∀ l, P (s, l))
    (hf : ∀ w ∈ s.videos, w.id = v → w.status.awaiting = true → P (f w)) : P (s.awaiting v f) := by
  unfold awaiting
  split
  · next video hfind =>
    split
    · next ha =>
      have hid : video.id = v := by simpa using List.find?_some hfind
      exact hf _ (find?_mem hfind) hid ha
    · exact hs _
  · exact hs _

theorem next_awaiting {r : Report} {st st' : Status} (h : r.next st = some st') :
    st.awaiting = false := by
  cases st <;> simp_all [Report.next, Status.awaiting]

theorem next_ready {r : Report} {st st' : Status} (h : r.next st = some st')
    (hr : st'.isReady = true) : ∃ round, r = .done round := by
  cases r with
  | done round => exact ⟨round, rfl⟩
  | failed round =>
    exfalso
    cases st <;> simp [Report.next] at h
    · obtain ⟨-, rfl⟩ := h
      simp [Status.isReady] at hr

/-- A report moves the video its round names, if it may; a done report it moves to ready only
with the evidence `hdone` gives. -/
theorem confirmed_settle {es : List Turn} {s : Site} (h : Confirmed config es s) (r : Report)
    (hdone : ∀ round, r = .done round → Transcoded config es round.video) :
    Confirmed config es (s.settle r) := by
  intro w hw
  simp only [settle, List.mem_map] at hw
  obtain ⟨video, hv, rfl⟩ := hw
  have hw := h video hv
  unfold Report.move
  split
  · next hid =>
    split
    · next status hnext =>
      refine ⟨fun _ => hw.1 (next_awaiting hnext), fun hr => ?_⟩
      obtain ⟨round, rfl⟩ := next_ready hnext hr
      simpa [hid, Report.round] using hdone round rfl
    · exact hw
  · exact hw

/-- What one input or start must keep, for the turns `es` before it with the turn added. -/
abbrev Keeps (config : Config) (es : List Turn) (r : Site × List Out) : Prop := Confirmed config es r.1

theorem keeps_report (hc : config.Honest) {es : List Turn} {s : Site} (h : Confirmed config es s)
    (req : ReqId) (r : Report) (signature : String) (at_s : Nat)
    (hin : (Sum.inl (Input.request (.report req r signature) at_s) : Turn) ∈ es) :
    Keeps config es (s.report config req r signature) := by
  unfold report
  split
  · next hsigned =>
    simp only [hc.trustUnsigned, Bool.false_or] at hsigned
    exact confirmed_settle h r fun round hr => by
      subst hr
      exact ⟨req, round, signature, at_s, rfl, hin, hsigned⟩
  · exact h

theorem keeps_request (hc : config.Honest) {es : List Turn} {s : Site} (h : Confirmed config es s)
    (c : Command) (at_s : Nat) (hin : (Sum.inl (Input.request c at_s) : Turn) ∈ es) :
    Keeps config es (s.request config c at_s) := by
  have same : ∀ l, Keeps config es (s, l) := fun _ => h
  have videos {s' : Site} (hv : s'.videos = s.videos) : Confirmed config es s' :=
    fun w hw => h w (hv ▸ hw)
  cases c with
  | signIn req who name => exact videos rfl
  | signOut req m session =>
    exact withSession_cases same fun _ => videos rfl
  | create req m session title about visibility media =>
    refine withSession_cases same fun _ => ?_
    unfold create
    split
    · exact h
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Evident.awaiting rfl
      · exact h w hw
  | uploaded req m session v =>
    refine withSession_cases same fun viewer => owned_cases same fun w hw => ?_
    unfold uploaded
    split
    · unfold check
      dsimp only
      simp only [hc.trustBrowser, Bool.false_eq_true, ↓reduceIte]
      exact confirmed_setVideo h (Evident.awaiting rfl)
    · exact h
  | like req m session v on => exact withSession_cases same fun _ => h
  | comment req m session v body => exact withSession_cases same fun _ => h
  | uncomment req m session v c => exact withSession_cases same fun _ => h
  | delete req m session v =>
    exact withSession_cases same fun _ => owned_cases same fun w _ => confirmed_filter h _
  | retry req m session v =>
    refine withSession_cases same fun _ => owned_cases same fun w hw => ?_
    unfold retry
    split
    · next size n hst =>
      exact confirmed_setVideo h ((h w hw).stays rfl (by simp [hst, Status.awaiting]) rfl)
    · exact h
  | report req r signature => exact keeps_report hc h req r signature at_s hin

theorem keeps_visit {es : List Turn} {s : Site} (h : Confirmed config es s) (v : Visit) :
    Keeps config es (s.visit config v) := by
  have same : ∀ l, Keeps config es (s, l) := fun _ => h
  cases v with
  | like req viewer m v on =>
    exact seen_cases same fun w hw => confirmed_setVideo h ((h w hw).same rfl rfl)
  | comment req viewer m name v body =>
    refine seen_cases same fun w hw => ?_
    unfold comment
    split
    · exact h
    · exact confirmed_setVideo h ((h w hw).same rfl rfl)
  | uncomment req viewer m v c =>
    refine seen_cases same fun w hw => ?_
    unfold uncomment
    split
    · exact confirmed_setVideo h ((h w hw).same rfl rfl)
    · exact h

theorem keeps_unconfirmed {es : List Turn} {s : Site} (h : Confirmed config es s) (video : Video)
    (req : ReqId) (r : Reply) : Keeps config es (s.unconfirmed video req r) := by
  unfold unconfirmed
  split
  · exact confirmed_setVideo h (Evident.awaiting rfl)
  · exact h

theorem keeps_job (hc : config.Honest) {es : List Turn} {s : Site} (h : Confirmed config es s)
    (key : Key) (o : Outcome) (hin : (Sum.inl (Input.job key o) : Turn) ∈ es) :
    Keeps config es (s.job config key o) := by
  have same : ∀ l, Keeps config es (s, l) := fun _ => h
  have found {w : Video} (hid : key.op = .head w.id) (size : Nat)
      (ho : o = .succeeded (.found size)) : Keeps config es (s.found config w size) :=
    confirmed_setVideo h ⟨fun _ => ⟨key, hid, size, ho ▸ hin⟩, fun hr => by simp [Status.isReady] at hr⟩
  cases key with
  | check v req =>
    refine awaiting_cases same fun w _ hid _ => ?_
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
    refine awaiting_cases same fun w _ hid _ => ?_
    have hop : (Key.expire v).op = .head w.id := by simp [Key.op, hid]
    unfold expired
    split
    · next size => exact found hop size rfl
    · exact confirmed_filter h _
    · exact h
  | transcode r =>
    show Keeps config es (if o.givenUp then s.settle (.failed r) else s, [])
    split
    · exact confirmed_settle h _ fun _ hr => by cases hr
    · exact h
  | delete v => exact h

theorem keeps_recover {es : List Turn} {s : Site} (h : Confirmed config es s) :
    Keeps config es s.recover := by
  intro w hw
  simp only [Site.recover, List.mem_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  split
  · exact Evident.awaiting rfl
  · exact h w' hw'

theorem confirmed_step (hc : config.Honest) {es : List Turn} {s : Site}
    (h : Confirmed config es s) (e : Turn) : Confirmed config (es ++ [e]) (s.step config e).1 := by
  have h' : Confirmed config (es ++ [e]) s := fun w hw => (h w hw).mono
  cases e with
  | inl i =>
    cases i with
    | request c at_s => exact keeps_request hc h' c at_s (by simp)
    | job key o => exact keeps_job hc h' key o (by simp)
    | noticed _ => exact h'
    | visit v => exact keeps_visit h' v
  | inr _ => exact keeps_recover h'

theorem confirmed_run_from (hc : config.Honest) (es : List Turn) {es₀ : List Turn} {s : Site}
    (h : Confirmed config es₀ s) : Confirmed config (es₀ ++ es) (s.run config es).1 := by
  induction es generalizing es₀ s with
  | nil => simpa [run_nil] using h
  | cons e es ih =>
    have := ih (confirmed_step hc h e)
    rw [run_cons]
    simpa using this

theorem confirmed_run (hc : config.Honest) (es : List Turn) :
    Confirmed config es (Site.run config {} es).1 := by
  simpa using confirmed_run_from hc es (es₀ := []) (s := {}) (by simp [Confirmed])

/-- What a read over the members' sites shows is a ready video of one of them, with the evidence
of that member's run. -/
theorem shown_evident (hc : config.Honest) (runs : List (Member × List Turn)) (r : Read) (at_s : Nat) :
    ∀ o ∈ (union (runs.map fun p => (p.1, (Site.run config {} p.2).1))).read config r at_s, ∀ c ∈ o.cards,
      ∃ p ∈ runs, ∃ w, w.id = c.id ∧ w.status.isReady = true ∧ Evident config p.2 w := by
  intro o ho c hc'
  obtain ⟨w, hw, rfl, hready, -⟩ := shows_read config _ r at_s o ho c hc'
  obtain ⟨t, ht, hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
  exact ⟨p, hp, w, rfl, hready, confirmed_run hc p.2 w (List.mem_filter.mp hw).1⟩

variable (config)

/-- A video is shown only once the store confirmed its upload: of every read over the sites of
members' runs from the empty site, a video it shows is in a run with an input in which the
scheduler said that a job asking the store whether the video's upload is there succeeded with
`found`. -/
theorem listed_confirmed (hc : config.Honest) (runs : List (Member × List Turn)) (r : Read) (at_s : Nat) :
    ∀ o ∈ (union (runs.map fun p => (p.1, (Site.run config {} p.2).1))).read config r at_s, ∀ c ∈ o.cards,
      ∃ p ∈ runs, ∃ key, key.op = .head c.id ∧ Found p.2 key := by
  intro o ho c hc'
  obtain ⟨p, hp, w, hid, hready, hw⟩ := shown_evident hc runs r at_s o ho c hc'
  exact ⟨p, hp, hid ▸ hw.1 (Status.awaiting_of_isReady hready)⟩

/-- A video is listed as ready only after a done report for it whose signature checks: of every
read over the sites of members' runs from the empty site, a video it shows is in a run with a
request in which the worker reported a round of the video's transcode done, with a signature
that checks under the worker's key. -/
theorem listed_transcoded (hc : config.Honest) (runs : List (Member × List Turn)) (r : Read) (at_s : Nat) :
    ∀ o ∈ (union (runs.map fun p => (p.1, (Site.run config {} p.2).1))).read config r at_s, ∀ c ∈ o.cards,
      ∃ p ∈ runs, Transcoded config p.2 c.id := by
  intro o ho c hc'
  obtain ⟨p, hp, w, hid, hready, hw⟩ := shown_evident hc runs r at_s o ho c hc'
  exact ⟨p, hp, hid ▸ hw.2 hready⟩

theorem settle_filter (s : Site) (r : Report) :
    (s.settle r).videos.filter (·.id != r.round.video) = s.videos.filter (·.id != r.round.video) := by
  simp only [settle]
  induction s.videos with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x.id = r.round.video
    · simp [Report.move_id, hx, ih]
    · have hm : r.move x = x := by simp [Report.move, hx]
      simp [hm, hx, ih]

/-- A report changes only the video its round names: every other video, every channel and every
count is as it was, whatever the report and its signature. -/
theorem report_names (s : Site) (req : ReqId) (r : Report) (signature : String) (at_s : Nat) :
    let s' := (s.handle config (.request (.report req r signature) at_s)).1
    s'.channels = s.channels ∧ s'.next = s.next ∧ s'.nextComment = s.nextComment ∧
      s'.videos.filter (·.id != r.round.video) = s.videos.filter (·.id != r.round.video) := by
  simp only [handle, request, report]
  split
  · exact ⟨rfl, rfl, rfl, settle_filter s r⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

end Site

end Videos
