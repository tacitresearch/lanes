/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.ObjectStore
public import Lanes.Outside.Events
public import Lanes.Proof.List.Basic

/-!
# A transcode worker

A service that turns an upload into what a page plays. It is given a job: a source key in an
object store and the keys to write, a playable rendition and a thumbnail. It reads the source,
writes the targets, and later reports the job done or failed with a webhook, as video pipelines
do (a worker of one's own, or a vendor's). The job is sent by a call under its id (rule 3.4): a
repeat of an id is the same job. The call's answer says only that the worker took the job, or
nothing; what became of it comes later, as a report.

`server made honest` is the worker and the object store it writes to, as one `Rpc.Server`: the
store's calls are `ObjectStore.server`'s, and a job's writes are the store's writes too. From
the moment a job is sent, each of its writes may land at any moment, or never, as a write
granted to someone else does (`ObjectStore.Request.granted`); a done report says they have
landed. `service` delivers each report late, again, or never (`Events.bounded`).

**The honesty assumption.** An honest worker (`honest`) reports a job done only if it was sent
the job, names the job's targets as what it wrote, could read the source (the store may hold an
object there), and has written the targets. Honest or not, it reports each job one way: a done
and a failed report of one job are never both delivered. Without honesty the worker may report
done for a job it was never sent, name any keys, and have written nothing. A caller trusts a
report only if it is signed with a key it shares with the worker alone: such a report is the
worker's, under the assumption `TRUSTED.md` makes of HMAC-SHA-256. A report not signed so is
anyone's, and is not this model's to allow.

Proved, in every run the model allows: under honesty, a done report names a job that was sent,
and the job's targets (`done_given`); honest or not, two reports of one job are the same report
(`reports_agree`), so at most one report counts for a job, however often it is delivered.
-/

@[expose] public section

namespace Lanes.Transcode

lanes_data structure Job (J K : Type) where
  id : J
  source : K
  /-- The keys the worker writes: a playable rendition and a thumbnail, in the order the caller
  names them. -/
  targets : List K
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Report (J K : Type) where
  | done (job : J) (written : List K)
  | failed (job : J)
  deriving DecidableEq, Repr, Hashable, Codable

def Report.job {J K : Type} : Report J K → J
  | .done job _ | .failed job => job

inductive Request (J K V : Type) where
  | store (r : ObjectStore.Request K V)
  | start (job : Job J K)
  deriving DecidableEq, Repr, Hashable

inductive Answer (V : Type) where
  | store (a : ObjectStore.Answer V)
  /-- The worker took the job. -/
  | accepted
  /-- An error, which may have come after the worker took the job. -/
  | refused
  deriving DecidableEq, Repr, Hashable

structure State (J K V : Type) where
  store : ObjectStore.State K V
  /-- Every job sent, once each by id, with the call that first sent it. -/
  jobs : List (Nat × Job J K)
  /-- The calls that sent a job and are not answered. -/
  starts : List Nat
  /-- The first report of each job: the one that counts. -/
  reports : List (Report J K)
  deriving DecidableEq, Repr, Hashable

variable {J K V : Type} [DecidableEq J] [DecidableEq K] [DecidableEq V]

/-- The write of `call` to `key` has landed, leaving what the worker made. -/
def landOne (made : V) (d : ObjectStore.State K V) (call : Nat) (key : K) : ObjectStore.State K V :=
  let mine (p : ObjectStore.Pending K V) : Bool := p.call == call && decide (p.request.key = key)
  match d.open_.find? mine with
  | some p =>
    { d with
      open_ := (d.open_.filter (!mine ·)).map fun q =>
        if q.request.key = key then { q with overlaps := ObjectStore.insertNew (some made) q.overlaps }
        else q
      settled := (key, some made :: p.overlaps) :: d.settled.filter (·.1 != key) }
  | none => d

/-- Every write of the job first sent by `call` has landed. -/
def land (made : V) (d : ObjectStore.State K V) (call : Nat) (targets : List K) :
    ObjectStore.State K V :=
  targets.foldl (fun d key => landOne made d call key) d

def receive (made : V) (d : State J K V) (call : Rpc.Call (Request J K V)) : State J K V :=
  match call.request with
  | .store r => { d with store := ObjectStore.server.receive d.store ⟨call.id, call.deadline_ms, r⟩ }
  | .start job =>
    if d.jobs.any (·.2.id == job.id) then { d with starts := call.id :: d.starts }
    else
      { d with
        starts := call.id :: d.starts
        jobs := (call.id, job) :: d.jobs
        store := job.targets.foldl
          (fun s key => ObjectStore.server.receive s ⟨call.id, 0, .granted key made⟩) d.store }

def answer (d : State J K V) (call : Nat) : Answer V → Option (State J K V)
  | .store a => (ObjectStore.server.answer d.store call a).map ({ d with store := · })
  | .accepted | .refused =>
    if call ∈ d.starts then some { d with starts := d.starts.erase call } else none

/-- What a done report of `job` may do: an honest worker's needs the job sent, its targets
named, its source readable, and lands its writes. -/
def finish (made : V) (honest : Bool) (d : State J K V) (job : J) (written : List K) :
    Option (State J K V) :=
  match d.jobs.find? (·.2.id == job) with
  | some (call, g) =>
    if g.targets = written ∧ (d.store.possible g.source).any Option.isSome then
      some { d with store := land made d.store call g.targets }
    else if honest then none else some d
  | none => if honest then none else some d

def event (made : V) (honest : Bool) (d : State J K V) (r : Report J K) : Option (State J K V) :=
  if d.reports.any (·.job == r.job) then none
  else
    let d' := { d with reports := r :: d.reports }
    match r with
    | .done job written => finish made honest d' job written
    | .failed job => if honest && !d.jobs.any (·.2.id == job) then none else some d'

def server (made : V) (honest : Bool) : Rpc.Server (State J K V) (Request J K V) (Answer V) (Report J K) where
  init := ⟨ObjectStore.server.init, [], [], []⟩
  receive := receive made
  answer := answer
  event := event made honest

/-- The worker and its store, its reports each delivered at most `maxDeliveries` times. -/
def service (maxDeliveries : Nat) (made : V) (honest : Bool) :
    Rpc.Server (Events.State (State J K V) (Report J K)) (Request J K V) (Answer V) (Report J K) :=
  Events.bounded maxDeliveries (server made honest)

/-! ## What every run keeps -/

theorem receive_reports (made : V) (d : State J K V) (call : Rpc.Call (Request J K V)) :
    (receive made d call).reports = d.reports := by
  unfold receive
  split
  · rfl
  · split <;> rfl

theorem receive_given (made : V) (d : State J K V) (call : Rpc.Call (Request J K V)) :
    (receive made d call).jobs = d.jobs ∨
      ∃ job, call.request = .start job ∧ (receive made d call).jobs = (call.id, job) :: d.jobs := by
  unfold receive
  split
  · exact .inl rfl
  · next job h =>
    split
    · exact .inl rfl
    · exact .inr ⟨job, h, rfl⟩

omit [DecidableEq J] in
theorem answer_keeps {d d' : State J K V} {call : Nat} {a : Answer V}
    (h : answer d call a = some d') : d'.reports = d.reports ∧ d'.jobs = d.jobs := by
  unfold answer at h
  split at h
  · obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, rfl⟩
  all_goals
    split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h

theorem finish_keeps {made : V} {honest : Bool} {d d' : State J K V} {job : J} {written : List K}
    (h : finish made honest d job written = some d') :
    d'.reports = d.reports ∧ d'.jobs = d.jobs ∧
      (honest = true → ∃ call g, (call, g) ∈ d.jobs ∧ g.id = job ∧ g.targets = written) := by
  unfold finish at h
  split at h
  · next call g hfind =>
    have hmem := List.mem_of_find?_eq_some hfind
    have hid : g.id = job := by simpa using List.find?_some hfind
    split at h
    · next hok => cases h; exact ⟨rfl, rfl, fun _ => ⟨call, g, hmem, hid, hok.1⟩⟩
    · split at h
      · cases h
      · next hh => cases h; exact ⟨rfl, rfl, fun h' => absurd h' hh⟩
  · split at h
    · cases h
    · next hh => cases h; exact ⟨rfl, rfl, fun h' => absurd h' hh⟩

/-- What a report the worker may give does to what it remembers: it is the first report of its
job, it is remembered, and the jobs sent stay; an honest worker's done report names a job sent,
and its targets. -/
theorem event_keeps {made : V} {honest : Bool} {d d' : State J K V} {r : Report J K}
    (h : event made honest d r = some d') :
    r.job ∉ d.reports.map Report.job ∧ d'.reports = r :: d.reports ∧ d'.jobs = d.jobs ∧
      (honest = true → ∀ job written, r = .done job written →
        ∃ call g, (call, g) ∈ d.jobs ∧ g.id = job ∧ g.targets = written) := by
  unfold event at h
  split at h
  · cases h
  · next hnew =>
    have hnot : r.job ∉ d.reports.map Report.job := by
      simp only [List.any_eq_true, beq_iff_eq, not_exists, not_and] at hnew
      simpa using hnew
    refine ⟨hnot, ?_⟩
    split at h
    · next job written =>
      obtain ⟨h1, h2, h3⟩ := finish_keeps h
      exact ⟨h1, h2, fun hh job' written' he => by
        cases he
        exact h3 hh⟩
    · split at h
      · cases h
      · cases h
        exact ⟨rfl, rfl, fun _ _ _ he => by cases he⟩

variable {σ : Signature}

/-- What every run the model allows keeps: each report delivered is the first report of its
job, which the worker remembers, once each job; each job it was sent was sent by a call of the
run; and, with `honest`, a done report names one of them, and its targets. -/
structure Inv (port : Rpc.Port σ (Request J K V) (Answer V) (Report J K)) (honest : Bool)
    (events : List (Event σ)) (d : Rpc.State (Events.State (State J K V) (Report J K))) : Prop where
  delivered : ∀ x r, Event.input x ∈ events → port.reported x = some r → r ∈ d.server.inner.reports
  counted : ∀ r, 0 < Events.count d.server.delivered r → r ∈ d.server.inner.reports
  once : (d.server.inner.reports.map Report.job).Nodup
  sent : ∀ call job, (call, job) ∈ d.server.inner.jobs →
    ∃ out c, Event.output out ∈ events ∧ port.called out = some c ∧ c.request = .start job
  named : honest = true → ∀ job written, Report.done job written ∈ d.server.inner.reports →
    ∃ call g, (call, g) ∈ d.server.inner.jobs ∧ g.id = job ∧ g.targets = written

omit [DecidableEq J] [DecidableEq K] [DecidableEq V] in
theorem count_bump_pos [DecidableEq J] [DecidableEq K] {delivered : List (Report J K × Nat)}
    {e r : Report J K} (h : 0 < Events.count (Events.bump delivered e) r) :
    r = e ∨ 0 < Events.count delivered r := by
  by_cases hre : r = e
  · exact .inl hre
  · rw [Events.count_bump_of_ne _ hre] at h
    exact .inr h

private theorem inv_input (port : Rpc.Port σ (Request J K V) (Answer V) (Report J K))
    (maxDeliveries : Nat) (made : V) (honest : Bool) {events : List (Event σ)}
    {d d' : Rpc.State (Events.State (State J K V) (Report J K))} {x : σ.In}
    (hinv : Inv port honest events d)
    (hallow : (Rpc.outside port (service maxDeliveries made honest)).allow d x = some d') :
    Inv port honest (events ++ [.input x]) d' := by
  have mono : ∀ out, Event.output out ∈ events → Event.output out ∈ events ++ [.input x] :=
    fun out h => List.mem_append_left _ h
  cases hrep : port.reported x with
  | some e =>
    obtain ⟨s, hs, rfl⟩ := Rpc.allow_reported hrep hallow
    simp only [service, Events.bounded] at hs
    split at hs
    · split at hs
      · next hpos =>
        cases hs
        refine ⟨?_, ?_, hinv.once, fun call job hj => ?_, hinv.named⟩
        · intro y r hy hr
          rcases List.mem_append.mp hy with hy | hy
          · exact hinv.delivered y r hy hr
          · simp only [List.mem_singleton, Event.input.injEq] at hy
            subst hy
            rw [hrep] at hr
            cases hr
            exact hinv.counted e hpos
        · intro r hr
          rcases count_bump_pos hr with rfl | hr
          · exact hinv.counted r hpos
          · exact hinv.counted r hr
        · obtain ⟨out, c, ho, hc, hreq⟩ := hinv.sent call job hj
          exact ⟨out, c, mono out ho, hc, hreq⟩
      · obtain ⟨inner, hinner, rfl⟩ := Option.map_eq_some_iff.mp hs
        obtain ⟨hnot, hreports, hgiven, hnamed⟩ := event_keeps hinner
        refine ⟨?_, ?_, ?_, fun call job hj => ?_, ?_⟩
        · intro y r hy hr
          simp only [hreports, List.mem_cons]
          rcases List.mem_append.mp hy with hy | hy
          · exact .inr (hinv.delivered y r hy hr)
          · simp only [List.mem_singleton, Event.input.injEq] at hy
            subst hy
            rw [hrep] at hr
            exact .inl (Option.some.inj hr).symm
        · intro r hr
          simp only [hreports, List.mem_cons]
          rcases count_bump_pos hr with rfl | hr
          · exact .inl rfl
          · exact .inr (hinv.counted r hr)
        · simp only [hreports, List.map_cons, List.nodup_cons]
          exact ⟨hnot, hinv.once⟩
        · rw [hgiven] at hj
          obtain ⟨out, c, ho, hc, hreq⟩ := hinv.sent call job hj
          exact ⟨out, c, mono out ho, hc, hreq⟩
        · intro hh job written hmem
          simp only [hreports, List.mem_cons] at hmem
          rw [hgiven]
          rcases hmem with he | hmem
          · exact hnamed hh job written he.symm
          · exact hinv.named hh job written hmem
    · cases hs
  | none =>
    have hsame : d'.server.inner.reports = d.server.inner.reports ∧
        d'.server.inner.jobs = d.server.inner.jobs ∧ d'.server.delivered = d.server.delivered := by
      rcases Rpc.allow_not_reported hrep hallow with h | ⟨_, _, _, hans⟩
      · rw [h]; exact ⟨rfl, rfl, rfl⟩
      · simp only [service, Events.bounded] at hans
        obtain ⟨s, hs, hd⟩ := Option.map_eq_some_iff.mp hans
        rw [← hd]
        obtain ⟨h1, h2⟩ := answer_keeps hs
        exact ⟨h1, h2, rfl⟩
    obtain ⟨hr, hg, hdel⟩ := hsame
    refine ⟨?_, ?_, ?_, fun call job hj => ?_, ?_⟩
    · intro y r hy hr'
      rw [hr]
      rcases List.mem_append.mp hy with hy | hy
      · exact hinv.delivered y r hy hr'
      · simp only [List.mem_singleton, Event.input.injEq] at hy
        subst hy
        rw [hrep] at hr'
        cases hr'
    · intro r h
      rw [hr]
      rw [hdel] at h
      exact hinv.counted r h
    · rw [hr]; exact hinv.once
    · rw [hg] at hj
      obtain ⟨out, c, ho, hc, hreq⟩ := hinv.sent call job hj
      exact ⟨out, c, mono out ho, hc, hreq⟩
    · rw [hr, hg]; exact hinv.named

private theorem inv_output (port : Rpc.Port σ (Request J K V) (Answer V) (Report J K))
    (maxDeliveries : Nat) (made : V) (honest : Bool) {events : List (Event σ)}
    {d : Rpc.State (Events.State (State J K V) (Report J K))} {out : σ.Out}
    (hinv : Inv port honest events d) :
    Inv port honest (events ++ [.output out])
      ((Rpc.outside port (service maxDeliveries made honest)).observe d out) := by
  have mono : ∀ o, Event.output o ∈ events → Event.output o ∈ events ++ [.output out] :=
    fun o h => List.mem_append_left _ h
  have hdel : ∀ y, Event.input y ∈ events ++ [.output out] → Event.input y ∈ events := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hy
    · simp at hy
  simp only [Rpc.outside]
  split
  · next call hcall =>
    simp only [service, Events.bounded, server]
    refine ⟨?_, ?_, ?_, fun c job hj => ?_, ?_⟩
    · intro y r hy hr
      rw [receive_reports]
      exact hinv.delivered y r (hdel y hy) hr
    · intro r hr
      rw [receive_reports]
      exact hinv.counted r hr
    · rw [receive_reports]; exact hinv.once
    · rcases receive_given made d.server.inner call with hg | ⟨job', hreq, hg⟩
      · rw [hg] at hj
        obtain ⟨o, c', ho, hc, hreq⟩ := hinv.sent c job hj
        exact ⟨o, c', mono o ho, hc, hreq⟩
      · rw [hg] at hj
        rcases List.mem_cons.mp hj with he | hj
        · obtain ⟨-, rfl⟩ := Prod.mk.inj he
          exact ⟨out, call, by simp, hcall, hreq⟩
        · obtain ⟨o, c', ho, hc, hreq⟩ := hinv.sent c job hj
          exact ⟨o, c', mono o ho, hc, hreq⟩
    · intro hh job written hmem
      rw [receive_reports] at hmem
      obtain ⟨c, g, hgv, hid, ht⟩ := hinv.named hh job written hmem
      refine ⟨c, g, ?_, hid, ht⟩
      rcases receive_given made d.server.inner call with hg | ⟨_, _, hg⟩
      · rw [hg]; exact hgv
      · rw [hg]; exact List.mem_cons_of_mem _ hgv
  · exact ⟨fun y r hy hr => hinv.delivered y r (hdel y hy) hr, hinv.counted, hinv.once,
      fun c job hj => by
        obtain ⟨o, c', ho, hc, hreq⟩ := hinv.sent c job hj
        exact ⟨o, c', mono o ho, hc, hreq⟩, hinv.named⟩

theorem inv_after (port : Rpc.Port σ (Request J K V) (Answer V) (Report J K))
    (maxDeliveries : Nat) (made : V) (honest : Bool) {events : List (Event σ)}
    {d : Rpc.State (Events.State (State J K V) (Report J K))}
    (h : (Rpc.outside port (service maxDeliveries made honest)).after events = some d) :
    Inv port honest events d := by
  refine (Rpc.outside port (service maxDeliveries made honest)).after_induction
    (P := Inv port honest) ⟨by simp, ?_, by simp [Rpc.outside, service, Events.bounded, server],
      by simp [Rpc.outside, service, Events.bounded, server],
      by simp [Rpc.outside, service, Events.bounded, server]⟩ ?_ h
  · intro r hr
    simp [Rpc.outside, service, Events.bounded, Events.count] at hr
  · intro events d event d' hinv hsee
    cases event with
    | input x => exact inv_input port maxDeliveries made honest hinv hsee
    | output out =>
      simp only [Outside.see, Option.some.injEq] at hsee
      subst hsee
      exact inv_output port maxDeliveries made honest hinv
    | _ =>
      simp only [Outside.see, Option.some.injEq] at hsee
      subst hsee
      exact ⟨fun y r hy hr => hinv.delivered y r (by simpa using hy) hr, hinv.counted, hinv.once,
        fun c job hj => by
          obtain ⟨o, c', ho, hc, hreq⟩ := hinv.sent c job hj
          exact ⟨o, c', List.mem_append_left _ ho, hc, hreq⟩, hinv.named⟩

/-- At most one report counts for a job: in every run the model allows, honest or not, two
reports delivered for one job are the same report, however often each is delivered. -/
theorem reports_agree (port : Rpc.Port σ (Request J K V) (Answer V) (Report J K))
    (maxDeliveries : Nat) (made : V) (honest : Bool) {events : List (Event σ)}
    {d : Rpc.State (Events.State (State J K V) (Report J K))}
    (h : (Rpc.outside port (service maxDeliveries made honest)).after events = some d)
    {x y : σ.In} {r r' : Report J K} (hx : Event.input x ∈ events) (hy : Event.input y ∈ events)
    (hr : port.reported x = some r) (hr' : port.reported y = some r') (hjob : r.job = r'.job) :
    r = r' :=
  let hinv := inv_after port maxDeliveries made honest h
  eq_of_mem_of_nodup_map hinv.once (hinv.delivered x r hx hr) (hinv.delivered y r' hy hr') hjob

/-- An honest worker's done report names a job that was sent, and its targets: in every run the
model allows, a done report delivered for `job` naming `written` comes with a call of the run
that sent a job of that id whose targets are `written`. -/
theorem done_given (port : Rpc.Port σ (Request J K V) (Answer V) (Report J K))
    (maxDeliveries : Nat) (made : V) {events : List (Event σ)}
    {d : Rpc.State (Events.State (State J K V) (Report J K))}
    (h : (Rpc.outside port (service maxDeliveries made true)).after events = some d)
    {x : σ.In} {job : J} {written : List K} (hx : Event.input x ∈ events)
    (hr : port.reported x = some (.done job written)) :
    ∃ out c g, Event.output out ∈ events ∧ port.called out = some c ∧
      c.request = .start g ∧ g.id = job ∧ g.targets = written := by
  have hinv := inv_after port maxDeliveries made true h
  obtain ⟨call, g, hg, hid, ht⟩ :=
    hinv.named rfl job written (hinv.delivered x _ hx hr)
  obtain ⟨out, c, ho, hc, hreq⟩ := hinv.sent call g hg
  exact ⟨out, c, g, ho, hc, hreq, hid, ht⟩

end Lanes.Transcode
