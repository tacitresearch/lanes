/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Db.JobsSound
public import Lanes.Db.Worker
public import Lanes.Proof.Outputs

/-!
What the worker (`Lanes/Db/Worker.lean`) does beside the store's model and a service's, in every
run, under every environment model (lost, repeated and reordered messages, crashes of the
worker, restarts of the process), with the application's transactions running on the same
database at any moment:

- **No effect is sent for a transaction that did not commit** (`Worker.committed_only`). Every
  attempt the worker hands to an adapter is of a job, with that job's work, in every database
  the store may hold after the run, also once any call still outstanding or lost takes effect.
  A transaction of the application whose `COMMIT` was lost may or may not have taken effect;
  the worker performs its effect only once a claim, a transaction that committed after it, has
  read it.
- **Each effect takes effect at most once, with a receiver that honours idempotency keys**
  (`Worker.once_each`). Every attempt is under its job's id (`Worker.runPort`), however often
  it is made: after a lost answer, a lease that ran out, a restart. Behind
  `Idempotent.server`, no two effects the service may have had are under one job.

What the store must be given: an application whose transactions keep the table
(`Jobs.Queue.Keeps`: they may add jobs, and leave those there alone), as `enqueue` does
(`Jobs.Queue.enqueue_keeps`), and a start whose table has no id twice with two works.

The worker attempts every job it is given: each job a committed claim answers is handed over in
the step that reads the answer (`Worker.stored_runs`). With the facts of
`Lanes/Db/JobsSound.lean` (a claim short of its limit takes every job due, `Queue.claim_takes`;
a lease that runs out makes a job due again; attempts are bounded) that is why a committed job
is attempted until it is done or given up. That this happens in every fair run is not proved
as one theorem: the store's model may fail every call forever.
-/

@[expose] public section

namespace Lanes.Db.Worker

open Jobs

variable {Q A W R : Type} [DecidableEq Q] [DecidableEq A] [DecidableEq W] [DecidableEq R]

/-! ## At most once -/

theorem filter_key_le {S' : Type} {f : S' → Option Int64} :
    ∀ (l : List S'), (l.filterMap f).Nodup → ∀ id, (l.filter fun x => f x == some id).length ≤ 1 := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons x l ih =>
    intro hnd id
    cases hx : f x with
    | none =>
      simp only [List.filterMap_cons, hx] at hnd
      simp only [List.filter_cons, hx]
      simpa using ih hnd id
    | some k =>
      simp only [List.filterMap_cons, hx, List.nodup_cons] at hnd
      simp only [List.filter_cons, hx]
      by_cases hk : k = id
      · subst hk
        simp only [beq_self_eq_true, ↓reduceIte, List.length_cons]
        have : l.filter (fun x => f x == some k) = [] := by
          refine List.filter_eq_nil_iff.mpr fun y hy hfy => hnd.1 ?_
          exact List.mem_filterMap.mpr ⟨y, hy, by simpa using hfy⟩
        simp [this]
      · have : (some k == some id) = false := by simpa using hk
        simp only [this, Bool.false_eq_true, ↓reduceIte]
        exact ih hnd.2 id

/-- **At most once.** Beside a service that honours idempotency keys (`Idempotent.server`),
whatever the inner service does, at most one effect the service may have had is under the key
of each job, in every run the model allows: an attempt made again, after an answer lost, a lease
run out or a restart, has no second effect. -/
theorem once_each {D S E : Type} (clients : Outside (sig Q A W R) D) (dbcfg : Db.Config)
    (h : Handler (Q ⊕ Req) (A ⊕ Ans W)) (start : Db) (inner : Rpc.Server S W R E)
    (refusal : R → Bool) (event : Q → Option E := fun _ => none) {events : List (Event (sig Q A W R))}
    {d : (D × Db.State (Q ⊕ Req) (A ⊕ Ans W)) × Rpc.State (Idempotent.State Int64 W R S)}
    (hd : (world clients dbcfg h start (Idempotent.server inner refusal) event).after events = some d)
    (id : Int64) : (d.2.server.slots.filter fun slot => slot.key == some id).length ≤ 1 :=
  filter_key_le _ (Idempotent.keys_nodup (runPort event) inner refusal
    (Outside.after_both _ _ _ hd).2) id

/-! ## Only what committed -/

variable (cfg : Config R) (q : Queue W) (app : Handler Q A)

/-- The store's handler: the application's transactions beside the worker's. -/
abbrev handler : Handler (Q ⊕ Req) (A ⊕ Ans W) := beside app (q.handler cfg.jobs)

/-- The table holds a job with this id and work, and no id twice with two works. -/
def Holding (id : Int64) (w : W) (db : Db) : Prop := q.Functional db ∧ q.Has db id w

/-- Of a world: no id twice with two works, and each claim that took effect answers jobs the
table holds. -/
def Claims (wd : Db.World (Q ⊕ Req) (A ⊕ Ans W)) : Prop :=
  q.Functional wd.db ∧ ∀ p ∈ wd.done, ∀ js, p.2 = .inr (.claimed js) → ∀ j ∈ js, q.Has wd.db j.id j.work

variable {cfg q app}

omit [DecidableEq Q] [DecidableEq A] [DecidableEq W] [DecidableEq R] in
theorem holding_preserves (happ : ∀ x, q.Keeps (app x)) (id : Int64) (w : W) :
    Preserves (handler cfg q app) (Holding q id w) := by
  intro x db a db' ⟨hF, hh⟩ hrun
  obtain ⟨hF', hk⟩ := Queue.keeps_beside happ cfg.jobs x db a db' hF hrun
  exact ⟨hF', hk id w hh⟩

omit [DecidableEq R] in
theorem claims_inv (happ : ∀ x, q.Keeps (app x)) : WorldInv (handler cfg q app) (Claims q) where
  effects wd hwd wd' hmem := by
    obtain ⟨hF, hdone⟩ := hwd
    rcases World.mem_effects hmem with ⟨c, -, a, hrun, hd⟩ | ⟨x, -, a, hrun, hd⟩
    · obtain ⟨hF', hk⟩ := Queue.keeps_beside happ cfg.jobs c.request _ _ _ hF hrun
      refine ⟨hF', fun p hp js hjs j hj => ?_⟩
      rw [hd] at hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hk _ _ (hdone p hp js hjs j hj)
      · simp only [List.mem_singleton] at hp
        subst hp
        simp only at hjs
        subst hjs
        exact Queue.claimed_has app cfg.jobs c.request hF hrun j hj
    · obtain ⟨hF', hk⟩ := Queue.keeps_beside happ cfg.jobs x _ _ _ hF hrun
      refine ⟨hF', fun p hp js hjs j hj => ?_⟩
      rw [hd] at hp
      exact hk _ _ (hdone p hp js hjs j hj)
  answer wd r hwd wd' hmem := by
    obtain ⟨hF, hdone⟩ := hwd
    have hdb := World.answer_db wd r wd' hmem
    refine ⟨hdb ▸ hF, fun p hp js hjs j hj => ?_⟩
    rw [hdb]
    exact hdone p (World.answer_done hmem p hp) js hjs j hj
  send dbcfg wd c hwd := by
    obtain ⟨hdb, hdone⟩ := World.send_done dbcfg wd c
    obtain ⟨hF, hd⟩ := hwd
    exact ⟨hdb ▸ hF, fun p hp js hjs j hj => hdb ▸ hd p (hdone ▸ hp) js hjs j hj⟩

/-- What holds of the worker beside its outsides: every world's claims answer jobs the table
holds; every committed claim in flight to the worker, and every attempt waiting to go out, is of
jobs every world's table holds; and the worker has no timer. -/
structure Inv {D S : Type} (c : SysState (system (Q := Q) (A := A) (W := W) cfg))
    (d : (D × Db.State (Q ⊕ Req) (A ⊕ Ans W)) × Rpc.State S) : Prop where
  worlds : WorldHolds (handler cfg q app) (Claims q) d.1.2
  replies : ∀ e ∈ c.net, ∀ r js, e.msg = .store r → r.result = .committed (.inr (.claimed js)) →
    ∀ j ∈ js, Db.Holds (handler cfg q app) (Holding q j.id j.work) d.1.2
  outbox : ∀ id lease dl w, Out.run id lease dl w ∈ c.outbox →
    Db.Holds (handler cfg q app) (Holding q id w) d.1.2
  timers : c.timers () = []

/-- Every attempt the worker emits on a message is of a job of a committed claim it reads. -/
theorem stored_runs (s : State) (msg : In Q A W R) {id lease : Int64} {w : W} {dl : Nat}
    (h : Effect.emit (Out.run id lease dl w) ∈ (step cfg s msg).2) :
    ∃ r js, msg = .store r ∧ r.result = .committed (.inr (.claimed js)) ∧ ∃ j ∈ js, j.id = id ∧ j.work = w := by
  cases msg with
  | tick now =>
    simp only [step, tick, call] at h
    split at h <;> simp at h
  | store r =>
    simp only [step, stored] at h
    split at h
    · next jobs hres =>
      obtain ⟨j, hj, he⟩ := List.mem_map.mp h
      simp only [attempt, Effect.emit.injEq, Out.run.injEq] at he
      obtain ⟨rfl, -, -, rfl⟩ := he
      refine ⟨r, jobs, rfl, ?_, j, List.mem_of_mem_take hj, rfl, rfl⟩
      exact hres
    · simp at h
  | ran id' lease' reply =>
    simp only [step, ran, call] at h
    simp at h
  | submit x =>
    simp only [step, call] at h
    simp at h


theorem step_effects (s : State) (msg : In Q A W R) : ∀ e ∈ (step cfg s msg).2, ∃ out, e = .emit out := by
  intro e he
  cases msg with
  | tick now =>
    simp only [step, tick, call] at he
    split at he <;> simp at he <;> exact ⟨_, he⟩
  | store r =>
    simp only [step, stored] at he
    split at he
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp he
      exact ⟨_, rfl⟩
    · simp at he
  | ran id lease reply =>
    simp only [step, ran, call] at he
    simp at he
    exact ⟨_, he⟩
  | submit x =>
    simp only [step, call] at he
    simp at he
    exact ⟨_, he⟩

theorem sends_nil {effs : List (Eff Q A W R)} (h : ∀ e ∈ effs, ∃ out, e = .emit out) :
    Effect.sends (σ := sig Q A W R) () effs = [] := by
  refine List.eq_nil_iff_forall_not_mem.mpr fun e he => ?_
  obtain ⟨-, hm⟩ := Effect.mem_sends.mp he
  obtain ⟨out, ho⟩ := h _ hm
  cases ho

theorem armed_nil {effs : List (Eff Q A W R)} (h : ∀ e ∈ effs, ∃ out, e = .emit out) :
    Effect.armed (σ := sig Q A W R) effs = [] := by
  refine List.eq_nil_iff_forall_not_mem.mpr fun m hm => ?_
  obtain ⟨delay, hd⟩ := Effect.mem_armed.mp hm
  obtain ⟨out, ho⟩ := h _ hd
  cases ho

variable {D S E : Type} {clients : Outside (sig Q A W R) D} {dbcfg : Db.Config} {start : Db}
  {svc : Rpc.Server S (Idempotent.Keyed Int64 W) R E} {event : Q → Option E}

omit [DecidableEq R] in
/-- A committed claim the store's model allows answers jobs every world's table holds. -/
theorem holding_of_allow (happ : ∀ x, q.Keeps (app x)) {s s' : Db.State (Q ⊕ Req) (A ⊕ Ans W)}
    {r : Db.Reply (A ⊕ Ans W)} {js : List (Job W)} (hw : WorldHolds (handler cfg q app) (Claims q) s)
    (hs : s.allow (handler cfg q app) r = some s') (hr : r.result = .committed (.inr (.claimed js))) :
    ∀ j ∈ js, Db.Holds (handler cfg q app) (Holding q j.id j.work) s' := by
  obtain ⟨rid, res⟩ := r
  simp only at hr
  subst hr
  intro j hj
  simp only [State.allow] at hs
  split at hs
  · cases hs
  · simp only [Option.some.injEq] at hs
    subst hs
    intro w hw' w' hw''
    have hw' := mem_dedup hw'
    simp only [List.mem_flatMap] at hw'
    obtain ⟨v, hv, u, hu, hans⟩ := hw'
    obtain ⟨hdone, hdb⟩ := World.answer_committed hans
    obtain ⟨hF, hc⟩ := hw v hv u hu
    have : Holding q j.id j.work w.db := hdb ▸ ⟨hF, hc _ hdone js rfl j hj⟩
    exact World.expand_inv (holding_preserves happ j.id j.work) _ w this w' hw''

/-- What the worker's outsides allow keeps what the store holds in every world. -/
theorem holds_allow {I : Db → Prop} (hI : Preserves (handler cfg q app) I)
    {d d' : (D × Db.State (Q ⊕ Req) (A ⊕ Ans W)) × Rpc.State S} {x : In Q A W R}
    (hallow : (world clients dbcfg (handler cfg q app) start svc event).allow d x = some d')
    (hd : Db.Holds (handler cfg q app) I d.1.2) : Db.Holds (handler cfg q app) I d'.1.2 := by
  simp only [world, Outside.both] at hallow
  split at hallow
  · obtain ⟨d₁, hd₁, rfl⟩ := Option.map_eq_some_iff.mp hallow
    split at hd₁
    · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hd₁
      exact hd
    · obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hd₁
      simp only [Db.outside, Option.bind_eq_some_iff] at hs'
      obtain ⟨r, -, hs⟩ := hs'
      exact allow_holds hI hd hs
  · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hallow
    exact hd

/-- Which outside an input went to, and what it left the store's model. -/
theorem allow_cases {d d' : (D × Db.State (Q ⊕ Req) (A ⊕ Ans W)) × Rpc.State S} {x : In Q A W R}
    (hallow : (world clients dbcfg (handler cfg q app) start svc event).allow d x = some d') :
    d'.1.2 = d.1.2 ∧ (∀ r, x ≠ .store r) ∨
      ∃ r, x = .store r ∧ d.1.2.allow (handler cfg q app) r = some d'.1.2 := by
  simp only [world, Outside.both] at hallow
  split at hallow
  · obtain ⟨d₁, hd₁, rfl⟩ := Option.map_eq_some_iff.mp hallow
    split at hd₁
    · next hx =>
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hd₁
      refine .inl ⟨rfl, fun r hr => ?_⟩
      subst hr
      simp [isClient] at hx
    · obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hd₁
      simp only [Db.outside, Option.bind_eq_some_iff] at hs'
      obtain ⟨r, hr, hs⟩ := hs'
      refine .inr ⟨r, ?_, hs⟩
      cases x <;> simp [storePort] at hr
      exact congrArg _ hr
  · next hx =>
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hallow
    refine .inl ⟨rfl, fun r hr => ?_⟩
    subst hr
    simp [isStored] at hx

theorem holds_observe {I : Db → Prop} (hI : Preserves (handler cfg q app) I) (out : Out Q W)
    {d : (D × Db.State (Q ⊕ Req) (A ⊕ Ans W)) × Rpc.State S}
    (hd : Db.Holds (handler cfg q app) I d.1.2) :
    Db.Holds (handler cfg q app) I ((world clients dbcfg (handler cfg q app) start svc event).observe d out).1.2 := by
  simp only [world, Outside.both, Db.outside]
  split
  · exact observe_holds dbcfg hI _ hd
  · exact hd

theorem worlds_observe (happ : ∀ x, q.Keeps (app x)) (out : Out Q W)
    {d : (D × Db.State (Q ⊕ Req) (A ⊕ Ans W)) × Rpc.State S}
    (hd : WorldHolds (handler cfg q app) (Claims q) d.1.2) :
    WorldHolds (handler cfg q app) (Claims q)
      ((world clients dbcfg (handler cfg q app) start svc event).observe d out).1.2 := by
  simp only [world, Outside.both, Db.outside]
  split
  · exact (claims_inv happ).observe dbcfg _ hd
  · exact hd

theorem inv_beside (happ : ∀ x, q.Keeps (app x)) (hstart : q.Functional start) (env : EnvModel (sig Q A W R)) :
    (world clients dbcfg (handler cfg q app) start svc event).Beside (system cfg) env
      (Inv (cfg := cfg) (q := q) (app := app)) where
  blank := by
    refine ⟨?_, by simp [SysState.blank], by simp [SysState.blank], rfl⟩
    intro w hw w' hw'
    simp only [world, Outside.both, Db.outside, List.mem_singleton] at hw
    subst hw
    exact (claims_inv happ).expand _ _ ⟨hstart, by simp⟩ w' hw'
  below c c' d h hb := by
    refine ⟨h.worlds, fun e he => h.replies e (hb.net e he), fun id lease dl w ho =>
      h.outbox id lease dl w (hb.outbox _ ho), ?_⟩
    exact List.eq_nil_iff_forall_not_mem.mpr fun m hm => by
      have := hb.timers () m hm
      rw [h.timers] at this
      cases this
  input c d x d' h hallow := by
    have hold : ∀ {I : Db → Prop}, Preserves (handler cfg q app) I →
        Db.Holds (handler cfg q app) I d.1.2 → Db.Holds (handler cfg q app) I d'.1.2 :=
      fun hI hd => holds_allow hI hallow hd
    rcases allow_cases hallow with ⟨hsame, hx⟩ | ⟨r, rfl, hs⟩
    · refine ⟨hsame ▸ h.worlds, fun e he r js hm hres j hj => ?_,
        fun id lease dl w ho => hold (holding_preserves happ id w) (h.outbox id lease dl w ho), h.timers⟩
      rcases List.mem_append.mp he with he | he
      · exact hold (holding_preserves happ _ _) (h.replies e he r js hm hres j hj)
      · simp only [List.mem_singleton] at he
        subst he
        exact absurd hm (hx r)
    · refine ⟨(claims_inv happ).allow h.worlds hs, fun e he r' js hm hres j hj => ?_,
        fun id lease dl w ho => hold (holding_preserves happ id w) (h.outbox id lease dl w ho), h.timers⟩
      rcases List.mem_append.mp he with he | he
      · exact hold (holding_preserves happ _ _) (h.replies e he r' js hm hres j hj)
      · simp only [List.mem_singleton] at he
        subst he
        obtain rfl : r = r' := by simpa using hm
        exact holding_of_allow happ h.worlds hs hres j hj
  output c d out h hout := by
    refine ⟨worlds_observe happ out h.worlds, fun e he r js hm hres j hj =>
      holds_observe (holding_preserves happ _ _) out (h.replies e he r js hm hres j hj),
      fun id lease dl w ho => holds_observe (holding_preserves happ _ _) out
        (h.outbox id lease dl w (List.mem_of_mem_erase ho)), h.timers⟩
  step c d i msg _ h hpending := by
    cases i
    have heffs : ∀ e ∈ ((actor (Q := Q) (A := A) (W := W) cfg).step (c.state ()) msg).2,
        ∃ out, e = .emit out := step_effects (cfg := cfg) (c.state ()) msg
    simp only [SysState.grow]
    rw [sends_nil heffs, armed_nil heffs]
    refine ⟨h.worlds, fun e he => h.replies e (by simpa using he), fun id lease dl w ho => ?_, by simp [h.timers]⟩
    rcases List.mem_append.mp ho with ho | ho
    · exact h.outbox id lease dl w ho
    · obtain ⟨r, js, rfl, hres, j, hj, rfl, rfl⟩ := stored_runs (cfg := cfg) (c.state ()) msg (Effect.mem_emits.mp ho)
      rcases hpending with ⟨src, he⟩ | hm
      · exact h.replies _ he r js rfl hres j hj
      · rw [h.timers] at hm; cases hm
  recover c d i h := by
    cases i
    have : (actor (Q := Q) (A := A) (W := W) cfg).recover (c.state ()) = ({}, []) := rfl
    simp only [SysState.grow, this, Effect.sends, Effect.armed, Effect.emits, List.filterMap_nil,
      List.append_nil]
    exact ⟨h.worlds, h.replies, h.outbox, by simp [h.timers]⟩
  restart _ c d _ h := by
    refine ⟨h.worlds, fun e he => ?_, fun id lease dl w ho => ?_, ?_⟩ <;>
      simp [SysState.init, SysState.startActor, SysState.settle, SysState.performAll,
        SysState.blank, actor] at *

/-- **No effect for a transaction that did not commit.** In every run of the worker, under every
environment model, beside any clients, the store's model with the application's transactions
beside the worker's, and any service: every attempt the worker hands over is of a job, with that
job's work, in every database the store may hold, also once any call still outstanding or lost
takes effect. -/
theorem committed_only (happ : ∀ x, q.Keeps (app x)) (hstart : q.Functional start)
    (env : EnvModel (sig Q A W R)) {events : List (Event (sig Q A W R))}
    {c : SysState (system (Q := Q) (A := A) (W := W) cfg)}
    (hrun : (SysState.init (system cfg) env).run env events = some c)
    {d : (D × Db.State (Q ⊕ Req) (A ⊕ Ans W)) × Rpc.State S}
    (hd : (world clients dbcfg (handler cfg q app) start svc event).after events = some d) :
    ∀ id lease dl w, Event.output (Out.run id lease dl w) ∈ events →
      Db.Holds (handler cfg q app) (Holding q id w) d.1.2 := by
  have hb := inv_beside (clients := clients) (dbcfg := dbcfg) (svc := svc) (event := event) (cfg := cfg)
    happ hstart env
  refine ((world clients dbcfg (handler cfg q app) start svc event).run_induction
    (P := fun events c d => Inv (cfg := cfg) (q := q) (app := app) c d ∧
      ∀ id lease dl w, Event.output (Out.run id lease dl w) ∈ events →
        Db.Holds (handler cfg q app) (Holding q id w) d.1.2)
    ⟨hb.init, by simp⟩ ?_ hrun hd).2
  intro evs c d ev c' d' hc ⟨hinv, hran⟩ hstep hsee
  have hkeep : ∀ id w, Db.Holds (handler cfg q app) (Holding q id w) d.1.2 →
      Db.Holds (handler cfg q app) (Holding q id w) d'.1.2 := by
    intro id w hh
    cases ev with
    | input x => exact holds_allow (holding_preserves happ id w) hsee hh
    | output out =>
      simp only [Outside.see, Option.some.injEq] at hsee
      subst hsee
      exact holds_observe (holding_preserves happ id w) out hh
    | _ => simp only [Outside.see, Option.some.injEq] at hsee; subst hsee; exact hh
  refine ⟨hb.keeps hc hinv hstep hsee, fun id lease dl w ho => ?_⟩
  rcases List.mem_append.mp ho with ho | ho
  · exact hkeep id w (hran id lease dl w ho)
  · simp only [List.mem_singleton] at ho
    subst ho
    exact hkeep id w (hinv.outbox id lease dl w (SysState.step_output.mp hstep).1)

/-- **What the service may have had, committed.** Behind a service that honours keys, every
effect the service may have had is under the key of a job, and of that job's work, in every
database the store may hold. -/
theorem slots_held {S' : Type} (happ : ∀ x, q.Keeps (app x)) (hstart : q.Functional start)
    (env : EnvModel (sig Q A W R)) {inner : Rpc.Server S' W R E} {refusal : R → Bool}
    {events : List (Event (sig Q A W R))} {c : SysState (system (Q := Q) (A := A) (W := W) cfg)}
    (hrun : (SysState.init (system cfg) env).run env events = some c)
    {d : (D × Db.State (Q ⊕ Req) (A ⊕ Ans W)) × Rpc.State (Idempotent.State Int64 W R S')}
    (hd : (world clients dbcfg (handler cfg q app) start (Idempotent.server inner refusal) event).after events = some d) :
    ∀ slot ∈ d.2.server.slots, ∃ id, slot.key = some id ∧
      Db.Holds (handler cfg q app) (Holding q id slot.request) d.1.2 := by
  have hc := committed_only (cfg := cfg) happ hstart env hrun hd
  have hh := Idempotent.holds (runPort event) inner refusal
    (fun r => ∃ id, r.1 = some id ∧ Db.Holds (handler cfg q app) (Holding q id r.2) d.1.2)
    (fun out hout call hcall => by
      have hout := (List.mem_filter.mp hout).1
      cases out with
      | run id lease dl w =>
        simp only [runPort, Option.some.injEq] at hcall
        subst hcall
        exact ⟨id, rfl, hc id lease dl w hout⟩
      | store _ => simp [runPort] at hcall)
    (Outside.after_both _ _ _ hd).2
  intro slot hslot
  exact hh.2 (slot.key, slot.request) (List.mem_map.mpr ⟨slot, hslot, rfl⟩)

end Lanes.Db.Worker
