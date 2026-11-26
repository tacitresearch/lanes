/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Step

/-!
An actor is at rest when it is up, has no timers, and is in a state a fresh start gives it
(`Actor.fresh`). Releasing it puts it back where an actor nobody has written to is: down, at its
initial state. Its next message starts it again, which gives it back as it was. So releasing
changes nothing anyone can see: `SysState.Released a b`, `b` is `a` with some actors at rest
released, is a simulation both ways up to the starts that bring released actors back
(`Released.step`, `Released.step_back`), and the same runs are possible from both
(`Released.runs`).

`SysState.Leads` is what a kernel's events do when the kernel releases actors as it goes: a run
that differs from them only in starts reaches a state the kernel is, with actors released.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

def Event.awake (events : List (Event σ)) : List (Event σ) :=
  events.filter fun
    | .start _ => false
    | _ => true

namespace Event

@[simp] theorem awake_nil : awake ([] : List (Event σ)) = [] := rfl

theorem awake_append (a b : List (Event σ)) : awake (a ++ b) = awake a ++ awake b :=
  List.filter_append ..

@[simp] theorem awake_start (i : σ.Id) (events : List (Event σ)) :
    awake (.start i :: events) = awake events := by
  simp [awake]

theorem awake_cons (ev : Event σ) (events : List (Event σ)) :
    awake (ev :: events) = awake [ev] ++ awake events :=
  awake_append [ev] events

/-- What leaves out every start sees the same of two lists of events that differ only in
starts. -/
theorem filterMap_eq_of_awake {β : Type} {f : Event σ → Option β} (hf : ∀ i, f (.start i) = none)
    {a b : List (Event σ)} (h : awake a = awake b) : a.filterMap f = b.filterMap f := by
  have hkeep : ∀ l : List (Event σ), (awake l).filterMap f = l.filterMap f := by
    intro l
    rw [awake, List.filterMap_filter]
    congr 1
    funext ev
    cases ev <;> simp [hf]
  rw [← hkeep a, h, hkeep b]

end Event

namespace SysState

variable {sys : System σ} {env : EnvModel σ} {a b c a' b' : SysState sys} {i : σ.Id}

/-- Actor `i` as it is in `a` is as it is in `b`. -/
def Same (a b : SysState sys) (i : σ.Id) : Prop :=
  b.state i = a.state i ∧ b.up i = a.up i ∧ b.timers i = a.timers i

theorem Same.refl (a : SysState sys) (i : σ.Id) : Same a a i := ⟨rfl, rfl, rfl⟩

theorem Same.trans (h₁ : Same a b i) (h₂ : Same b c i) : Same a c i :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

/-- Actor `i` at rest in `a`, and released in `b`. -/
structure Asleep (a b : SysState sys) (i : σ.Id) : Prop where
  up : a.up i = true
  fresh : (sys.actor i).fresh (a.state i) = true
  timers : a.timers i = []
  down : b.up i = false
  init : b.state i = (sys.actor i).init
  idle : b.timers i = []

/-- `b` is `a` with some actors at rest released. -/
structure Released (a b : SysState sys) : Prop where
  actor : ∀ i, Same a b i ∨ Asleep a b i
  net : b.net = a.net
  outbox : b.outbox = a.outbox

/-- Actor `i` down at its initial state, with no timers: as if nobody had written to it. -/
def release (c : SysState sys) (i : σ.Id) : SysState sys :=
  { c with
    state := update c.state i (sys.actor i).init
    up := update c.up i false
    timers := update c.timers i [] }

theorem settle_nil (c : SysState sys) (i : σ.Id) (s : sys.State i) :
    c.settle env i (s, []) = { c with state := update c.state i s } := rfl

theorem perform_up (c : SysState sys) (i : σ.Id) (eff : Effect σ i) :
    (c.perform i eff).up = c.up := by
  cases eff <;> rfl

theorem perform_same_of_ne (c : SysState sys) {i j : σ.Id} (eff : Effect σ i) (hj : j ≠ i) :
    Same c (c.perform i eff) j := by
  cases eff <;> simp [Same, perform, hj]

namespace Released

theorem refl (a : SysState sys) : Released a a := ⟨fun i => .inl (Same.refl a i), rfl, rfl⟩

theorem same (h : Released a b) (hup : b.up i = a.up i) : Same a b i :=
  (h.actor i).elim id fun hi => by
    have := hup.symm.trans hi.down
    rw [hi.up] at this
    cases this

theorem same_of_up (h : Released a b) (hup : b.up i = true) : Same a b i :=
  (h.actor i).elim id fun hi => by rw [hi.down] at hup; cases hup

theorem same_of_down (h : Released a b) (hdown : a.up i = false) : Same a b i :=
  (h.actor i).elim id fun hi => by rw [hi.up] at hdown; cases hdown

theorem trans (h₁ : Released a b) (h₂ : Released b c) : Released a c := by
  refine ⟨fun i => ?_, h₂.net.trans h₁.net, h₂.outbox.trans h₁.outbox⟩
  rcases h₁.actor i with ⟨hs, hu, ht⟩ | h₁i <;> rcases h₂.actor i with h₂i | h₂i
  · exact .inl (Same.trans ⟨hs, hu, ht⟩ h₂i)
  · exact .inr ⟨hu.symm.trans h₂i.up, by rw [← hs]; exact h₂i.fresh, ht.symm.trans h₂i.timers,
      h₂i.down, h₂i.init, h₂i.idle⟩
  · obtain ⟨hs, hu, ht⟩ := h₂i
    exact .inr ⟨h₁i.up, h₁i.fresh, h₁i.timers, hu.trans h₁i.down, hs.trans h₁i.init,
      ht.trans h₁i.idle⟩
  · have := h₂i.up
    rw [h₁i.down] at this
    cases this

/-- Releasing one more actor at rest. -/
theorem release (h : Released a b) (hup : b.up i = true) (htimers : b.timers i = [])
    (hfresh : (sys.actor i).fresh (b.state i) = true) : Released a (b.release i) := by
  refine h.trans ⟨fun j => ?_, rfl, rfl⟩
  by_cases hj : j = i
  · subst hj
    exact .inr ⟨hup, hfresh, htimers, by simp [SysState.release], by simp [SysState.release],
      by simp [SysState.release]⟩
  · exact .inl ⟨by simp [SysState.release, hj], by simp [SysState.release, hj],
      by simp [SysState.release, hj]⟩

/-- A change to actor `i`, the net and the outbox, the same on both sides. -/
theorem modify (h : Released a b) (i : σ.Id) (hi : Same a' b' i)
    (ha : ∀ j, j ≠ i → Same a a' j) (hb : ∀ j, j ≠ i → Same b b' j)
    (hnet : b'.net = a'.net) (hout : b'.outbox = a'.outbox) : Released a' b' := by
  refine ⟨fun j => ?_, hnet, hout⟩
  by_cases hj : j = i
  · subst hj
    exact .inl hi
  · obtain ⟨has, hau, hat⟩ := ha j hj
    obtain ⟨hbs, hbu, hbt⟩ := hb j hj
    rcases h.actor j with ⟨hs, hu, ht⟩ | hs
    · exact .inl ⟨hbs.trans (hs.trans has.symm), hbu.trans (hu.trans hau.symm),
        hbt.trans (ht.trans hat.symm)⟩
    · exact .inr ⟨hau.trans hs.up, by rw [has]; exact hs.fresh, hat.trans hs.timers,
        hbu.trans hs.down, hbs.trans hs.init, hbt.trans hs.idle⟩

theorem withNet (h : Released a b) (f : List (Envelope σ) → List (Envelope σ)) :
    Released { a with net := f a.net } { b with net := f b.net } :=
  ⟨h.actor, congrArg f h.net, h.outbox⟩

theorem withOutbox (h : Released a b) (f : List σ.Out → List σ.Out) :
    Released { a with outbox := f a.outbox } { b with outbox := f b.outbox } :=
  ⟨h.actor, h.net, congrArg f h.outbox⟩

theorem deliverable (h : Released a b) (e : Envelope σ) :
    a.deliverable env e = b.deliverable env e := by
  unfold SysState.deliverable
  rw [h.net]

theorem hasMail (h : Released a b) (i : σ.Id) : a.hasMail i = b.hasMail i := by
  unfold SysState.hasMail
  rw [h.net]

theorem setState (h : Released a b) (hi : Same a b i) (s : sys.State i) :
    Released { a with state := update a.state i s } { b with state := update b.state i s } :=
  h.modify i ⟨by simp, hi.2.1, hi.2.2⟩ (fun j hj => ⟨by simp [hj], rfl, rfl⟩)
    (fun j hj => ⟨by simp [hj], rfl, rfl⟩) h.net h.outbox

theorem setUp (h : Released a b) (hi : Same a b i) (up : Bool) :
    Released { a with up := update a.up i up } { b with up := update b.up i up } :=
  h.modify i ⟨hi.1, by simp, hi.2.2⟩ (fun j hj => ⟨rfl, by simp [hj], rfl⟩)
    (fun j hj => ⟨rfl, by simp [hj], rfl⟩) h.net h.outbox

theorem setTimers (h : Released a b) (hi : Same a b i) (timers : List (σ.Msg i)) :
    Released { a with timers := update a.timers i timers }
      { b with timers := update b.timers i timers } :=
  h.modify i ⟨hi.1, hi.2.1, by simp⟩ (fun j hj => ⟨rfl, rfl, by simp [hj]⟩)
    (fun j hj => ⟨rfl, rfl, by simp [hj]⟩) h.net h.outbox

theorem perform (h : Released a b) (hi : Same a b i) (eff : Effect σ i) :
    Released (a.perform i eff) (b.perform i eff) := by
  cases eff with
  | send to msg => exact h.withNet (· ++ _)
  | emit out => exact h.withOutbox (· ++ _)
  | after delay_ms msg =>
    have := h.setTimers hi (if msg ∈ a.timers i then a.timers i else a.timers i ++ [msg])
    simpa only [SysState.perform, hi.2.2] using this
  | cancel msg =>
    have := h.setTimers hi ((a.timers i).erase msg)
    simpa only [SysState.perform, hi.2.2] using this
  | stop => exact h

theorem performAll (h : Released a b) (hi : Same a b i) (effs : List (Effect σ i)) :
    Released (a.performAll i effs) (b.performAll i effs) := by
  induction effs generalizing a b with
  | nil => exact h
  | cons eff effs ih =>
    have h' := h.perform hi eff
    exact ih h' (h'.same (by rw [perform_up, perform_up, hi.2.1]))

theorem down (h : Released a b) (hi : Same a b i) : Released (a.down env i) (b.down env i) :=
  h.modify i ⟨hi.1, by simp [SysState.down], by simp [SysState.down]⟩
    (fun j hj => ⟨rfl, by simp [SysState.down, hj], by simp [SysState.down, hj]⟩)
    (fun j hj => ⟨rfl, by simp [SysState.down, hj], by simp [SysState.down, hj]⟩)
    (by simp only [SysState.down, h.net]) h.outbox

theorem settle (h : Released a b) (hi : Same a b i) (r : sys.State i × List (Effect σ i)) :
    Released (a.settle env i r) (b.settle env i r) := by
  have h₁ := h.setState hi r.1
  have h₂ := h₁.performAll (h₁.same hi.2.1) r.2
  unfold SysState.settle
  split
  · exact h₂.down (h₂.same (by
      simp only [show ∀ c : SysState sys, (c.performAll i r.2).up = c.up from fun c =>
        performAll_induction (P := fun c' => c'.up = c.up) rfl fun c' eff _ hc' => by
          rw [perform_up]; exact hc']
      exact hi.2.1))
  · exact h₂

theorem handle (h : Released a b) (hi : Same a b i) (msg : σ.Msg i) :
    Released (a.handle env i msg) (b.handle env i msg) := by
  unfold SysState.handle
  rw [hi.1]
  exact h.settle hi _

theorem startActor (h : Released a b) (hi : Same a b i) :
    Released (a.startActor env i) (b.startActor env i) := by
  unfold SysState.startActor
  rw [hi.1]
  have h₁ := h.setUp hi true
  exact h₁.settle (h₁.same (by simp))

theorem startActor_asleep (hi : Asleep a b i) :
    b.startActor env i = { b with up := update b.up i true, state := update b.state i (a.state i) } := by
  have hrecover : (sys.actor i).recover (b.state i) = (a.state i, []) := by
    rw [hi.init]
    exact (sys.actor i).fresh_recover _ hi.fresh
  unfold SysState.startActor
  rw [hrecover, settle_nil]

/-- A released actor started again is the actor it was. -/
theorem wake (h : Released a b) (hi : Asleep a b i) :
    Released a (b.startActor env i) ∧ Same a (b.startActor env i) i := by
  rw [startActor_asleep hi]
  have hsame : Same a { b with up := update b.up i true, state := update b.state i (a.state i) } i :=
    ⟨by simp, by simp [hi.up], by simp [hi.idle, hi.timers]⟩
  refine ⟨(Released.refl a).modify i hsame (fun j _ => Same.refl a j) (fun j hj => ?_) h.net
    h.outbox, hsame⟩
  rcases h.actor j with hs | hs
  · exact ⟨by simp [hj, hs.1], by simp [hj, hs.2.1], hs.2.2⟩
  · exact ⟨by simp [hj, hs.init], by simp [hj, hs.down], hs.idle⟩

/-- Every step of `b` is one of `a`, or a start that brings a released actor back. -/
theorem step (h : Released a b) {ev : Event σ} (hstep : b.step env ev = some b') :
    (∃ a', a.step env ev = some a' ∧ Released a' b') ∨ (∃ i, ev = .start i ∧ Released a b') := by
  cases ev with
  | input x =>
    obtain rfl := step_input.mp hstep
    exact .inl ⟨_, step_input.mpr rfl, h.withNet (· ++ _)⟩
  | deliver e =>
    obtain ⟨hup, hdel, rfl⟩ := step_deliver.mp hstep
    have hi := h.same_of_up hup
    exact .inl ⟨_, step_deliver.mpr ⟨hi.2.1.symm.trans hup, (h.deliverable e).trans hdel, rfl⟩,
      (h.withNet (·.erase e)).handle hi e.msg⟩
  | duplicate e =>
    obtain ⟨hup, hdup, hdel, rfl⟩ := step_duplicate.mp hstep
    have hi := h.same_of_up hup
    exact .inl ⟨_, step_duplicate.mpr ⟨hi.2.1.symm.trans hup, hdup,
      (h.deliverable e).trans hdel, rfl⟩, h.handle hi e.msg⟩
  | drop e =>
    obtain ⟨hlossy, hmem, rfl⟩ := step_drop.mp hstep
    exact .inl ⟨_, step_drop.mpr ⟨hlossy, h.net ▸ hmem, rfl⟩, h.withNet (·.erase e)⟩
  | timeout i msg =>
    obtain ⟨hup, hmem, rfl⟩ := step_timeout.mp hstep
    have hi := h.same_of_up hup
    have h₁ := h.setTimers hi ((a.timers i).erase msg)
    refine .inl ⟨_, step_timeout.mpr ⟨hi.2.1.symm.trans hup, hi.2.2 ▸ hmem, rfl⟩, ?_⟩
    rw [hi.2.2]
    exact h₁.handle (h₁.same hi.2.1) msg
  | output out =>
    obtain ⟨hmem, rfl⟩ := step_output.mp hstep
    exact .inl ⟨_, step_output.mpr ⟨h.outbox ▸ hmem, rfl⟩, h.withOutbox (·.erase out)⟩
  | crash i =>
    obtain ⟨hup, hcrash, rfl⟩ := step_crash.mp hstep
    have hi := h.same_of_up hup
    exact .inl ⟨_, step_crash.mpr ⟨hi.2.1.symm.trans hup, hcrash, rfl⟩, h.down hi⟩
  | start i =>
    obtain ⟨hdown, hmail, rfl⟩ := step_start.mp hstep
    rcases h.actor i with hi | hi
    · exact .inl ⟨_, step_start.mpr ⟨hi.2.1.symm.trans hdown, (h.hasMail i).symm ▸ hmail, rfl⟩,
        h.startActor hi⟩
    · exact .inr ⟨i, rfl, (h.wake hi).1⟩

theorem run (h : Released a b) {events : List (Event σ)} (hrun : b.run env events = some b') :
    ∃ evs a', a.run env evs = some a' ∧ Event.awake evs = Event.awake events
      ∧ Released a' b' := by
  induction events generalizing a b with
  | nil =>
    simp only [SysState.run, Option.some.injEq] at hrun
    exact ⟨[], a, rfl, rfl, hrun ▸ h⟩
  | cons ev events ih =>
    simp only [SysState.run] at hrun
    cases hb : b.step env ev with
    | none => simp [hb] at hrun
    | some b₁ =>
      rw [hb, Option.bind_some] at hrun
      rcases h.step hb with ⟨a₁, ha, h₁⟩ | ⟨i, rfl, h₁⟩
      · obtain ⟨evs, a', hrun', hawake, h'⟩ := ih h₁ hrun
        refine ⟨ev :: evs, a', by simp [SysState.run, ha, hrun'], ?_, h'⟩
        rw [Event.awake_cons, hawake, ← Event.awake_cons]
      · obtain ⟨evs, a', hrun', hawake, h'⟩ := ih h₁ hrun
        exact ⟨evs, a', hrun', by rw [hawake, Event.awake_start], h'⟩

/-- An actor that is up in `a`, awake in `b` after at most a start. -/
theorem awaken (h : Released a b) (hup : a.up i = true) (hmail : a.hasMail i = true) :
    ∃ pre b₁, b.run env pre = some b₁ ∧ Event.awake pre = [] ∧ Released a b₁ ∧ Same a b₁ i := by
  rcases h.actor i with hi | hi
  · exact ⟨[], b, rfl, rfl, h, hi⟩
  · have hstart : b.step env (.start i) = some (b.startActor env i) :=
      step_start.mpr ⟨hi.down, .inl ((h.hasMail i) ▸ hmail), rfl⟩
    exact ⟨[.start i], _, by simp [SysState.run, hstart], by simp, h.wake hi⟩

theorem hasMail_of_mem {e : Envelope σ} (hmem : e ∈ a.net) : a.hasMail e.dst = true :=
  List.any_eq_true.mpr ⟨e, hmem, by simp⟩

/-- Every step of `a` is one of `b`, after a start that brings a released actor back if it is
the one the step is for. A crash would tell them apart: the actor `a` crashes keeps its state,
the one `b` released has its initial one. -/
theorem step_back (h : Released a b) (hcrash : ∀ i, env.mayCrash i = false) {ev : Event σ}
    (hstep : a.step env ev = some a') :
    ∃ evs b', b.run env evs = some b' ∧ Event.awake evs = Event.awake [ev] ∧ Released a' b' := by
  have after : ∀ pre b₁ b', b.run env pre = some b₁ → Event.awake pre = [] →
      b₁.step env ev = some b' → Released a' b' →
      ∃ evs b', b.run env evs = some b' ∧ Event.awake evs = Event.awake [ev]
        ∧ Released a' b' := fun pre b₁ b' hpre hawake hb h' =>
    ⟨pre ++ [ev], b', by simp [SysState.run_append, hpre, SysState.run, hb],
      by rw [Event.awake_append, hawake, List.nil_append], h'⟩
  cases ev with
  | input x =>
    obtain rfl := step_input.mp hstep
    exact after [] b _ rfl rfl (step_input.mpr rfl) (h.withNet (· ++ _))
  | deliver e =>
    obtain ⟨hup, hdel, rfl⟩ := step_deliver.mp hstep
    obtain ⟨pre, b₁, hpre, hawake, h₁, hs₁⟩ :=
      h.awaken (env := env) hup (hasMail_of_mem (mem_of_deliverable hdel))
    exact after pre b₁ _ hpre hawake (step_deliver.mpr ⟨hs₁.2.1.trans hup,
      (h₁.deliverable e).symm.trans hdel, rfl⟩) ((h₁.withNet (·.erase e)).handle hs₁ e.msg)
  | duplicate e =>
    obtain ⟨hup, hdup, hdel, rfl⟩ := step_duplicate.mp hstep
    obtain ⟨pre, b₁, hpre, hawake, h₁, hs₁⟩ :=
      h.awaken (env := env) hup (hasMail_of_mem (mem_of_deliverable hdel))
    exact after pre b₁ _ hpre hawake (step_duplicate.mpr ⟨hs₁.2.1.trans hup, hdup,
      (h₁.deliverable e).symm.trans hdel, rfl⟩) (h₁.handle hs₁ e.msg)
  | drop e =>
    obtain ⟨hlossy, hmem, rfl⟩ := step_drop.mp hstep
    exact after [] b _ rfl rfl (step_drop.mpr ⟨hlossy, h.net ▸ hmem, rfl⟩) (h.withNet (·.erase e))
  | timeout i msg =>
    obtain ⟨hup, hmem, rfl⟩ := step_timeout.mp hstep
    have hi : Same a b i := (h.actor i).elim id fun hi => by rw [hi.timers] at hmem; cases hmem
    have h₁ := h.setTimers hi ((a.timers i).erase msg)
    refine after [] b _ rfl rfl (step_timeout.mpr ⟨hi.2.1.trans hup, hi.2.2 ▸ hmem, rfl⟩) ?_
    rw [hi.2.2]
    exact h₁.handle (h₁.same hi.2.1) msg
  | output out =>
    obtain ⟨hmem, rfl⟩ := step_output.mp hstep
    exact after [] b _ rfl rfl (step_output.mpr ⟨h.outbox ▸ hmem, rfl⟩) (h.withOutbox (·.erase out))
  | crash i =>
    obtain ⟨_, hmay, -⟩ := step_crash.mp hstep
    rw [hcrash i] at hmay
    cases hmay
  | start i =>
    obtain ⟨hdown, hmail, rfl⟩ := step_start.mp hstep
    have hi := h.same_of_down hdown
    exact after [] b _ rfl rfl (step_start.mpr ⟨hi.2.1.trans hdown, (h.hasMail i) ▸ hmail, rfl⟩)
      (h.startActor hi)

theorem run_back (h : Released a b) (hcrash : ∀ i, env.mayCrash i = false)
    {events : List (Event σ)} (hrun : a.run env events = some a') :
    ∃ evs b', b.run env evs = some b' ∧ Event.awake evs = Event.awake events
      ∧ Released a' b' := by
  induction events generalizing a b with
  | nil =>
    simp only [SysState.run, Option.some.injEq] at hrun
    exact ⟨[], b, rfl, rfl, hrun ▸ h⟩
  | cons ev events ih =>
    simp only [SysState.run] at hrun
    cases ha : a.step env ev with
    | none => simp [ha] at hrun
    | some a₁ =>
      rw [ha, Option.bind_some] at hrun
      obtain ⟨pre, b₁, hpre, hawake₁, h₁⟩ := h.step_back hcrash ha
      obtain ⟨evs, b', hrun', hawake, h'⟩ := ih h₁ hrun
      refine ⟨pre ++ evs, b', by simp [SysState.run_append, hpre, hrun'], ?_, h'⟩
      rw [Event.awake_append, hawake₁, hawake, ← Event.awake_append]
      rfl

/-- Releasing actors at rest changes nothing that can be seen: whatever runs one state allows,
the other allows too, up to the starts that bring released actors back. -/
theorem runs (h : Released a b) (hcrash : ∀ i, env.mayCrash i = false)
    (events : List (Event σ)) :
    (∃ evs a', a.run env evs = some a' ∧ Event.awake evs = Event.awake events)
      ↔ ∃ evs b', b.run env evs = some b' ∧ Event.awake evs = Event.awake events := by
  constructor
  · rintro ⟨evs, a', hrun, hawake⟩
    obtain ⟨evs', b', hrun', hawake', -⟩ := h.run_back hcrash hrun
    exact ⟨evs', b', hrun', hawake'.trans hawake⟩
  · rintro ⟨evs, b', hrun, hawake⟩
    obtain ⟨evs', a', hrun', hawake', -⟩ := h.run hrun
    exact ⟨evs', a', hrun', hawake'.trans hawake⟩

end Released

/-- What the events of a kernel that releases actors do: a run that differs from them only in
starts takes `a` to a state that `b` is, with actors at rest released. -/
def Leads (env : EnvModel σ) (a : SysState sys) (events : List (Event σ)) (b : SysState sys) :
    Prop :=
  ∃ evs c, a.run env evs = some c ∧ Event.awake evs = Event.awake events ∧ c.Released b

namespace Leads

theorem of_run {events : List (Event σ)} (h : a.run env events = some b) : a.Leads env events b :=
  ⟨events, b, h, rfl, .refl b⟩

theorem released {events : List (Event σ)} (h : a.Leads env events b) (hb : b.Released c) :
    a.Leads env events c :=
  let ⟨evs, c', hrun, hawake, hc'⟩ := h
  ⟨evs, c', hrun, hawake, hc'.trans hb⟩

theorem append {e₁ e₂ : List (Event σ)} (h₁ : a.Leads env e₁ b) (h₂ : b.Leads env e₂ c) :
    a.Leads env (e₁ ++ e₂) c := by
  obtain ⟨evs₁, c₁, hrun₁, hawake₁, hc₁⟩ := h₁
  obtain ⟨evs₂, c₂, hrun₂, hawake₂, hc₂⟩ := h₂
  obtain ⟨evs, c', hrun, hawake, hc'⟩ := hc₁.run hrun₂
  refine ⟨evs₁ ++ evs, c', by simp [SysState.run_append, hrun₁, hrun], ?_, hc'.trans hc₂⟩
  rw [Event.awake_append, Event.awake_append, hawake₁, hawake, hawake₂]

/-- From a reachable state, what a kernel's events lead to is a reachable state with actors at
rest released. -/
theorem reachable {events : List (Event σ)} (ha : sys.Reachable env a) (h : a.Leads env events b) :
    ∃ c, sys.Reachable env c ∧ c.Released b :=
  let ⟨_, c, hrun, _, hc⟩ := h
  ⟨c, ha.run hrun, hc⟩

end Leads

end SysState

end Lanes
