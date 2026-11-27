/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Proof.Lift
public import Lanes.Core.Step

/-!
# History variables that cost nothing at run time

Some invariants need to talk about the past: "this node voted for that candidate in term 3" is
not something a node still remembers in term 5. A `Ghost` adds a history to each actor, updated
on every step from the state and the message. `System.withGhost` is the system that carries
the histories along.

The histories cannot influence anything: `SysState.erase_step` proves the system with ghosts
takes exactly the steps of the system without them. So an invariant proved with ghosts holds of
the real system (`System.Invariant.of_ghost`), which never computes or stores a history.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

structure Ghost (sys : System σ) where
  Hist : σ.Id → Type
  init : (i : σ.Id) → Hist i
  /-- The history after actor `i`, in state `s`, handles `msg`. -/
  step : (i : σ.Id) → Hist i → sys.State i → σ.Msg i → Hist i
  /-- The history after actor `i` recovers from state `s`. A history is not lost in a crash. -/
  recover : (i : σ.Id) → Hist i → sys.State i → Hist i := fun _ h _ => h

def System.withGhost (sys : System σ) (g : Ghost sys) : System σ where
  State i := sys.State i × g.Hist i
  actor i :=
    { init := ((sys.actor i).init, g.init i)
      step := fun s msg =>
        ((((sys.actor i).step s.1 msg).1, g.step i s.2 s.1 msg), ((sys.actor i).step s.1 msg).2)
      recover := fun s =>
        ((((sys.actor i).recover s.1).1, g.recover i s.2 s.1), ((sys.actor i).recover s.1).2) }
  accept := sys.accept
  boot := sys.boot

namespace SysState

variable {sys : System σ} {g : Ghost sys}

def erase (c : SysState (sys.withGhost g)) : SysState sys where
  state i := (c.state i).1
  up := c.up
  net := c.net
  timers := c.timers
  outbox := c.outbox

@[simp] theorem erase_up (c : SysState (sys.withGhost g)) : c.erase.up = c.up := rfl
@[simp] theorem erase_net (c : SysState (sys.withGhost g)) : c.erase.net = c.net := rfl
@[simp] theorem erase_timers (c : SysState (sys.withGhost g)) : c.erase.timers = c.timers := rfl
@[simp] theorem erase_outbox (c : SysState (sys.withGhost g)) : c.erase.outbox = c.outbox := rfl

@[simp] theorem erase_deliverable (env : EnvModel σ) (c : SysState (sys.withGhost g))
    (e : Envelope σ) : c.erase.deliverable env e = c.deliverable env e := rfl

@[simp] theorem erase_hasMail (c : SysState (sys.withGhost g)) (i : σ.Id) :
    c.erase.hasMail i = c.hasMail i := rfl

theorem erase_perform (c : SysState (sys.withGhost g)) (i : σ.Id) (eff : Effect σ i) :
    (c.perform i eff).erase = c.erase.perform i eff := by
  cases eff <;> rfl

theorem erase_performAll (c : SysState (sys.withGhost g)) (i : σ.Id) (effs : List (Effect σ i)) :
    (c.performAll i effs).erase = c.erase.performAll i effs := by
  induction effs generalizing c with
  | nil => rfl
  | cons eff effs ih => rw [performAll_cons, ih, erase_perform, performAll_cons]

theorem erase_down (env : EnvModel σ) (c : SysState (sys.withGhost g)) (i : σ.Id) :
    (c.down env i).erase = c.erase.down env i := rfl

theorem erase_settle (env : EnvModel σ) (c : SysState (sys.withGhost g)) (i : σ.Id)
    (r : (sys.State i × g.Hist i) × List (Effect σ i)) :
    (c.settle env i r).erase = c.erase.settle env i (r.1.1, r.2) := by
  have hstate : ({ c with state := update c.state i r.1 } : SysState (sys.withGhost g)).erase
      = { c.erase with state := update c.erase.state i r.1.1 } := by
    simp only [erase]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      exact (congrArg Prod.fst (update_self c.state j r.1)).trans (update_self _ j r.1.1).symm
    · exact (congrArg Prod.fst (update_of_ne c.state r.1 hj)).trans
        (update_of_ne (fun j => (c.state j).1) r.1.1 hj).symm
  unfold settle
  split
  · rw [erase_down, erase_performAll, hstate]
  · rw [erase_performAll, hstate]

theorem erase_handle (env : EnvModel σ) (c : SysState (sys.withGhost g)) (i : σ.Id)
    (msg : σ.Msg i) : (c.handle env i msg).erase = c.erase.handle env i msg :=
  erase_settle env c i _

theorem erase_startActor (env : EnvModel σ) (c : SysState (sys.withGhost g)) (i : σ.Id) :
    (c.startActor env i).erase = c.erase.startActor env i :=
  erase_settle env { c with up := update c.up i true } i _

private theorem map_ite {α β : Type} (f : α → β) (b : Bool) (x : α) :
    Option.map f (if b then some x else none) = if b then some (f x) else none := by
  cases b <;> rfl

/-- A system with ghosts takes exactly the steps of the system without them. -/
theorem erase_step (env : EnvModel σ) (c : SysState (sys.withGhost g)) (ev : Event σ) :
    (c.step env ev).map erase = c.erase.step env ev := by
  cases ev with
  | input x => rfl
  | deliver e =>
    exact (map_ite erase (c.up e.dst && c.deliverable env e) _).trans (by rw [erase_handle]; rfl)
  | duplicate e =>
    exact (map_ite erase (c.up e.dst && (env.link e.src e.dst).duplicating
      && c.deliverable env e) _).trans (by rw [erase_handle]; rfl)
  | drop e => exact map_ite erase ((env.link e.src e.dst).lossy && c.net.contains e) _
  | timeout i msg =>
    exact (map_ite erase (c.up i && (c.timers i).contains msg) _).trans
      (by rw [erase_handle]; rfl)
  | output out => exact map_ite erase (c.outbox.contains out) _
  | crash i => exact map_ite erase (c.up i && env.mayCrash i) _
  | start i =>
    exact (map_ite erase (!c.up i && (c.hasMail i || env.restarts i)) _).trans
      (by rw [erase_startActor]; rfl)

theorem erase_run (env : EnvModel σ) (c : SysState (sys.withGhost g)) (evs : List (Event σ)) :
    (c.run env evs).map erase = c.erase.run env evs := by
  induction evs generalizing c with
  | nil => rfl
  | cons ev evs ih =>
    rw [run, run, ← erase_step]
    cases c.step env ev with
    | none => rfl
    | some c' => exact ih c'

theorem erase_init (sys : System σ) (g : Ghost sys) (env : EnvModel σ) :
    (SysState.init (sys.withGhost g) env).erase = SysState.init sys env :=
  (List.foldl_hom erase fun c i => (erase_startActor env c i).symm).symm

end SysState

namespace System

variable {sys : System σ} {g : Ghost sys} {env : EnvModel σ}

theorem Reachable.erase {c : SysState (sys.withGhost g)}
    (h : (sys.withGhost g).Reachable env c) : sys.Reachable env c.erase := by
  induction h with
  | init => rw [SysState.erase_init]; exact .init
  | step ev _ hstep ih =>
    refine .step ev ih ?_
    rw [← SysState.erase_step, hstep]
    rfl

/-- Every reachable state of the real system is a reachable state with ghosts, erased. -/
theorem Reachable.exists_ghost (g : Ghost sys) {c : SysState sys} (h : sys.Reachable env c) :
    ∃ c' : SysState (sys.withGhost g), (sys.withGhost g).Reachable env c' ∧ c'.erase = c := by
  induction h with
  | init => exact ⟨_, .init, SysState.erase_init sys g env⟩
  | step ev _ hstep ih =>
    obtain ⟨c', hreach, rfl⟩ := ih
    rw [← SysState.erase_step] at hstep
    obtain ⟨c'', hstep', rfl⟩ := Option.map_eq_some_iff.mp hstep
    exact ⟨c'', .step ev hreach hstep', rfl⟩

/-- A run of the real system from a reachable state is a run with ghosts, erased. -/
theorem Reachable.exists_ghost_run (g : Ghost sys) {c c' : SysState sys} {evs : List (Event σ)}
    (h : sys.Reachable env c) (hrun : c.run env evs = some c') :
    ∃ d d' : SysState (sys.withGhost g), (sys.withGhost g).Reachable env d ∧ d.erase = c ∧
      d.run env evs = some d' ∧ d'.erase = c' := by
  obtain ⟨d, hreach, rfl⟩ := h.exists_ghost g
  rw [← SysState.erase_run] at hrun
  obtain ⟨d', hrun', rfl⟩ := Option.map_eq_some_iff.mp hrun
  exact ⟨d, d', hreach, rfl, hrun', rfl⟩

/-- An invariant proved with ghosts, about the part of the state that is not ghost, holds of
the real system. -/
theorem Invariant.of_ghost (g : Ghost sys) {P : SysState sys → Prop}
    (h : (sys.withGhost g).Invariant env fun c => P c.erase) : sys.Invariant env P := by
  intro c hc
  obtain ⟨c', hreach, rfl⟩ := hc.exists_ghost g
  exact h c' hreach

/-- An invariant of the real system holds of it with ghosts. -/
theorem Invariant.to_ghost (g : Ghost sys) {P : SysState sys → Prop} (h : sys.Invariant env P) :
    (sys.withGhost g).Invariant env fun c => P c.erase :=
  fun _ hc => h _ hc.erase

end System

end Lanes
