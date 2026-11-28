/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Proof.JoinSound
public import Lanes.Proof.MapIOSound
public import Lanes.Semantics.Projection

/-!
# A fair run of a join is a fair run of each side

`SysState.run_left` says that a finite run of `a.join b w`, seen from `a`, is a run of `a` alone
that shows the same deeds. This file gives the same of fair runs: every fair run of the join is
seen as a fair run of `a` alone under `EnvModel.left` (`System.Run.Fair.left`), so what `a` alone
leads to, it leads to in every join (`System.LeadsTo.join_left`). The same holds behind hidden
inputs and outputs (`System.underView_projects`), which is the other half of what `fronted` is.

The view is the thinnest one: the join seen from `a` with the messages from outside in flight
left out (`SysState.thinLeft`). Alone, `a` is given each message from outside just before the
join delivers it, and is never given one the join drops or a crash removes. With that view a
step of the join is a run of `a` alone with nothing left to choose (`SysState.exists_block`).
The view that keeps the messages from outside is not one: two equal messages from different
senders are one kind of message to `a`, and the join may deliver the newer, while `a` alone
removes the older, so the two orders of what remains in flight differ (D25).

Fairness carries over because every obligation of `a` that is due in the view is an obligation
of the join that is due (`Obligation.inl`): a message between actors of `a` is deliverable in
both or neither, a stopped actor with mail in the view has mail in the join, and an output of
`a` waiting in the view waits in the join. A message from outside is never in the view, and so
never owed by `a`. An output of `a` that the wiring routes to `b` is the one obligation of `a`
alone that is not one of the join, where it is a message to `b`; the run alone hands it over in
the same step as the join sends it, so it never waits. A step that arms a timer of `a` in the
join arms it alone, so a wait the join does not start again `a` alone does not either.

The same holds of `b` under `EnvModel.right` (`System.Run.Fair.right`, `System.LeadsTo.join_right`),
though `b` boots after `a`. What the boot of `a` sends `b` is from outside, so the view
`SysState.thinRight` leaves it out and starts where `b` alone starts. A step of the join is a run
of `b` alone because the join with its sides exchanged takes the same steps, though it is not
reachable (`SysState.exists_blockRight`).

Neither view shows what one side sends the other through the wiring: seen from the sender it
is handed over, seen from the receiver it is from outside. It is a message in flight in the join,
and fairness delivers it as any other (`System.Run.Fair.routed_right`).

## Main definitions

- `Obligation.inl`: an obligation of `a` alone as one of the join.
- `Wiring.leftView`: the join seen from `a`.
- `Obligation.inr`, `Wiring.rightView`: the same for `b`.
- `System.underView`: `sys.filterMapIO input output` seen as `sys`.

## Main statements

- `Wiring.leftView_projects`: the view projects fair runs.
- `System.Run.Fair.left`: a fair run of the join is seen as a fair run of `a` alone, state for
  state at corresponding positions and with the same deeds up to them.
- `System.LeadsTo.join_left`: leads-to about the actors of `a` holds of `a` in every join.
- `Wiring.rightView_projects`, `System.Run.Fair.right`, `System.LeadsTo.join_right`: the same
  for `b`.
- `System.underView_projects`, `System.LeadsTo.filterMapIO`: the same behind other inputs and
  outputs, when `output` shows different outputs differently.
- `System.Run.Fair.routed_right`, `System.Run.Fair.routed_left`: an output one side emits and
  the wiring routes to the other is handled there, on a link that loses nothing, by an actor
  that is not crashed and never stops (`System.Run.Fair.handled_right`, `handled_left`).
-/

@[expose] public section

namespace Lanes

variable {σ τ : Signature} {a : System σ} {b : System τ} {w : Wiring σ τ}
  {env : EnvModel (joinSig σ τ)}

/-- An obligation of `a` alone as the obligation of the join that meets it. -/
def Obligation.inl : Obligation σ → Obligation (joinSig σ τ)
  | .deliver ⟨src, i, msg⟩ => .deliver ⟨src.map .inl, .inl i, msg⟩
  | .timeout i msg => .timeout (.inl i) msg
  | .start i => .start (.inl i)
  | .output out => .output (.inl out)

/-- The event that meets an obligation of the join that stands for one of `a` is, seen from `a`,
the event that meets that one. -/
theorem Obligation.left?_inl (ob : Obligation σ) :
    (ob.inl (τ := τ)).event.left? = some ob.event := by
  cases ob with
  | deliver e =>
    obtain ⟨src, i, msg⟩ := e
    cases src <;> rfl
  | _ => rfl

/-- The only event of a join that shows `a` handing over an output is that output handed over. -/
theorem Event.leftDeed_eq_output {ev : Event (joinSig σ τ)} {out : σ.Out}
    (h : ev.leftDeed = some (.output out)) : ev = .output (.inl out) := by
  cases ev with
  | output o =>
    rcases o with o | o
    · simp only [Event.leftDeed, Option.some.injEq, Deed.output.injEq] at h
      rw [h]
    · simp [Event.leftDeed] at h
  | deliver e | duplicate e =>
    obtain ⟨_, i | j, _⟩ := e <;> simp [Event.leftDeed] at h
  | timeout i msg => rcases i with i | j <;> simp [Event.leftDeed] at h
  | _ => simp [Event.leftDeed] at h

/-- The join seen from its left system `a`, without the messages from outside in flight: states
agree on the actors of `a`, and the join's events show the deeds of `a`. -/
def Wiring.leftView (w : Wiring σ τ) : (a.join b w).View a (Deed σ) where
  rel c d := d = c.thinLeft
  near c d := d.state = c.left.state ∧ d.up = c.left.up
  lift ob := some ob.inl
  shows := Event.leftDeed
  shows' := w.shown

/-- What `a` owes without the messages from outside, the join owes. -/
theorem Obligation.Due.of_thinLeft {c : SysState (a.join b w)} {ob : Obligation σ}
    (h : ob.Due env.left c.thinLeft) : (ob.inl (τ := τ)).Due env c := by
  cases ob with
  | deliver e =>
    obtain ⟨src, i, msg⟩ := e
    obtain ⟨s, hs, hdel⟩ := SysState.deliverable_of_thinLeft h.2
    obtain rfl : src = some s := hs
    exact ⟨h.1, hdel⟩
  | timeout i msg => exact h
  | start i => exact ⟨h.1, SysState.hasMail_of_thinLeft h.2⟩
  | output out =>
    obtain ⟨x, hx, hxo⟩ := List.mem_filterMap.mp (show out ∈ c.left.outbox from h)
    cases x with
    | inl x =>
      obtain rfl : x = out := by simpa using hxo
      exact hx
    | inr x => simp at hxo

/-- The block a step of the join is, as a block of the view. -/
private theorem Wiring.Block.view {c c' : SysState (a.join b w)} {ev : Event (joinSig σ τ)}
    {evs : List (Event σ)} (hb : w.Block env c c' ev evs) :
    w.leftView.Block env.left c (some ev) c' c.thinLeft evs c'.thinLeft where
  run := hb.run
  rel := rfl
  shown := hb.shown
  taken ob' ob hlift hev := by
    obtain rfl := Option.some.inj hlift
    exact hb.taken _ (by rw [Option.some.inj hev]; exact ob'.left?_inl)
  restarts ob' ob ev' hlift hev hrestart := by
    obtain rfl := Option.some.inj hlift
    obtain rfl := Option.some.inj hev
    cases ob' with
    | timeout i msg => exact hb.arms i msg hrestart
    | deliver _ | start _ | output _ => exact hrestart.elim
  near := hb.near

/-- The join seen from `a`, without the messages from outside, projects every fair run of the
join onto a fair run of `a` alone, under `EnvModel.left`. -/
theorem Wiring.leftView_projects (w : Wiring σ τ) (env : EnvModel (joinSig σ τ)) :
    (w.leftView (a := a) (b := b)).Projects env env.left where
  near _ _ h := h ▸ ⟨rfl, rfl⟩
  init := by
    obtain ⟨evs, hrun, hquiet⟩ := SysState.init_thinLeft (a := a) (b := b) (w := w) env
    have hstate := SysState.run_quiet (fun ev hev => (hquiet ev hev).1) hrun
    refine ⟨evs, _, hrun, rfl, List.filterMap_eq_nil_iff.mpr fun ev hev => (hquiet ev hev).2,
      fun _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h), fun j dj hj => .inl ?_⟩
    have hdj := SysState.run_quiet (fun ev hev => (hquiet ev (List.mem_of_mem_take hev)).1) hj
    exact ⟨hdj.1.trans hstate.1.symm, hdj.2.1.trans hstate.2.1.symm⟩
  step c ev c' d hc hd hstep := by
    subst hd
    obtain ⟨evs, hb⟩ := SysState.exists_block hc hstep
    exact ⟨evs, _, hb.view⟩
  due c d ob' _ hd hdue := ⟨_, rfl, hd ▸ hdue |>.of_thinLeft⟩

/-- A fair run of a join, seen from its left system without the messages from outside, is a fair
run of that system alone, when its inputs may be lost, repeated and reordered: position `n` of
the join is position `f n` alone, and up to there the two runs show the same deeds. -/
theorem System.Run.Fair.left {r : (a.join b w).Run env} (hfair : r.Fair) :
    ∃ (r' : a.Run env.left) (f : Nat → Nat), r'.Fair ∧ StrictMono f ∧
      (∀ n, r'.state (f n) = (r.state n).thinLeft) ∧
      ∀ n, (r'.event.take (f n)).filterMap (·.bind w.shown)
        = (r.event.take n).filterMap (·.bind Event.leftDeed) := by
  obtain ⟨r', f, hfair', hsees⟩ := (w.leftView_projects env).fair_run hfair
  exact ⟨r', f, hfair', hsees.mono, hsees.rel, hsees.deeds⟩

/-- What `a` alone leads to, it leads to in every join, of its actors' states: from a state that
satisfies `P` without the messages from outside, to one in which its actors satisfy `Q`. -/
theorem System.LeadsTo.join_left {P : SysState a → Prop}
    {Q : ((i : σ.Id) → a.State i) → (σ.Id → Bool) → Prop}
    (h : a.LeadsTo env.left P fun d => Q d.state d.up) :
    (a.join b w).LeadsTo env (fun c => P c.thinLeft) fun c => Q c.left.state c.left.up :=
  (w.leftView_projects env).leadsTo (fun _ _ hd hP => hd ▸ hP)
    (fun _ _ ⟨hstate, hup⟩ hQ => hstate ▸ hup ▸ hQ) h

/-! ### The right side

The same holds of `b`, the system that boots second. What the boot of `a` sends `b` is from
outside, so the view leaves it out, and the view starts where `b` alone starts once it has handed
over the outputs the wiring routes to `a` (`SysState.init_thinRight`). -/

/-- An obligation of `b` alone as the obligation of the join that meets it. -/
def Obligation.inr : Obligation τ → Obligation (joinSig σ τ)
  | .deliver ⟨src, j, msg⟩ => .deliver ⟨src.map .inr, .inr j, msg⟩
  | .timeout j msg => .timeout (.inr j) msg
  | .start j => .start (.inr j)
  | .output out => .output (.inr out)

theorem Obligation.right?_inr (ob : Obligation τ) :
    (ob.inr (σ := σ)).event.right? = some ob.event := by
  cases ob with
  | deliver e =>
    obtain ⟨src, j, msg⟩ := e
    cases src <;> rfl
  | _ => rfl

/-- The join seen from its right system `b`, without the messages from outside in flight. -/
def Wiring.rightView (w : Wiring σ τ) : (a.join b w).View b (Deed τ) where
  rel c d := d = c.thinRight
  near c d := d.state = c.right.state ∧ d.up = c.right.up
  lift ob := some ob.inr
  shows := Event.rightDeed
  shows' := w.shownRight

/-- What `b` owes without the messages from outside, the join owes. -/
theorem Obligation.Due.of_thinRight {c : SysState (a.join b w)} {ob : Obligation τ}
    (h : ob.Due env.right c.thinRight) : (ob.inr (σ := σ)).Due env c := by
  cases ob with
  | deliver e =>
    obtain ⟨src, j, msg⟩ := e
    obtain ⟨s, hs, hdel⟩ := SysState.deliverable_of_thinRight h.2
    obtain rfl : src = some s := hs
    exact ⟨h.1, hdel⟩
  | timeout j msg => exact h
  | start j => exact ⟨h.1, SysState.hasMail_of_thinRight h.2⟩
  | output out =>
    obtain ⟨x, hx, hxo⟩ := List.mem_filterMap.mp (show out ∈ c.right.outbox from h)
    cases x with
    | inl x => simp at hxo
    | inr x =>
      obtain rfl : x = out := by simpa using hxo
      exact hx

/-- The block a step of the join is, as a block of the right view. -/
private theorem Wiring.BlockRight.view {c c' : SysState (a.join b w)} {ev : Event (joinSig σ τ)}
    {evs : List (Event τ)} (hb : w.BlockRight env c c' ev evs) :
    w.rightView.Block env.right c (some ev) c' c.thinRight evs c'.thinRight where
  run := hb.run
  rel := rfl
  shown := hb.shown
  taken ob' ob hlift hev := by
    obtain rfl := Option.some.inj hlift
    exact hb.taken _ (by rw [Option.some.inj hev]; exact ob'.right?_inr)
  restarts ob' ob ev' hlift hev hrestart := by
    obtain rfl := Option.some.inj hlift
    obtain rfl := Option.some.inj hev
    cases ob' with
    | timeout j msg => exact hb.arms j msg hrestart
    | deliver _ | start _ | output _ => exact hrestart.elim
  near := hb.near

/-- The join seen from `b`, without the messages from outside, projects every fair run of the
join onto a fair run of `b` alone, under `EnvModel.right`. -/
theorem Wiring.rightView_projects (w : Wiring σ τ) (env : EnvModel (joinSig σ τ)) :
    (w.rightView (a := a) (b := b)).Projects env env.right where
  near _ _ h := h ▸ ⟨rfl, rfl⟩
  init := by
    obtain ⟨evs, hrun, hquiet⟩ := SysState.init_thinRight (a := a) (b := b) (w := w) env
    have hstate := SysState.run_quiet (fun ev hev => (hquiet ev hev).1) hrun
    refine ⟨evs, _, hrun, rfl, List.filterMap_eq_nil_iff.mpr fun ev hev => (hquiet ev hev).2,
      fun _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h), fun j dj hj => .inl ?_⟩
    have hdj := SysState.run_quiet (fun ev hev => (hquiet ev (List.mem_of_mem_take hev)).1) hj
    exact ⟨hdj.1.trans hstate.1.symm, hdj.2.1.trans hstate.2.1.symm⟩
  step c ev c' d hc hd hstep := by
    subst hd
    obtain ⟨evs, hb⟩ := SysState.exists_blockRight hc hstep
    exact ⟨evs, _, hb.view⟩
  due c d ob' _ hd hdue := ⟨_, rfl, hd ▸ hdue |>.of_thinRight⟩

/-- A fair run of a join, seen from its right system without the messages from outside, is a
fair run of that system alone, when its inputs may be lost, repeated and reordered: position `n`
of the join is position `f n` alone, and up to there the two runs show the same deeds. -/
theorem System.Run.Fair.right {r : (a.join b w).Run env} (hfair : r.Fair) :
    ∃ (r' : b.Run env.right) (f : Nat → Nat), r'.Fair ∧ StrictMono f ∧
      (∀ n, r'.state (f n) = (r.state n).thinRight) ∧
      ∀ n, (r'.event.take (f n)).filterMap (·.bind w.shownRight)
        = (r.event.take n).filterMap (·.bind Event.rightDeed) := by
  obtain ⟨r', f, hfair', hsees⟩ := (w.rightView_projects env).fair_run hfair
  exact ⟨r', f, hfair', hsees.mono, hsees.rel, hsees.deeds⟩

/-- What `b` alone leads to, it leads to in every join, of its actors' states: from a state that
satisfies `P` without the messages from outside, to one in which its actors satisfy `Q`. -/
theorem System.LeadsTo.join_right {P : SysState b → Prop}
    {Q : ((j : τ.Id) → b.State j) → (τ.Id → Bool) → Prop}
    (h : b.LeadsTo env.right P fun d => Q d.state d.up) :
    (a.join b w).LeadsTo env (fun c => P c.thinRight) fun c => Q c.right.state c.right.up :=
  (w.rightView_projects env).leadsTo (fun _ _ hd hP => hd ▸ hP)
    (fun _ _ ⟨hstate, hup⟩ hQ => hstate ▸ hup ▸ hQ) h

/-! ### Across the wiring

An output of `a` that the wiring routes to `b` is, in the join, a message in flight from an actor
of `a` to an actor of `b`. Neither view above shows it: seen from `a` it is handed over, seen
from `b` it is from outside. Fairness delivers it as it delivers any message, on a link that
does not lose it, to an actor that the environment does not crash and that never stops
(`System.Run.Fair.handled`). Each premise is needed. A lossy link may drop it, which is the
environment's choice, so no fairness rules it out. A crash or a stop takes the receiver down,
and its mail with it on a link that loses nothing (`SysState.down`). -/

namespace Wiring

variable {i : σ.Id} {j : τ.Id}

theorem isStop_right (effs : List (Effect τ j)) :
    (effs.flatMap fun eff => [w.right a eff]).any Effect.isStop = effs.any Effect.isStop :=
  Effect.any_isStop_flatMap (fun eff => by
    cases eff with
    | emit out => cases h : w.toLeft out <;> simp [Effect.isStop, Wiring.right, h]
    | _ => simp [Effect.isStop, Wiring.right]) effs

/-- An output of `a` that the wiring routes to `b` is sent to the actor of `b` that takes it. -/
theorem mem_sends_left {effs : List (Effect σ i)} {out : σ.Out} {x : τ.In}
    (hout : .emit out ∈ effs) (hx : w.toRight out = some x) :
    (⟨some (.inl i), .inr (b.accept x).1, (b.accept x).2⟩ : Envelope (joinSig σ τ)) ∈
      Effect.sends (σ := joinSig σ τ) (.inl i) (effs.flatMap fun eff => [w.left b eff]) :=
  Effect.mem_sends.mpr ⟨rfl, List.mem_flatMap.mpr ⟨_, hout, by simp [Wiring.left, hx]⟩⟩

/-- An output of `b` that the wiring routes to `a` is sent to the actor of `a` that takes it. -/
theorem mem_sends_right {effs : List (Effect τ j)} {out : τ.Out} {x : σ.In}
    (hout : .emit out ∈ effs) (hx : w.toLeft out = some x) :
    (⟨some (.inr j), .inl (a.accept x).1, (a.accept x).2⟩ : Envelope (joinSig σ τ)) ∈
      Effect.sends (σ := joinSig σ τ) (.inr j) (effs.flatMap fun eff => [w.right a eff]) :=
  Effect.mem_sends.mpr ⟨rfl, List.mem_flatMap.mpr ⟨_, hout, by simp [Wiring.right, hx]⟩⟩

end Wiring

/-- A step of the join in which an actor of `a` handles a message puts in flight what that
actor sends to the other actors. -/
theorem SysState.mem_net_of_leftDeed {c c' : SysState (a.join b w)} {ev : Event (joinSig σ τ)}
    (hstep : c.step env ev = some c') {i : σ.Id} {msg : σ.Msg i}
    (hdeed : ev.leftDeed = some (.handle i msg)) {e : Envelope (joinSig σ τ)}
    (he : e ∈ Effect.sends (σ := joinSig σ τ) (.inl i)
      (((a.actor i).step (c.state (.inl i)) msg).2.flatMap fun eff => [w.left b eff]))
    (hne : e.dst ≠ .inl i) : e ∈ c'.net := by
  cases ev with
  | deliver x =>
    obtain ⟨src, i' | j, m⟩ := x
    · simp only [Event.leftDeed, Option.some.injEq, Deed.handle.injEq] at hdeed
      obtain ⟨rfl, hm⟩ := hdeed
      cases hm
      obtain ⟨-, -, rfl⟩ := SysState.step_deliver.mp hstep
      exact SysState.mem_net_settle_of_sends he hne
    · simp [Event.leftDeed] at hdeed
  | duplicate x =>
    obtain ⟨src, i' | j, m⟩ := x
    · simp only [Event.leftDeed, Option.some.injEq, Deed.handle.injEq] at hdeed
      obtain ⟨rfl, hm⟩ := hdeed
      cases hm
      obtain ⟨-, -, -, rfl⟩ := SysState.step_duplicate.mp hstep
      exact SysState.mem_net_settle_of_sends he hne
    · simp [Event.leftDeed] at hdeed
  | timeout x m =>
    rcases x with i' | j
    · simp only [Event.leftDeed, Option.some.injEq, Deed.handle.injEq] at hdeed
      obtain ⟨rfl, hm⟩ := hdeed
      cases hm
      obtain ⟨-, -, rfl⟩ := SysState.step_timeout.mp hstep
      exact SysState.mem_net_settle_of_sends he hne
    · simp [Event.leftDeed] at hdeed
  | output o => rcases o with o | o <;> simp [Event.leftDeed] at hdeed
  | input _ | drop _ | crash _ | start _ => simp [Event.leftDeed] at hdeed

/-- A step of the join in which an actor of `b` handles a message puts in flight what that
actor sends to the other actors. -/
theorem SysState.mem_net_of_rightDeed {c c' : SysState (a.join b w)} {ev : Event (joinSig σ τ)}
    (hstep : c.step env ev = some c') {j : τ.Id} {msg : τ.Msg j}
    (hdeed : ev.rightDeed = some (.handle j msg)) {e : Envelope (joinSig σ τ)}
    (he : e ∈ Effect.sends (σ := joinSig σ τ) (.inr j)
      (((b.actor j).step (c.state (.inr j)) msg).2.flatMap fun eff => [w.right a eff]))
    (hne : e.dst ≠ .inr j) : e ∈ c'.net := by
  cases ev with
  | deliver x =>
    obtain ⟨src, i | j', m⟩ := x
    · simp [Event.rightDeed] at hdeed
    · simp only [Event.rightDeed, Option.some.injEq, Deed.handle.injEq] at hdeed
      obtain ⟨rfl, hm⟩ := hdeed
      cases hm
      obtain ⟨-, -, rfl⟩ := SysState.step_deliver.mp hstep
      exact SysState.mem_net_settle_of_sends he hne
  | duplicate x =>
    obtain ⟨src, i | j', m⟩ := x
    · simp [Event.rightDeed] at hdeed
    · simp only [Event.rightDeed, Option.some.injEq, Deed.handle.injEq] at hdeed
      obtain ⟨rfl, hm⟩ := hdeed
      cases hm
      obtain ⟨-, -, -, rfl⟩ := SysState.step_duplicate.mp hstep
      exact SysState.mem_net_settle_of_sends he hne
  | timeout x m =>
    rcases x with i | j'
    · simp [Event.rightDeed] at hdeed
    · simp only [Event.rightDeed, Option.some.injEq, Deed.handle.injEq] at hdeed
      obtain ⟨rfl, hm⟩ := hdeed
      cases hm
      obtain ⟨-, -, rfl⟩ := SysState.step_timeout.mp hstep
      exact SysState.mem_net_settle_of_sends he hne
  | output o => rcases o with o | o <;> simp [Event.rightDeed] at hdeed
  | input _ | drop _ | crash _ | start _ => simp [Event.rightDeed] at hdeed

/-- A step of the join leaves an actor of `a` as it was, or is that actor handling a message, or
starting. -/
theorem SysState.step_left_state {c c' : SysState (a.join b w)} {ev : Event (joinSig σ τ)}
    (hstep : c.step env ev = some c') (i : σ.Id) :
    c'.state (.inl i) = c.state (.inl i) ∨
      (∃ msg, ev.leftDeed = some (.handle i msg) ∧
        c'.state (.inl i) = ((a.actor i).step (c.state (.inl i)) msg).1) ∨
      (ev = .start (.inl i) ∧
        c'.state (.inl i) = ((a.actor i).recover (c.state (.inl i))).1) := by
  have hhandle (c₀ : SysState (a.join b w)) (hs : c₀.state = c.state) (x : σ.Id ⊕ τ.Id)
      (m : JoinMsg σ τ x) (hdeed : ∀ m' : σ.Msg i, x = .inl i → HEq m m' →
        ev.leftDeed = some (.handle i m')) :
      (c₀.handle env x m).state (.inl i) = c.state (.inl i) ∨
        ∃ msg, ev.leftDeed = some (.handle i msg) ∧
          (c₀.handle env x m).state (.inl i) = ((a.actor i).step (c.state (.inl i)) msg).1 := by
    rw [SysState.handle_state, hs]
    rcases x with i' | j
    · by_cases h : i' = i
      · subst h
        exact .inr ⟨m, hdeed m rfl HEq.rfl, by simp [Actor.mapEff]⟩
      · exact .inl (update_of_ne _ _ (by simpa using Ne.symm h))
    · exact .inl (update_of_ne _ _ (by simp))
  cases ev with
  | input _ =>
    obtain rfl := SysState.step_input.mp hstep
    exact .inl rfl
  | deliver e =>
    obtain ⟨src, x, m⟩ := e
    obtain ⟨-, -, rfl⟩ := SysState.step_deliver.mp hstep
    exact (hhandle { c with net := c.net.erase ⟨src, x, m⟩ } rfl x m fun _ hx hm => by
      subst hx; cases hm; rfl).imp_right .inl
  | duplicate e =>
    obtain ⟨src, x, m⟩ := e
    obtain ⟨-, -, -, rfl⟩ := SysState.step_duplicate.mp hstep
    exact (hhandle c rfl x m fun _ hx hm => by
      subst hx; cases hm; rfl).imp_right .inl
  | timeout x m =>
    obtain ⟨-, -, rfl⟩ := SysState.step_timeout.mp hstep
    exact (hhandle { c with timers := update c.timers x ((c.timers x).erase m) } rfl x m fun _ hx hm => by
      subst hx; cases hm; rfl).imp_right .inl
  | drop _ =>
    obtain ⟨-, -, rfl⟩ := SysState.step_drop.mp hstep
    exact .inl rfl
  | output _ =>
    obtain ⟨-, rfl⟩ := SysState.step_output.mp hstep
    exact .inl rfl
  | crash _ =>
    obtain ⟨-, -, rfl⟩ := SysState.step_crash.mp hstep
    exact .inl rfl
  | start x =>
    obtain ⟨-, -, rfl⟩ := SysState.step_start.mp hstep
    rw [SysState.startActor_state]
    rcases x with i' | j
    · by_cases h : i' = i
      · subst h
        exact .inr (.inr ⟨rfl, by simp [Actor.mapEff]⟩)
      · exact .inl (update_of_ne _ _ (by simpa using Ne.symm h))
    · exact .inl (update_of_ne _ _ (by simp))

/-- In a fair run of a join, a message in flight to an actor of `b` is handled by it, on a link
that does not lose it, when the environment does not crash that actor and it never stops. -/
theorem System.Run.Fair.handled_right {r : (a.join b w).Run env} (hfair : r.Fair) {n : Nat}
    {src : Option (σ.Id ⊕ τ.Id)} {j : τ.Id} {msg : τ.Msg j}
    (hlossless : (env.link src (.inr j)).lossy = false) (hcrash : env.mayCrash (.inr j) = false)
    (hruns : ∀ s m, ((b.actor j).step s m).2.any Effect.isStop = false)
    (hrecovers : ∀ s, ((b.actor j).recover s).2.any Effect.isStop = false)
    (he : (⟨src, .inr j, msg⟩ : Envelope (joinSig σ τ)) ∈ (r.state n).net) :
    ∃ m, n ≤ m ∧ (r.event m = some (.deliver ⟨src, .inr j, msg⟩) ∨
      r.event m = some (.duplicate ⟨src, .inr j, msg⟩)) :=
  hfair.handled hlossless hcrash (fun s m => (w.isStop_right _).trans (hruns s m))
    (fun s => (w.isStop_right _).trans (hrecovers s)) he

/-- In a fair run of a join, a message in flight to an actor of `a` is handled by it, on a link
that does not lose it, when the environment does not crash that actor and it never stops. -/
theorem System.Run.Fair.handled_left {r : (a.join b w).Run env} (hfair : r.Fair) {n : Nat}
    {src : Option (σ.Id ⊕ τ.Id)} {i : σ.Id} {msg : σ.Msg i}
    (hlossless : (env.link src (.inl i)).lossy = false) (hcrash : env.mayCrash (.inl i) = false)
    (hruns : ∀ s m, ((a.actor i).step s m).2.any Effect.isStop = false)
    (hrecovers : ∀ s, ((a.actor i).recover s).2.any Effect.isStop = false)
    (he : (⟨src, .inl i, msg⟩ : Envelope (joinSig σ τ)) ∈ (r.state n).net) :
    ∃ m, n ≤ m ∧ (r.event m = some (.deliver ⟨src, .inl i, msg⟩) ∨
      r.event m = some (.duplicate ⟨src, .inl i, msg⟩)) :=
  hfair.handled hlossless hcrash (fun s m => (w.isStop_left _).trans (hruns s m))
    (fun s => (w.isStop_left _).trans (hrecovers s)) he

/-- In a fair run of a join, an output that an actor of `a` emits as it handles a message, and
that the wiring routes to `b`, is handled by the actor of `b` that takes it, at a later
position: on a link that does not lose it, when the environment does not crash that actor and
it never stops. -/
theorem System.Run.Fair.routed_right {r : (a.join b w).Run env} (hfair : r.Fair) {n : Nat}
    {ev : Event (joinSig σ τ)} {i : σ.Id} {msg : σ.Msg i} {out : σ.Out} {x : τ.In}
    (hev : r.event n = some ev) (hdeed : ev.leftDeed = some (.handle i msg))
    (hout : .emit out ∈ ((a.actor i).step ((r.state n).state (.inl i)) msg).2)
    (hx : w.toRight out = some x)
    (hlossless : (env.link (some (.inl i)) (.inr (b.accept x).1)).lossy = false)
    (hcrash : env.mayCrash (.inr (b.accept x).1) = false)
    (hruns : ∀ s m, ((b.actor (b.accept x).1).step s m).2.any Effect.isStop = false)
    (hrecovers : ∀ s, ((b.actor (b.accept x).1).recover s).2.any Effect.isStop = false) :
    ∃ m, n < m ∧
      (r.event m = some (.deliver ⟨some (.inl i), .inr (b.accept x).1, (b.accept x).2⟩) ∨
        r.event m = some (.duplicate ⟨some (.inl i), .inr (b.accept x).1, (b.accept x).2⟩)) := by
  have he := SysState.mem_net_of_leftDeed (System.Run.step_some hev) hdeed
    (w.mem_sends_left hout hx) (by simp)
  obtain ⟨m, hm, h⟩ := hfair.handled_right hlossless hcrash hruns hrecovers he
  exact ⟨m, by omega, h⟩

/-- In a fair run of a join, an output that an actor of `b` emits as it handles a message, and
that the wiring routes to `a`, is handled by the actor of `a` that takes it, at a later
position: on a link that does not lose it, when the environment does not crash that actor and
it never stops. -/
theorem System.Run.Fair.routed_left {r : (a.join b w).Run env} (hfair : r.Fair) {n : Nat}
    {ev : Event (joinSig σ τ)} {j : τ.Id} {msg : τ.Msg j} {out : τ.Out} {x : σ.In}
    (hev : r.event n = some ev) (hdeed : ev.rightDeed = some (.handle j msg))
    (hout : .emit out ∈ ((b.actor j).step ((r.state n).state (.inr j)) msg).2)
    (hx : w.toLeft out = some x)
    (hlossless : (env.link (some (.inr j)) (.inl (a.accept x).1)).lossy = false)
    (hcrash : env.mayCrash (.inl (a.accept x).1) = false)
    (hruns : ∀ s m, ((a.actor (a.accept x).1).step s m).2.any Effect.isStop = false)
    (hrecovers : ∀ s, ((a.actor (a.accept x).1).recover s).2.any Effect.isStop = false) :
    ∃ m, n < m ∧
      (r.event m = some (.deliver ⟨some (.inr j), .inl (a.accept x).1, (a.accept x).2⟩) ∨
        r.event m = some (.duplicate ⟨some (.inr j), .inl (a.accept x).1, (a.accept x).2⟩)) := by
  have he := SysState.mem_net_of_rightDeed (System.Run.step_some hev) hdeed
    (w.mem_sends_right hout hx) (by simp)
  obtain ⟨m, hm, h⟩ := hfair.handled_left hlossless hcrash hruns hrecovers he
  exact ⟨m, by omega, h⟩

/-! ### Behind other inputs and outputs

A fair run of `sys.filterMapIO input output` is a fair run of `sys` event for event, but for
the outputs that `output` hides: alone, `sys` would owe their hand-over, so the run of `sys`
hands each over in the step that emits it. An output that is shown is owed in both. When two
outputs of `sys` are shown alike, handing one over in `sys.filterMapIO input output` hands over
either in `sys`, and which one is not fixed; so the projection asks that `output` show different
outputs differently. -/

section Hidden

variable {In Out : Type} [DecidableEq In] [DecidableEq Out] {sys : System σ}
  {input : In → σ.In} {output : σ.Out → Option Out} {env : EnvModel (σ.withIO In Out)}

/-- `c` with the outputs that `output` hides handed over. -/
def SysState.unhidden (output : σ.Out → Option Out) (c : SysState sys) : SysState sys :=
  { c with outbox := c.outbox.filter fun out => (output out).isSome }

/-- Handing over the outputs that `output` hides. -/
def SysState.hidden (output : σ.Out → Option Out) (c : SysState sys) : List (Event σ) :=
  (c.outbox.filter fun out => !(output out).isSome).map .output

omit [DecidableEq Out] in
/-- The hidden outputs can be handed over, and that changes nothing that is seen. -/
theorem SysState.run_hidden (env : EnvModel σ) (c : SysState sys) :
    c.run env (c.hidden output) = some (c.unhidden output) := by
  exact SysState.run_outputs_filter env c (fun out => (output out).isSome) [] c.outbox (by simp)

omit [DecidableEq Out] in
/-- Handing over the hidden outputs is quiet. -/
theorem SysState.hidden_quiet (c : SysState sys) : ∀ ev ∈ c.hidden output, ev.quiet = true := by
  intro ev hev
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hev
  rfl

/-- What is seen of `c` does not change when its hidden outputs are handed over. -/
theorem SysState.over_unhidden (c : SysState sys) :
    (c.unhidden output).over input output = c.over input output := by
  refine SysState.ext' rfl rfl rfl rfl ?_
  show (c.outbox.filter _).filterMap output = c.outbox.filterMap output
  rw [List.filterMap_filter]
  congr 1
  funext out
  cases output out <;> rfl

/-- `sys.filterMapIO input output` seen as `sys`, with no hidden output waiting. -/
def System.underView (sys : System σ) (input : In → σ.In) (output : σ.Out → Option Out) :
    (sys.filterMapIO input output).View sys Out where
  rel d c := c.over input output = d ∧ ∀ out ∈ c.outbox, (output out).isSome = true
  near d c := c.state = d.state ∧ c.up = d.up
  lift
    | .deliver e => some (.deliver e.over)
    | .timeout i msg => some (.timeout i msg)
    | .start i => some (.start i)
    | .output out => (output out).map .output
  shows
    | .output o => some o
    | _ => none
  shows'
    | .output out => output out
    | _ => none

/-- The run of `sys` that stands for a step of `sys.filterMapIO input output`: the step it
stands for, then the hidden outputs it emitted handed over. -/
private theorem underView_block
    (hinj : ∀ o₁ o₂ x, output o₁ = some x → output o₂ = some x → o₁ = o₂)
    {d d' : SysState (sys.filterMapIO input output)} {c : SysState sys}
    {ev : Event (σ.withIO In Out)}
    (hrel : (sys.underView input output).rel d c) (hstep : d.step env ev = some d') :
    ∃ evs c', (sys.underView input output).Block env.under d (some ev) d' c evs c' := by
  obtain ⟨rfl, hshown⟩ := hrel
  obtain ⟨ev', c₁, hunder, hstep', rfl⟩ := SysState.step_under hstep
  have hrun : c.run env.under (ev' :: c₁.hidden output) = some (c₁.unhidden output) := by
    simp [SysState.run, hstep', SysState.run_hidden]
  refine ⟨_, _, hrun, ⟨SysState.over_unhidden c₁, fun out hout => (List.mem_filter.mp hout).2⟩,
    ?_, fun ob' ob hlift hev => ?_, fun ob' ob ev₁ hlift hev hrestart => ?_, fun j dj hj => ?_⟩
  · have hhidden : (c₁.hidden output).filterMap (sys.underView input output).shows' = [] := by
      refine List.filterMap_eq_nil_iff.mpr fun ev hev => ?_
      obtain ⟨out, hout, rfl⟩ := List.mem_map.mp hev
      simpa [System.underView] using (List.mem_filter.mp hout).2
    rw [filterMap_cons_toList, hhidden, List.append_nil]
    cases ev with
    | output o =>
      obtain ⟨out', rfl, hout'⟩ := hunder
      simp [System.underView, hout']
    | _ =>
      cases hunder
      rfl
  · obtain rfl := Option.some.inj hev
    refine List.mem_cons.mpr (.inl ?_)
    cases ob' with
    | deliver e =>
      obtain rfl := Option.some.inj hlift
      exact hunder.symm
    | timeout i msg =>
      obtain rfl := Option.some.inj hlift
      exact hunder.symm
    | start i =>
      obtain rfl := Option.some.inj hlift
      exact hunder.symm
    | output out =>
      cases hout : output out with
      | none => simp [System.underView, hout] at hlift
      | some o =>
        simp only [System.underView, hout, Option.map_some, Option.some.injEq] at hlift
        subst hlift
        obtain ⟨out'', rfl, hout''⟩ := hunder
        rw [hinj _ _ _ hout'' hout]
        rfl
  · obtain rfl := Option.some.inj hev
    cases ob' with
    | timeout i msg =>
      obtain rfl := Option.some.inj hlift
      exact ⟨0, by simp, c, rfl, SysState.arms_under hunder hrestart⟩
    | deliver e =>
      obtain rfl := Option.some.inj hlift
      exact hrestart.elim
    | start i =>
      obtain rfl := Option.some.inj hlift
      exact hrestart.elim
    | output out =>
      cases hout : output out with
      | none => simp [System.underView, hout] at hlift
      | some o =>
        simp only [System.underView, hout, Option.map_some, Option.some.injEq] at hlift
        subst hlift
        exact hrestart.elim
  · cases j with
    | zero =>
      simp only [List.take_zero, SysState.run, Option.some.injEq] at hj
      exact .inl (hj ▸ ⟨rfl, rfl⟩)
    | succ j =>
      simp only [List.take_succ_cons, SysState.run, hstep', Option.bind_some] at hj
      have hdj := SysState.run_quiet
        (fun ev hev => SysState.hidden_quiet c₁ ev (List.mem_of_mem_take hev)) hj
      exact .inr ⟨hdj.1, hdj.2.1⟩

/-- `sys.filterMapIO input output` seen as `sys` projects fair runs onto fair runs, when `output`
shows different outputs differently. -/
theorem System.underView_projects
    (hinj : ∀ o₁ o₂ x, output o₁ = some x → output o₂ = some x → o₁ = o₂)
    (env : EnvModel (σ.withIO In Out)) :
    (sys.underView input output).Projects env env.under where
  near _ _ h := h.1 ▸ ⟨rfl, rfl⟩
  init := by
    have hquiet := SysState.run_quiet (SysState.hidden_quiet _)
      (SysState.run_hidden (output := output) env.under (SysState.init sys env.under))
    refine ⟨_, _, SysState.run_hidden env.under _,
      ⟨(SysState.over_unhidden _).trans SysState.init_over, fun out hout =>
        (List.mem_filter.mp hout).2⟩, ?_, fun _ _ _ h => (by cases h),
      fun _ _ _ _ h => (by cases h), fun j dj hj => .inl ?_⟩
    · refine List.filterMap_eq_nil_iff.mpr fun ev hev => ?_
      obtain ⟨out, hout, rfl⟩ := List.mem_map.mp hev
      simpa [System.underView] using (List.mem_filter.mp hout).2
    · have hdj := SysState.run_quiet (fun ev hev =>
        SysState.hidden_quiet (output := output) _ ev (List.mem_of_mem_take hev)) hj
      rw [← SysState.init_over (input := input) (output := output)]
      exact ⟨hdj.1, hdj.2.1⟩
  step _ _ _ _ _ hrel hstep := underView_block hinj hrel hstep
  due d c ob' _ hrel hdue := by
    obtain ⟨rfl, hshown⟩ := hrel
    cases ob' with
    | deliver e =>
      exact ⟨_, rfl, hdue.1, (SysState.deliverable_over c e).trans hdue.2⟩
    | timeout i msg => exact ⟨_, rfl, hdue⟩
    | start i => exact ⟨_, rfl, hdue.1, (SysState.hasMail_over c i).trans hdue.2⟩
    | output out =>
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (hshown out hdue)
      exact ⟨.output o, by simp [System.underView, ho],
        List.mem_filterMap.mpr ⟨out, hdue, ho⟩⟩

/-- What `sys` leads to, of its actors' states, it leads to behind other inputs and outputs,
when `output` shows different outputs differently. -/
theorem System.LeadsTo.filterMapIO
    (hinj : ∀ o₁ o₂ x, output o₁ = some x → output o₂ = some x → o₁ = o₂)
    {P Q : ((i : σ.Id) → sys.State i) → (σ.Id → Bool) → Prop}
    (h : sys.LeadsTo env.under (fun c => P c.state c.up) fun c => Q c.state c.up) :
    (sys.filterMapIO input output).LeadsTo env (fun d => P d.state d.up)
      fun d => Q d.state d.up :=
  (System.underView_projects hinj env).leadsTo
    (fun _ _ hrel hP => by obtain ⟨rfl, -⟩ := hrel; exact hP)
    (fun _ _ ⟨hstate, hup⟩ hQ => hstate ▸ hup ▸ hQ) h

end Hidden

end Lanes
