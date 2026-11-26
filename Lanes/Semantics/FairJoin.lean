/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.JoinSound
public import Lanes.Actors.MapIOSound
public import Lanes.Semantics.Projection

/-!
# A fair run of a join is a fair run of its left side

`SysState.run_left` says that a finite run of `a.join b w`, seen from `a`, is a run of `a` alone
that shows the same deeds. This file gives the same of fair runs: every fair run of the join is
seen as a fair run of `a` alone under `EnvModel.left` (`System.Run.Fair.left`), so what `a` alone
leads to, it leads to in every join (`System.LeadsTo.join_left`).

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

## Main definitions

- `Obligation.inl`: an obligation of `a` alone as one of the join.
- `Wiring.leftView`: the join seen from `a`.

## Main statements

- `Wiring.leftView_projects`: the view projects fair runs.
- `System.Run.Fair.left`: a fair run of the join is seen as a fair run of `a` alone, state for
  state at corresponding positions and with the same deeds up to them.
- `System.LeadsTo.join_left`: leads-to about the actors of `a` holds of `a` in every join.
-/

@[expose] public section

namespace Lanes

open Cslib

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
theorem Obligation.left?_inl (ob : Obligation σ) : (ob.inl (τ := τ)).event.left? = some ob.event := by
  cases ob with
  | deliver e =>
    obtain ⟨src, i, msg⟩ := e
    cases src <;> rfl
  | _ => rfl

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
    ∃ (r' : a.Run env.left) (f : ℕ → ℕ), r'.Fair ∧ StrictMono f ∧
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
    {d d' : SysState (sys.filterMapIO input output)} {c : SysState sys} {ev : Event (σ.withIO In Out)}
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
  (System.underView_projects hinj env).leadsTo (fun _ _ hrel hP => by obtain ⟨rfl, -⟩ := hrel; exact hP)
    (fun _ _ ⟨hstate, hup⟩ hQ => hstate ▸ hup ▸ hQ) h

end Hidden

end Lanes
