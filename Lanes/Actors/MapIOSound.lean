/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Join
public import Lanes.Actors.KernelSound

/-!
# What hiding inputs and outputs keeps

`sys.filterMapIO input output` does nothing `sys` does not do. `SysState.over` is a state of
`sys` seen through the new inputs and outputs: the same actors, timers and messages, and of the
outputs waiting those that are shown. `SysState.run_filterMapIO` proves that every run of
`sys.filterMapIO input output` is a run of `sys`, event for event (`Event.AllUnder`): an input
is the input it stands for, an output is an output of `sys` shown as it, and every other event
is itself. So whatever is proved of every run of `sys` holds of it behind other inputs and outputs.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature} {In Out : Type} [DecidableEq In] [DecidableEq Out]

namespace Envelope

def over (e : Envelope σ) : Envelope (σ.withIO In Out) := ⟨e.src, e.dst, e.msg⟩

def under (e : Envelope (σ.withIO In Out)) : Envelope σ := ⟨e.src, e.dst, e.msg⟩

end Envelope

def EnvModel.under (env : EnvModel (σ.withIO In Out)) : EnvModel σ where
  link := env.link
  mayCrash := env.mayCrash
  restarts := env.restarts

def SysState.over {sys : System σ} (input : In → σ.In) (output : σ.Out → Option Out)
    (c : SysState sys) : SysState (sys.filterMapIO input output) where
  state := c.state
  up := c.up
  net := c.net.map Envelope.over
  timers := c.timers
  outbox := c.outbox.filterMap output

/-- `ev'` is an event of `sys` that the event `ev` of `sys.filterMapIO input output` stands
for. -/
def Event.Under (input : In → σ.In) (output : σ.Out → Option Out) :
    Event (σ.withIO In Out) → Event σ → Prop
  | .input x, ev' => ev' = .input (input x)
  | .output out, ev' => ∃ out', ev' = .output out' ∧ output out' = some out
  | .deliver e, ev' => ev' = .deliver e.under
  | .duplicate e, ev' => ev' = .duplicate e.under
  | .drop e, ev' => ev' = .drop e.under
  | .timeout i msg, ev' => ev' = .timeout i msg
  | .crash i, ev' => ev' = .crash i
  | .start i, ev' => ev' = .start i

def Event.AllUnder (input : In → σ.In) (output : σ.Out → Option Out) :
    List (Event (σ.withIO In Out)) → List (Event σ) → Prop
  | [], [] => True
  | ev :: events, ev' :: events' =>
    Event.Under input output ev ev' ∧ AllUnder input output events events'
  | _, _ => False

end Lanes

end

public section

namespace Lanes

variable {σ : Signature} {In Out : Type} [DecidableEq In] [DecidableEq Out] {sys : System σ}
  {input : In → σ.In} {output : σ.Out → Option Out} {env : EnvModel (σ.withIO In Out)}

private theorem map_erase {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : ∀ x y, f x = f y → x = y) (l : List α) (a : α) :
    (l.erase a).map f = (l.map f).erase (f a) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : x = a
    · subst hx
      simp
    · have hfx : f x ≠ f a := fun h => hx (hf _ _ h)
      simp [hx, hfx, ih]

/-- An output shown as `out` waits: handing over the first such is handing over `out`. -/
private theorem filterMap_erase_shown {α β : Type} [DecidableEq α] [DecidableEq β]
    {f : α → Option β} {b : β} :
    ∀ l : List α, b ∈ l.filterMap f →
      ∃ a ∈ l, f a = some b ∧ (l.erase a).filterMap f = (l.filterMap f).erase b := by
  intro l
  induction l with
  | nil => exact fun h => absurd h (by simp)
  | cons x l ih =>
    intro h
    cases hfx : f x with
    | none =>
      rw [List.filterMap_cons_none hfx] at h
      obtain ⟨a, ha, hfa, heq⟩ := ih h
      have hx : x ≠ a := fun hxa => by simp [hxa, hfa] at hfx
      exact ⟨a, List.mem_cons_of_mem _ ha, hfa, by simp [hx, hfx, heq]⟩
    | some y =>
      by_cases hy : y = b
      · subst hy
        exact ⟨x, List.mem_cons_self, hfx, by simp [hfx]⟩
      · rw [List.filterMap_cons_some hfx] at h
        obtain ⟨a, ha, hfa, heq⟩ := ih ((List.mem_cons.mp h).resolve_left fun hb => hy hb.symm)
        have hx : x ≠ a := fun hxa => hy (by simpa [hxa, hfa] using hfx.symm)
        exact ⟨a, List.mem_cons_of_mem _ ha, hfa, by simp [hx, hfx, heq, hy]⟩

/-- What every event shows as the event it stands for shows, the two runs show. -/
theorem Event.AllUnder.filterMap_eq {β : Type} {f : Event (σ.withIO In Out) → Option β}
    {g : Event σ → Option β} (hfg : ∀ ev ev', Event.Under input output ev ev' → f ev = g ev') :
    ∀ {events : List (Event (σ.withIO In Out))} {events' : List (Event σ)},
      Event.AllUnder input output events events' → events.filterMap f = events'.filterMap g
  | [], [], _ => rfl
  | ev :: events, ev' :: events', h => by
    rw [List.filterMap_cons, List.filterMap_cons, hfg ev ev' h.1, filterMap_eq hfg h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

namespace Envelope

private theorem over_inj (x y : Envelope σ) (h : (x.over : Envelope (σ.withIO In Out)) = y.over) :
    x = y := by
  obtain ⟨_, _, _⟩ := x
  obtain ⟨_, _, _⟩ := y
  simp only [over, Envelope.mk.injEq] at h
  obtain ⟨rfl, rfl, h⟩ := h
  rw [eq_of_heq h]

private theorem over_under (e : Envelope (σ.withIO In Out)) :
    (e.under.over : Envelope (σ.withIO In Out)) = e := rfl

end Envelope

namespace SysState

private theorem over_perform (c : SysState sys) (i : σ.Id) (eff : Effect σ i) :
    (c.perform i eff).over input output
      = (c.over input output).performAll i (Effect.filterMapOut output eff) := by
  cases eff with
  | send to msg => simp [over, perform, performAll, Effect.filterMapOut, Envelope.over]
  | emit out => cases h : output out <;> simp [over, perform, performAll, Effect.filterMapOut, h]
  | after delay_ms msg => rfl
  | cancel msg => rfl
  | stop => rfl

private theorem over_performAll (c : SysState sys) (i : σ.Id) (effs : List (Effect σ i)) :
    (c.performAll i effs).over input output
      = (c.over input output).performAll i (effs.flatMap (Effect.filterMapOut output)) := by
  induction effs generalizing c with
  | nil => rfl
  | cons eff effs ih =>
    rw [performAll_cons, ih, over_perform, List.flatMap_cons]
    simp [performAll, List.foldl_append]

private theorem isStop_filterMapOut {i : σ.Id} (effs : List (Effect σ i)) :
    (effs.flatMap (Effect.filterMapOut (In := In) output)).any Effect.isStop
      = effs.any Effect.isStop := by
  induction effs with
  | nil => rfl
  | cons eff effs ih =>
    have head : (Effect.filterMapOut (In := In) output eff).any Effect.isStop = eff.isStop := by
      cases eff with
      | emit out => cases h : output out <;> simp [Effect.filterMapOut, Effect.isStop, h]
      | _ => simp [Effect.filterMapOut, Effect.isStop]
    rw [List.flatMap_cons, List.any_append, List.any_cons, ih, head]

private theorem over_down (c : SysState sys) (i : σ.Id) :
    (c.down env.under i).over input output = (c.over input output).down env i := by
  simp only [over, down, List.filter_map]
  rfl

private theorem over_settle (c : SysState sys) (i : σ.Id) (r : sys.State i × List (Effect σ i)) :
    (c.settle env.under i r).over input output
      = (c.over input output).settle env i (r.1, r.2.flatMap (Effect.filterMapOut output)) := by
  unfold settle
  simp only [isStop_filterMapOut]
  split
  · rw [over_down, over_performAll]
    rfl
  · rw [over_performAll]
    rfl

private theorem over_handle (c : SysState sys) (i : σ.Id) (msg : σ.Msg i) :
    (c.handle env.under i msg).over input output = (c.over input output).handle env i msg :=
  over_settle c i _

private theorem over_startActor (c : SysState sys) (i : σ.Id) :
    (c.startActor env.under i).over input output = (c.over input output).startActor env i :=
  over_settle { c with up := update c.up i true } i _

private theorem over_deliverable (c : SysState sys) (e : Envelope (σ.withIO In Out)) :
    (c.over input output).deliverable env e = c.deliverable env.under e.under := by
  have hlink : env.under.link e.under.src e.under.dst = env.link e.src e.dst := rfl
  simp only [deliverable, hlink]
  split
  · show ((c.net.map Envelope.over).find? e.sameLink == some e) = _
    rw [List.find?_map,
      show (e.sameLink ∘ Envelope.over (In := In) (Out := Out)) = e.under.sameLink from rfl]
    cases c.net.find? e.under.sameLink with
    | none => rfl
    | some y =>
      rw [Bool.eq_iff_iff]
      simp only [Option.map_some, beq_iff_eq, Option.some.injEq]
      exact ⟨fun h => Envelope.over_inj _ _ (h.trans e.over_under.symm),
        fun h => h ▸ e.over_under⟩
  · show (c.net.map Envelope.over).contains e = _
    rw [Bool.eq_iff_iff]
    simp only [List.contains_iff_mem, List.mem_map]
    exact ⟨fun ⟨y, hy, h⟩ => Envelope.over_inj _ _ (h.trans e.over_under.symm) ▸ hy,
      fun h => ⟨_, h, e.over_under⟩⟩

private theorem over_init :
    (SysState.init sys env.under).over input output
      = SysState.init (sys.filterMapIO input output) env := by
  have hfold : ∀ (ids : List σ.Id) (c : SysState sys),
      (ids.foldl (fun c i => c.startActor env.under i) c).over input output
        = ids.foldl (fun c i => c.startActor env i) (c.over input output) := by
    intro ids
    induction ids with
    | nil => exact fun _ => rfl
    | cons i ids ih => exact fun c => by rw [List.foldl_cons, ih, over_startActor, List.foldl_cons]
  exact hfold _ _

/-- One event of `sys.filterMapIO input output` is the event of `sys` it stands for. -/
private theorem step_under {c : SysState sys} {ev : Event (σ.withIO In Out)}
    {d : SysState (sys.filterMapIO input output)} (h : (c.over input output).step env ev = some d) :
    ∃ ev' c', Event.Under input output ev ev' ∧ c.step env.under ev' = some c'
      ∧ c'.over input output = d := by
  have herase (e : Envelope (σ.withIO In Out)) :
      ({ c with net := c.net.erase e.under } : SysState sys).over input output
        = { c.over input output with net := (c.over input output).net.erase e } := by
    simp only [over]
    rw [map_erase Envelope.over_inj]
    rfl
  cases ev with
  | input x =>
    obtain rfl := step_input.mp h
    exact ⟨_, _, rfl, step_input.mpr rfl, by simp [over, Envelope.over]⟩
  | deliver e =>
    obtain ⟨hup, hdeliverable, rfl⟩ := step_deliver.mp h
    rw [over_deliverable] at hdeliverable
    exact ⟨_, _, rfl, step_deliver.mpr ⟨hup, hdeliverable, rfl⟩,
      (over_handle _ _ _).trans (congrArg (·.handle env e.dst e.msg) (herase e))⟩
  | duplicate e =>
    obtain ⟨hup, hduplicating, hdeliverable, rfl⟩ := step_duplicate.mp h
    rw [over_deliverable] at hdeliverable
    exact ⟨_, _, rfl, step_duplicate.mpr ⟨hup, hduplicating, hdeliverable, rfl⟩,
      over_handle _ _ _⟩
  | drop e =>
    obtain ⟨hlossy, hmem, rfl⟩ := step_drop.mp h
    obtain ⟨y, hy, hye⟩ := List.mem_map.mp hmem
    have hunder : e.under ∈ c.net := Envelope.over_inj _ _ (hye.trans e.over_under.symm) ▸ hy
    exact ⟨_, _, rfl, step_drop.mpr ⟨hlossy, hunder, rfl⟩, herase e⟩
  | timeout i msg =>
    obtain ⟨hup, hmem, rfl⟩ := step_timeout.mp h
    exact ⟨_, _, rfl, step_timeout.mpr ⟨hup, hmem, rfl⟩, over_handle _ _ _⟩
  | output out =>
    obtain ⟨hmem, rfl⟩ := step_output.mp h
    obtain ⟨out', hout', hshown, heq⟩ := filterMap_erase_shown c.outbox hmem
    exact ⟨_, _, ⟨out', rfl, hshown⟩, step_output.mpr ⟨hout', rfl⟩, by simp only [over, heq]⟩
  | crash i =>
    obtain ⟨hup, hcrash, rfl⟩ := step_crash.mp h
    exact ⟨_, _, rfl, step_crash.mpr ⟨hup, hcrash, rfl⟩, over_down c i⟩
  | start i =>
    obtain ⟨hup, hmail, rfl⟩ := step_start.mp h
    have hhasMail : (c.over input output).hasMail i = c.hasMail i := by
      show (c.net.map Envelope.over).any _ = _
      rw [List.any_map]
      rfl
    rw [hhasMail] at hmail
    exact ⟨_, _, rfl, step_start.mpr ⟨hup, hmail, rfl⟩, over_startActor c i⟩

/-- Every run of `sys.filterMapIO input output` is a run of `sys`, event for event. -/
theorem run_filterMapIO {events : List (Event (σ.withIO In Out))}
    {d : SysState (sys.filterMapIO input output)}
    (h : (SysState.init (sys.filterMapIO input output) env).run env events = some d) :
    ∃ (events' : List (Event σ)) (c : SysState sys),
      (SysState.init sys env.under).run env.under events' = some c
        ∧ c.over input output = d ∧ Event.AllUnder input output events events' := by
  suffices hrun : ∀ (events : List (Event (σ.withIO In Out))) (c : SysState sys),
      (c.over input output).run env events = some d →
      ∃ (events' : List (Event σ)) (c' : SysState sys), c.run env.under events' = some c'
        ∧ c'.over input output = d ∧ Event.AllUnder input output events events' from
    hrun events _ (by rw [over_init]; exact h)
  intro events
  induction events with
  | nil =>
    intro c h
    simp only [run, Option.some.injEq] at h
    exact ⟨[], c, rfl, h, trivial⟩
  | cons ev events ih =>
    intro c h
    simp only [run] at h
    cases hstep : (c.over input output).step env ev with
    | none => simp [hstep] at h
    | some d₁ =>
      obtain ⟨ev', c₁, hunder, hstep', rfl⟩ := step_under hstep
      obtain ⟨events', c', hrun', hover, hall⟩ := ih c₁ (by simpa [hstep] using h)
      exact ⟨ev' :: events', c', by simp [run, hstep', hrun'], hover, hunder, hall⟩

end SysState

end Lanes
