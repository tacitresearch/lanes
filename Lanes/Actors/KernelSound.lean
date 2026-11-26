/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Kernel
public import Lanes.Actors.Step

/-!
The kernel cannot leave the semantics: every kernel operation is a run of `SysState.step` under
`Kernel.env`, and the events it reports are that run. So a trace recorded from the kernel
replays by theorem, not by test.
-/

public section

namespace Lanes

variable {σ : Signature}

theorem apply_update {ι : Type} [DecidableEq ι] {β γ : ι → Type} (f : (j : ι) → β j → γ j)
    (g : (j : ι) → β j) (i : ι) (v : β i) :
    (fun j => f j (update g i v j)) = update (fun j => f j (g j)) i (f i v) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem SysState.ext' {sys : System σ} {a b : SysState sys} (hstate : a.state = b.state)
    (hup : a.up = b.up) (hnet : a.net = b.net) (htimers : a.timers = b.timers)
    (houtbox : a.outbox = b.outbox) : a = b := by
  cases a; cases b; simp_all

theorem map_fst_eraseP {α β : Type} [DecidableEq α] (l : List (α × β)) (a : α) :
    (l.eraseP (·.1 = a)).map (·.1) = (l.map (·.1)).erase a := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    by_cases h : p.1 = a
    · simp [h]
    · simp [h, ih]

namespace Kernel

variable {sys : System σ} [Hashable σ.Id]

theorem cell_setCell (k : Kernel sys) (i : σ.Id) (c : Cell sys i) :
    (k.setCell i c).cell = update k.cell i c := by
  funext j
  by_cases h : j = i
  · subst h
    simp [cell, setCell, Std.DHashMap.get?_insert_self]
  · have h' : ¬ i = j := fun h' => h h'.symm
    simp [cell, setCell, Std.DHashMap.get?_insert, h, h']

@[simp] theorem abs_state (k : Kernel sys) (ob : List σ.Out) :
    (k.abs ob).state = fun i => (k.cell i).state := rfl

@[simp] theorem abs_up (k : Kernel sys) (ob : List σ.Out) :
    (k.abs ob).up = fun i => (k.cell i).up := rfl

@[simp] theorem abs_net (k : Kernel sys) (ob : List σ.Out) : (k.abs ob).net = k.queue.toList := rfl

@[simp] theorem abs_timers (k : Kernel sys) (ob : List σ.Out) :
    (k.abs ob).timers = fun i => (k.cell i).timers.map (·.1) := rfl

@[simp] theorem abs_outbox (k : Kernel sys) (ob : List σ.Out) : (k.abs ob).outbox = ob := rfl

@[simp] theorem abs_unschedule (k : Kernel sys) (dues : List Due) (ob : List σ.Out) :
    (k.unschedule dues).abs ob = k.abs ob := rfl

@[simp] theorem cell_unschedule (k : Kernel sys) (dues : List Due) :
    (k.unschedule dues).cell = k.cell := rfl

theorem map_fst_arm {α β : Type} [DecidableEq α] (l : List (α × β)) (a : α) (token : β) :
    (if l.any (·.1 = a) then l.map fun t => if t.1 = a then (a, token) else t
      else l ++ [(a, token)]).map (·.1)
      = if a ∈ l.map (·.1) then l.map (·.1) else l.map (·.1) ++ [a] := by
  by_cases h : a ∈ l.map (·.1)
  · have hany : l.any (·.1 = a) = true := by
      simp only [List.mem_map] at h
      obtain ⟨t, ht, rfl⟩ := h
      exact List.any_eq_true.mpr ⟨t, ht, by simp⟩
    simp only [hany, h, ite_true, List.map_map]
    apply List.map_congr_left
    intro t _
    by_cases ht : t.1 = a <;> simp [ht]
  · have hany : l.any (·.1 = a) = false := by
      simp only [List.mem_map, not_exists, not_and] at h
      simp only [List.any_eq_false, decide_eq_true_eq]
      exact fun t ht => h t ht
    simp [hany, h]

theorem abs_setCell (k : Kernel sys) (ob : List σ.Out) (i : σ.Id) (c : Cell sys i) :
    (k.setCell i c).abs ob =
      { k.abs ob with
        state := update (k.abs ob).state i c.state
        up := update (k.abs ob).up i c.up
        timers := update (k.abs ob).timers i (c.timers.map (·.1)) } := by
  apply SysState.ext'
  · simp only [abs_state, cell_setCell]; exact apply_update (fun _ c => Cell.state c) k.cell i c
  · simp only [abs_up, cell_setCell]; exact apply_update (fun _ c => Cell.up c) k.cell i c
  · rfl
  · simp only [abs_timers, cell_setCell]
    exact apply_update (fun _ (c : Cell sys _) => c.timers.map (·.1)) k.cell i c
  · rfl

theorem abs_perform (k : Kernel sys) (ob : List σ.Out) (i : σ.Id) (eff : Effect σ i) :
    (k.perform i eff).1.abs (ob ++ (k.perform i eff).2) = (k.abs ob).perform i eff := by
  cases eff with
  | send to msg => apply SysState.ext' <;> simp [perform, SysState.perform, cell]
  | emit out => apply SysState.ext' <;> simp [perform, SysState.perform]
  | after delay_ms msg =>
    simp only [perform, List.append_nil]
    rw [abs_setCell]
    apply SysState.ext'
    · exact update_eq_self _ i
    · exact update_eq_self _ i
    · rfl
    · simp only [SysState.perform, abs_timers]
      congr 1
      exact map_fst_arm (k.cell i).timers msg _
    · rfl
  | cancel msg =>
    simp only [perform, List.append_nil]
    rw [abs_setCell]
    apply SysState.ext'
    · exact update_eq_self _ i
    · exact update_eq_self _ i
    · rfl
    · simp only [SysState.perform, abs_timers]
      congr 1
      exact map_fst_eraseP (k.cell i).timers msg
    · rfl
  | stop => apply SysState.ext' <;> simp [perform, SysState.perform]

/-! The definitions take pairs apart by pattern, for the compiler's sake. These say the same
with projections, which is easier to reason about. -/

theorem performAll_eq (k : Kernel sys) (i : σ.Id) (effs : List (Effect σ i)) :
    k.performAll i effs = effs.foldl
      (fun acc eff => ((acc.1.perform i eff).1, acc.2 ++ (acc.1.perform i eff).2)) (k, []) := rfl

theorem settle_eq (k : Kernel sys) (i : σ.Id) (r : sys.State i × List (Effect σ i)) :
    k.settle i r =
      (if r.2.any Effect.isStop then
          ((k.setCell i { (k.cell i) with state := r.1 }).performAll i r.2).1.down i
        else ((k.setCell i { (k.cell i) with state := r.1 }).performAll i r.2).1,
        ((k.setCell i { (k.cell i) with state := r.1 }).performAll i r.2).2) := rfl

omit [Hashable σ.Id] in
theorem boot_eq (sys : System σ) [Hashable σ.Id] :
    boot sys = sys.boot.foldl
      (fun acc i => ((acc.1.startActor i).1, acc.2 ++ (acc.1.startActor i).2)) ({}, []) := rfl

theorem run1_eq (k : Kernel sys) :
    k.run1 = match k.queue.pop? with
      | none => { kernel := k }
      | some (e, rest) =>
        if (k.cell e.dst).up then
          { kernel := (({ k with queue := rest }).handle e.dst e.msg).1
            events := .deliver e :: (({ k with queue := rest }).handle e.dst e.msg).2.map .output
            outputs := (({ k with queue := rest }).handle e.dst e.msg).2 }
        else
          { kernel := (k.startActor e.dst).1
            events := .start e.dst :: (k.startActor e.dst).2.map .output
            outputs := (k.startActor e.dst).2 } := rfl

theorem fire_eq (k : Kernel sys) (i : σ.Id) (msg : σ.Msg i) (due : Due) :
    k.fire i msg due =
      if (k.cell i).up && (k.cell i).timers.contains (msg, due) then
        { kernel := (((k.unschedule [due]).setCell i
            { (k.cell i) with timers := (k.cell i).timers.eraseP (·.1 = msg) }).handle i msg).1
          events := .timeout i msg :: (((k.unschedule [due]).setCell i
            { (k.cell i) with timers := (k.cell i).timers.eraseP (·.1 = msg) }).handle i msg).2.map
              .output
          outputs := (((k.unschedule [due]).setCell i
            { (k.cell i) with timers := (k.cell i).timers.eraseP (·.1 = msg) }).handle i msg).2 }
      else { kernel := k } := rfl

theorem runBatch_succ (k : Kernel sys) (fuel : Nat) :
    k.runBatch (fuel + 1) =
      if k.wait = .none then
        { kernel := (k.step.kernel.runBatch fuel).kernel
          events := k.step.events ++ (k.step.kernel.runBatch fuel).events
          outputs := k.step.outputs ++ (k.step.kernel.runBatch fuel).outputs }
      else { kernel := k } := rfl

theorem exec_cons (k : Kernel sys) (op : Op σ) (ops : List (Op σ)) :
    k.exec (op :: ops) =
      { kernel := ((k.apply op).kernel.exec ops).kernel
        events := (k.apply op).events ++ ((k.apply op).kernel.exec ops).events
        outputs := (k.apply op).outputs ++ ((k.apply op).kernel.exec ops).outputs } := rfl

private theorem abs_foldl_perform (i : σ.Id) (effs : List (Effect σ i)) :
    ∀ (k : Kernel sys) (cs : List σ.Out) (ob : List σ.Out),
      let r := effs.foldl
        (fun acc eff => ((acc.1.perform i eff).1, acc.2 ++ (acc.1.perform i eff).2)) (k, cs)
      r.1.abs (ob ++ r.2) = (k.abs (ob ++ cs)).performAll i effs := by
  induction effs with
  | nil => intro k cs ob; rfl
  | cons eff effs ih =>
    intro k cs ob
    simp only [List.foldl_cons, SysState.performAll_cons]
    rw [ih, ← List.append_assoc, abs_perform]

theorem abs_performAll (k : Kernel sys) (ob : List σ.Out) (i : σ.Id) (effs : List (Effect σ i)) :
    (k.performAll i effs).1.abs (ob ++ (k.performAll i effs).2)
      = (k.abs ob).performAll i effs := by
  have h := abs_foldl_perform i effs k [] ob
  simpa [performAll_eq] using h

theorem abs_down (k : Kernel sys) (ob : List σ.Out) (i : σ.Id) :
    (k.down i).abs ob = (k.abs ob).down env i := by
  show (((({ k with queue := k.queue.filter fun e => decide (e.dst ≠ i) }).unschedule
    ((k.cell i).timers.map Prod.snd)).setCell i
      { (k.cell i) with up := false, timers := [] }).abs ob) = _
  rw [abs_setCell]
  apply SysState.ext'
  · exact update_eq_self _ i
  · rfl
  · simp [SysState.down, env, Link.reliable]
  · rfl
  · rfl

theorem abs_settle (k : Kernel sys) (ob : List σ.Out) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) :
    (k.settle i r).1.abs (ob ++ (k.settle i r).2) = (k.abs ob).settle env i r := by
  have hset : (k.setCell i { (k.cell i) with state := r.1 }).abs ob
      = { k.abs ob with state := update (k.abs ob).state i r.1 } := by
    rw [abs_setCell]
    apply SysState.ext'
    · rfl
    · exact update_eq_self _ i
    · rfl
    · exact update_eq_self _ i
    · rfl
  have hall := abs_performAll (k.setCell i { (k.cell i) with state := r.1 }) ob i r.2
  rw [hset] at hall
  rw [settle_eq]
  unfold SysState.settle
  by_cases hstop : r.2.any Effect.isStop = true
  · simp only [hstop, ite_true]
    rw [abs_down, hall]
  · simp only [hstop, ite_false, Bool.false_eq_true]
    exact hall

theorem abs_handle (k : Kernel sys) (ob : List σ.Out) (i : σ.Id) (msg : σ.Msg i) :
    (k.handle i msg).1.abs (ob ++ (k.handle i msg).2) = (k.abs ob).handle env i msg :=
  abs_settle k ob i _

theorem abs_startActor (k : Kernel sys) (ob : List σ.Out) (i : σ.Id) :
    (k.startActor i).1.abs (ob ++ (k.startActor i).2) = (k.abs ob).startActor env i := by
  have hup : (k.setCell i { (k.cell i) with up := true }).abs ob
      = { k.abs ob with up := update (k.abs ob).up i true } := by
    rw [abs_setCell]
    apply SysState.ext'
    · exact update_eq_self _ i
    · rfl
    · rfl
    · exact update_eq_self _ i
    · rfl
  unfold SysState.startActor
  rw [← hup]
  exact abs_settle (k.setCell i { (k.cell i) with up := true }) ob i
    ((sys.actor i).recover (k.cell i).state)

omit [Hashable σ.Id] in
/-- Handing over every waiting output, oldest first, empties the outbox. -/
theorem run_outputs (envm : EnvModel σ) (c : SysState sys) (outs : List σ.Out) :
    ({ c with outbox := outs }).run envm (outs.map .output) = some { c with outbox := [] } := by
  induction outs with
  | nil => rfl
  | cons out outs ih => simpa [SysState.run, SysState.step] using ih

omit [Hashable σ.Id] in
/-- The kernel of a freshly booted system stands for the semantics' initial state, with the
boot actors' outputs still to hand over. -/
theorem abs_boot (sys : System σ) [Hashable σ.Id] :
    (boot sys).1.abs (boot sys).2 = SysState.init sys env := by
  suffices h : ∀ (l : List σ.Id) (k : Kernel sys) (cs : List σ.Out),
      let r := l.foldl
        (fun acc i => ((acc.1.startActor i).1, acc.2 ++ (acc.1.startActor i).2)) (k, cs)
      r.1.abs r.2 = l.foldl (fun c i => c.startActor env i) (k.abs cs) by
    have h0 := h sys.boot {} []
    have hblank : ({} : Kernel sys).abs ([] : List σ.Out) = SysState.blank sys := by
      apply SysState.ext' <;> simp [cell, SysState.blank]
    simpa [boot_eq, SysState.init, hblank] using h0
  intro l
  induction l with
  | nil => intro k cs; rfl
  | cons i l ih =>
    intro k cs
    simp only [List.foldl_cons]
    rw [ih, abs_startActor]

/-- Accepting an input is the semantics' `input` event. -/
theorem accept_sound (k : Kernel sys) (x : σ.In) :
    (k.abs).run env (k.accept x).events = some ((k.accept x).kernel.abs) := by
  simp only [accept, SysState.run, SysState.step, Option.bind_some]
  congr 1
  apply SysState.ext' <;> simp [cell]

/--
Handling the oldest message is a run of the semantics: start its receiver or let the receiver
handle it, then hand over the outputs. The events reported are that run.
-/
theorem run1_sound (k : Kernel sys) :
    (k.abs).run env k.run1.events = some (k.run1.kernel.abs) := by
  rw [run1_eq]
  split
  · rfl
  · next e rest hpop =>
    have hnet : k.queue.toList = e :: rest.toList := Fifo.toList_of_pop? hpop
    by_cases hup : (k.cell e.dst).up = true
    · simp only [hup, ite_true]
      have hstep : (k.abs).step env (.deliver e)
          = some ((({ k with queue := rest }).handle e.dst e.msg).1.abs
              (({ k with queue := rest }).handle e.dst e.msg).2) := by
        have hdel : (k.abs).deliverable env e = true := by
          simp [SysState.deliverable, env, Link.reliable, hnet, Envelope.sameLink]
        rw [SysState.step_deliver]
        refine ⟨hup, hdel, ?_⟩
        have habs : ({ k with queue := rest } : Kernel sys).abs
            = { k.abs with net := (k.abs).net.erase e } := by
          apply SysState.ext' <;> simp [cell, hnet]
        rw [← habs]
        simpa using abs_handle ({ k with queue := rest }) [] e.dst e.msg
      simp only [SysState.run, hstep, Option.bind_some]
      exact run_outputs env ((({ k with queue := rest }).handle e.dst e.msg).1.abs) _
    · simp only [hup, ite_false, Bool.false_eq_true]
      have hstep : (k.abs).step env (.start e.dst)
          = some ((k.startActor e.dst).1.abs (k.startActor e.dst).2) := by
        rw [SysState.step_start]
        refine ⟨by simpa using hup, .inl ?_, ?_⟩
        · simp [SysState.hasMail, hnet]
        · simpa using abs_startActor k [] e.dst
      simp only [SysState.run, hstep, Option.bind_some]
      exact run_outputs env ((k.startActor e.dst).1.abs) _

/-- The kernel is never stuck with mail queued: `run1` reports no event exactly when its queue
is empty. -/
theorem run1_events_eq_nil_iff (k : Kernel sys) : k.run1.events = [] ↔ (k.abs).net = [] := by
  rw [run1_eq]
  split
  · next h => simpa using Fifo.pop?_eq_none.mp h
  · next e rest h =>
    have := Fifo.toList_of_pop? h
    split <;> simp [this]

/-- A timer going off is the semantics' `timeout` event if that timer is still pending, and
nothing at all otherwise. This holds for any `due`, so nothing depends on what the agenda
holds. -/
theorem fire_sound (k : Kernel sys) (i : σ.Id) (msg : σ.Msg i) (due : Due) :
    (k.abs).run env (k.fire i msg due).events = some ((k.fire i msg due).kernel.abs) := by
  rw [fire_eq]
  by_cases hfire : ((k.cell i).up && (k.cell i).timers.contains (msg, due)) = true
  · simp only [hfire, ite_true]
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hfire
    generalize hk' : (k.unschedule [due]).setCell i
      { (k.cell i) with timers := (k.cell i).timers.eraseP (·.1 = msg) } = k'
    have hstep : (k.abs).step env (.timeout i msg)
        = some ((k'.handle i msg).1.abs (k'.handle i msg).2) := by
      rw [SysState.step_timeout]
      refine ⟨hfire.1, ?_, ?_⟩
      · simp only [abs_timers, List.mem_map]
        exact ⟨(msg, due), hfire.2, rfl⟩
      · have habs : k'.abs
            = { k.abs with timers := update (k.abs).timers i (((k.abs).timers i).erase msg) } := by
          rw [← hk', abs_setCell]
          apply SysState.ext'
          · exact update_eq_self _ i
          · exact update_eq_self _ i
          · rfl
          · simp only [abs_timers, abs_unschedule]
            congr 1
            exact map_fst_eraseP (k.cell i).timers msg
          · rfl
        rw [← habs]
        simpa using abs_handle k' [] i msg
    simp only [SysState.run, hstep, Option.bind_some]
    exact run_outputs env ((k'.handle i msg).1.abs) _
  · simp only [hfire, Bool.false_eq_true, ite_false]
    rfl

theorem step_sound (k : Kernel sys) :
    (k.abs).run env k.step.events = some (k.step.kernel.abs) := by
  unfold step
  split
  · split
    · exact fire_sound k _ _ _
    · exact run1_sound k
  · exact run1_sound k

theorem apply_sound (k : Kernel sys) (op : Op σ) :
    (k.abs).run env (k.apply op).events = some ((k.apply op).kernel.abs) := by
  cases op with
  | input x => exact accept_sound k x
  | advance now_ms => rfl
  | step => exact step_sound k
  | fire i msg due => exact fire_sound k i msg due

omit [Hashable σ.Id] in
theorem _root_.Lanes.SysState.run_append (envm : EnvModel σ) (c : SysState sys)
    (a b : List (Event σ)) : c.run envm (a ++ b) = (c.run envm a).bind (·.run envm b) := by
  induction a generalizing c with
  | nil => rfl
  | cons ev a ih =>
    simp only [List.cons_append, SysState.run]
    cases c.step envm ev with
    | none => rfl
    | some c' => simpa using ih c'

omit [Hashable σ.Id] in
theorem _root_.Lanes.System.Reachable.run {envm : EnvModel σ} {c c' : SysState sys}
    {evs : List (Event σ)} (h : sys.Reachable envm c) (hrun : c.run envm evs = some c') :
    sys.Reachable envm c' := by
  induction evs generalizing c with
  | nil => simp only [SysState.run, Option.some.injEq] at hrun; exact hrun ▸ h
  | cons ev evs ih =>
    simp only [SysState.run] at hrun
    cases hstep : c.step envm ev with
    | none => simp [hstep] at hrun
    | some c₁ => exact ih (h.step ev hstep) (by simpa [hstep] using hrun)

omit [Hashable σ.Id] in
/-- Induction along a run, for properties that relate the events so far to the state reached. -/
theorem _root_.Lanes.System.Reachable.run_induction {envm : EnvModel σ}
    {P : List (Event σ) → SysState sys → Prop} {c c' : SysState sys} {events : List (Event σ)}
    (hc : sys.Reachable envm c) (hrun : c.run envm events = some c') (start : P [] c)
    (step : ∀ evs c₁ ev c₂, sys.Reachable envm c₁ → P evs c₁ → c₁.step envm ev = some c₂ →
      P (evs ++ [ev]) c₂) : P events c' := by
  suffices h : ∀ (rest evs : List (Event σ)) (c₁ : SysState sys), sys.Reachable envm c₁ →
      P evs c₁ → c₁.run envm rest = some c' → P (evs ++ rest) c' from h events [] c hc start hrun
  intro rest
  induction rest with
  | nil =>
    intro evs c₁ _ hP hrun
    simp only [SysState.run, Option.some.injEq] at hrun
    simpa [← hrun] using hP
  | cons ev rest ih =>
    intro evs c₁ hc₁ hP hrun
    simp only [SysState.run] at hrun
    cases hstep : c₁.step envm ev with
    | none => simp [hstep] at hrun
    | some c₂ =>
      have h := ih (evs ++ [ev]) c₂ (hc₁.step ev hstep) (step evs c₁ ev c₂ hc₁ hP hstep)
        (by simpa [hstep] using hrun)
      simpa using h

theorem exec_sound (k : Kernel sys) (ops : List (Op σ)) :
    (k.abs).run env (k.exec ops).events = some ((k.exec ops).kernel.abs) := by
  induction ops generalizing k with
  | nil => rfl
  | cons op ops ih =>
    simp only [exec_cons, SysState.run_append, apply_sound, Option.bind_some]
    exact ih _

theorem runBatch_sound (k : Kernel sys) (fuel : Nat) :
    (k.abs).run env (k.runBatch fuel).events = some ((k.runBatch fuel).kernel.abs) := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
    rw [runBatch_succ]
    split
    · simp only [SysState.run_append, step_sound, Option.bind_some]
      exact ih _
    · rfl

theorem boot_sound (sys : System σ) :
    (SysState.init sys env).run env ((boot sys).2.map .output) = some ((boot sys).1.abs) := by
  rw [← abs_boot]
  exact run_outputs env ((boot sys).1.abs) _

/--
Whatever a shell does with a kernel, in any order: any inputs, any clock readings, work at any
time, timers fired early, late, twice or never armed. The kernel is still in a state the
semantics can reach, and the events it reported are a run that reaches it. Nothing is assumed
about the shell, the inbox or the clock.
-/
theorem exec_reachable (sys : System σ) (ops : List (Op σ)) :
    (SysState.init sys env).run env ((boot sys).2.map .output ++ ((boot sys).1.exec ops).events)
      = some (((boot sys).1.exec ops).kernel.abs)
    ∧ sys.Reachable env (((boot sys).1.exec ops).kernel.abs) := by
  have hrun : (SysState.init sys env).run env
      ((boot sys).2.map .output ++ ((boot sys).1.exec ops).events)
        = some (((boot sys).1.exec ops).kernel.abs) := by
    rw [SysState.run_append, boot_sound, Option.bind_some]
    exact exec_sound _ ops
  exact ⟨hrun, System.Reachable.init.run hrun⟩

/-! What the kernel hands the shell is exactly what its events say was output. -/

/-- The outputs among a list of events, in order. -/
def _root_.Lanes.Event.outputs (events : List (Event σ)) : List σ.Out :=
  events.filterMap fun
    | .output out => some out
    | _ => none

omit [Hashable σ.Id] in
theorem outputs_cons_map (ev : Event σ) (outs : List σ.Out) (h : Event.outputs [ev] = []) :
    Event.outputs (ev :: outs.map .output) = outs := by
  have hmap : Event.outputs (outs.map (Event.output (σ := σ))) = outs := by
    induction outs with
    | nil => rfl
    | cons out outs ih => simpa [Event.outputs] using ih
  cases ev <;> simp_all [Event.outputs]

omit [Hashable σ.Id] in
theorem _root_.Lanes.Event.outputs_append (a b : List (Event σ)) :
    Event.outputs (a ++ b) = Event.outputs a ++ Event.outputs b := by
  simp [Event.outputs]

theorem fire_outputs (k : Kernel sys) (i : σ.Id) (msg : σ.Msg i) (due : Due) :
    Event.outputs (k.fire i msg due).events = (k.fire i msg due).outputs := by
  rw [fire_eq]
  split
  · exact outputs_cons_map _ _ rfl
  · rfl

theorem run1_outputs (k : Kernel sys) : Event.outputs k.run1.events = k.run1.outputs := by
  rw [run1_eq]
  split
  · rfl
  · split <;> exact outputs_cons_map _ _ rfl

theorem step_outputs (k : Kernel sys) : Event.outputs k.step.events = k.step.outputs := by
  unfold step
  split
  · split
    · exact fire_outputs k _ _ _
    · exact run1_outputs k
  · exact run1_outputs k

theorem apply_outputs (k : Kernel sys) (op : Op σ) :
    Event.outputs (k.apply op).events = (k.apply op).outputs := by
  cases op with
  | input x => rfl
  | advance now_ms => rfl
  | step => exact step_outputs k
  | fire i msg due => exact fire_outputs k i msg due

/-- The outputs a shell is handed are the outputs of the run, no more, no fewer, in order. -/
theorem exec_outputs (k : Kernel sys) (ops : List (Op σ)) :
    Event.outputs (k.exec ops).events = (k.exec ops).outputs := by
  induction ops generalizing k with
  | nil => rfl
  | cons op ops ih => simp only [exec_cons, Event.outputs_append, apply_outputs, ih]

theorem runBatch_outputs (k : Kernel sys) (fuel : Nat) :
    Event.outputs (k.runBatch fuel).events = (k.runBatch fuel).outputs := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
    rw [runBatch_succ]
    split
    · simp only [Event.outputs_append, step_outputs, ih]
    · rfl

end Kernel

end Lanes
