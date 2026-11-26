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

theorem map_fst_arm {α : Type} [DecidableEq α] (l : List (α × Nat)) (a : α) (token : Nat) :
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
    (k.perform i eff).1.abs (ob ++ outputs (k.perform i eff).2) = (k.abs ob).perform i eff := by
  cases eff with
  | send to msg => apply SysState.ext' <;> simp [perform, SysState.perform, outputs, cell]
  | emit out => apply SysState.ext' <;> simp [perform, SysState.perform, outputs]
  | after delay_ms msg =>
    simp only [perform, outputs, List.filterMap_cons, List.filterMap_nil, List.append_nil]
    rw [abs_setCell]
    apply SysState.ext'
    · exact update_eq_self _ i
    · exact update_eq_self _ i
    · rfl
    · simp only [SysState.perform, abs_timers]
      congr 1
      exact map_fst_arm (k.cell i).timers msg k.nextToken
    · rfl
  | cancel msg =>
    simp only [perform, outputs, List.filterMap_nil, List.append_nil]
    rw [abs_setCell]
    apply SysState.ext'
    · exact update_eq_self _ i
    · exact update_eq_self _ i
    · rfl
    · simp only [SysState.perform, abs_timers]
      congr 1
      exact map_fst_eraseP (k.cell i).timers msg
    · rfl
  | stop => apply SysState.ext' <;> simp [perform, SysState.perform, outputs]

omit [Hashable σ.Id] in
theorem outputs_append (a b : List (Command σ)) : outputs (a ++ b) = outputs a ++ outputs b := by
  simp [outputs]

private theorem abs_foldl_perform (i : σ.Id) (effs : List (Effect σ i)) :
    ∀ (k : Kernel sys) (cs : List (Command σ)) (ob : List σ.Out),
      let r := effs.foldl
        (fun acc eff => ((acc.1.perform i eff).1, acc.2 ++ (acc.1.perform i eff).2)) (k, cs)
      r.1.abs (ob ++ outputs r.2) = (k.abs (ob ++ outputs cs)).performAll i effs := by
  induction effs with
  | nil => intro k cs ob; rfl
  | cons eff effs ih =>
    intro k cs ob
    simp only [List.foldl_cons, SysState.performAll_cons]
    rw [ih, outputs_append, ← List.append_assoc, abs_perform]

theorem abs_performAll (k : Kernel sys) (ob : List σ.Out) (i : σ.Id) (effs : List (Effect σ i)) :
    (k.performAll i effs).1.abs (ob ++ outputs (k.performAll i effs).2)
      = (k.abs ob).performAll i effs := by
  have h := abs_foldl_perform i effs k [] ob
  simpa [performAll, outputs] using h

theorem abs_down (k : Kernel sys) (ob : List σ.Out) (i : σ.Id) :
    (k.down i).abs ob = (k.abs ob).down env i := by
  unfold down
  rw [abs_setCell]
  apply SysState.ext'
  · exact update_eq_self _ i
  · rfl
  · simp [SysState.down, env, Link.reliable]
  · rfl
  · rfl

theorem abs_settle (k : Kernel sys) (ob : List σ.Out) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) :
    (k.settle i r).1.abs (ob ++ outputs (k.settle i r).2) = (k.abs ob).settle env i r := by
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
  unfold settle SysState.settle
  by_cases hstop : r.2.any Effect.isStop = true
  · simp only [hstop, ite_true]
    rw [abs_down, hall]
  · simp only [hstop, ite_false, Bool.false_eq_true]
    exact hall

theorem abs_handle (k : Kernel sys) (ob : List σ.Out) (i : σ.Id) (msg : σ.Msg i) :
    (k.handle i msg).1.abs (ob ++ outputs (k.handle i msg).2) = (k.abs ob).handle env i msg :=
  abs_settle k ob i _

theorem abs_startActor (k : Kernel sys) (ob : List σ.Out) (i : σ.Id) :
    (k.startActor i).1.abs (ob ++ outputs (k.startActor i).2) = (k.abs ob).startActor env i := by
  have hup : (k.setCell i { (k.cell i) with up := true }).abs ob
      = { k.abs ob with up := update (k.abs ob).up i true } := by
    rw [abs_setCell]
    apply SysState.ext'
    · exact update_eq_self _ i
    · rfl
    · rfl
    · exact update_eq_self _ i
    · rfl
  have hcell : ((k.setCell i { (k.cell i) with up := true }).cell i).state = (k.cell i).state := by
    rw [cell_setCell, update_self]
  unfold startActor SysState.startActor
  rw [← hup]
  have h := abs_settle (k.setCell i { (k.cell i) with up := true }) ob i
    ((sys.actor i).recover (k.cell i).state)
  exact h

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
    (boot sys).1.abs (outputs (boot sys).2) = SysState.init sys env := by
  suffices h : ∀ (l : List σ.Id) (k : Kernel sys) (cs : List (Command σ)),
      let r := l.foldl
        (fun acc i => ((acc.1.startActor i).1, acc.2 ++ (acc.1.startActor i).2)) (k, cs)
      r.1.abs (outputs r.2)
        = l.foldl (fun c i => c.startActor env i) (k.abs (outputs cs)) by
    have h0 := h sys.boot {} []
    have hblank : ({} : Kernel sys).abs (outputs ([] : List (Command σ))) = SysState.blank sys := by
      apply SysState.ext' <;> simp [cell, SysState.blank, outputs]
    simpa [boot, SysState.init, hblank] using h0
  intro l
  induction l with
  | nil => intro k cs; rfl
  | cons i l ih =>
    intro k cs
    simp only [List.foldl_cons]
    rw [ih, outputs_append, abs_startActor]

/-- Accepting an input is the semantics' `input` event. -/
theorem accept_sound (k : Kernel sys) (x : σ.In) :
    (k.abs).run env (k.accept x).events = some ((k.accept x).kernel.abs) := by
  simp only [accept, SysState.run, SysState.step, Option.bind_some]
  congr 1
  apply SysState.ext' <;> simp [cell]

/--
One kernel step is a run of the semantics: it starts the receiver of the oldest message or lets
it handle that message, then hands over the outputs. The events it reports are that run.
-/
theorem run1_sound {k : Kernel sys} {r : Step sys} (h : k.run1 = some r) :
    (k.abs).run env r.events = some (r.kernel.abs) := by
  unfold run1 at h
  split at h
  · exact absurd h (by simp)
  · next e rest hpop =>
    have hnet : k.queue.toList = e :: rest.toList := Fifo.toList_of_pop? hpop
    by_cases hup : (k.cell e.dst).up = true
    · simp only [hup, ite_true, Option.some.injEq] at h
      subst h
      have hstep : (k.abs).step env (.deliver e)
          = some ((({ k with queue := rest }).handle e.dst e.msg).1.abs
              (outputs (({ k with queue := rest }).handle e.dst e.msg).2)) := by
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
    · simp only [hup, ite_false, Bool.false_eq_true, Option.some.injEq] at h
      subst h
      have hstep : (k.abs).step env (.start e.dst)
          = some ((k.startActor e.dst).1.abs (outputs (k.startActor e.dst).2)) := by
        rw [SysState.step_start]
        refine ⟨by simpa using hup, .inl ?_, ?_⟩
        · simp [SysState.hasMail, hnet]
        · simpa using abs_startActor k [] e.dst
      simp only [SysState.run, hstep, Option.bind_some]
      exact run_outputs env ((k.startActor e.dst).1.abs) _

/-- The kernel is never stuck with mail queued: it can step exactly when its queue is not
empty. -/
theorem run1_eq_none_iff (k : Kernel sys) : k.run1 = none ↔ (k.abs).net = [] := by
  unfold run1
  split
  · next h => simpa using Fifo.pop?_eq_none.mp h
  · next e rest h =>
    have := Fifo.toList_of_pop? h
    split <;> simp [this]

/-- A timer firing is the semantics' `timeout` event if its token is still pending, and nothing
at all otherwise. -/
theorem fire_sound (k : Kernel sys) (i : σ.Id) (msg : σ.Msg i) (token : Nat) :
    (k.abs).run env (k.fire i msg token).events = some ((k.fire i msg token).kernel.abs) := by
  unfold fire
  by_cases hfire : ((k.cell i).up && (k.cell i).timers.contains (msg, token)) = true
  · simp only [hfire, ite_true]
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hfire
    have hstep : (k.abs).step env (.timeout i msg) = some
        (((k.setCell i { (k.cell i) with timers := (k.cell i).timers.eraseP (·.1 = msg) }).handle
            i msg).1.abs
          (outputs ((k.setCell i
            { (k.cell i) with timers := (k.cell i).timers.eraseP (·.1 = msg) }).handle i msg).2)) := by
      rw [SysState.step_timeout]
      refine ⟨hfire.1, ?_, ?_⟩
      · simp only [abs_timers, List.mem_map]
        exact ⟨(msg, token), hfire.2, rfl⟩
      · have habs : (k.setCell i
              { (k.cell i) with timers := (k.cell i).timers.eraseP (·.1 = msg) }).abs
            = { k.abs with timers := update (k.abs).timers i (((k.abs).timers i).erase msg) } := by
          rw [abs_setCell]
          apply SysState.ext'
          · exact update_eq_self _ i
          · exact update_eq_self _ i
          · rfl
          · simp only [abs_timers]
            congr 1
            exact map_fst_eraseP (k.cell i).timers msg
          · rfl
        rw [← habs]
        simpa using abs_handle _ [] i msg
    simp only [SysState.run, hstep, Option.bind_some]
    exact run_outputs env (((k.setCell i
      { (k.cell i) with timers := (k.cell i).timers.eraseP (·.1 = msg) }).handle i msg).1.abs) _
  · simp only [hfire, ite_false, Bool.false_eq_true]
    rfl

end Kernel

end Lanes
