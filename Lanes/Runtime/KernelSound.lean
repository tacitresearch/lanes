/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.Kernel
public import Lanes.Runtime.Release
public import Lanes.Proof.Lift
public import Lanes.Proof.HashMap

/-!
The kernel cannot leave the semantics: every kernel operation is a run of `SysState.step` under
`Kernel.env`, and the events it reports are that run, except that the kernel releases actors at
rest (`Kernel.rest`). So what it reports is a run up to the starts that bring released actors
back, and its state is the run's with those actors released (`SysState.Leads`). Releasing
changes nothing anyone can see (`Kernel.exec_visible`).
-/

public section

namespace Lanes

variable {σ : Signature}

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

private theorem get?_ofList_toList {α : Type} {β : α → Type} [DecidableEq α] [Hashable α]
    (m : Std.DHashMap α β) (a : α) : (Std.DHashMap.ofList m.toList).get? a = m.get? a := by
  cases h : m.get? a with
  | some b =>
    rw [Std.DHashMap.get?_ofList_of_mem (k := a) (by simp) Std.DHashMap.distinct_keys_toList
      (Std.DHashMap.mem_toList_iff_get?_eq_some.mpr h)]
    rfl
  | none =>
    refine Std.DHashMap.get?_ofList_of_contains_eq_false ?_
    rw [Std.DHashMap.map_fst_toList_eq_keys, Std.DHashMap.contains_keys,
      Std.DHashMap.contains_eq_isSome_get?, h]
    rfl

theorem cell_image_kernel (k : Kernel sys) : k.image.kernel.cell = k.cell := by
  funext i
  simp [cell, image, Image.kernel, get?_ofList_toList]

/-- A kernel restored from its image stands for the same system state. -/
theorem abs_image_kernel (k : Kernel sys) (ob : List σ.Out) : k.image.kernel.abs ob = k.abs ob := by
  simp only [abs, cell_image_kernel]
  simp [image, Image.kernel, Fifo.toList]

theorem cell_setCell (k : Kernel sys) (i : σ.Id) (c : Cell sys i) :
    (k.setCell i c).cell = update k.cell i c := by
  funext j
  by_cases h : j = i
  · subst h
    simp [cell, setCell, Std.DHashMap.get?_insert_self]
  · have h' : ¬ i = j := fun h' => h h'.symm
    simp [cell, setCell, Std.DHashMap.get?_insert, h, h']

theorem cell_rest (k : Kernel sys) (i : σ.Id) :
    (k.rest i).cell = k.cell ∨ ((sys.actor i).fresh (k.cell i).state = true ∧ (k.cell i).up = true
      ∧ (k.cell i).timers = [] ∧ (k.rest i).cell = update k.cell i { state := (sys.actor i).init }) := by
  simp only [rest]
  split
  · rename_i hrest
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hrest
    refine .inr ⟨hrest.1.1, hrest.1.2, hrest.2, ?_⟩
    funext j
    by_cases h : j = i
    · subst h
      simp [cell]
    · have h' : ¬ (i == j) = true := by simpa using fun h' => h h'.symm
      simp [cell, Std.DHashMap.get?_erase, h, h']
  · exact .inl rfl

@[simp] theorem rest_queue (k : Kernel sys) (i : σ.Id) : (k.rest i).queue = k.queue := by
  simp only [rest]; split <;> rfl

@[simp] theorem rest_agenda (k : Kernel sys) (i : σ.Id) : (k.rest i).agenda = k.agenda := by
  simp only [rest]; split <;> rfl

@[simp] theorem rest_nextToken (k : Kernel sys) (i : σ.Id) : (k.rest i).nextToken = k.nextToken := by
  simp only [rest]; split <;> rfl

@[simp] theorem rest_clock (k : Kernel sys) (i : σ.Id) : (k.rest i).clock_ms = k.clock_ms := by
  simp only [rest]; split <;> rfl

@[simp] theorem rest_timerTurn (k : Kernel sys) (i : σ.Id) : (k.rest i).timerTurn = k.timerTurn := by
  simp only [rest]; split <;> rfl

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

/-- What `rest` releases is at rest, so the kernel stands for the same state with it released. -/
theorem abs_rest (k : Kernel sys) (ob : List σ.Out) (i : σ.Id) :
    (k.abs ob).Released ((k.rest i).abs ob) := by
  rcases cell_rest k i with hcell | ⟨hfresh, hup, htimers, hcell⟩
  · have : (k.rest i).abs ob = k.abs ob := by
      apply SysState.ext' <;> simp [hcell]
    exact this ▸ SysState.Released.refl _
  · have : (k.rest i).abs ob = (k.abs ob).release i := by
      have hset : (k.rest i).abs ob = (k.setCell i { state := (sys.actor i).init }).abs ob := by
        simp only [abs, hcell, cell_setCell, rest_queue]
        rfl
      rw [hset, abs_setCell]
      rfl
    exact this ▸ (SysState.Released.refl _).release hup (by simp [htimers]) hfresh

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

/-- Running one list of operations and then another is running both. -/
theorem exec_append (k : Kernel sys) (a b : List (Op σ)) :
    k.exec (a ++ b) =
      { kernel := ((k.exec a).kernel.exec b).kernel
        events := (k.exec a).events ++ ((k.exec a).kernel.exec b).events
        outputs := (k.exec a).outputs ++ ((k.exec a).kernel.exec b).outputs } := by
  induction a generalizing k with
  | nil => rfl
  | cons op a ih => simp only [List.cons_append, exec_cons, ih, List.append_assoc]

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

/-- Writing a cell twice is writing it once: the table is the same value, not only the same
map. -/
theorem setCell_setCell {k : Kernel sys} {i : σ.Id} (h : k.cells.contains i = true)
    (c c' : Cell sys i) : (k.setCell i c).setCell i c' = k.setCell i c' := by
  simp only [setCell, DHashMap.insert_insert_of_contains h]

/-- `settle` reads only the cell's `up` and `timers`, and writes the whole cell: so whatever
state a cell held for `i` before, the kernel `settle` leaves is the same. -/
theorem settle_setCell {k : Kernel sys} {i : σ.Id} {c : Cell sys i} (h : k.cells.get? i = some c)
    (s : sys.State i) (r : sys.State i × List (Effect σ i)) :
    (k.setCell i { c with state := s }).settle i r = k.settle i r := by
  have hc : k.cell i = c := by simp [cell, h]
  have hcontains : k.cells.contains i = true := by
    rw [Std.DHashMap.contains_eq_isSome_get?, h]; rfl
  simp only [settle_eq, cell_setCell, update_self, hc, setCell_setCell hcontains]

/-- `handle` takes the state out of its cell before the step (`takeState`), and that changes no
value: it is `settle` on the step from the state the cell holds. -/
theorem handle_eq (k : Kernel sys) (i : σ.Id) (msg : σ.Msg i) :
    k.handle i msg = (((k.settle i ((sys.actor i).step (k.cell i).state msg)).1).rest i,
      (k.settle i ((sys.actor i).step (k.cell i).state msg)).2) := by
  unfold handle takeState
  cases h : k.cells.get? i with
  | none =>
    have hc : k.cell i = { state := (sys.actor i).init } := by simp [cell, h]
    rw [hc]
  | some c =>
    have hc : k.cell i = c := by simp [cell, h]
    simp only [settle_setCell h, hc]

/-- Handling a message is the semantics' `handle`, with the actor released if that leaves it at
rest. -/
theorem abs_handle (k : Kernel sys) (ob : List σ.Out) (i : σ.Id) (msg : σ.Msg i) :
    ((k.abs ob).handle env i msg).Released ((k.handle i msg).1.abs (ob ++ (k.handle i msg).2)) := by
  rw [handle_eq]
  have h := abs_rest (k.settle i ((sys.actor i).step (k.cell i).state msg)).1
    (ob ++ (k.settle i ((sys.actor i).step (k.cell i).state msg)).2) i
  rw [abs_settle] at h
  exact h

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

/-- An event that ends in a state the kernel stands for, with an actor released, and then the
outputs handed over. -/
private theorem leads_step {a c : SysState sys} {ev : Event σ} {k' : Kernel sys}
    {outs : List σ.Out} (hstep : a.step env ev = some c) (hc : c.Released (k'.abs outs)) :
    a.Leads env (ev :: outs.map .output) k'.abs := by
  have hrun := run_outputs env c outs
  have hout : c.outbox = outs := hc.outbox.symm
  rw [show { c with outbox := outs } = c by rw [← hout]] at hrun
  exact ⟨_, _, by simp only [SysState.run, hstep, Option.bind_some]; exact hrun, rfl,
    hc.withOutbox fun _ => []⟩

/--
Handling the oldest message is a run of the semantics: start its receiver or let the receiver
handle it, then hand over the outputs. The events reported are that run, and the kernel is its
state with the receiver released if it is at rest.
-/
theorem run1_sound (k : Kernel sys) : (k.abs).Leads env k.run1.events k.run1.kernel.abs := by
  rw [run1_eq]
  split
  · exact .of_run rfl
  · next e rest hpop =>
    have hnet : k.queue.toList = e :: rest.toList := Fifo.toList_of_pop? hpop
    by_cases hup : (k.cell e.dst).up = true
    · simp only [hup, ite_true]
      have hdel : (k.abs).deliverable env e = true := by
        simp [SysState.deliverable, env, Link.reliable, hnet, Envelope.sameLink]
      have habs : ({ k with queue := rest } : Kernel sys).abs
          = { k.abs with net := (k.abs).net.erase e } := by
        apply SysState.ext' <;> simp [cell, hnet]
      refine leads_step (SysState.step_deliver.mpr ⟨hup, hdel, rfl⟩) ?_
      rw [← habs]
      simpa using abs_handle ({ k with queue := rest }) [] e.dst e.msg
    · simp only [hup, ite_false, Bool.false_eq_true]
      have hstep : (k.abs).step env (.start e.dst)
          = some ((k.startActor e.dst).1.abs (k.startActor e.dst).2) := by
        rw [SysState.step_start]
        refine ⟨by simpa using hup, .inl ?_, ?_⟩
        · simp [SysState.hasMail, hnet]
        · simpa using abs_startActor k [] e.dst
      exact leads_step hstep (.refl _)

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
    (k.abs).Leads env (k.fire i msg due).events (k.fire i msg due).kernel.abs := by
  rw [fire_eq]
  by_cases hfire : ((k.cell i).up && (k.cell i).timers.contains (msg, due)) = true
  · simp only [hfire, ite_true]
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hfire
    generalize hk' : (k.unschedule [due]).setCell i
      { (k.cell i) with timers := (k.cell i).timers.eraseP (·.1 = msg) } = k'
    have habs : k'.abs
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
    refine leads_step (SysState.step_timeout.mpr ⟨hfire.1, ?_, rfl⟩) ?_
    · simp only [abs_timers, List.mem_map]
      exact ⟨(msg, due), hfire.2, rfl⟩
    · rw [← habs]
      simpa using abs_handle k' [] i msg
  · simp only [hfire, Bool.false_eq_true, ite_false]
    exact .of_run rfl

theorem step_sound (k : Kernel sys) : (k.abs).Leads env k.step.events k.step.kernel.abs := by
  unfold step
  split
  · exact fire_sound { k with timerTurn := false } _ _ _
  · exact run1_sound { k with timerTurn := true }

theorem runBatch_sound (k : Kernel sys) (fuel : Nat) :
    (k.abs).Leads env (k.runBatch fuel).events (k.runBatch fuel).kernel.abs := by
  induction fuel generalizing k with
  | zero => exact .of_run rfl
  | succ fuel ih =>
    rw [runBatch_succ]
    split
    · exact (step_sound k).append (ih _)
    · exact .of_run rfl

theorem apply_sound (k : Kernel sys) (op : Op σ) :
    (k.abs).Leads env (k.apply op).events (k.apply op).kernel.abs := by
  cases op with
  | input x => exact .of_run (accept_sound k x)
  | advance now_ms => exact .of_run rfl
  | step => exact step_sound k
  | batch fuel => exact runBatch_sound k fuel
  | fire i msg due => exact fire_sound k i msg due
  | snapshot => exact .of_run (congrArg some (abs_image_kernel k []).symm)

theorem exec_sound (k : Kernel sys) (ops : List (Op σ)) :
    (k.abs).Leads env (k.exec ops).events (k.exec ops).kernel.abs := by
  induction ops generalizing k with
  | nil => exact .of_run rfl
  | cons op ops ih =>
    rw [exec_cons]
    exact (apply_sound k op).append (ih _)

theorem boot_sound (sys : System σ) :
    (SysState.init sys env).run env ((boot sys).2.map .output) = some ((boot sys).1.abs) := by
  rw [← abs_boot]
  exact run_outputs env ((boot sys).1.abs) _

/--
Whatever a shell does with a kernel, in any order: any inputs, any clock readings, work at any
time and in batches of any size, timers fired early, late, twice or never armed. The events the
kernel reported are a run of the semantics, but for the starts that bring released actors back,
and the kernel is that run's state with actors at rest released: a state the semantics can
reach, with them released. Nothing is assumed about the shell, the inbox or the clock.
-/
theorem exec_reachable (sys : System σ) (ops : List (Op σ)) :
    (SysState.init sys env).Leads env ((boot sys).2.map .output ++ ((boot sys).1.exec ops).events)
      ((boot sys).1.exec ops).kernel.abs
    ∧ ∃ c, sys.Reachable env c ∧ c.Released ((boot sys).1.exec ops).kernel.abs := by
  have h := (SysState.Leads.of_run (boot_sound sys)).append (exec_sound (boot sys).1 ops)
  exact ⟨h, SysState.Leads.reachable .init h⟩

/-- Releasing actors changes nothing anyone can see: whatever the shell did, the inputs,
outputs and deadlines passing possible from the kernel's state are those of a state the
semantics reaches, which keeps every actor it started. -/
theorem exec_visible {T : Type} (sys : System σ) (ops : List (Op σ)) (deadlines : Deadlines σ T) :
    ∃ c, sys.Reachable env c ∧ ∀ trace : List (Visible σ.In σ.Out T),
      (∃ evs c', c.run env evs = some c' ∧ evs.filterMap (Event.timed deadlines) = trace)
        ↔ ∃ evs c', (((boot sys).1.exec ops).kernel.abs).run env evs = some c'
          ∧ evs.filterMap (Event.timed deadlines) = trace :=
  let ⟨c, hc, hrel⟩ := (exec_reachable sys ops).2
  ⟨c, hc, hrel.visible (fun _ => rfl) deadlines⟩

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
  · exact fire_outputs { k with timerTurn := false } _ _ _
  · exact run1_outputs { k with timerTurn := true }

theorem runBatch_outputs (k : Kernel sys) (fuel : Nat) :
    Event.outputs (k.runBatch fuel).events = (k.runBatch fuel).outputs := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
    rw [runBatch_succ]
    split
    · simp only [Event.outputs_append, step_outputs, ih]
    · rfl

theorem apply_outputs (k : Kernel sys) (op : Op σ) :
    Event.outputs (k.apply op).events = (k.apply op).outputs := by
  cases op with
  | input x => rfl
  | advance now_ms => rfl
  | step => exact step_outputs k
  | batch fuel => exact runBatch_outputs k fuel
  | fire i msg due => exact fire_outputs k i msg due
  | snapshot => rfl

/-- The outputs a shell is handed are the outputs of the run, no more, no fewer, in order. -/
theorem exec_outputs (k : Kernel sys) (ops : List (Op σ)) :
    Event.outputs (k.exec ops).events = (k.exec ops).outputs := by
  induction ops generalizing k with
  | nil => rfl
  | cons op ops ih => simp only [exec_cons, Event.outputs_append, apply_outputs, ih]

/-! What holds of each actor from any kernel, not only from boot: a shard whose kernel was
migrated from another system's starts from a kernel that boot never gives. -/

/-- A property of each actor that its own steps and restarts keep, and that holds of every actor
of a kernel, holds of every actor after any operations on it. -/
theorem exec_inductive (k : Kernel sys) (ops : List (Op σ)) {P : ∀ i, sys.State i → Prop}
    (hP : ∀ i, (sys.actor i).Inductive (P i)) (hk : ∀ i, P i (k.cell i).state) :
    ∀ i, P i ((k.exec ops).kernel.cell i).state := by
  obtain ⟨evs, c, hrun, -, hrel⟩ := exec_sound k ops
  have hc := SysState.run_inductive hP hrun hk
  intro i
  rcases hrel.actor i with hsame | hasleep
  · show P i (((k.exec ops).kernel.abs).state i)
    rw [hsame.1]
    exact hc i
  · show P i (((k.exec ops).kernel.abs).state i)
    rw [hasleep.init]
    exact (hP i).init

omit [Hashable σ.Id] in
/-- Every actor of a kernel that a shard can have is in a state the actor reaches on its own. -/
theorem exec_cell_reachable (sys : System σ) [Hashable σ.Id] (ops : List (Op σ)) (i : σ.Id) :
    (sys.actor i).Reachable (((boot sys).1.exec ops).kernel.cell i).state := by
  obtain ⟨c, hc, hrel⟩ := (exec_reachable sys ops).2
  show (sys.actor i).Reachable ((((boot sys).1.exec ops).kernel.abs).state i)
  rcases hrel.actor i with hsame | hasleep
  · rw [hsame.1]
    exact System.Reachable.actor hc i
  · rw [hasleep.init]
    exact .init

end Kernel

end Lanes
