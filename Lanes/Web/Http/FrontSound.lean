/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Proof.JoinSound
public import Lanes.Proof.Lift
public import Lanes.Proof.MapIOSound
public import Lanes.Runtime.KernelSound
public import Lanes.Web.Http.Front

/-!
`fronted sys` answers no request more often than it arrived (`fronted_answered_le_arrived`)
and keeps the deadline of every waiting request armed (`fronted_deadlines_armed`), for every
system behind the gate, and both proofs look at the gate alone. Both carry to `served sys`, the
system `Http.serve` runs, through its hidden inputs and outputs (`served_answered_le_arrived`,
`served_deadlines_armed`).

The second is an invariant of the gate's state, so `System.Invariant.join_left` carries it
into the join as it is. The first counts events, and takes more.

Alone, the gate answers no request more often than it handles an arrival of it
(`Gate.answered_le_handled`): in every environment, whatever arrives on its two inputs. That is
a statement about what a run shows the gate doing, so it holds of the gate inside any join
(`SysState.run_left`). It does not say "more often than it arrived": seen from the gate, a
message from outside travels on a link that may duplicate, since in a join the system behind
is part of the gate's outside.

What is left is about the join and not about the gate. No actor of `fronted sys` sends the gate
an arrival, so one is handled no more often than it is put in, if the link from outside to the
gate does not duplicate (`System.handled_le_put`). Every other link may.
-/

@[expose] public section

namespace Lanes.Http

variable {σ : Signature}

namespace Gate

def answered (shown : List (Deed (gateSig σ))) : List ReqId :=
  shown.filterMap fun
    | .output (.inl (id, _)) => some id
    | _ => none

/-- The arrivals the gate handled, as often as it handled them. -/
def handled (shown : List (Deed (gateSig σ))) : List ReqId :=
  shown.filterMap fun
    | .handle _ (.arrive id _) => some id
    | _ => none

/-- While the gate is up, every pending request has its deadline armed. -/
def Armed {bridge : Bridge σ} {config : GateConfig} (c : SysState (gateSystem bridge config)) :
    Prop :=
  c.up () = true → ∀ id ∈ (c.state () : List ReqId), GateMsg.expire id ∈ c.timers ()

end Gate

namespace Fronted

def arrived (events : List (Event (frontedSig σ))) : List ReqId :=
  events.filterMap fun
    | .input (.inl (id, _)) => some id
    | _ => none

def answered (events : List (Event (frontedSig σ))) : List ReqId :=
  events.filterMap fun
    | .output (.inl (id, _)) => some id
    | _ => none

/-- While the gate is up, every pending request has its deadline armed. -/
def Armed {sys : System σ} {bridge : Bridge σ} {config : GateConfig}
    (c : SysState (fronted sys bridge config)) : Prop :=
  c.up (.inl ()) = true →
    ∀ id ∈ (c.state (.inl ()) : List ReqId), GateMsg.expire id ∈ c.timers (.inl ())

end Fronted

namespace Served

def arrived (events : List (Event (servedSig σ))) : List ReqId :=
  events.filterMap fun
    | .input (id, _) => some id
    | _ => none

def answered (events : List (Event (servedSig σ))) : List ReqId :=
  events.filterMap fun
    | .output (id, _) => some id
    | _ => none

/-- While the gate is up, every pending request has its deadline armed. -/
def Armed {sys : System σ} {bridge : Bridge σ} {config : GateConfig}
    (c : SysState (served sys bridge config)) : Prop :=
  c.up (.inl ()) = true →
    ∀ id ∈ (c.state (.inl ()) : List ReqId), GateMsg.expire id ∈ c.timers (.inl ())

end Served

end Lanes.Http

end

public section

namespace Lanes.Http

variable {σ : Signature} {sys : System σ} {bridge : Bridge σ} {config : GateConfig}

namespace Gate

private def answers (id : ReqId) : (gateSig σ).Out → Bool
  | .inl (id', _) => id' == id
  | .inr _ => false

private def arrives (id : ReqId) : GateMsg σ → Bool
  | .arrive id' _ => id' == id
  | _ => false

/-- What the gate owes `id`: the answers waiting to leave and its place in the waiting list. -/
private def owed (id : ReqId) (c : SysState (gateSystem bridge config)) : Nat :=
  c.outbox.countP (answers id) + List.count id (c.state ())

/-- One step of the gate adds at most one to what it owes `id`, and only for an arrival. -/
private theorem owed_step (id : ReqId) (pending : List ReqId) (msg : GateMsg σ) :
    (Effect.emits ((gateActor bridge config).step pending msg).2).countP (answers id)
        + List.count id ((gateActor bridge config).step pending msg).1
      ≤ List.count id pending + (arrives id msg).toNat := by
  cases msg with
  | arrive id' request =>
    simp only [gateActor, Gate.step]
    repeat' split
    all_goals simp [Effect.emits, answers, arrives, Bool.toNat, List.count_cons]
    all_goals split <;> simp_all <;> omega
  | answer out =>
    simp only [gateActor, Gate.step]
    repeat' split
    all_goals simp [Effect.emits, answers, arrives]
    grind [List.count_eq_zero]
  | expire id' =>
    simp only [gateActor, Gate.step]
    split
    · simp [Effect.emits, answers, arrives]
      grind [List.count_eq_zero]
    · simp [Effect.emits, arrives]

variable {env : EnvModel (gateSig σ)}

private theorem owed_settle (id : ReqId) (c : SysState (gateSystem bridge config)) (i : Unit)
    (r : List ReqId × List (Effect (gateSig σ) i)) :
    owed id (c.settle env i r)
      = c.outbox.countP (answers id) + (Effect.emits r.2).countP (answers id)
        + List.count id r.1 := by
  rw [SysState.settle_eq]
  split <;> simp [owed, SysState.down, List.countP_append]

private theorem owed_handle (id : ReqId) (c : SysState (gateSystem bridge config)) (i : Unit)
    (msg : GateMsg σ) : owed id (c.handle env i msg) ≤ owed id c + (arrives id msg).toNat := by
  obtain rfl : i = () := rfl
  have h := owed_step (bridge := bridge) (config := config) id (c.state ()) msg
  rw [SysState.handle, owed_settle]
  simp only [owed]
  omega

private theorem owed_start (id : ReqId) (c : SysState (gateSystem bridge config)) (i : Unit) :
    owed id (c.startActor env i) = owed id c := by
  have hquiet : (Effect.emits ((gateActor bridge config).recover (c.state ())).2) = [] := by
    simp [gateActor, Effect.emits]
  rw [SysState.startActor, owed_settle, hquiet]
  simp [owed, gateActor]

private theorem owed_output (id : ReqId) {c c' : SysState (gateSystem bridge config)}
    {out : (gateSig σ).Out} (hstep : c.step env (.output out) = some c') :
    owed id c' + (answers id out).toNat = owed id c := by
  have h := SysState.countP_outbox_of_output (answers id) hstep
  obtain ⟨-, rfl⟩ := SysState.step_output.mp hstep
  simp only [owed] at h ⊢
  omega

private theorem handled_snoc (events : List (Event (gateSig σ))) (ev : Event (gateSig σ))
    (id : ReqId) :
    (handled (deeds (events ++ [ev]))).count id
      = (handled (deeds events)).count id + (handled ev.deed.toList).count id := by
  simp only [handled, deeds, List.filterMap_append, List.count_append]
  cases h : ev.deed <;> simp [h]

private theorem answered_snoc (events : List (Event (gateSig σ))) (ev : Event (gateSig σ))
    (id : ReqId) :
    (answered (deeds (events ++ [ev]))).count id
      = (answered (deeds events)).count id + (answered ev.deed.toList).count id := by
  simp only [answered, deeds, List.filterMap_append, List.count_append]
  cases h : ev.deed <;> simp [h]

private theorem handled_handle (i : Unit) (msg : GateMsg σ) (id : ReqId) :
    (handled [Deed.handle (σ := gateSig σ) i msg]).count id = (arrives id msg).toNat := by
  cases msg <;> simp [handled, arrives, Bool.toNat, List.count_cons]

private theorem answered_output (out : (gateSig σ).Out) (id : ReqId) :
    (answered [Deed.output (σ := gateSig σ) out]).count id = (answers id out).toNat := by
  rcases out with ⟨id', response⟩ | x <;>
    simp [answered, answers, Bool.toNat, List.count_cons]

private theorem quiet {ev : Event (gateSig σ)} (h : ev.deed = none) (id : ReqId) :
    (answered ev.deed.toList).count id = 0 ∧ (handled ev.deed.toList).count id = 0 := by
  rw [h]
  exact ⟨rfl, rfl⟩

/-- One event: the answer it hands over and what the gate owes after it are covered by what
the gate owed before and the arrival it handles. -/
private theorem owed_event (id : ReqId) {c c' : SysState (gateSystem bridge config)}
    {ev : Event (gateSig σ)} (hstep : c.step env ev = some c') :
    (answered ev.deed.toList).count id + owed id c'
      ≤ owed id c + (handled ev.deed.toList).count id := by
  cases ev with
  | input x =>
    obtain rfl := SysState.step_input.mp hstep
    have := quiet (ev := .input x) rfl id
    simp only [owed]
    omega
  | deliver e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_deliver.mp hstep
    have h := owed_handle (env := env) id { c with net := c.net.erase e } e.dst e.msg
    have hhandled := handled_handle e.dst e.msg id
    have hsame : owed id { c with net := c.net.erase e } = owed id c := rfl
    have hanswered : (answered [Deed.handle (σ := gateSig σ) e.dst e.msg]).count id = 0 := rfl
    simp only [Event.deed, Option.toList_some]
    omega
  | duplicate e =>
    obtain ⟨_, _, _, rfl⟩ := SysState.step_duplicate.mp hstep
    have h := owed_handle (env := env) id c e.dst e.msg
    have hhandled := handled_handle e.dst e.msg id
    have hanswered : (answered [Deed.handle (σ := gateSig σ) e.dst e.msg]).count id = 0 := rfl
    simp only [Event.deed, Option.toList_some]
    omega
  | drop e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_drop.mp hstep
    have := quiet (ev := .drop e) rfl id
    simp only [owed]
    omega
  | timeout i msg =>
    obtain ⟨_, _, rfl⟩ := SysState.step_timeout.mp hstep
    have h := owed_handle (env := env) id
      { c with timers := update c.timers i ((c.timers i).erase msg) } i msg
    have hhandled := handled_handle i msg id
    have hsame : owed id { c with timers := update c.timers i ((c.timers i).erase msg) }
        = owed id c := rfl
    have hanswered : (answered [Deed.handle (σ := gateSig σ) i msg]).count id = 0 := rfl
    simp only [Event.deed, Option.toList_some]
    omega
  | output out =>
    have h := owed_output id hstep
    have hanswered := answered_output out id
    have hhandled : (handled [Deed.output (σ := gateSig σ) out]).count id = 0 := rfl
    simp only [Event.deed, Option.toList_some]
    omega
  | crash i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_crash.mp hstep
    have := quiet (ev := .crash i) rfl id
    simp only [owed, SysState.down]
    omega
  | start i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
    have h := owed_start (env := env) id c i
    have := quiet (ev := .start i) rfl id
    omega

/-- The gate alone answers no request more often than it handles an arrival of it: in every
environment, whatever arrives on its two inputs and however often. The gate may crash and
restart, and its links may lose, reorder and duplicate. -/
theorem answered_le_handled (env : EnvModel (gateSig σ)) {events : List (Event (gateSig σ))}
    {c : SysState (gateSystem bridge config)}
    (hrun : (SysState.init (gateSystem bridge config) env).run env events = some c) (id : ReqId) :
    (answered (deeds events)).count id ≤ (handled (deeds events)).count id := by
  suffices h : (answered (deeds events)).count id + owed id c
      ≤ (handled (deeds events)).count id from Nat.le_trans (Nat.le_add_right _ _) h
  refine System.Reachable.run_induction
    (P := fun events c => (answered (deeds events)).count id + owed id c
      ≤ (handled (deeds events)).count id) .init hrun ?_ ?_
  · have hinit : owed id (SysState.init (gateSystem bridge config) env) = 0 :=
      (owed_start (env := env) id (SysState.blank _) ()).trans
        (by simp [owed, SysState.blank, gateActor])
    simp [hinit, answered, handled, deeds]
  rintro evs c₁ ev c₂ - hle hstep
  have h := owed_event (env := env) id hstep
  rw [handled_snoc, answered_snoc]
  omega

local macro "armed" : tactic => `(tactic|
  (simp [Armed, SysState.settle, SysState.perform, Effect.isStop] <;>
    first
    | done
    | grind [List.Nodup.mem_erase_iff]
    | skip))

/-- A firing deadline has left the timers when the gate handles it, hence `≠ msg`. -/
private theorem armed_handle {c : SysState (gateSystem bridge config)} (msg : GateMsg σ)
    (hnodup : List.Nodup (c.state ()))
    (h : ∀ id ∈ (c.state () : List ReqId), GateMsg.expire id ≠ msg →
      GateMsg.expire id ∈ c.timers ()) :
    Armed (c.handle env () msg) := by
  cases msg with
  | arrive id' request =>
    replace h := fun id hid => h id hid nofun
    simp only [SysState.handle, gateActor, Gate.step]
    split
    · armed
    · split
      · armed
      · split
        · armed
        · armed
          intro _
          split
          · next harmed => exact ⟨harmed, h⟩
          · exact ⟨by simp, fun id hid => List.mem_append_left _ (h id hid)⟩
  | answer out =>
    replace h := fun id hid => h id hid nofun
    simp only [SysState.handle, gateActor, Gate.step]
    split
    · split
      · armed
        intro _ id hid
        obtain ⟨hne, hid⟩ := hnodup.mem_erase_iff.mp hid
        exact (List.mem_erase_of_ne (by simpa using hne)).mpr (h id hid)
      · armed
    · armed
  | expire id' =>
    simp only [SysState.handle, gateActor, Gate.step]
    split
    · armed
    · armed

private theorem armed_start (c : SysState (gateSystem bridge config)) :
    Armed (c.startActor env ()) := by
  intro _ id hid
  have hrunning : ((c.state () : List ReqId).map fun id =>
      (Effect.after config.requestTimeout_ms (.expire id) : Effect (gateSig σ) ())).any
        Effect.isStop = false := by
    simp [List.any_map, Effect.isStop]
  simp [SysState.startActor, SysState.settle, gateActor, hrunning] at hid ⊢
  exact SysState.mem_timers_performAll_after _ _ _ _ _ (.inr ⟨id, hid, rfl⟩)

/-- The gate alone cannot forget a pending request, in any environment: while it is up the
request's deadline is armed. -/
theorem deadlines_armed (bridge : Bridge σ) (config : GateConfig) (env : EnvModel (gateSig σ)) :
    (gateSystem bridge config).Invariant env Armed := by
  intro c hc
  induction hc with
  | init => exact armed_start (env := env) (SysState.blank _)
  | @step c c' ev hc hstep ih =>
    have hnodup : List.Nodup (c.state ()) :=
      (System.invariant_of_actor _ () (gateActor_bounded bridge config) env c hc).2
    cases ev with
    | input x =>
      obtain rfl := SysState.step_input.mp hstep
      exact ih
    | deliver e =>
      obtain ⟨hup, _, rfl⟩ := SysState.step_deliver.mp hstep
      exact armed_handle (c := { c with net := c.net.erase e }) e.msg hnodup
        fun id hid _ => ih hup id hid
    | duplicate e =>
      obtain ⟨hup, _, _, rfl⟩ := SysState.step_duplicate.mp hstep
      exact armed_handle e.msg hnodup fun id hid _ => ih hup id hid
    | drop e =>
      obtain ⟨_, _, rfl⟩ := SysState.step_drop.mp hstep
      exact ih
    | timeout i msg =>
      obtain ⟨hup, _, rfl⟩ := SysState.step_timeout.mp hstep
      refine armed_handle msg hnodup fun id hid hne => ?_
      simpa using (List.mem_erase_of_ne hne).mpr (ih hup id hid)
    | output out =>
      obtain ⟨_, rfl⟩ := SysState.step_output.mp hstep
      exact ih
    | crash i =>
      obtain ⟨_, _, rfl⟩ := SysState.step_crash.mp hstep
      simp [Armed, SysState.down]
    | start i =>
      obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
      exact armed_start c

end Gate

/-! From the gate alone to `fronted sys`. -/

section Fronted

private abbrev wired (sys : System σ) (bridge : Bridge σ) (config : GateConfig) :
    System (joinSig (gateSig σ) σ) :=
  (gateSystem bridge config).join sys (frontWiring bridge)

/-- An arrival of `id` on its way to the gate. -/
private def arriving (id : ReqId) : Kind (joinSig (gateSig σ) σ)
  | .inl _, .arrive id' _ => id' == id
  | _, _ => false

private def tame : Effect (gateSig σ) () → Bool
  | .emit _ | .after _ (.expire _) | .cancel _ => true
  | _ => false

private theorem gate_tame (pending : List ReqId) (msg : GateMsg σ) :
    ((gateActor bridge config).step pending msg).2.all tame = true := by
  cases msg <;> simp only [gateActor, Gate.step] <;> repeat' split
  all_goals simp [tame]

private theorem avoids_left (id : ReqId) {effs : List (Effect (gateSig σ) ())}
    (h : effs.all tame = true) :
    Effect.Avoids (arriving id) (i := .inl ())
      (effs.flatMap fun eff => [(frontWiring bridge).left sys eff]) := by
  refine ⟨fun to msg hmem => ?_, fun delay_ms msg hmem => ?_⟩
  all_goals
    obtain ⟨eff, heff, hmem⟩ := List.mem_flatMap.mp hmem
    have htame := List.all_eq_true.mp h eff heff
    rw [List.mem_singleton] at hmem
  · cases eff with
    | emit out =>
      rcases out with answer | x
      · cases hmem
      · cases hmem
        rfl
    | send to' msg' => cases htame
    | _ => cases hmem
  · cases eff with
    | after d m =>
      cases hmem
      cases msg <;> first | rfl | cases htame
    | emit out => rcases out with answer | x <;> cases hmem
    | _ => cases hmem

private theorem avoids_right (id : ReqId) {j : σ.Id} (effs : List (Effect σ j)) :
    Effect.Avoids (arriving id) (i := .inr j)
      (effs.flatMap fun eff => [(frontWiring bridge).right (gateSystem bridge config) eff]) := by
  refine ⟨fun to msg hmem => ?_, fun delay_ms msg hmem => rfl⟩
  obtain ⟨eff, -, hmem⟩ := List.mem_flatMap.mp hmem
  rw [List.mem_singleton] at hmem
  cases eff with
  | send to' msg' =>
    cases hmem
    rfl
  | emit out =>
    simp only [Wiring.right, frontWiring] at hmem
    split at hmem
    · next x hx =>
      split at hx
      · cases hx
        cases hmem
        rfl
      · cases hx
    · cases hmem
  | _ => cases hmem

/-- No actor of `fronted sys` sends the gate an arrival, and none is a timer. -/
private theorem onlyPut (sys : System σ) (bridge : Bridge σ) (config : GateConfig) (id : ReqId) :
    (wired sys bridge config).OnlyPut (arriving id) where
  step
    | .inl (), _, msg => avoids_left id (gate_tame _ msg)
    | .inr _, _, _ => avoids_right id _
  recover
    | .inl (), pending => avoids_left id (by simp [gateActor, tame])
    | .inr _, _ => avoids_right id _

/-- The gate's deeds alone are its deeds in the join: what the wiring hides is no answer. -/
private theorem shown_answered (events : List (Event (gateSig σ))) :
    Gate.answered (events.filterMap (frontWiring bridge).shown) = Gate.answered (deeds events)
      ∧ Gate.handled (events.filterMap (frontWiring bridge).shown)
        = Gate.handled (deeds events) := by
  induction events with
  | nil => exact ⟨rfl, rfl⟩
  | cons ev events ih =>
    simp only [deeds, filterMap_cons_toList, Gate.answered, Gate.handled, List.filterMap_append]
      at ih ⊢
    rw [ih.1, ih.2]
    have hshown : (frontWiring bridge).shown ev = match ev.deed with
        | some (.output (.inr _)) => none
        | deed => deed := by
      rw [Wiring.shown]
      cases ev.deed with
      | none => rfl
      | some deed =>
        cases deed with
        | handle i msg => rfl
        | output out => rcases out with answer | x <;> rfl
    rw [hshown]
    cases ev.deed with
    | none => exact ⟨rfl, rfl⟩
    | some deed =>
      cases deed with
      | handle i msg => exact ⟨rfl, rfl⟩
      | output out => rcases out with answer | x <;> exact ⟨rfl, rfl⟩

/-- Handling an arrival, as the join's events show it and as the gate's deeds do. -/
private theorem handled_left (id : ReqId) (events : List (Event (joinSig (gateSig σ) σ))) :
    (Gate.handled (events.filterMap Event.leftDeed)).count id = handled (arriving id) events := by
  induction events with
  | nil => rfl
  | cons ev events ih =>
    simp only [handled, deeds, filterMap_cons_toList, Gate.handled, List.filterMap_append,
      List.count_append, List.countP_append] at ih ⊢
    rw [ih, Nat.add_comm, Nat.add_comm (List.countP _ _)]
    congr 1
    cases ev with
    | deliver e | duplicate e =>
      obtain ⟨src, u | j, msg⟩ := e
      · cases msg <;>
          simp [Event.leftDeed, Event.deed, Deed.handles, arriving, List.count_cons]
      · simp [Event.leftDeed, Event.deed, Deed.handles, arriving]
    | timeout i msg =>
      rcases i with u | j
      · cases msg <;>
          simp [Event.leftDeed, Event.deed, Deed.handles, arriving, List.count_cons]
      · simp [Event.leftDeed, Event.deed, Deed.handles, arriving]
    | output out => rcases out with out | out <;> simp [Event.leftDeed, Event.deed, Deed.handles]
    | _ => simp [Event.leftDeed, Event.deed]

/-- The requests put into the join, as often as each was. -/
private def putIn : Event (joinSig (gateSig σ) σ) → Option ReqId
  | .input (.inl (.inl (id, _))) => some id
  | _ => none

private theorem put_eq (sys : System σ) (bridge : Bridge σ) (config : GateConfig) (id : ReqId)
    (events : List (Event (joinSig (gateSig σ) σ))) :
    put (wired sys bridge config) (arriving id) events = (events.filterMap putIn).count id := by
  induction events with
  | nil => rfl
  | cons ev events ih =>
    simp only [put, filterMap_cons_toList, List.countP_cons, List.count_append] at ih ⊢
    rw [ih, Nat.add_comm]
    congr 1
    cases ev with
    | input x =>
      rcases x with (⟨id', request⟩ | out) | x <;>
        simp [putIn, arriving, List.count_cons]
    | _ => simp [putIn]

variable {env : EnvModel (frontedSig σ)}

/-- `fronted sys` answers no request more often than it arrived, whatever `sys` is. Every actor
may crash, restart and stop, the gate included, and every link may lose, reorder and
duplicate but one: the link from outside to the gate must not duplicate. -/
theorem fronted_answered_le_arrived (henv : (env.link none (.inl ())).duplicating = false)
    {events : List (Event (frontedSig σ))} {c : SysState (fronted sys bridge config)}
    (hrun : (SysState.init (fronted sys bridge config) env).run env events = some c)
    (id : ReqId) :
    (Fronted.answered events).count id ≤ (Fronted.arrived events).count id := by
  obtain ⟨wiredEvents, c', hwired, -, hunder⟩ := SysState.run_filterMapIO hrun
  obtain ⟨gateEvents, hgate, hshown⟩ := SysState.run_left hwired
  have hanswered : Fronted.answered events
      = Gate.answered (wiredEvents.filterMap Event.leftDeed) := by
    simp only [Fronted.answered, Gate.answered, List.filterMap_filterMap]
    refine hunder.filterMap_eq fun ev ev' h => ?_
    cases ev with
    | output out =>
      obtain ⟨out', rfl, hout'⟩ := h
      rcases out' with (answer | x) | out' <;> simp only [frontedOutput] at hout' <;> cases hout'
      all_goals rfl
    | deliver e | duplicate e =>
      cases h
      obtain ⟨src, u | j, msg⟩ := e <;> rfl
    | timeout i msg =>
      cases h
      rcases i with u | j <;> rfl
    | _ =>
      cases h
      rfl
  have harrived : Fronted.arrived events = wiredEvents.filterMap putIn := by
    refine hunder.filterMap_eq fun ev ev' h => ?_
    cases ev with
    | input x =>
      cases h
      rcases x with ⟨id', request⟩ | x <;> rfl
    | output out =>
      obtain ⟨out', rfl, -⟩ := h
      rfl
    | _ =>
      cases h
      rfl
  have hlink : ∀ i msg, arriving id i msg = true →
      (env.under.link none i).duplicating = false := by
    rintro (⟨⟩ | j) msg h
    · exact henv
    · cases h
  rw [hanswered, harrived, ← hshown, (shown_answered gateEvents).1, ← put_eq sys bridge config]
  refine Nat.le_trans (Gate.answered_le_handled _ hgate id) ?_
  rw [← (shown_answered gateEvents).2, hshown, handled_left]
  exact System.handled_le_put (onlyPut sys bridge config id) hlink hwired

/-- The gate cannot forget a pending request behind which anything sits: what
`Gate.deadlines_armed` says of the gate alone holds of it in the join. -/
theorem fronted_deadlines_armed (sys : System σ) (bridge : Bridge σ) (config : GateConfig)
    (env : EnvModel (frontedSig σ)) : (fronted sys bridge config).Invariant env Fronted.Armed :=
  System.Invariant.filterMapIO (Gate.deadlines_armed bridge config env.under.left).join_left

/-- When the ids that arrive are distinct, as the adapter's are, no id is answered twice. -/
theorem fronted_answered_nodup (henv : (env.link none (.inl ())).duplicating = false)
    {events : List (Event (frontedSig σ))} {c : SysState (fronted sys bridge config)}
    (hrun : (SysState.init (fronted sys bridge config) env).run env events = some c)
    (hdistinct : (Fronted.arrived events).Nodup) : (Fronted.answered events).Nodup :=
  List.nodup_iff_count.mpr fun id =>
    Nat.le_trans (fronted_answered_le_arrived henv hrun id) (List.nodup_iff_count.mp hdistinct id)

/-- The same of the events the runtime's kernel reports, whatever the shell does with it. -/
theorem kernel_fronted_answered_le_arrived (sys : System σ) (bridge : Bridge σ)
    (config : GateConfig) [Hashable (frontedSig σ).Id]
    (ops : List (Kernel.Op (frontedSig σ))) (id : ReqId) :
    let booted := Kernel.boot (fronted sys bridge config)
    let events := booted.2.map .output ++ (booted.1.exec ops).events
    (Fronted.answered events).count id ≤ (Fronted.arrived events).count id := by
  dsimp only
  obtain ⟨evs, _, hrun, hawake, -⟩ := (Kernel.exec_reachable (fronted sys bridge config) ops).1
  have hanswered : Fronted.answered evs = Fronted.answered _ := Event.filterMap_eq_of_awake (fun _ => rfl) hawake
  have harrived : Fronted.arrived evs = Fronted.arrived _ := Event.filterMap_eq_of_awake (fun _ => rfl) hawake
  rw [← hanswered, ← harrived]
  exact fronted_answered_le_arrived rfl hrun id

end Fronted

/-! From `fronted sys` to `served sys`, the system `Http.serve` runs. -/

section Served

variable {env : EnvModel (servedSig σ)}

/-- `served sys` answers no request more often than it arrived, under the assumptions of
`fronted_answered_le_arrived`. -/
theorem served_answered_le_arrived (henv : (env.link none (.inl ())).duplicating = false)
    {events : List (Event (servedSig σ))} {c : SysState (served sys bridge config)}
    (hrun : (SysState.init (served sys bridge config) env).run env events = some c)
    (id : ReqId) :
    (Served.answered events).count id ≤ (Served.arrived events).count id := by
  obtain ⟨frontedEvents, c', hfronted, -, hunder⟩ := SysState.run_filterMapIO hrun
  have hanswered : Served.answered events = Fronted.answered frontedEvents := by
    refine hunder.filterMap_eq fun ev ev' h => ?_
    cases ev with
    | output out =>
      obtain ⟨out', rfl, hout'⟩ := h
      rcases out' with answer | out' <;> cases hout'
      rfl
    | _ =>
      cases h
      rfl
  have harrived : Served.arrived events = Fronted.arrived frontedEvents := by
    refine hunder.filterMap_eq fun ev ev' h => ?_
    cases ev with
    | output out =>
      obtain ⟨out', rfl, -⟩ := h
      rfl
    | _ =>
      cases h
      rfl
  rw [hanswered, harrived]
  exact fronted_answered_le_arrived henv hfronted id

theorem served_deadlines_armed (sys : System σ) (bridge : Bridge σ) (config : GateConfig)
    (env : EnvModel (servedSig σ)) : (served sys bridge config).Invariant env Served.Armed :=
  System.Invariant.filterMapIO (fronted_deadlines_armed sys bridge config env.under)

/-- When the ids that arrive are distinct, as the server's are, no id is answered twice. -/
theorem served_answered_nodup (henv : (env.link none (.inl ())).duplicating = false)
    {events : List (Event (servedSig σ))} {c : SysState (served sys bridge config)}
    (hrun : (SysState.init (served sys bridge config) env).run env events = some c)
    (hdistinct : (Served.arrived events).Nodup) : (Served.answered events).Nodup :=
  List.nodup_iff_count.mpr fun id =>
    Nat.le_trans (served_answered_le_arrived henv hrun id) (List.nodup_iff_count.mp hdistinct id)

/-- The same of the events the runtime's kernel reports, whatever the shell does with it. -/
theorem kernel_served_answered_le_arrived (sys : System σ) (bridge : Bridge σ)
    (config : GateConfig) [Hashable (servedSig σ).Id]
    (ops : List (Kernel.Op (servedSig σ))) (id : ReqId) :
    let booted := Kernel.boot (served sys bridge config)
    let events := booted.2.map .output ++ (booted.1.exec ops).events
    (Served.answered events).count id ≤ (Served.arrived events).count id := by
  dsimp only
  obtain ⟨evs, _, hrun, hawake, -⟩ := (Kernel.exec_reachable (served sys bridge config) ops).1
  have hanswered : Served.answered evs = Served.answered _ :=
    Event.filterMap_eq_of_awake (fun _ => rfl) hawake
  have harrived : Served.arrived evs = Served.arrived _ :=
    Event.filterMap_eq_of_awake (fun _ => rfl) hawake
  rw [← hanswered, ← harrived]
  exact served_answered_le_arrived rfl hrun id

end Served

end Lanes.Http
