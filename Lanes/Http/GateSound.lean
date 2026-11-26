/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.KernelSound
public import Lanes.Actors.Lift
public import Lanes.Actors.Run
public import Lanes.Http.Gate

/-!
The gate answers each arrival at most once, for every system, bridge and configuration
(`answered_le_arrived`), and it cannot forget a pending request, because the request's deadline
stays armed (`deadlines_armed`).

The first is a count kept along a run. For each request id, the answers already output, the
answers waiting in the outbox, the id's place in the pending list and its arrivals still in
flight never add up to more than the arrivals so far. An arrival pays for one of these, and
each step of the gate moves the payment along or drops it.
-/

@[expose] public section

namespace Lanes.Http

variable {σ : Signature} {sys : System σ} {bridge : Bridge σ} {config : GateConfig}
  {env : EnvModel (gatedSig σ)}

def arrived (events : List (Event (gatedSig σ))) : List ReqId :=
  events.filterMap fun
    | .input x => some x.1
    | _ => none

def answered (events : List (Event (gatedSig σ))) : List ReqId :=
  events.filterMap fun
    | .output out => some out.1
    | _ => none

private def arriving (id : ReqId) : Envelope (gatedSig σ) → Bool
  | ⟨_, none, .arrive id' _⟩ => id' == id
  | _ => false

@[simp] private theorem arriving_arrive (id id' : ReqId) (src : Option (Option σ.Id))
    (request : Request) :
    arriving id (⟨src, none, GateMsg.arrive id' request⟩ : Envelope (gatedSig σ)) = (id' == id) :=
  rfl

@[simp] private theorem arriving_answer (id : ReqId) (src : Option (Option σ.Id)) (out : σ.Out) :
    arriving id (⟨src, none, GateMsg.answer out⟩ : Envelope (gatedSig σ)) = false := rfl

@[simp] private theorem arriving_expire (id id' : ReqId) (src : Option (Option σ.Id)) :
    arriving id (⟨src, none, GateMsg.expire id'⟩ : Envelope (gatedSig σ)) = false := rfl

@[simp] private theorem arriving_inner (id : ReqId) (src : Option (Option σ.Id)) (i : σ.Id)
    (msg : σ.Msg i) : arriving id (⟨src, some i, msg⟩ : Envelope (gatedSig σ)) = false := rfl

private def owed (id : ReqId) (c : SysState (gated sys bridge config)) : Nat :=
  c.outbox.countP (·.1 == id) + List.count id (c.state none) + c.net.countP (arriving id)

/-- The gate owes at most `n` answers for `id`. The other two clauses say an arrival is counted
when it is handled and at no other time: only the outside world sends one, and none is a
timer. -/
private structure Owes (id : ReqId) (n : Nat) (c : SysState (gated sys bridge config)) :
    Prop where
  atMost : owed id c ≤ n
  fromOutside : ∀ j id' request, (⟨some j, none, GateMsg.arrive id' request⟩ : Envelope _) ∉ c.net
  noArrivalTimer : ∀ id' request, GateMsg.arrive id' request ∉ c.timers none

namespace Owes

variable {id : ReqId} {n : Nat} {c c' : SysState (gated sys bridge config)}

private theorem of_le (h : Owes id n c) (houtbox : c'.outbox = c.outbox)
    (hstate : c'.state none = c.state none) (hnet : c'.net.Sublist c.net)
    (htimers : ∀ msg ∈ c'.timers none, msg ∈ c.timers none) : Owes id n c' where
  atMost := by
    have := hnet.countP_le (p := arriving id)
    have := h.atMost
    simp only [owed, houtbox, hstate] at *
    omega
  fromOutside j id' request he := h.fromOutside j id' request (hnet.subset he)
  noArrivalTimer id' request hmsg := h.noArrivalTimer id' request (htimers _ hmsg)

private theorem down (h : Owes id n c) (i : Option σ.Id) : Owes id n (c.down env i) := by
  refine h.of_le rfl rfl List.filter_sublist ?_
  cases i <;> simp [SysState.down]

local macro "settled" : tactic => `(tactic|
  (refine ⟨?_, ?_, ?_⟩ <;>
    simp [owed, SysState.settle, SysState.perform, Effect.isStop, List.mem_erase_of_ne, *] <;>
    first
    | done
    | grind [List.count_eq_zero]
    | (intros; split <;> simp [*])))

private theorem handle_gate (h : Owes id n c) (src : Option (Option σ.Id)) (msg : GateMsg σ) :
    Owes id (n + (arriving id ⟨src, none, msg⟩).toNat) (c.handle env none msg) := by
  obtain ⟨hatMost, hsrc, htimers⟩ := h
  simp only [owed] at hatMost
  cases msg with
  | arrive id' request =>
    simp only [SysState.handle, gate, Gate.step]
    split
    · settled
    · split
      · settled
      · split
        · settled
        · settled
  | answer out =>
    simp only [SysState.handle, gate, Gate.step]
    split
    · split
      · settled
      · settled
    · settled
  | expire id' =>
    simp only [SysState.handle, gate, Gate.step]
    split
    · settled
    · settled

private theorem start_gate (h : Owes id n c) : Owes id n (c.startActor env none) := by
  apply SysState.settle_induction
  · exact h.of_le rfl (by simp [gate]) (List.Sublist.refl _) fun _ hmsg => hmsg
  · intro c' eff heff ⟨hatMost, hsrc, htimers⟩
    obtain ⟨id', -, rfl⟩ := List.mem_map.mp heff
    simp only [owed] at hatMost
    settled
  · exact fun c' hc' => hc'.down none

private theorem perform_inner (h : Owes id n c) {j : σ.Id} (eff : Effect σ j) :
    Owes id n (c.perform (some j) (liftEffect eff)) := by
  obtain ⟨hatMost, hsrc, htimers⟩ := h
  simp only [owed] at hatMost
  cases eff <;> simp only [liftEffect] <;> settled

private theorem settle_inner (h : Owes id n c) (j : σ.Id)
    (r : sys.State j × List (Effect σ j)) :
    Owes id n (c.settle env (some j) (r.1, r.2.flatMap fun eff => [liftEffect eff])) := by
  apply SysState.settle_induction
  · exact h.of_le rfl (by simp) (List.Sublist.refl _) fun _ hmsg => hmsg
  · intro c' eff heff hc'
    obtain ⟨eff, -, heff⟩ := List.mem_flatMap.mp heff
    exact List.mem_singleton.mp heff ▸ hc'.perform_inner eff
  · exact fun c' hc' => hc'.down (some j)

private theorem start (h : Owes id n c) (i : Option σ.Id) : Owes id n (c.startActor env i) := by
  cases i with
  | none =>
    refine start_gate ?_
    exact h.of_le rfl rfl (List.Sublist.refl _) fun _ hmsg => hmsg
  | some j =>
    refine settle_inner ?_ j _
    exact h.of_le rfl rfl (List.Sublist.refl _) fun _ hmsg => hmsg

private theorem init (id : ReqId) : Owes id 0 (SysState.init (gated sys bridge config) env) := by
  apply SysState.init_induction
  · exact ⟨by simp [owed, SysState.blank, gate], by simp [SysState.blank],
      by simp [SysState.blank]⟩
  · exact fun c i h => h.start i

private theorem input (h : Owes id n c) (x : ReqId × Request) :
    Owes id (n + if x.1 = id then 1 else 0)
      { c with net := c.net ++ [⟨none, none, GateMsg.arrive x.1 x.2⟩] } := by
  obtain ⟨hatMost, hsrc, htimers⟩ := h
  simp only [owed] at hatMost
  settled

private theorem output (h : Owes id n c) {out : ReqId × Response} (hout : out ∈ c.outbox) :
    ∃ m, (m + if out.1 = id then 1 else 0) = n ∧
      Owes id m { c with outbox := c.outbox.erase out } := by
  have hcount := countP_erase_add (·.1 == id) hout
  have hatMost := h.atMost
  simp only [owed, Bool.toNat] at hatMost hcount
  refine ⟨n - if out.1 = id then 1 else 0, by split <;> simp_all <;> omega, ?_, h.fromOutside,
    h.noArrivalTimer⟩
  simp only [owed]
  split <;> simp_all <;> omega

private theorem erase (h : Owes id n c) {e : Envelope (gatedSig σ)} (he : e ∈ c.net) :
    ∃ m, m + (arriving id e).toNat = n ∧ Owes id m { c with net := c.net.erase e } := by
  have hcount := countP_erase_add (arriving id) he
  have hatMost := h.atMost
  simp only [owed] at hatMost
  refine ⟨n - (arriving id e).toNat, by omega, ?_, ?_, h.noArrivalTimer⟩
  · simp only [owed]
    omega
  · exact fun j id' request he' => h.fromOutside j id' request (List.mem_of_mem_erase he')

private theorem handle (h : Owes id n c) (e : Envelope (gatedSig σ)) :
    Owes id (n + (arriving id e).toNat) (c.handle env e.dst e.msg) := by
  obtain ⟨src, dst, msg⟩ := e
  cases dst with
  | none => exact h.handle_gate src msg
  | some j => exact h.settle_inner j _

private theorem not_arriving_of_duplicating (h : Owes id n c)
    (henv : (env.link none none).duplicating = false) {e : Envelope (gatedSig σ)} (he : e ∈ c.net)
    (hduplicating : (env.link e.src e.dst).duplicating = true) : arriving id e = false := by
  obtain ⟨src, dst, msg⟩ := e
  cases dst with
  | some j => rfl
  | none =>
    cases msg with
    | arrive id' request =>
      cases src with
      | none => simp [henv] at hduplicating
      | some j => exact absurd he (h.fromOutside j id' request)
    | _ => rfl

private theorem not_arriving_of_timer (h : Owes id n c) {i : Option σ.Id}
    {msg : (gatedSig σ).Msg i} (hmsg : msg ∈ c.timers i) : arriving id ⟨none, i, msg⟩ = false := by
  cases i with
  | some j => rfl
  | none =>
    cases msg with
    | arrive id' request => exact absurd hmsg (h.noArrivalTimer id' request)
    | _ => rfl

private theorem internal (h : Owes id n c) (henv : (env.link none none).duplicating = false)
    {ev : Event (gatedSig σ)} (hvisible : ev.visible = none) (hstep : c.step env ev = some c') :
    Owes id n c' := by
  cases ev with
  | input x => simp [Event.visible] at hvisible
  | output out => simp [Event.visible] at hvisible
  | deliver e =>
    obtain ⟨_, hdeliverable, rfl⟩ := SysState.step_deliver.mp hstep
    obtain ⟨m, rfl, hm⟩ := h.erase (SysState.mem_of_deliverable hdeliverable)
    exact hm.handle e
  | duplicate e =>
    obtain ⟨_, hduplicating, hdeliverable, rfl⟩ := SysState.step_duplicate.mp hstep
    have hmem := SysState.mem_of_deliverable hdeliverable
    simpa [h.not_arriving_of_duplicating henv hmem hduplicating] using h.handle (env := env) e
  | drop e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_drop.mp hstep
    exact h.of_le rfl rfl List.erase_sublist fun _ hmsg => hmsg
  | timeout i msg =>
    obtain ⟨_, hmem, rfl⟩ := SysState.step_timeout.mp hstep
    have h' : Owes id n { c with timers := update c.timers i ((c.timers i).erase msg) } := by
      refine h.of_le rfl rfl (List.Sublist.refl _) ?_
      cases i with
      | none => simpa using fun _ => List.mem_of_mem_erase
      | some j => simp
    simpa [h.not_arriving_of_timer hmem] using h'.handle (env := env) ⟨none, i, msg⟩
  | crash i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_crash.mp hstep
    exact h.down i
  | start i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
    exact h.start i

end Owes

/-- The gate answers each arrival at most once, whatever is behind it. Actors may crash,
restart and stop, and links may lose, reorder and duplicate. The one assumption is that the
outside world hands each arrival to the gate once. -/
theorem answered_le_arrived (henv : (env.link none none).duplicating = false)
    {events : List (Event (gatedSig σ))} {c : SysState (gated sys bridge config)}
    (hrun : (SysState.init (gated sys bridge config) env).run env events = some c) (id : ReqId) :
    (answered events).count id ≤ (arrived events).count id := by
  suffices h : ∃ n, (answered events).count id + n ≤ (arrived events).count id ∧ Owes id n c by
    obtain ⟨n, hle, -⟩ := h
    omega
  refine System.Reachable.run_induction
    (P := fun events c => ∃ n, (answered events).count id + n ≤ (arrived events).count id
      ∧ Owes id n c) .init hrun ⟨0, by simp [answered, arrived], .init id⟩ ?_
  rintro evs c₁ ev c₂ - ⟨n, hle, howes⟩ hstep
  cases ev with
  | input x =>
    obtain rfl := SysState.step_input.mp hstep
    refine ⟨_, ?_, howes.input x⟩
    have harrived : arrived (evs ++ [.input x]) = arrived evs ++ [x.1] := by simp [arrived]
    have hanswered : answered (evs ++ [.input x]) = answered evs := by simp [answered]
    rw [harrived, hanswered, List.count_append, List.count_singleton]
    by_cases hx : x.1 = id <;> simp [hx] <;> omega
  | output out =>
    obtain ⟨hout, rfl⟩ := SysState.step_output.mp hstep
    obtain ⟨m, rfl, hm⟩ := howes.output hout
    refine ⟨m, ?_, hm⟩
    have harrived : arrived (evs ++ [.output out]) = arrived evs := by simp [arrived]
    have hanswered : answered (evs ++ [.output out]) = answered evs ++ [out.1] := by
      simp [answered]
    rw [harrived, hanswered, List.count_append, List.count_singleton]
    by_cases hout : out.1 = id <;> simp [hout] at hle ⊢ <;> omega
  | _ => exact ⟨n, by simpa [answered, arrived] using hle, howes.internal henv rfl hstep⟩

/-- When the ids that arrive are distinct, as the adapter's are, no id is answered twice. -/
theorem answered_nodup (henv : (env.link none none).duplicating = false)
    {events : List (Event (gatedSig σ))} {c : SysState (gated sys bridge config)}
    (hrun : (SysState.init (gated sys bridge config) env).run env events = some c)
    (hdistinct : (arrived events).Nodup) : (answered events).Nodup :=
  List.nodup_iff_count.mpr fun id =>
    Nat.le_trans (answered_le_arrived henv hrun id) (List.nodup_iff_count.mp hdistinct id)

/-- The same of the events the runtime's kernel reports, whatever the shell does with it. -/
theorem kernel_answered_le_arrived (sys : System σ) (bridge : Bridge σ) (config : GateConfig)
    [Hashable (Option σ.Id)] (ops : List (Kernel.Op (gatedSig σ))) (id : ReqId) :
    let booted := Kernel.boot (gated sys bridge config)
    let events := booted.2.map .output ++ (booted.1.exec ops).events
    (answered events).count id ≤ (arrived events).count id := by
  dsimp only
  obtain ⟨evs, _, hrun, hawake, -⟩ := (Kernel.exec_reachable (gated sys bridge config) ops).1
  have hanswered : answered evs = answered _ := Event.filterMap_eq_of_awake (fun _ => rfl) hawake
  have harrived : arrived evs = arrived _ := Event.filterMap_eq_of_awake (fun _ => rfl) hawake
  rw [← hanswered, ← harrived]
  exact answered_le_arrived rfl hrun id

/-- While the gate is up, every pending request has its deadline armed. -/
def Armed (c : SysState (gated sys bridge config)) : Prop :=
  c.up none = true → ∀ id ∈ (c.state none : List ReqId), GateMsg.expire id ∈ c.timers none

local macro "armed" : tactic => `(tactic|
  (simp [Armed, SysState.settle, SysState.perform, Effect.isStop] <;>
    first
    | done
    | grind [List.Nodup.mem_erase_iff]
    | skip))

/-- A firing deadline has left the timers when the gate handles it, hence `≠ msg`. -/
private theorem armed_handle_gate {c : SysState (gated sys bridge config)} (msg : GateMsg σ)
    (hnodup : List.Nodup (c.state none))
    (h : ∀ id ∈ (c.state none : List ReqId), GateMsg.expire id ≠ msg →
      GateMsg.expire id ∈ c.timers none) :
    Armed (c.handle env none msg) := by
  cases msg with
  | arrive id' request =>
    replace h := fun id hid => h id hid nofun
    simp only [SysState.handle, gate, Gate.step]
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
    simp only [SysState.handle, gate, Gate.step]
    split
    · split
      · armed
        intro _ id hid
        obtain ⟨hne, hid⟩ := hnodup.mem_erase_iff.mp hid
        exact (List.mem_erase_of_ne (by simpa using hne)).mpr (h id hid)
      · armed
    · armed
  | expire id' =>
    simp only [SysState.handle, gate, Gate.step]
    split
    · armed
    · armed

private theorem armed_start_gate (c : SysState (gated sys bridge config)) :
    Armed (c.startActor env none) := by
  intro _ id hid
  have hrunning : ((c.state none : List ReqId).map fun id =>
      (Effect.after config.requestTimeout_ms (.expire id) : Effect (gatedSig σ) none)).any
        Effect.isStop = false := by
    simp [List.any_map, Effect.isStop]
  simp [SysState.startActor, SysState.settle, gate, hrunning] at hid ⊢
  exact SysState.mem_timers_performAll_after _ _ _ _ _ (.inr ⟨id, hid, rfl⟩)

private theorem Armed.settle_inner {c : SysState (gated sys bridge config)} (h : Armed c)
    (j : σ.Id) (r : (gated sys bridge config).State (some j) × List (Effect (gatedSig σ) (some j))) :
    Armed (c.settle env (some j) r) := by
  simpa [Armed, SysState.settle_up_of_ne, SysState.settle_timers_of_ne] using h

private theorem Armed.handle {c : SysState (gated sys bridge config)} (h : Armed c)
    (hnodup : List.Nodup (c.state none)) {i : Option σ.Id} (hup : c.up i = true)
    (msg : (gatedSig σ).Msg i) : Armed (c.handle env i msg) := by
  cases i with
  | none => exact armed_handle_gate msg hnodup fun id hid _ => h hup id hid
  | some j => exact h.settle_inner j _

private theorem Armed.start {c : SysState (gated sys bridge config)} (h : Armed c)
    (i : Option σ.Id) : Armed (c.startActor env i) := by
  cases i with
  | none => exact armed_start_gate c
  | some j =>
    refine Armed.settle_inner ?_ j _
    simpa [Armed] using h

/-- The gate cannot forget a pending request: while the gate is up the request's deadline is
armed, so the gate answers it when the system does or when the deadline fires. -/
theorem deadlines_armed (sys : System σ) (bridge : Bridge σ) (config : GateConfig)
    (env : EnvModel (gatedSig σ)) : (gated sys bridge config).Invariant env Armed := by
  intro c hc
  induction hc with
  | init =>
    apply SysState.init_induction
    · simp [Armed, SysState.blank]
    · exact fun c i h => h.start i
  | @step c c' ev hc hstep ih =>
    have hnodup : List.Nodup (c.state none) :=
      (System.invariant_of_actor _ none (gate_bounded sys bridge config) env c hc).2
    cases ev with
    | input x =>
      obtain rfl := SysState.step_input.mp hstep
      exact ih
    | deliver e =>
      obtain ⟨hup, _, rfl⟩ := SysState.step_deliver.mp hstep
      exact Armed.handle (c := { c with net := c.net.erase e }) ih hnodup hup e.msg
    | duplicate e =>
      obtain ⟨hup, _, _, rfl⟩ := SysState.step_duplicate.mp hstep
      exact ih.handle hnodup hup e.msg
    | drop e =>
      obtain ⟨_, _, rfl⟩ := SysState.step_drop.mp hstep
      exact ih
    | timeout i msg =>
      obtain ⟨hup, _, rfl⟩ := SysState.step_timeout.mp hstep
      cases i with
      | none =>
        refine armed_handle_gate msg hnodup fun id hid hne => ?_
        simpa using (List.mem_erase_of_ne hne).mpr (ih hup id hid)
      | some j =>
        refine Armed.settle_inner ?_ j _
        simpa [Armed] using ih
    | output out =>
      obtain ⟨_, rfl⟩ := SysState.step_output.mp hstep
      exact ih
    | crash i =>
      obtain ⟨_, _, rfl⟩ := SysState.step_crash.mp hstep
      cases i with
      | none => simp [Armed, SysState.down]
      | some j => simpa [Armed, SysState.down] using ih
    | start i =>
      obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
      exact ih.start i

end Lanes.Http
