/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Http.GateSound
public import Lanes.Semantics.Liveness

/-!
# The gate answers every request it admits

`Lanes.Http.GateSound` proves that the gate answers an arrival at most once. This file proves
the other half for a request the gate has admitted: it is answered, for every system behind the
gate, every bridge and every configuration, in every environment that does not crash the gate.

The obligation that makes it true is the request's deadline. While the request waits its
`expire` timer is armed (`deadlines_armed`), the gate stays up, no step arms the timer again
(`deadline_not_restarted`), and firing the timer removes the request. So whatever the system
behind the gate does or fails to do, the request stops waiting (`pending_leaves`). A request
stops waiting only in a step that emits its answer (`answered_of_leaves`), and an emitted
answer is handed over (`System.Run.Fair.output_taken`). Together: every admitted request is
answered (`pending_answered`).

The gate must not crash. Without that the statement is false: the gate crashes after admitting
a request, nothing obliges anyone to start an actor that has no mail, and the request waits in
its state forever. A gate that restarts arms the deadlines again, so the statement could be
recovered from an assumption that a crashed gate is restarted; no such assumption can be stated
yet.

## Main statements

- `deadline_not_restarted`: no step arms the deadline of a waiting request again, so the
  runtime does not start its delay again and fairness obliges it to fire.
- `pending_leaves`: a request waiting in the gate leads to that request no longer waiting.
- `answered_of_leaves`: the step in which a request stops waiting emits an answer to it.
- `pending_answered`: in a fair run, an answer to a waiting request is eventually handed over.
-/

@[expose] public section

namespace Lanes.Http

variable {σ : Signature} {sys : System σ} {bridge : Bridge σ} {config : GateConfig}
  {env : EnvModel (gatedSig σ)}

/-- The gate never stops itself. -/
theorem gate_never_stops (pending : List ReqId) (msg : GateMsg σ) :
    ((gate sys bridge config).step pending msg).2.any Effect.isStop = false := by
  cases msg <;> simp only [gate] <;> repeat' split
  all_goals simp [Effect.isStop]

/-- A gate that the environment does not crash stays up. -/
theorem gate_stays_up (hcrash : env.mayCrash none = false)
    {c c' : SysState (gated sys bridge config)} {ev : Event (gatedSig σ)}
    (hup : c.up none = true) (hstep : c.step env ev = some c') : c'.up none = true :=
  SysState.up_of_step hcrash (fun pending msg => gate_never_stops pending msg) hup hstep

/-- No step starts the deadline of a waiting request again. The gate arms a deadline in two
places: when it admits a request, which was not waiting, and when it starts, which it cannot do
while it is up. No other actor arms a timer of the gate. -/
theorem deadline_not_restarted {c c' : SysState (gated sys bridge config)}
    {ev : Event (gatedSig σ)} {id : ReqId} (hup : c.up none = true)
    (hid : id ∈ (c.state none : List ReqId)) (hstep : c.step env ev = some c') :
    ¬(Obligation.timeout (σ := gatedSig σ) none (.expire id)).Restarted c ev := by
  have hgate (msg : GateMsg σ) :
      Event.timeout (σ := gatedSig σ) none (.expire id) ∉
        Effect.timeouts none ((gate sys bridge config).step (c.state none) msg).2 := by
    rw [Effect.mem_timeouts]
    cases msg <;> simp only [gate] <;> repeat' split
    all_goals simp
    rintro rfl
    contradiction
  have hinner (j : σ.Id) (effs : List (Effect (gatedSig σ) (some j))) :
      Event.timeout (σ := gatedSig σ) none (.expire id) ∉ Effect.timeouts (some j) effs := by
    intro h
    obtain ⟨_, h⟩ := Effect.eq_of_mem_timeouts h
    cases h
  cases ev with
  | deliver e | duplicate e =>
    obtain ⟨src, dst, msg⟩ := e
    cases dst with
    | none => exact hgate msg
    | some j => exact hinner j _
  | timeout i msg =>
    cases i with
    | none => exact hgate msg
    | some j => exact hinner j _
  | start i =>
    cases i with
    | none =>
      obtain ⟨hdown, -⟩ := SysState.step_start.mp hstep
      simp [hup] at hdown
    | some j => exact hinner j _
  | input _ | drop _ | output _ | crash _ => exact List.not_mem_nil

/-- A request waiting in the gate is eventually no longer waiting, whatever is behind the gate,
in any environment that does not crash the gate: its deadline is armed, is not armed again,
and fires. -/
theorem pending_leaves (sys : System σ) (bridge : Bridge σ) (config : GateConfig)
    (hcrash : env.mayCrash none = false) (id : ReqId) :
    (gated sys bridge config).LeadsTo env
      (fun c => c.up none = true ∧ id ∈ (c.state none : List ReqId))
      (fun c => id ∉ (c.state none : List ReqId)) := by
  refine System.LeadsTo.ensures_of_invariant
    (I := fun c => Armed c ∧ List.Nodup (c.state none)) ?_ (.timeout none (.expire id)) ?_ ?_ ?_
    ?_
  · exact fun c hc => ⟨deadlines_armed sys bridge config env c hc,
      (System.invariant_of_actor _ none (gate_bounded sys bridge config) env c hc).2⟩
  · intro c ev c' _ ⟨hup, _⟩ _ hstep
    by_cases hid : id ∈ (c'.state none : List ReqId)
    · exact .inl ⟨gate_stays_up hcrash hup hstep, hid⟩
    · exact .inr hid
  · exact fun c ⟨harmed, _⟩ ⟨hup, hid⟩ _ => ⟨hup, harmed hup id hid⟩
  · intro c c' ⟨_, hnodup⟩ ⟨_, hid⟩ _ hstep
    obtain ⟨_, _, rfl⟩ := SysState.step_timeout.mp hstep
    simp [gate, hid, hnodup.mem_erase_iff]
  · exact fun c ev c' _ ⟨hup, hid⟩ _ hstep hrestarted =>
      absurd hrestarted (deadline_not_restarted hup hid hstep)

/-- A step of the gate in which `id` stops waiting emits an answer to `id`. -/
private theorem answered_of_leaves_gate {c : SysState (gated sys bridge config)} {id : ReqId}
    (msg : GateMsg σ) (hin : id ∈ (c.state none : List ReqId))
    (hout : id ∉ ((c.handle env none msg).state none : List ReqId)) :
    ∃ response, (c.handle env none msg).outbox = c.outbox ++ [(id, response)] := by
  cases msg with
  | arrive id' request =>
    simp only [SysState.handle_state, update_self, gate] at hout
    repeat' split at hout
    all_goals simp [hin] at hout
  | answer out =>
    simp only [SysState.handle_state, update_self, gate] at hout
    simp only [SysState.handle, gate]
    split
    · next id' response hencode =>
      simp only [hencode] at hout
      split
      · next hpending =>
        simp only [hpending, ↓reduceIte] at hout
        have hid : id' = id := by
          by_contra hne
          exact hout ((List.mem_erase_of_ne (Ne.symm hne)).mpr hin)
        exact ⟨response, by simp [SysState.settle, SysState.perform, Effect.isStop, hid]⟩
      · next hpending => simp [hpending, hin] at hout
    · next hencode => simp [hencode, hin] at hout
  | expire id' =>
    simp only [SysState.handle_state, update_self, gate] at hout
    simp only [SysState.handle, gate]
    split
    · next hpending =>
      simp only [hpending, ↓reduceIte] at hout
      have hid : id' = id := by
        by_contra hne
        exact hout ((List.mem_erase_of_ne (Ne.symm hne)).mpr hin)
      exact ⟨timedOut, by simp [SysState.settle, SysState.perform, Effect.isStop, hid]⟩
    · next hpending => simp [hpending, hin] at hout

/-- A request leaves the gate only by being answered: the step in which `id` stops waiting
emits an output for `id`, the system's response or the gate's `504`. -/
theorem answered_of_leaves {c c' : SysState (gated sys bridge config)} {ev : Event (gatedSig σ)}
    {id : ReqId} (hstep : c.step env ev = some c') (hin : id ∈ (c.state none : List ReqId))
    (hout : id ∉ (c'.state none : List ReqId)) :
    ∃ response, c'.outbox = c.outbox ++ [(id, response)] := by
  have hhandle (c₁ : SysState (gated sys bridge config)) (i : Option σ.Id)
      (msg : (gatedSig σ).Msg i) (hstate : c₁.state none = c.state none)
      (houtbox : c₁.outbox = c.outbox)
      (hout : id ∉ ((c₁.handle env i msg).state none : List ReqId)) :
      ∃ response, (c₁.handle env i msg).outbox = c.outbox ++ [(id, response)] := by
    cases i with
    | none => exact houtbox ▸ answered_of_leaves_gate msg (hstate ▸ hin) hout
    | some j => simp [hstate, hin] at hout
  cases ev with
  | input x =>
    obtain rfl := SysState.step_input.mp hstep
    exact absurd hin hout
  | deliver e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_deliver.mp hstep
    exact hhandle _ _ _ rfl rfl hout
  | duplicate e =>
    obtain ⟨_, _, _, rfl⟩ := SysState.step_duplicate.mp hstep
    exact hhandle _ _ _ rfl rfl hout
  | drop e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_drop.mp hstep
    exact absurd hin hout
  | timeout i msg =>
    obtain ⟨_, _, rfl⟩ := SysState.step_timeout.mp hstep
    exact hhandle _ _ _ rfl rfl hout
  | output out =>
    obtain ⟨_, rfl⟩ := SysState.step_output.mp hstep
    exact absurd hin hout
  | crash i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_crash.mp hstep
    exact absurd hin hout
  | start i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
    cases i with
    | none => simp [gate, hin] at hout
    | some j => simp [hin] at hout

/-- Every request the gate admits is answered: in a fair run, in any environment that does not
crash the gate, a request waiting while the gate is up has an answer handed to the outside
world at a later position. -/
theorem pending_answered (hcrash : env.mayCrash none = false) (id : ReqId)
    {r : (gated sys bridge config).Run env} (hfair : r.Fair) {n : ℕ}
    (hup : (r.state n).up none = true) (hid : id ∈ ((r.state n).state none : List ReqId)) :
    ∃ m, n ≤ m ∧ ∃ response, r.event m = some (.output (id, response)) := by
  obtain ⟨m, hm, hgone⟩ := System.LeadsTo.iff.mp (pending_leaves sys bridge config hcrash id)
    r hfair n ⟨hup, hid⟩
  have hleaves : ∃ k, n ≤ k ∧ id ∈ ((r.state k).state none : List ReqId) ∧
      id ∉ ((r.state (k + 1)).state none : List ReqId) := by
    induction m, hm using Nat.le_induction with
    | base => exact absurd hid hgone
    | succ m hm ih =>
      by_cases hin : id ∈ ((r.state m).state none : List ReqId)
      · exact ⟨m, hm, hin, hgone⟩
      · exact ih hin
  obtain ⟨k, hk, hin, hout⟩ := hleaves
  cases hev : r.event k with
  | none => exact absurd (System.Run.step_none hev ▸ hin) hout
  | some ev =>
    obtain ⟨response, hemitted⟩ := answered_of_leaves (System.Run.step_some hev) hin hout
    obtain ⟨m', hm', htaken⟩ := hfair.output_taken (n := k + 1) (out := (id, response))
      (by simp [hemitted])
    exact ⟨m', by omega, response, htaken⟩

end Lanes.Http
