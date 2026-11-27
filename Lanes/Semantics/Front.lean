/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.FrontSound
public import Lanes.Semantics.FairJoin

/-!
# A fronted system answers every request its gate admits

A request the gate of `fronted sys` admits is answered, for every `sys`, in every fair run in
which the gate does not crash. This file proves it of the gate alone and carries it through the
join and the hidden inputs and outputs (`Lanes.Semantics.FairJoin`); nothing here looks at a step
of `fronted sys`. Then once more through the hidden inputs and outputs of `served sys`, the system
`Http.serve` runs.

Alone, the gate is one actor whose outside is a link that may lose, reorder and duplicate. While
a request waits its deadline is armed (`Gate.deadlines_armed`), the gate stays up if it is not
crashed, no step arms the deadline again (`Gate.deadline_not_restarted`), and firing it removes
the request (`Gate.pending_leaves`). A request stops waiting only in a step that emits its answer
(`Gate.answered_of_leaves`), and an emitted answer is handed over (`Gate.pending_answered`).

In `fronted sys` the gate is the left side of a join, behind `frontedInput` and `frontedOutput`.
A fair run of `fronted sys` is a fair run of the join (`System.underView_projects`:
`frontedOutput` shows different outputs differently), and that one is a fair run of the gate
alone (`Wiring.leftView_projects`). So a request waiting in the gate leaves it
(`fronted_pending_leaves`), and the answer the gate hands over alone is, by the deeds the
projections keep, an answer `fronted sys` hands over (`fronted_pending_answered`). `served sys`
hides more outputs of `fronted sys`, and shows different ones differently too.

The gate must not crash. Without that the statement is false: the gate crashes after admitting
a request, nothing obliges anyone to start an actor that has no mail, and the request waits in
its state forever. A gate that restarts arms the deadlines again, so the statement could be
recovered from an assumption that a crashed gate is restarted; no such assumption can be stated
yet.

## Main statements

- `Gate.pending_leaves`, `Gate.pending_answered`: the gate alone answers what it admits.
- `fronted_pending_leaves`, `served_pending_leaves`: a request waiting in the gate stops waiting.
- `fronted_pending_answered`, `served_pending_answered`: in a fair run, an answer to a waiting
  request is handed over.
-/

@[expose] public section

namespace Lanes.Http

variable {σ : Signature} {bridge : Bridge σ} {config : GateConfig}

namespace Gate

variable {env : EnvModel (gateSig σ)}

/-- The gate never stops itself. -/
theorem never_stops (pending : List ReqId) (msg : GateMsg σ) :
    ((gateActor bridge config).step pending msg).2.any Effect.isStop = false := by
  cases msg <;> simp only [gateActor, Gate.step] <;> repeat' split
  all_goals simp [Effect.isStop]

/-- A gate that the environment does not crash stays up. -/
theorem stays_up (hcrash : env.mayCrash () = false) {c c' : SysState (gateSystem bridge config)}
    {ev : Event (gateSig σ)} (hup : c.up () = true) (hstep : c.step env ev = some c') :
    c'.up () = true :=
  SysState.up_of_step hcrash (fun pending msg => never_stops pending msg) hup hstep

/-- No step starts the deadline of a waiting request again: the gate arms a deadline when it
admits a request, which was not waiting, and when it starts, which it cannot do while it is
up. -/
theorem deadline_not_restarted {c c' : SysState (gateSystem bridge config)}
    {ev : Event (gateSig σ)} {id : ReqId} (hup : c.up () = true)
    (hid : id ∈ (c.state () : List ReqId)) (hstep : c.step env ev = some c') :
    ¬(Obligation.timeout (σ := gateSig σ) () (.expire id)).Restarted c ev := by
  have hgate (msg : GateMsg σ) :
      Event.timeout (σ := gateSig σ) () (.expire id) ∉
        Effect.timeouts () ((gateActor bridge config).step (c.state ()) msg).2 := by
    rw [Effect.mem_timeouts]
    cases msg <;> simp only [gateActor, Gate.step] <;> repeat' split
    all_goals simp
    rintro rfl
    contradiction
  cases ev with
  | deliver e | duplicate e => exact hgate e.msg
  | timeout i msg => exact hgate msg
  | start i =>
    obtain ⟨hdown, -⟩ := SysState.step_start.mp hstep
    simp [hup] at hdown
  | input _ | drop _ | output _ | crash _ => exact List.not_mem_nil

/-- A request waiting in the gate alone is eventually no longer waiting, whatever arrives on its
two inputs, in any environment that does not crash it. -/
theorem pending_leaves (bridge : Bridge σ) (config : GateConfig)
    (hcrash : env.mayCrash () = false) (id : ReqId) :
    (gateSystem bridge config).LeadsTo env
      (fun c => c.up () = true ∧ id ∈ (c.state () : List ReqId))
      (fun c => id ∉ (c.state () : List ReqId)) := by
  refine System.LeadsTo.ensures_of_invariant
    (I := fun c => Armed c ∧ List.Nodup (c.state ())) ?_ (.timeout () (.expire id)) ?_ ?_ ?_ ?_
  · exact fun c hc => ⟨deadlines_armed bridge config env c hc,
      (System.invariant_of_actor _ () (gateActor_bounded bridge config) env c hc).2⟩
  · intro c ev c' _ ⟨hup, _⟩ _ hstep
    by_cases hid : id ∈ (c'.state () : List ReqId)
    · exact .inl ⟨stays_up hcrash hup hstep, hid⟩
    · exact .inr hid
  · exact fun c ⟨harmed, _⟩ ⟨hup, hid⟩ _ => ⟨hup, harmed hup id hid⟩
  · intro c c' ⟨_, hnodup⟩ ⟨_, hid⟩ _ hstep
    obtain ⟨_, _, rfl⟩ := SysState.step_timeout.mp hstep
    simp [gateActor, Gate.step, hid, hnodup.mem_erase_iff]
  · exact fun c ev c' _ ⟨hup, hid⟩ _ hstep hrestarted =>
      absurd hrestarted (deadline_not_restarted hup hid hstep)

/-- A step of the gate in which `id` stops waiting emits an answer to `id`. -/
private theorem answered_of_handle {c : SysState (gateSystem bridge config)} {id : ReqId}
    (msg : GateMsg σ) (hin : id ∈ (c.state () : List ReqId))
    (hout : id ∉ ((c.handle env () msg).state () : List ReqId)) :
    ∃ response, (c.handle env () msg).outbox = c.outbox ++ [.inl (id, response)] := by
  cases msg with
  | arrive id' request =>
    simp only [SysState.handle_state, update_self, gateActor, Gate.step] at hout
    repeat' split at hout
    all_goals simp [hin] at hout
  | answer out =>
    simp only [SysState.handle_state, update_self, gateActor, Gate.step] at hout
    simp only [SysState.handle, gateActor, Gate.step]
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
    simp only [SysState.handle_state, update_self, gateActor, Gate.step] at hout
    simp only [SysState.handle, gateActor, Gate.step]
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
theorem answered_of_leaves {c c' : SysState (gateSystem bridge config)} {ev : Event (gateSig σ)}
    {id : ReqId} (hstep : c.step env ev = some c') (hin : id ∈ (c.state () : List ReqId))
    (hout : id ∉ (c'.state () : List ReqId)) :
    ∃ response, c'.outbox = c.outbox ++ [.inl (id, response)] := by
  cases ev with
  | input x =>
    obtain rfl := SysState.step_input.mp hstep
    exact absurd hin hout
  | deliver e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_deliver.mp hstep
    exact answered_of_handle (c := { c with net := c.net.erase e }) e.msg hin hout
  | duplicate e =>
    obtain ⟨_, _, _, rfl⟩ := SysState.step_duplicate.mp hstep
    exact answered_of_handle e.msg hin hout
  | drop e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_drop.mp hstep
    exact absurd hin hout
  | timeout i msg =>
    obtain ⟨_, _, rfl⟩ := SysState.step_timeout.mp hstep
    exact answered_of_handle msg hin hout
  | output out =>
    obtain ⟨_, rfl⟩ := SysState.step_output.mp hstep
    exact absurd hin hout
  | crash i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_crash.mp hstep
    exact absurd hin hout
  | start i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
    simp [gateActor, hin] at hout

/-- The gate alone answers every request it admits: in a fair run in which it is not crashed, a
request waiting while it is up has an answer handed over at a later position. -/
theorem pending_answered (hcrash : env.mayCrash () = false) (id : ReqId)
    {r : (gateSystem bridge config).Run env} (hfair : r.Fair) {n : ℕ}
    (hup : (r.state n).up () = true) (hid : id ∈ ((r.state n).state () : List ReqId)) :
    ∃ m, n ≤ m ∧ ∃ response, r.event m = some (.output (.inl (id, response))) := by
  obtain ⟨m, hm, hgone⟩ := System.LeadsTo.iff.mp (pending_leaves bridge config hcrash id)
    r hfair n ⟨hup, hid⟩
  have hleaves : ∃ k, n ≤ k ∧ id ∈ ((r.state k).state () : List ReqId) ∧
      id ∉ ((r.state (k + 1)).state () : List ReqId) := by
    induction m, hm using Nat.le_induction with
    | base => exact absurd hid hgone
    | succ m hm ih =>
      by_cases hin : id ∈ ((r.state m).state () : List ReqId)
      · exact ⟨m, hm, hin, hgone⟩
      · exact ih hin
  obtain ⟨k, hk, hin, hout⟩ := hleaves
  cases hev : r.event k with
  | none => exact absurd (System.Run.step_none hev ▸ hin) hout
  | some ev =>
    obtain ⟨response, hemitted⟩ := answered_of_leaves (System.Run.step_some hev) hin hout
    obtain ⟨m', hm', htaken⟩ := hfair.output_taken (n := k + 1) (out := .inl (id, response))
      (by simp [hemitted])
    exact ⟨m', by omega, response, htaken⟩

end Gate

/-- `frontedOutput` shows different outputs differently, so `fronted sys` hides only what it
must. -/
theorem frontedOutput_inj {o₁ o₂ : (joinSig (gateSig σ) σ).Out} {x : (ReqId × Response) ⊕ σ.Out}
    (h₁ : frontedOutput o₁ = some x) (h₂ : frontedOutput o₂ = some x) : o₁ = o₂ := by
  rcases o₁ with (a₁ | b₁) | c₁ <;> rcases o₂ with (a₂ | b₂) | c₂ <;>
    simp only [frontedOutput, Option.some.injEq, reduceCtorEq] at h₁ h₂ <;> subst h₁ <;>
    simp_all

variable {sys : System σ} {env : EnvModel (frontedSig σ)}

/-- A request waiting in the gate of `fronted sys` is eventually no longer waiting, whatever
`sys` is, in any environment that does not crash the gate: what the gate alone does, it does in
front of `sys`. -/
theorem fronted_pending_leaves (sys : System σ) (bridge : Bridge σ) (config : GateConfig)
    (hcrash : env.mayCrash (.inl ()) = false) (id : ReqId) :
    (fronted sys bridge config).LeadsTo env
      (fun c => c.up (.inl ()) = true ∧ id ∈ (c.state (.inl ()) : List ReqId))
      (fun c => id ∉ (c.state (.inl ()) : List ReqId)) := by
  have hjoin : ((gateSystem bridge config).join sys (frontWiring bridge)).LeadsTo env.under
      (fun c => c.up (.inl ()) = true ∧ id ∈ (c.state (.inl ()) : List ReqId))
      (fun c => id ∉ (c.state (.inl ()) : List ReqId)) :=
    System.LeadsTo.join_left
      (P := fun c : SysState (gateSystem bridge config) =>
        c.up () = true ∧ id ∈ (c.state () : List ReqId))
      (Q := fun s _ => id ∉ (s () : List ReqId))
      (Gate.pending_leaves bridge config (env := env.under.left) hcrash id)
  exact System.LeadsTo.filterMapIO (sys := (gateSystem bridge config).join sys (frontWiring bridge))
    (input := frontedInput) (output := frontedOutput) (fun _ _ _ h₁ h₂ => frontedOutput_inj h₁ h₂)
    (P := fun s u => u (.inl ()) = true ∧ id ∈ (s (.inl ()) : List ReqId))
    (Q := fun s _ => id ∉ (s (.inl ()) : List ReqId)) hjoin

/-- Every request the gate of `fronted sys` admits is answered, whatever `sys` is: in a fair
run, in any environment that does not crash the gate, a request waiting while the gate is up
has an answer handed to the outside world at a later position. -/
theorem fronted_pending_answered (hcrash : env.mayCrash (.inl ()) = false) (id : ReqId)
    {r : (fronted sys bridge config).Run env} (hfair : r.Fair) {n : ℕ}
    (hup : (r.state n).up (.inl ()) = true)
    (hid : id ∈ ((r.state n).state (.inl ()) : List ReqId)) :
    ∃ m, n ≤ m ∧ ∃ response, r.event m = some (.output (.inl (id, response))) := by
  obtain ⟨r₁, f, hfair₁, hsees₁⟩ :=
    (System.underView_projects (fun _ _ _ h₁ h₂ => frontedOutput_inj h₁ h₂) env).fair_run hfair
  obtain ⟨r₂, g, hfair₂, hsees₂⟩ := ((frontWiring bridge).leftView_projects env.under).fair_run
    hfair₁
  obtain ⟨hover, -⟩ := hsees₁.rel n
  have hrel : r₂.state (g (f n)) = (r₁.state (f n)).thinLeft := hsees₂.rel (f n)
  rw [← hover] at hup hid
  have hup₂ : (r₂.state (g (f n))).up () = true := by
    rw [hrel]
    exact hup
  have hid₂ : id ∈ ((r₂.state (g (f n))).state () : List ReqId) := by
    rw [hrel]
    exact hid
  obtain ⟨m, hm, response, hev⟩ := Gate.pending_answered hcrash id hfair₂ hup₂ hid₂
  obtain ⟨N, hN, ev, hev₁, hdeed⟩ := hsees₂.shown_after hm hev rfl
  obtain rfl := Event.leftDeed_eq_output hdeed
  obtain ⟨M, hM, ev', hev', hshows⟩ := hsees₁.shown_after hN hev₁ rfl
  refine ⟨M, hM, response, ?_⟩
  rw [hev']
  cases ev' with
  | output o =>
    obtain rfl : o = .inl (id, response) := by simpa [System.underView] using hshows
    rfl
  | _ => simp [System.underView] at hshows

/-- `Sum.getLeft?` shows different outputs differently, so `served sys` hides only what it
must. -/
theorem servedOutput_inj {o₁ o₂ : (frontedSig σ).Out} {x : ReqId × Response}
    (h₁ : o₁.getLeft? = some x) (h₂ : o₂.getLeft? = some x) : o₁ = o₂ := by
  rcases o₁ with a₁ | b₁ <;> rcases o₂ with a₂ | b₂ <;> simp_all

/-- A request waiting in the gate of `served sys` is eventually no longer waiting, under the
assumption of `fronted_pending_leaves`. -/
theorem served_pending_leaves (sys : System σ) (bridge : Bridge σ) (config : GateConfig)
    {env : EnvModel (servedSig σ)} (hcrash : env.mayCrash (.inl ()) = false) (id : ReqId) :
    (served sys bridge config).LeadsTo env
      (fun c => c.up (.inl ()) = true ∧ id ∈ (c.state (.inl ()) : List ReqId))
      (fun c => id ∉ (c.state (.inl ()) : List ReqId)) :=
  System.LeadsTo.filterMapIO (sys := fronted sys bridge config) (input := .inl)
    (output := Sum.getLeft?) (fun _ _ _ h₁ h₂ => servedOutput_inj h₁ h₂)
    (P := fun s u => u (.inl ()) = true ∧ id ∈ (s (.inl ()) : List ReqId))
    (Q := fun s _ => id ∉ (s (.inl ()) : List ReqId))
    (fronted_pending_leaves sys bridge config (env := env.under) hcrash id)

/-- Every request the gate of `served sys` admits is answered: in a fair run, in any environment
that does not crash the gate, a request waiting while the gate is up has a response handed to
the outside world at a later position. -/
theorem served_pending_answered {env : EnvModel (servedSig σ)}
    (hcrash : env.mayCrash (.inl ()) = false) (id : ReqId)
    {r : (served sys bridge config).Run env} (hfair : r.Fair) {n : ℕ}
    (hup : (r.state n).up (.inl ()) = true)
    (hid : id ∈ ((r.state n).state (.inl ()) : List ReqId)) :
    ∃ m, n ≤ m ∧ ∃ response, r.event m = some (.output (id, response)) := by
  obtain ⟨r₁, f, hfair₁, hsees₁⟩ :=
    (System.underView_projects (fun _ _ _ h₁ h₂ => servedOutput_inj h₁ h₂) env).fair_run hfair
  obtain ⟨hover, -⟩ := hsees₁.rel n
  rw [← hover] at hup hid
  obtain ⟨m, hm, response, hev⟩ := fronted_pending_answered hcrash id hfair₁ hup hid
  obtain ⟨M, hM, ev, hev', hshows⟩ := hsees₁.shown_after hm hev rfl
  refine ⟨M, hM, response, ?_⟩
  rw [hev']
  cases ev with
  | output o =>
    obtain rfl : o = (id, response) := by simpa [System.underView] using hshows
    rfl
  | _ => simp [System.underView] at hshows

end Lanes.Http
