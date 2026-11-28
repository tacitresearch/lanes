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
- `fronted_arrival_answered`, `served_arrival_answered`: in a fair run whose link from outside to
  the gate loses nothing, every request that arrives is answered.
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
          refine Classical.byContradiction fun hne => ?_
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
        refine Classical.byContradiction fun hne => ?_
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
    {r : (gateSystem bridge config).Run env} (hfair : r.Fair) {n : Nat}
    (hup : (r.state n).up () = true) (hid : id ∈ ((r.state n).state () : List ReqId)) :
    ∃ m, n ≤ m ∧ ∃ response, r.event m = some (.output (.inl (id, response))) := by
  obtain ⟨m, hm, hgone⟩ := System.LeadsTo.iff.mp (pending_leaves bridge config hcrash id)
    r hfair n ⟨hup, hid⟩
  have hleaves : ∃ k, n ≤ k ∧ id ∈ ((r.state k).state () : List ReqId) ∧
      id ∉ ((r.state (k + 1)).state () : List ReqId) := by
    induction m, hm using le_induction with
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
    {r : (fronted sys bridge config).Run env} (hfair : r.Fair) {n : Nat}
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
    {r : (served sys bridge config).Run env} (hfair : r.Fair) {n : Nat}
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

/-! ## Every arrival is answered

An arrival is a message from outside to the gate. On a link that loses nothing, to a gate that
is always up, a fair run hands it to the gate (`System.Run.Fair.delivered`). The gate answers it
in that step or admits it (`Gate.step_arrive`); an answer is handed over, and an admitted request
is answered (`served_pending_answered`). No premise on ids is needed: an arrival whose id is
waiting already is answered with it. -/

/-- A gate that the environment does not crash is up in every state. -/
theorem Gate.always_up {env : EnvModel (gateSig σ)} (hcrash : env.mayCrash () = false) :
    (gateSystem bridge config).Invariant env fun c => c.up () = true := by
  refine System.Inductive.invariant ⟨?_, fun c ev c' hup hstep => Gate.stays_up hcrash hup hstep⟩
  show (SysState.blank (gateSystem bridge config) |>.startActor env ()).up () = true
  rw [SysState.startActor, SysState.settle_up_of_running (by simp [gateActor, Effect.isStop])]
  simp

/-- The gate of `fronted sys` is up in every state, in an environment that does not crash it. -/
theorem fronted_gate_up {env : EnvModel (frontedSig σ)} (hcrash : env.mayCrash (.inl ()) = false) :
    (fronted sys bridge config).Invariant env fun c => c.up (.inl ()) = true :=
  System.Invariant.filterMapIO (Gate.always_up (env := env.under.left) hcrash).join_left

/-- The gate of `served sys` is up in every state, in an environment that does not crash it. -/
theorem served_gate_up {env : EnvModel (servedSig σ)} (hcrash : env.mayCrash (.inl ()) = false) :
    (served sys bridge config).Invariant env fun c => c.up (.inl ()) = true :=
  System.Invariant.filterMapIO (fronted_gate_up (env := env.under) hcrash)

private theorem gateActor_arrive (pending : List ReqId) (id : ReqId) (request : Request) :
    id ∈ ((gateActor bridge config).step pending (.arrive id request)).1 ∨
      ∃ response, Effect.emit (σ := gateSig σ) (.inl (id, response)) ∈
        ((gateActor bridge config).step pending (.arrive id request)).2 :=
  Gate.step_arrive bridge config _ pending id request

/-- An answer of the gate alone is an answer of `fronted sys`. -/
private theorem fronted_respond {pending : List ReqId} {msg : GateMsg σ} {id : ReqId}
    {response : Response}
    (h : Effect.emit (σ := gateSig σ) (.inl (id, response)) ∈
      ((gateActor bridge config).step pending msg).2) :
    Effect.emit (σ := frontedSig σ) (self := .inl ()) (.inl (id, response)) ∈
      (((fronted sys bridge config).actor (.inl ())).step pending msg).2 :=
  List.mem_flatMap.mpr ⟨_, List.mem_flatMap.mpr ⟨_, h, List.mem_singleton_self _⟩,
    List.mem_singleton_self _⟩

/-- The gate of `fronted sys` answers an arrival in the step that handles it, or it is waiting
after that step. -/
theorem fronted_handle_arrive {env : EnvModel (frontedSig σ)}
    (c : SysState (fronted sys bridge config)) (id : ReqId) (request : Request) :
    id ∈ ((c.handle env (.inl ()) (.arrive id request)).state (.inl ()) : List ReqId) ∨
      ∃ response, .inl (id, response) ∈ (c.handle env (.inl ()) (.arrive id request)).outbox := by
  rcases gateActor_arrive (c.state (.inl ())) id request with h | ⟨response, h⟩
  · rw [SysState.handle_state, update_self]
    exact .inl h
  · refine .inr ⟨response, ?_⟩
    rw [SysState.handle, SysState.settle_outbox_eq]
    exact List.mem_append_right _ (Effect.mem_emits.mpr (fronted_respond h))

/-- The gate of `served sys` answers an arrival in the step that handles it, or it is waiting
after that step. -/
theorem served_handle_arrive {env : EnvModel (servedSig σ)}
    (c : SysState (served sys bridge config)) (id : ReqId) (request : Request) :
    id ∈ ((c.handle env (.inl ()) (.arrive id request)).state (.inl ()) : List ReqId) ∨
      ∃ response, (id, response) ∈ (c.handle env (.inl ()) (.arrive id request)).outbox := by
  rcases gateActor_arrive (c.state (.inl ())) id request with h | ⟨response, h⟩
  · rw [SysState.handle_state, update_self]
    exact .inl h
  · refine .inr ⟨response, ?_⟩
    rw [SysState.handle, SysState.settle_outbox_eq]
    exact List.mem_append_right _ (Effect.mem_emits.mpr
      (List.mem_flatMap.mpr ⟨_, fronted_respond (sys := sys) h, List.mem_singleton_self _⟩))

/-- Every request that arrives at `fronted sys` is answered, whatever `sys` is: in a fair run, in
any environment that does not crash the gate and whose link from outside to the gate loses
nothing, an arrival is followed by a response to its id handed to the outside world. -/
theorem fronted_arrival_answered {env : EnvModel (frontedSig σ)}
    (hcrash : env.mayCrash (.inl ()) = false)
    (hlossless : (env.link none (.inl ())).lossy = false)
    {r : (fronted sys bridge config).Run env} (hfair : r.Fair) {n : Nat} {id : ReqId}
    {request : Request} (hin : r.event n = some (.input (.inl (id, request)))) :
    ∃ m, n ≤ m ∧ ∃ response, r.event m = some (.output (.inl (id, response))) := by
  have hup (m : Nat) : (r.state m).up (.inl ()) = true := fronted_gate_up hcrash _ (r.reachable m)
  let e : Envelope (frontedSig σ) := ⟨none, .inl (), .arrive id request⟩
  have he : e ∈ (r.state (n + 1)).net := by
    rw [SysState.step_input.mp (System.Run.step_some hin)]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨m, hm, hev⟩ := hfair.delivered hlossless (fun m _ => hup m) he
  have hQ : id ∈ ((r.state (m + 1)).state (.inl ()) : List ReqId) ∨
      ∃ response, .inl (id, response) ∈ (r.state (m + 1)).outbox := by
    rcases hev with hev | hev
    · obtain ⟨-, -, hc⟩ := SysState.step_deliver.mp (System.Run.step_some hev)
      rw [hc]
      exact fronted_handle_arrive _ id request
    · obtain ⟨-, -, -, hc⟩ := SysState.step_duplicate.mp (System.Run.step_some hev)
      rw [hc]
      exact fronted_handle_arrive _ id request
  rcases hQ with hid | ⟨response, hout⟩
  · obtain ⟨m', hm', response, hev'⟩ := fronted_pending_answered hcrash id hfair (hup (m + 1)) hid
    exact ⟨m', by omega, response, hev'⟩
  · obtain ⟨m', hm', hev'⟩ := hfair.output_taken hout
    exact ⟨m', by omega, response, hev'⟩

/-- Every request that arrives at `served sys` is answered, under the assumptions of
`fronted_arrival_answered`. With `served_answered_le_arrived`, a request whose id is used once
is answered exactly once. -/
theorem served_arrival_answered {env : EnvModel (servedSig σ)}
    (hcrash : env.mayCrash (.inl ()) = false)
    (hlossless : (env.link none (.inl ())).lossy = false)
    {r : (served sys bridge config).Run env} (hfair : r.Fair) {n : Nat} {id : ReqId}
    {request : Request} (hin : r.event n = some (.input (id, request))) :
    ∃ m, n ≤ m ∧ ∃ response, r.event m = some (.output (id, response)) := by
  have hup (m : Nat) : (r.state m).up (.inl ()) = true := served_gate_up hcrash _ (r.reachable m)
  let e : Envelope (servedSig σ) := ⟨none, .inl (), .arrive id request⟩
  have he : e ∈ (r.state (n + 1)).net := by
    rw [SysState.step_input.mp (System.Run.step_some hin)]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨m, hm, hev⟩ := hfair.delivered hlossless (fun m _ => hup m) he
  have hQ : id ∈ ((r.state (m + 1)).state (.inl ()) : List ReqId) ∨
      ∃ response, (id, response) ∈ (r.state (m + 1)).outbox := by
    rcases hev with hev | hev
    · obtain ⟨-, -, hc⟩ := SysState.step_deliver.mp (System.Run.step_some hev)
      rw [hc]
      exact served_handle_arrive _ id request
    · obtain ⟨-, -, -, hc⟩ := SysState.step_duplicate.mp (System.Run.step_some hev)
      rw [hc]
      exact served_handle_arrive _ id request
  rcases hQ with hid | ⟨response, hout⟩
  · obtain ⟨m', hm', response, hev'⟩ := served_pending_answered hcrash id hfair (hup (m + 1)) hid
    exact ⟨m', by omega, response, hev'⟩
  · obtain ⟨m', hm', hev'⟩ := hfair.output_taken hout
    exact ⟨m', by omega, response, hev'⟩

end Lanes.Http
