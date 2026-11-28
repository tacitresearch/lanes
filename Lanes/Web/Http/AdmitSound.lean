/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Step
public import Lanes.Proof.List
public import Lanes.Web.Http.Admit
public import Lanes.Web.Http.FrontSound

/-!
# The gate before the shard is the gate in the system

`Http.serve` makes the gate's decisions before the shard (`Lanes.Web.Http.Admit`). This file
proves that nothing is lost by it: the gate keeps its three theorems, and a run of the front
with the shard is a run of `served sys`, the system with the gate as an actor, with the same
requests arriving and the same answers handed over.

**The front alone.** The front is `Gate.step` folded over the messages it sees, with the
deadlines it arms (`Front`). It answers no request more often than it arrived
(`Front.run_answered_le`), its waiting list stays within `maxPending` and free of repeats
(`Front.run_bounded`), and every request that waits is answered, if every deadline that stays
armed is eventually passed to it (`Front.pending_answered`). The last is what the server's
ticker is trusted to do.

**The front with the shard.** `Front.World` is what the server runs, as a transition system:
the front's state and its answers not yet handed over, beside the shard's state, a state of
`admitted sys` under the kernel's environment (`EnvModel.reliable`). Its events are a request
arriving, a deadline passing, the front taking an output of the shard, an answer handed over,
and the shard's own events. `Front.World.refines` proves that every run of it is a run of
`served sys bridge config` under `Front.servedEnv`, with the same inputs and outputs in the
same order: the gate's waiting list and deadlines are the front's, the application's actors
have the same states, timers and messages, and the answers on their way to the gate are the
outputs the front has not yet taken. So every theorem about the runs of `served sys` holds of
the server (`Front.World.answered_le_arrived`).

`Front.servedEnv` is the kernel's environment but for one thing: the gate takes the system's
answers in any order, as the front takes the shard's outputs. The journal is the shard's
inputs: the requests the gate admitted, in the order it admitted them.
-/

@[expose] public section

namespace Lanes.Http

variable {σ : Signature}

/-! ## The front alone -/

namespace Gate

def Act.answers (id : ReqId) : Gate.Act σ → Bool
  | .respond i _ => i == id
  | _ => false

def Act.passes : Gate.Act σ → Bool
  | .forward _ => true
  | _ => false

end Gate

def GateMsg.arrives (id : ReqId) : GateMsg σ → Bool
  | .arrive i _ => i == id
  | _ => false

/-- The front's state: the gate's waiting list, and the requests whose deadline is armed. -/
structure Front where
  pending : List ReqId := []
  armed : List ReqId := []

namespace Front

/-- What an act of the gate does to the deadlines. -/
def arm (armed : List ReqId) : Gate.Act σ → List ReqId
  | .arm id => if id ∈ armed then armed else armed ++ [id]
  | .disarm id => armed.erase id
  | _ => armed

/-- The front on `msg`: a deadline that passes is no longer armed, and the gate decides. -/
def step (bridge : Bridge σ) (config : GateConfig) (f : Front) (msg : GateMsg σ) :
    Front × List (Gate.Act σ) :=
  let armed := match msg with
    | .expire id => f.armed.erase id
    | _ => f.armed
  let r := Gate.step bridge config Gate.acts f.pending msg
  ({ pending := r.1, armed := r.2.foldl arm armed }, r.2)

/-- The front on messages in order: its state after them, and all it did. -/
def run (bridge : Bridge σ) (config : GateConfig) (f : Front) : List (GateMsg σ) →
    Front × List (Gate.Act σ)
  | [] => (f, [])
  | msg :: msgs =>
    let r := f.step bridge config msg
    let rs := run bridge config r.1 msgs
    (rs.1, r.2 ++ rs.2)

variable {bridge : Bridge σ} {config : GateConfig}

/-- One step answers `id` no more often than it handles an arrival of it, counting the times
`id` waits before and after. -/
theorem step_count (id : ReqId) (pending : List ReqId) (msg : GateMsg σ) :
    (Gate.step bridge config Gate.acts pending msg).1.count id
        + (Gate.step bridge config Gate.acts pending msg).2.countP (·.answers id)
      ≤ pending.count id + (msg.arrives id).toNat := by
  cases msg with
  | arrive i request =>
    simp only [Gate.step]
    split
    · simp
    · split
      · by_cases hid : i = id <;> simp [Gate.acts, Gate.Act.answers, GateMsg.arrives, hid]
      · split
        · by_cases hid : i = id <;> simp [Gate.acts, Gate.Act.answers, GateMsg.arrives, hid]
        · by_cases hid : i = id <;> simp [Gate.acts, Gate.Act.answers, GateMsg.arrives, hid]
  | answer out =>
    simp only [Gate.step]
    split
    · split
      · next i _ _ hi =>
        by_cases hid : i = id
        · subst hid
          have := List.count_pos_iff.mpr hi
          simp [Gate.acts, Gate.Act.answers, GateMsg.arrives, List.count_erase_self]
          omega
        · simp [Gate.acts, Gate.Act.answers, GateMsg.arrives, List.count_erase, hid]
      · simp
    · simp
  | expire i =>
    simp only [Gate.step]
    split
    · next hi =>
      by_cases hid : i = id
      · subst hid
        have := List.count_pos_iff.mpr hi
        simp [Gate.acts, Gate.Act.answers, GateMsg.arrives, List.count_erase_self]
        omega
      · simp [Gate.acts, Gate.Act.answers, GateMsg.arrives, List.count_erase, hid]
    · simp

theorem run_count (id : ReqId) (f : Front) (msgs : List (GateMsg σ)) :
    (f.run bridge config msgs).1.pending.count id
        + (f.run bridge config msgs).2.countP (·.answers id)
      ≤ f.pending.count id + msgs.countP (·.arrives id) := by
  induction msgs generalizing f with
  | nil => simp [run]
  | cons msg msgs ih =>
    have h1 := step_count (bridge := bridge) (config := config) id f.pending msg
    have h2 := ih (f.step bridge config msg).1
    simp only [run, List.countP_append, List.countP_cons] at h2 ⊢
    simp only [step] at h1 h2 ⊢
    cases h : msg.arrives id <;> simp [h] at h1 ⊢ <;> omega

/-- The front answers no request more often than it arrived. With the server's ids, which are
used once each, no request is answered twice. -/
theorem run_answered_le (id : ReqId) (msgs : List (GateMsg σ)) :
    (({} : Front).run bridge config msgs).2.countP (·.answers id)
      ≤ msgs.countP (·.arrives id) := by
  have := run_count (bridge := bridge) (config := config) id {} msgs
  simp at this
  omega

/-- The front's waiting list stays within `maxPending` and free of repeats. -/
theorem run_bounded (msgs : List (GateMsg σ)) {f : Front}
    (h : f.pending.length ≤ config.maxPending ∧ f.pending.Nodup) :
    (f.run bridge config msgs).1.pending.length ≤ config.maxPending
      ∧ (f.run bridge config msgs).1.pending.Nodup := by
  induction msgs generalizing f with
  | nil => exact h
  | cons msg msgs ih => exact ih (Gate.step_bounded bridge config Gate.acts msg h)

/-! Every request that waits is answered. -/

/-- What the front keeps: every waiting request has its deadline armed, and none waits twice. -/
def Inv (f : Front) : Prop :=
  f.pending.Nodup ∧ ∀ id ∈ f.pending, id ∈ f.armed

theorem mem_foldl_arm {armed : List ReqId} {id : ReqId} (h : id ∈ armed) :
    ∀ acts : List (Gate.Act σ), (∀ a ∈ acts, a ≠ .disarm id) → id ∈ acts.foldl arm armed := by
  intro acts
  induction acts generalizing armed with
  | nil => intro _; exact h
  | cons a acts ih =>
    intro hacts
    refine ih ?_ fun b hb => hacts b (List.mem_cons_of_mem _ hb)
    cases a with
    | arm i => simp only [arm]; split <;> simp [h]
    | disarm i =>
      have hne : i ≠ id := fun e => hacts _ List.mem_cons_self (by rw [e])
      exact (List.mem_erase_of_ne (Ne.symm hne)).mpr h
    | _ => exact h

theorem inv_step (msg : GateMsg σ) {f : Front} (h : f.Inv) : (f.step bridge config msg).1.Inv := by
  obtain ⟨hnodup, harmed⟩ := h
  cases msg with
  | arrive i request =>
    simp only [step, Gate.step]
    split
    · exact ⟨hnodup, harmed⟩
    · next hnew =>
      split
      · exact ⟨hnodup, fun id hid => mem_foldl_arm (harmed id hid) _ (by simp [Gate.acts])⟩
      · split
        · exact ⟨hnodup, fun id hid => mem_foldl_arm (harmed id hid) _ (by simp [Gate.acts])⟩
        · refine ⟨List.nodup_cons.mpr ⟨hnew, hnodup⟩, fun id hid => ?_⟩
          simp only [Gate.acts, List.foldl_cons, List.foldl_nil, arm]
          rcases List.mem_cons.mp hid with rfl | hid
          · split <;> simp_all
          · have := harmed id hid
            split <;> simp [this]
  | answer out =>
    simp only [step, Gate.step]
    split
    · split
      · next i _ _ _ =>
        refine ⟨hnodup.erase i, fun id hid => ?_⟩
        have hne : id ≠ i := fun e => by subst e; exact (List.Nodup.not_mem_erase hnodup) hid
        simp only [Gate.acts, List.foldl_cons, List.foldl_nil, arm]
        exact (List.mem_erase_of_ne hne).mpr (harmed id (List.mem_of_mem_erase hid))
      · exact ⟨hnodup, fun id hid => harmed id hid⟩
    · exact ⟨hnodup, fun id hid => harmed id hid⟩
  | expire i =>
    simp only [step, Gate.step]
    split
    · refine ⟨hnodup.erase i, fun id hid => ?_⟩
      have hne : id ≠ i := fun e => by subst e; exact (List.Nodup.not_mem_erase hnodup) hid
      simp only [Gate.acts, List.foldl_cons, List.foldl_nil, arm]
      exact (List.mem_erase_of_ne hne).mpr (harmed id (List.mem_of_mem_erase hid))
    · next hi =>
      refine ⟨hnodup, fun id hid => ?_⟩
      have hne : id ≠ i := fun e => by subst e; exact hi hid
      exact (List.mem_erase_of_ne hne).mpr (harmed id hid)

/-- A request waiting stays waiting through a step that does not answer it. -/
theorem stays (msg : GateMsg σ) {f : Front} {id : ReqId} (hid : id ∈ f.pending)
    (hno : ∀ r, Gate.Act.respond id r ∉ (f.step bridge config msg).2) :
    id ∈ (f.step bridge config msg).1.pending := by
  cases msg with
  | arrive i request =>
    simp only [step, Gate.step] at hno ⊢
    split
    · exact hid
    · split
      · exact hid
      · split
        · exact hid
        · exact List.mem_cons_of_mem _ hid
  | answer out =>
    simp only [step, Gate.step] at hno ⊢
    split
    · next i r heq =>
      rw [heq] at hno
      split
      · next hi =>
        simp only [hi, ↓reduceIte] at hno
        have hne : id ≠ i := fun e => by subst e; exact hno r (by simp [Gate.acts])
        exact (List.mem_erase_of_ne hne).mpr hid
      · exact hid
    · exact hid
  | expire i =>
    simp only [step, Gate.step] at hno ⊢
    split
    · next hi =>
      simp only [hi, ↓reduceIte] at hno
      have hne : id ≠ i := fun e => by subst e; exact hno timedOut (by simp [Gate.acts])
      exact (List.mem_erase_of_ne hne).mpr hid
    · exact hid

/-- A deadline passing for a request that waits answers it `504`. -/
theorem expire_answers {f : Front} {id : ReqId} (hid : id ∈ f.pending) :
    Gate.Act.respond id timedOut ∈ (f.step bridge config (.expire id)).2 := by
  simp [step, Gate.step, hid, Gate.acts]

/-- Every request that waits in the front is answered: in an endless sequence of messages from
a state where the front keeps `Inv`, if every deadline that stays armed is eventually passed to
the front, a later step answers the request. The server's ticker is trusted to pass every
deadline on once it is due. -/
theorem pending_answered (msgs : Nat → GateMsg σ) (fs : Nat → Front)
    (hstep : ∀ n, fs (n + 1) = ((fs n).step bridge config (msgs n)).1) (hinit : (fs 0).Inv)
    (hfair : ∀ n id, (∀ m, n ≤ m → id ∈ (fs m).armed) → ∃ m, n ≤ m ∧ msgs m = .expire id)
    {n : Nat} {id : ReqId} (hid : id ∈ (fs n).pending) :
    ∃ m, n ≤ m ∧ ∃ r, Gate.Act.respond id r ∈ ((fs m).step bridge config (msgs m)).2 := by
  have hinv : ∀ m, (fs m).Inv := by
    intro m
    induction m with
    | zero => exact hinit
    | succ m ih => rw [hstep]; exact inv_step _ ih
  apply Classical.byContradiction
  intro hnot
  have hno : ∀ m, n ≤ m → ∀ r, Gate.Act.respond id r ∉ ((fs m).step bridge config (msgs m)).2 :=
    fun m hm r hr => hnot ⟨m, hm, r, hr⟩
  have hwait : ∀ m, n ≤ m → id ∈ (fs m).pending := by
    intro m hm
    induction m with
    | zero => rwa [Nat.le_zero.mp hm] at hid
    | succ m ih =>
      rcases Nat.lt_or_ge m n with hlt | hge
      · rwa [show n = m + 1 by omega] at hid
      · rw [hstep]; exact stays _ (ih hge) (hno m hge)
  obtain ⟨m, hm, hexp⟩ := hfair n id fun m hm => (hinv m).2 id (hwait m hm)
  exact hno m hm timedOut (hexp ▸ expire_answers (hwait m hm))

end Front

end Lanes.Http
