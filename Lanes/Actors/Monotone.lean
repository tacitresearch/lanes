/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Lift
public import Lanes.Actors.Step

/-!
# Invariants that survive every fault

Most safety properties of a fault-tolerant protocol have one shape: something holds of every
actor state, of every message in flight and of every armed timer. Such a property cannot be
broken by losing a message, delivering one twice, reordering, or a crash, because each of those
only removes messages and timers or replays a step.

`System.Inductive.of_monotone` turns that into a proof rule. Instead of the eight events of the
semantics under an arbitrary environment model, the proof has five cases: the blank state, an
input, an actor's `step`, an actor's `recover`, and that the property still holds when
messages, timers and outputs are removed. The result holds under every `EnvModel`.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature} {sys : System σ}

namespace Effect

variable {i : σ.Id}

def sends (i : σ.Id) (effs : List (Effect σ i)) : List (Envelope σ) :=
  effs.filterMap fun
    | .send to msg => some ⟨some i, to, msg⟩
    | _ => none

def armed (effs : List (Effect σ i)) : List (σ.Msg i) :=
  effs.filterMap fun
    | .after _ msg => some msg
    | _ => none

def emits (effs : List (Effect σ i)) : List σ.Out :=
  effs.filterMap fun
    | .emit out => some out
    | _ => none

theorem mem_sends {effs : List (Effect σ i)} {e : Envelope σ} :
    e ∈ sends i effs ↔ e.src = some i ∧ .send e.dst e.msg ∈ effs := by
  obtain ⟨src, dst, msg⟩ := e
  induction effs with
  | nil => simp [sends]
  | cons eff effs ih =>
    simp only [sends, List.filterMap_cons, List.mem_cons] at ih ⊢
    cases eff <;> simp only [List.mem_cons, ih, reduceCtorEq, false_or]
    simp only [Envelope.mk.injEq, send.injEq]
    exact ⟨fun h => h.elim (fun h => ⟨h.1, .inl h.2⟩) fun h => ⟨h.1, .inr h.2⟩,
      fun h => h.2.elim (fun h' => .inl ⟨h.1, h'⟩) fun h' => .inr ⟨h.1, h'⟩⟩

theorem mem_armed {effs : List (Effect σ i)} {msg : σ.Msg i} :
    msg ∈ armed effs ↔ ∃ delay, .after delay msg ∈ effs := by
  induction effs with
  | nil => simp [armed]
  | cons eff effs ih =>
    simp only [armed, List.filterMap_cons, List.mem_cons] at ih ⊢
    cases eff <;> simp only [List.mem_cons, ih, reduceCtorEq, false_or]
    simp only [after.injEq, exists_or, exists_eq_left]

theorem emits_map_emit (outs : List σ.Out) : emits (outs.map (emit (self := i))) = outs := by
  induction outs with
  | nil => rfl
  | cons out outs ih => simpa [emits] using ih

theorem sends_map_emit (outs : List σ.Out) : sends i (outs.map emit) = [] := by
  induction outs with
  | nil => rfl
  | cons out outs ih => simp [sends]

theorem armed_map_emit (outs : List σ.Out) : armed (outs.map (emit (self := i))) = [] := by
  induction outs with
  | nil => rfl
  | cons out outs ih => simp [armed]

end Effect

namespace SysState

/-- `c` after actor `i` moves to `r.1` with effects `r.2`, with nothing removed: every message
stays in flight and every timer stays armed. -/
def grow (c : SysState sys) (i : σ.Id) (r : sys.State i × List (Effect σ i)) : SysState sys :=
  { c with
    state := update c.state i r.1
    net := c.net ++ Effect.sends i r.2
    timers := update c.timers i (c.timers i ++ Effect.armed r.2)
    outbox := c.outbox ++ Effect.emits r.2 }

/-- The same actor states, with nothing in flight, armed or waiting to go out that `c` lacks. -/
structure Below (c' c : SysState sys) : Prop where
  state : c'.state = c.state
  net : ∀ e ∈ c'.net, e ∈ c.net
  timers : ∀ i msg, msg ∈ c'.timers i → msg ∈ c.timers i
  outbox : ∀ out ∈ c'.outbox, out ∈ c.outbox

@[simp] theorem grow_state_self (c : SysState sys) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) : (c.grow i r).state i = r.1 := by
  simp [grow]

@[simp] theorem grow_state_of_ne (c : SysState sys) {i j : σ.Id}
    (r : sys.State i × List (Effect σ i)) (h : j ≠ i) : (c.grow i r).state j = c.state j := by
  simp [grow, h]

theorem mem_grow_net {c : SysState sys} {i : σ.Id} {r : sys.State i × List (Effect σ i)}
    {e : Envelope σ} :
    e ∈ (c.grow i r).net ↔ e ∈ c.net ∨ (e.src = some i ∧ .send e.dst e.msg ∈ r.2) := by
  simp [grow, Effect.mem_sends]

theorem mem_grow_timers {c : SysState sys} {i j : σ.Id} {r : sys.State i × List (Effect σ i)}
    {msg : σ.Msg j} :
    msg ∈ (c.grow i r).timers j ↔
      msg ∈ c.timers j ∨ ∃ h : j = i, ∃ delay, .after delay (h ▸ msg) ∈ r.2 := by
  by_cases hj : j = i
  · subst hj; simp [grow, Effect.mem_armed]
  · simp [grow, hj]

theorem Below.refl (c : SysState sys) : c.Below c :=
  ⟨rfl, fun _ h => h, fun _ _ h => h, fun _ h => h⟩

theorem mem_performAll_net {c : SysState sys} {i : σ.Id} {effs : List (Effect σ i)}
    {e : Envelope σ} (h : e ∈ (c.performAll i effs).net) : e ∈ c.net ∨ e ∈ Effect.sends i effs := by
  induction effs generalizing c with
  | nil => exact .inl h
  | cons eff effs ih =>
    rcases ih h with h | h
    · cases eff <;> simp only [perform, List.mem_append, List.mem_singleton] at h <;>
        simp only [Effect.sends, List.filterMap_cons, List.mem_cons] <;>
        first | exact .inl h | (rcases h with h | h <;> simp [h])
    · exact .inr (by
        simp only [Effect.sends, List.filterMap_cons] at h ⊢
        split <;> simp_all)

theorem mem_performAll_outbox {c : SysState sys} {i : σ.Id} {effs : List (Effect σ i)}
    {out : σ.Out} (h : out ∈ (c.performAll i effs).outbox) :
    out ∈ c.outbox ∨ out ∈ Effect.emits effs := by
  induction effs generalizing c with
  | nil => exact .inl h
  | cons eff effs ih =>
    rcases ih h with h | h
    · cases eff <;> simp only [perform, List.mem_append, List.mem_singleton] at h <;>
        simp only [Effect.emits, List.filterMap_cons, List.mem_cons] <;>
        first | exact .inl h | (rcases h with h | h <;> simp [h])
    · exact .inr (by
        simp only [Effect.emits, List.filterMap_cons] at h ⊢
        split <;> simp_all)

theorem performAll_timers_of_ne {c : SysState sys} {i j : σ.Id} {effs : List (Effect σ i)}
    (hne : j ≠ i) : (c.performAll i effs).timers j = c.timers j := by
  induction effs generalizing c with
  | nil => rfl
  | cons eff effs ih =>
    rw [performAll_cons, ih]
    cases eff <;> simp [perform, hne]

theorem mem_performAll_timers {c : SysState sys} {i : σ.Id} {effs : List (Effect σ i)}
    {msg : σ.Msg i} (h : msg ∈ (c.performAll i effs).timers i) :
    msg ∈ c.timers i ∨ msg ∈ Effect.armed effs := by
  induction effs generalizing c with
  | nil => exact .inl h
  | cons eff effs ih =>
    rcases ih h with h | h
    · cases eff with
      | after delay m =>
        simp only [perform, update_self] at h
        split at h
        · exact .inl h
        · rcases List.mem_append.mp h with h | h
          · exact .inl h
          · exact .inr (by simp_all [Effect.armed])
      | cancel m =>
        simp only [perform, update_self] at h
        exact .inl (List.mem_of_mem_erase h)
      | _ => exact .inl h
    · exact .inr (by
        simp only [Effect.armed, List.filterMap_cons] at h ⊢
        split <;> simp_all)

/-- Whatever was removed before an actor moved, and whether or not it stopped, the result has
nothing that `grow` lacks. -/
theorem Below.settle {c₀ c : SysState sys} (h : c₀.Below c) (env : EnvModel σ) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) : (c₀.settle env i r).Below (c.grow i r) := by
  have hnet : ∀ e ∈ (({ c₀ with state := update c₀.state i r.1 }).performAll i r.2).net,
      e ∈ (c.grow i r).net := fun e he =>
    List.mem_append.mpr ((mem_performAll_net he).imp_left (h.net e))
  have htimers : ∀ j msg,
      msg ∈ (({ c₀ with state := update c₀.state i r.1 }).performAll i r.2).timers j →
        msg ∈ (c.grow i r).timers j := by
    intro j msg hmsg
    by_cases hj : j = i
    · subst hj
      simp only [grow, update_self]
      exact List.mem_append.mpr ((mem_performAll_timers hmsg).imp_left (h.timers j msg))
    · rw [performAll_timers_of_ne hj] at hmsg
      simpa [grow, hj] using h.timers j msg hmsg
  have hout : ∀ out ∈ (({ c₀ with state := update c₀.state i r.1 }).performAll i r.2).outbox,
      out ∈ (c.grow i r).outbox := fun out ho =>
    List.mem_append.mpr ((mem_performAll_outbox ho).imp_left (h.outbox out))
  refine ⟨by simp [grow, h.state], ?_, ?_, ?_⟩
  · intro e he
    unfold SysState.settle at he
    split at he
    · exact hnet e (List.mem_filter.mp he).1
    · exact hnet e he
  · intro j msg hmsg
    unfold SysState.settle at hmsg
    split at hmsg
    · by_cases hj : j = i
      · subst hj; simp [down] at hmsg
      · exact htimers j msg (by simpa [down, hj] using hmsg)
    · exact htimers j msg hmsg
  · intro out ho
    unfold SysState.settle at ho
    split at ho
    · exact hout out ho
    · exact hout out ho

theorem Below.handle {c₀ c : SysState sys} (h : c₀.Below c) (env : EnvModel σ) (i : σ.Id)
    (msg : σ.Msg i) :
    (c₀.handle env i msg).Below (c.grow i ((sys.actor i).step (c.state i) msg)) := by
  rw [← congrFun h.state i]
  exact Below.settle h env i _

theorem Below.startActor (c : SysState sys) (env : EnvModel σ) (i : σ.Id) :
    (c.startActor env i).Below (c.grow i ((sys.actor i).recover (c.state i))) :=
  Below.settle (c₀ := { c with up := update c.up i true }) (c := c)
    ⟨rfl, fun _ h => h, fun _ _ h => h, fun _ h => h⟩ env i _

end SysState

namespace System

open SysState

/--
The proof rule for a property that removing messages, timers and outputs cannot break
(`below`). It is enough that it holds of the blank state and is kept by an input, by any actor
handling a message that is in flight to it or armed as its timer, and by any actor recovering,
all without anything being removed. It then holds under every environment model.
-/
theorem Inductive.of_monotone {P : SysState sys → Prop} (env : EnvModel σ)
    (blank : P (SysState.blank sys))
    (below : ∀ c c', P c → c'.Below c → P c')
    (input : ∀ c x, P c →
      P { c with net := c.net ++ [⟨none, (sys.accept x).1, (sys.accept x).2⟩] })
    (step : ∀ c i msg, P c → ((∃ src, ⟨src, i, msg⟩ ∈ c.net) ∨ msg ∈ c.timers i) →
      P (c.grow i ((sys.actor i).step (c.state i) msg)))
    (recover : ∀ c i, P c → P (c.grow i ((sys.actor i).recover (c.state i)))) :
    sys.Inductive env P where
  init := by
    have hstart : ∀ c i, P c → P (c.startActor env i) := fun c i hc =>
      below _ _ (recover c i hc) (Below.startActor c env i)
    have hfold : ∀ (ids : List σ.Id) c, P c → P (ids.foldl (fun c i => c.startActor env i) c) := by
      intro ids
      induction ids with
      | nil => exact fun _ h => h
      | cons i ids ih => exact fun c hc => ih _ (hstart c i hc)
    exact hfold _ _ blank
  step c ev c' hc hstep := by
    cases ev with
    | input x => obtain rfl := step_input.mp hstep; exact input c x hc
    | deliver e =>
      obtain ⟨_, hdeliverable, rfl⟩ := step_deliver.mp hstep
      have hbelow : SysState.Below { c with net := c.net.erase e } c :=
        ⟨rfl, fun _ h => List.mem_of_mem_erase h, fun _ _ h => h, fun _ h => h⟩
      exact below _ _ (step c e.dst e.msg hc (.inl ⟨e.src, mem_of_deliverable hdeliverable⟩))
        (Below.handle hbelow ..)
    | duplicate e =>
      obtain ⟨_, _, hdeliverable, rfl⟩ := step_duplicate.mp hstep
      exact below _ _ (step c e.dst e.msg hc (.inl ⟨e.src, mem_of_deliverable hdeliverable⟩))
        (Below.handle (Below.refl c) ..)
    | drop e =>
      obtain ⟨_, _, rfl⟩ := step_drop.mp hstep
      exact below _ _ hc ⟨rfl, fun _ h => List.mem_of_mem_erase h, fun _ _ h => h, fun _ h => h⟩
    | timeout i msg =>
      obtain ⟨_, hmem, rfl⟩ := step_timeout.mp hstep
      have hbelow : SysState.Below
          { c with timers := update c.timers i ((c.timers i).erase msg) } c := by
        refine ⟨rfl, fun _ h => h, ?_, fun _ h => h⟩
        intro j m hm
        by_cases hj : j = i
        · subst hj
          simp only [update_self] at hm
          exact List.mem_of_mem_erase hm
        · simpa [hj] using hm
      exact below _ _ (step c i msg hc (.inr hmem)) (Below.handle hbelow ..)
    | output out =>
      obtain ⟨_, rfl⟩ := step_output.mp hstep
      exact below _ _ hc ⟨rfl, fun _ h => h, fun _ _ h => h, fun _ h => List.mem_of_mem_erase h⟩
    | crash i =>
      obtain ⟨_, _, rfl⟩ := step_crash.mp hstep
      refine below _ _ hc ⟨rfl, fun _ h => (List.mem_filter.mp h).1, ?_, fun _ h => h⟩
      intro j m hm
      by_cases hj : j = i
      · subst hj; simp [down] at hm
      · simpa [down, hj] using hm
    | start i =>
      obtain ⟨_, _, rfl⟩ := step_start.mp hstep
      exact below _ _ (recover c i hc) (Below.startActor c env i)

/-- The five cases of `Inductive.of_monotone` as one value, so that proofs of them can be
combined (`Monotone.and`) before an environment model is chosen. -/
structure Monotone (sys : System σ) (P : SysState sys → Prop) : Prop where
  blank : P (SysState.blank sys)
  below : ∀ c c', P c → c'.Below c → P c'
  input : ∀ c x, P c →
    P { c with net := c.net ++ [⟨none, (sys.accept x).1, (sys.accept x).2⟩] }
  step : ∀ c i msg, P c → ((∃ src, ⟨src, i, msg⟩ ∈ c.net) ∨ msg ∈ c.timers i) →
    P (c.grow i ((sys.actor i).step (c.state i) msg))
  recover : ∀ c i, P c → P (c.grow i ((sys.actor i).recover (c.state i)))

namespace Monotone

variable {P Q : SysState sys → Prop}

theorem to_inductive (h : sys.Monotone P) (env : EnvModel σ) : sys.Inductive env P :=
  .of_monotone env h.blank h.below h.input h.step h.recover

theorem invariant (h : sys.Monotone P) (env : EnvModel σ) : sys.Invariant env P :=
  (h.to_inductive env).invariant

/-- Add `Q` to a property already shown. Each case of `Q` may use `P` of the state it starts
from and of the state it ends in. -/
theorem and (hP : sys.Monotone P) (blank : Q (SysState.blank sys))
    (below : ∀ c c', P c → Q c → c'.Below c → Q c')
    (input : ∀ c x, P c → Q c →
      Q { c with net := c.net ++ [⟨none, (sys.accept x).1, (sys.accept x).2⟩] })
    (step : ∀ c i msg, P c → P (c.grow i ((sys.actor i).step (c.state i) msg)) → Q c →
      ((∃ src, ⟨src, i, msg⟩ ∈ c.net) ∨ msg ∈ c.timers i) →
        Q (c.grow i ((sys.actor i).step (c.state i) msg)))
    (recover : ∀ c i, P c → P (c.grow i ((sys.actor i).recover (c.state i))) → Q c →
      Q (c.grow i ((sys.actor i).recover (c.state i)))) :
    sys.Monotone fun c => P c ∧ Q c where
  blank := ⟨hP.blank, blank⟩
  below c c' h hbelow := ⟨hP.below c c' h.1 hbelow, below c c' h.1 h.2 hbelow⟩
  input c x h := ⟨hP.input c x h.1, input c x h.1 h.2⟩
  step c i msg h hpending :=
    ⟨hP.step c i msg h.1 hpending, step c i msg h.1 (hP.step c i msg h.1 hpending) h.2 hpending⟩
  recover c i h := ⟨hP.recover c i h.1, recover c i h.1 (hP.recover c i h.1) h.2⟩

/-- Timers carry only what actors arm: a message no actor arms never arrives as a timer. -/
theorem timers (sys : System σ) {T : (i : σ.Id) → σ.Msg i → Prop}
    (step : ∀ i s msg delay m, Effect.after delay m ∈ ((sys.actor i).step s msg).2 → T i m)
    (recover : ∀ i s delay m, Effect.after delay m ∈ ((sys.actor i).recover s).2 → T i m) :
    sys.Monotone fun c => ∀ i m, m ∈ c.timers i → T i m where
  blank := fun _ _ h => nomatch h
  below _ _ h hbelow := fun i m hm => h i m (hbelow.timers i m hm)
  input _ _ h := h
  step c i msg h _ := fun j m hm => by
    rcases SysState.mem_grow_timers.mp hm with hold | ⟨rfl, delay, hnew⟩
    · exact h j m hold
    · exact step j _ msg delay m hnew
  recover c i h := fun j m hm => by
    rcases SysState.mem_grow_timers.mp hm with hold | ⟨rfl, delay, hnew⟩
    · exact h j m hold
    · exact recover j _ delay m hnew

end Monotone

end System

end Lanes
