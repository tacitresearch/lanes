/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Proof.Lift
public import Lanes.Core.Run

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

A proof is built in layers (`Monotone.and`), each using those under it. A layer that reads only
the actors' states and the messages in flight, as most do, is added with `Monotone.and_net` or
`Monotone.and_state`, which leave only the steps to prove.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature} {sys : System σ}

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
all without anything being removed. It then holds under every environment model, restarts
included.
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
  init := init_induction blank fun c i hc =>
    below _ _ (recover c i hc) (Below.startActor c env i)
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
    | restart =>
      obtain ⟨_, rfl⟩ := step_restart.mp hstep
      exact init_induction blank fun c i hc => below _ _ (recover c i hc) (Below.startActor c env i)

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

/-- `Monotone.and` for a layer that reads the actors' states and asks something of each message
in flight, which every input meets. `net` says so: `Q` survives any change of what is in flight
that brings no message but inputs, and any change of timers, outputs and which actors are up.
Nothing then has to be shown of removing messages or of an input. -/
theorem and_net (hP : sys.Monotone P) (blank : Q (SysState.blank sys))
    (net : ∀ c up net timers outbox, Q c →
      (∀ e ∈ net, e ∈ c.net ∨ ∃ x, e = ⟨none, (sys.accept x).1, (sys.accept x).2⟩) →
        Q { c with up, net, timers, outbox })
    (step : ∀ c i msg, P c → P (c.grow i ((sys.actor i).step (c.state i) msg)) → Q c →
      ((∃ src, ⟨src, i, msg⟩ ∈ c.net) ∨ msg ∈ c.timers i) →
        Q (c.grow i ((sys.actor i).step (c.state i) msg)))
    (recover : ∀ c i, P c → P (c.grow i ((sys.actor i).recover (c.state i))) → Q c →
      Q (c.grow i ((sys.actor i).recover (c.state i)))) :
    sys.Monotone fun c => P c ∧ Q c :=
  hP.and blank
    (fun c c' _ hq hbelow =>
      (congrArg Q (SysState.ext' hbelow.state rfl rfl rfl rfl : c' = { c with
        up := c'.up, net := c'.net, timers := c'.timers, outbox := c'.outbox })).mpr
        (net c _ _ _ _ hq fun e he => .inl (hbelow.net e he)))
    (fun c x _ hq => net c c.up _ c.timers c.outbox hq fun _ he =>
      (List.mem_append.mp he).imp_right fun he => ⟨x, List.mem_singleton.mp he⟩)
    step recover

/-- `Monotone.and` for a layer that reads only the actors' states, which is what `state` says. -/
theorem and_state (hP : sys.Monotone P) (blank : Q (SysState.blank sys))
    (state : ∀ c up net timers outbox, Q c → Q { c with up, net, timers, outbox })
    (step : ∀ c i msg, P c → P (c.grow i ((sys.actor i).step (c.state i) msg)) → Q c →
      ((∃ src, ⟨src, i, msg⟩ ∈ c.net) ∨ msg ∈ c.timers i) →
        Q (c.grow i ((sys.actor i).step (c.state i) msg)))
    (recover : ∀ c i, P c → P (c.grow i ((sys.actor i).recover (c.state i))) → Q c →
      Q (c.grow i ((sys.actor i).recover (c.state i)))) :
    sys.Monotone fun c => P c ∧ Q c :=
  hP.and_net blank (fun c up net timers outbox hq _ => state c up net timers outbox hq) step
    recover

/-- The same property under another name. Layers added with `and` nest, and a proof that uses
the third of four reads `h.1.1.2`; give the stack a structure with a field for each layer and
it reads `h.votes`. -/
theorem of_iff (hP : sys.Monotone P) (h : ∀ c, Q c ↔ P c) : sys.Monotone Q where
  blank := (h _).mpr hP.blank
  below c c' hc hbelow := (h _).mpr (hP.below c c' ((h _).mp hc) hbelow)
  input c x hc := (h _).mpr (hP.input c x ((h _).mp hc))
  step c i msg hc hpending := (h _).mpr (hP.step c i msg ((h _).mp hc) hpending)
  recover c i hc := (h _).mpr (hP.recover c i ((h _).mp hc))

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

namespace SysState

variable {T : (i : σ.Id) → σ.Msg i → Prop} {c : SysState sys} {i : σ.Id}

/-- The message an actor is handling, `none` for a recovery, is in flight to it or is a timer
of the kind `T`. This is what a `step` case knows once `Monotone.timers` has shown that every
armed timer is of that kind, in a form that a recovery meets too. -/
def Pending (T : (i : σ.Id) → σ.Msg i → Prop) (c : SysState sys) (i : σ.Id)
    (msg : Option (σ.Msg i)) : Prop :=
  ∀ m, msg = some m → (∃ src, ⟨src, i, m⟩ ∈ c.net) ∨ T i m

theorem pending_none : c.Pending T i none :=
  nofun

theorem Pending.of_timers (ht : ∀ i m, m ∈ c.timers i → T i m) {m : σ.Msg i}
    (h : (∃ src, ⟨src, i, m⟩ ∈ c.net) ∨ m ∈ c.timers i) : c.Pending T i (some m) := by
  intro m' hm
  obtain rfl := Option.some.inj hm
  exact h.imp id (ht i _)

end SysState

end Lanes
