/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Step
public import Lanes.Proof.List

/-!
Two states are the same to every actor when they differ only in the order of messages that no
actor can tell apart: across links always, and within a link when the link is unordered. The
net is one list, so a state records that order although nothing observes it.
`SysState.Equiv` is the relation that forgets it, and `Equiv.step` proves it is a bisimulation:
equivalent states enable the same events and lead to equivalent states.

The checker merges states by it. So do theorems about systems put together: a join seen from
one side, or shards seen as one system, is a state of that system up to this relation, not up
to equality.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

def onLink (src : Option σ.Id) (dst : σ.Id) (e : Envelope σ) : Bool :=
  decide (e.src = src) && decide (e.dst = dst)

/-- The same traffic: on every link the same messages, and in the same order where the link is
ordered. -/
structure NetEquiv (env : EnvModel σ) (a b : List (Envelope σ)) : Prop where
  perm : ∀ src dst, (a.filter (onLink src dst)).Perm (b.filter (onLink src dst))
  ordered : ∀ src dst, (env.link src dst).ordered = true →
    a.filter (onLink src dst) = b.filter (onLink src dst)

namespace NetEquiv

variable {env : EnvModel σ} {a b : List (Envelope σ)}

theorem refl (env : EnvModel σ) (a : List (Envelope σ)) : NetEquiv env a a :=
  ⟨fun _ _ => .refl _, fun _ _ _ => rfl⟩

theorem symm (h : NetEquiv env a b) : NetEquiv env b a :=
  ⟨fun s d => (h.perm s d).symm, fun s d ho => (h.ordered s d ho).symm⟩

theorem trans {c : List (Envelope σ)} (h₁ : NetEquiv env a b) (h₂ : NetEquiv env b c) :
    NetEquiv env a c :=
  ⟨fun s d => (h₁.perm s d).trans (h₂.perm s d),
    fun s d ho => (h₁.ordered s d ho).trans (h₂.ordered s d ho)⟩

theorem mem_iff (h : NetEquiv env a b) (e : Envelope σ) : e ∈ a ↔ e ∈ b := by
  have hself : onLink e.src e.dst e = true := by simp [onLink]
  have ha : e ∈ a ↔ e ∈ a.filter (onLink e.src e.dst) := by simp [hself]
  have hb : e ∈ b ↔ e ∈ b.filter (onLink e.src e.dst) := by simp [hself]
  rw [ha, hb]
  exact (h.perm e.src e.dst).mem_iff

theorem append (h : NetEquiv env a b) (l : List (Envelope σ)) : NetEquiv env (a ++ l) (b ++ l) :=
  ⟨fun s d => by simpa using (h.perm s d).append_right _,
    fun s d ho => by simp [h.ordered s d ho]⟩

theorem erase (h : NetEquiv env a b) (e : Envelope σ) : NetEquiv env (a.erase e) (b.erase e) := by
  refine ⟨fun s d => ?_, fun s d ho => ?_⟩
  · by_cases hp : onLink s d e = true
    · rw [filter_erase_of_pos _ _ hp, filter_erase_of_pos _ _ hp]
      exact (h.perm s d).erase e
    · have hp' : onLink s d e = false := by simpa using hp
      rw [filter_erase_of_neg _ _ hp', filter_erase_of_neg _ _ hp']
      exact h.perm s d
  · by_cases hp : onLink s d e = true
    · rw [filter_erase_of_pos _ _ hp, filter_erase_of_pos _ _ hp, h.ordered s d ho]
    · have hp' : onLink s d e = false := by simpa using hp
      rw [filter_erase_of_neg _ _ hp', filter_erase_of_neg _ _ hp']
      exact h.ordered s d ho

theorem filter (h : NetEquiv env a b) (q : Envelope σ → Bool) :
    NetEquiv env (a.filter q) (b.filter q) := by
  refine ⟨fun s d => ?_, fun s d ho => ?_⟩
  · rw [List.filter_filter, List.filter_filter]
    have := (h.perm s d).filter q
    simpa [List.filter_filter, Bool.and_comm] using this
  · rw [List.filter_filter, List.filter_filter]
    have := congrArg (List.filter q) (h.ordered s d ho)
    simpa [List.filter_filter, Bool.and_comm] using this

theorem toPerm (h : NetEquiv env a b) : a.Perm b := by
  rw [List.perm_iff_count]
  intro e
  have hself : onLink e.src e.dst e = true := by simp [onLink]
  rw [← List.count_filter (l := a) hself, ← List.count_filter (l := b) hself]
  exact (h.perm e.src e.dst).count_eq e

/-- What two senders add may come in either order. -/
theorem append_comm (n a b : List (Envelope σ)) (h : ∀ e ∈ a, ∀ e' ∈ b, e.src ≠ e'.src) :
    NetEquiv env (n ++ a ++ b) (n ++ b ++ a) := by
  refine ⟨fun src dst => ?_, fun src dst _ => ?_⟩
  · simp only [List.filter_append, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
  · by_cases ha : a.filter (onLink src dst) = []
    · simp [List.filter_append, ha]
    · have hb : b.filter (onLink src dst) = [] := by
        rw [List.filter_eq_nil_iff]
        intro e' he' hon'
        obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ ha
        have hon := (List.mem_filter.mp he).2
        simp only [onLink, Bool.and_eq_true, decide_eq_true_eq] at hon hon'
        exact h e (List.mem_filter.mp he).1 e' he' (hon.1.trans hon'.1.symm)
      simp [List.filter_append, hb]

end NetEquiv

variable {sys : System σ}

/-- States the checker may merge: the same actors, timers and outputs, and the same traffic. -/
structure SysState.Equiv (env : EnvModel σ) (a b : SysState sys) : Prop where
  state : a.state = b.state
  up : a.up = b.up
  timers : a.timers = b.timers
  net : NetEquiv env a.net b.net
  outbox : a.outbox.Perm b.outbox

namespace SysState.Equiv

variable {env : EnvModel σ} {a b : SysState sys}

theorem refl (env : EnvModel σ) (a : SysState sys) : Equiv env a a :=
  ⟨rfl, rfl, rfl, .refl env _, .refl _⟩

theorem symm (h : Equiv env a b) : Equiv env b a :=
  ⟨h.state.symm, h.up.symm, h.timers.symm, h.net.symm, h.outbox.symm⟩

theorem trans {c : SysState sys} (h₁ : Equiv env a b) (h₂ : Equiv env b c) : Equiv env a c :=
  ⟨h₁.state.trans h₂.state, h₁.up.trans h₂.up, h₁.timers.trans h₂.timers, h₁.net.trans h₂.net,
    h₁.outbox.trans h₂.outbox⟩

theorem perform (h : Equiv env a b) (i : σ.Id) (eff : Effect σ i) :
    Equiv env (a.perform i eff) (b.perform i eff) := by
  obtain ⟨hs, hu, ht, hn, ho⟩ := h
  cases eff with
  | send to msg => exact ⟨hs, hu, ht, hn.append _, ho⟩
  | emit out => exact ⟨hs, hu, ht, hn, ho.append_right _⟩
  | after delay_ms msg => exact ⟨hs, hu, by simp only [SysState.perform, ht], hn, ho⟩
  | cancel msg => exact ⟨hs, hu, by simp only [SysState.perform, ht], hn, ho⟩
  | stop => exact ⟨hs, hu, ht, hn, ho⟩

theorem performAll (h : Equiv env a b) (i : σ.Id) (effs : List (Effect σ i)) :
    Equiv env (a.performAll i effs) (b.performAll i effs) := by
  induction effs generalizing a b with
  | nil => exact h
  | cons eff effs ih => exact ih (h.perform i eff)

theorem down (h : Equiv env a b) (i : σ.Id) : Equiv env (a.down env i) (b.down env i) :=
  ⟨h.state, by simp only [SysState.down, h.up], by simp only [SysState.down, h.timers],
    h.net.filter _, h.outbox⟩

theorem settle (h : Equiv env a b) (i : σ.Id) (r : sys.State i × List (Effect σ i)) :
    Equiv env (a.settle env i r) (b.settle env i r) := by
  have hset : Equiv env { a with state := update a.state i r.1 }
      { b with state := update b.state i r.1 } :=
    ⟨by simp only [h.state], h.up, h.timers, h.net, h.outbox⟩
  unfold SysState.settle
  by_cases hstop : r.2.any Effect.isStop = true
  · simp only [hstop, ite_true]
    exact (hset.performAll i r.2).down i
  · simp only [hstop, ite_false, Bool.false_eq_true]
    exact hset.performAll i r.2

theorem handle (h : Equiv env a b) (i : σ.Id) (msg : σ.Msg i) :
    Equiv env (a.handle env i msg) (b.handle env i msg) := by
  have hi : b.state i = a.state i := by rw [h.state]
  unfold SysState.handle
  rw [hi]
  exact h.settle i _

theorem startActor (h : Equiv env a b) (i : σ.Id) :
    Equiv env (a.startActor env i) (b.startActor env i) := by
  have hup : Equiv env { a with up := update a.up i true } { b with up := update b.up i true } :=
    ⟨h.state, by simp only [h.up], h.timers, h.net, h.outbox⟩
  have hi : b.state i = a.state i := by rw [h.state]
  unfold SysState.startActor
  rw [hi]
  exact hup.settle i _

theorem deliverable (h : Equiv env a b) (e : Envelope σ) :
    a.deliverable env e = b.deliverable env e := by
  have hlink : e.sameLink = onLink e.src e.dst := by
    funext x
    simp only [Envelope.sameLink, onLink]
    congr 1 <;> exact decide_eq_decide.mpr eq_comm
  unfold SysState.deliverable
  by_cases ho : (env.link e.src e.dst).ordered = true
  · simp only [ho, ite_true, ← List.head?_filter, hlink, h.net.ordered e.src e.dst ho]
  · simp only [ho, ite_false, Bool.false_eq_true]
    exact Bool.eq_iff_iff.mpr (by simpa using h.net.mem_iff e)

theorem hasMail (h : Equiv env a b) (i : σ.Id) : a.hasMail i = b.hasMail i := by
  apply Bool.eq_iff_iff.mpr
  simp only [SysState.hasMail, List.any_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨e, he, hd⟩ => ⟨e, (h.net.mem_iff e).mp he, hd⟩,
    fun ⟨e, he, hd⟩ => ⟨e, (h.net.mem_iff e).mpr he, hd⟩⟩

/--
Equivalent states enable the same events and step to equivalent states. Merging them loses no
behaviour, so exploring one stands for exploring both.
-/
theorem step (h : Equiv env a b) {ev : Event σ} {a' : SysState sys}
    (hstep : a.step env ev = some a') : ∃ b', b.step env ev = some b' ∧ Equiv env a' b' := by
  cases ev with
  | input x =>
    obtain rfl := step_input.mp hstep
    exact ⟨_, step_input.mpr rfl, h.state, h.up, h.timers, h.net.append _, h.outbox⟩
  | deliver e =>
    obtain ⟨hup, hdel, rfl⟩ := step_deliver.mp hstep
    have hmid : Equiv env { a with net := a.net.erase e } { b with net := b.net.erase e } :=
      ⟨h.state, h.up, h.timers, h.net.erase e, h.outbox⟩
    exact ⟨_, step_deliver.mpr ⟨h.up ▸ hup, h.deliverable e ▸ hdel, rfl⟩, hmid.handle e.dst e.msg⟩
  | duplicate e =>
    obtain ⟨hup, hdup, hdel, rfl⟩ := step_duplicate.mp hstep
    exact ⟨_, step_duplicate.mpr ⟨h.up ▸ hup, hdup, h.deliverable e ▸ hdel, rfl⟩,
      h.handle e.dst e.msg⟩
  | drop e =>
    obtain ⟨hlossy, hmem, rfl⟩ := step_drop.mp hstep
    exact ⟨_, step_drop.mpr ⟨hlossy, (h.net.mem_iff e).mp hmem, rfl⟩,
      h.state, h.up, h.timers, h.net.erase e, h.outbox⟩
  | timeout i msg =>
    obtain ⟨hup, hmem, rfl⟩ := step_timeout.mp hstep
    have hmid : Equiv env { a with timers := update a.timers i ((a.timers i).erase msg) }
        { b with timers := update b.timers i ((b.timers i).erase msg) } :=
      ⟨h.state, h.up, by simp only [h.timers], h.net, h.outbox⟩
    exact ⟨_, step_timeout.mpr ⟨h.up ▸ hup, h.timers ▸ hmem, rfl⟩, hmid.handle i msg⟩
  | output out =>
    obtain ⟨hmem, rfl⟩ := step_output.mp hstep
    exact ⟨_, step_output.mpr ⟨h.outbox.mem_iff.mp hmem, rfl⟩,
      h.state, h.up, h.timers, h.net, h.outbox.erase out⟩
  | crash i =>
    obtain ⟨hup, hcrash, rfl⟩ := step_crash.mp hstep
    exact ⟨_, step_crash.mpr ⟨h.up ▸ hup, hcrash, rfl⟩, h.down i⟩
  | start i =>
    obtain ⟨hup, hmail, rfl⟩ := step_start.mp hstep
    exact ⟨_, step_start.mpr ⟨h.up ▸ hup, h.hasMail i ▸ hmail, rfl⟩, h.startActor i⟩

end SysState.Equiv

/-- Reached, up to the order of messages that no actor can tell apart. -/
def System.Near (sys : System σ) (env : EnvModel σ) (c : SysState sys) : Prop :=
  ∃ c', sys.Reachable env c' ∧ SysState.Equiv env c' c

namespace System.Near

variable {env : EnvModel σ} {c c' : SysState sys}

theorem step (ev : Event σ) (h : sys.Near env c) (hstep : c.step env ev = some c') :
    sys.Near env c' := by
  obtain ⟨x, hx, hxc⟩ := h
  obtain ⟨x', hx', hcx'⟩ := hxc.symm.step hstep
  exact ⟨x', hx.step ev hx', hcx'.symm⟩

theorem equiv (h : sys.Near env c) (hc : SysState.Equiv env c c') : sys.Near env c' :=
  h.elim fun x hx => ⟨x, hx.1, hx.2.trans hc⟩

end System.Near

end Lanes
