/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Semantics.Sent
public import Lanes.Semantics.Service
public import Lanes.Semantics.Simulation

/-!
# A service behind actors: the standard simulation

A system that implements a service holds, at every moment, inputs that have arrived and not yet
taken effect, and outputs produced and not yet handed over: on messages in flight, in actors'
states, or only in what has happened, which the proof names with a witness. An `Account` says
where, and how the actors' states read as the service's value. `Account.Sim` is then the
relation every such proof uses: the spec's value is one the account allows, and the spec still
has pending at least the inputs the system holds and owes at least the outputs it has waiting
or holds. Bounds, not equalities, so a message lost leaves its input pending in the spec for
ever, which the spec allows (D34).

What is left to an application is, for each message an actor handles, `Account.Moves`: which
inputs take effect, and that what the state after holds and owes is no more than what the state
before held and owed, less those inputs and plus their outputs. `Moves.forward` and
`Moves.take` are the two shapes such a step usually has, as equations about its sends and
outputs.

## Main definitions

- `Service.run`: inputs taking effect one after another.
- `Account`: where a system holds its service's inputs and outputs, and how it reads as its value.
- `Account.Sim`: the standard simulation.
- `Account.Moves`: what a step of an actor must do to keep it.

## Main statements

- `Service.takes`: pending inputs taking effect in order are internal steps of the spec.
- `Account.implements`: a system implements its service when every step of an actor `Moves`.
- `Account.implements_timed`: the same with deadlines, a step that passes one `Fires` it.
-/

@[expose] public section

namespace Lanes

namespace Service

variable {In Out S T : Type}

/-- The inputs `xs` taking effect in order from `v`: the value after, and the outputs. -/
def run (svc : Service In Out S T) (v : S) : List In → S × List Out
  | [] => (v, [])
  | x :: xs =>
    ((svc.run (svc.step v x).1 xs).1, (svc.step v x).2 ++ (svc.run (svc.step v x).1 xs).2)

/-- No input, no change. -/
@[simp] theorem run_nil (svc : Service In Out S T) (v : S) : svc.run v [] = (v, []) := rfl

/-- One input is one step. -/
@[simp] theorem run_singleton (svc : Service In Out S T) (v : S) (x : In) :
    svc.run v [x] = svc.step v x := by
  simp [run]

/-- Inputs taking effect one list after another. -/
theorem run_append (svc : Service In Out S T) (v : S) (xs ys : List In) :
    svc.run v (xs ++ ys) =
      ((svc.run (svc.run v xs).1 ys).1, (svc.run v xs).2 ++ (svc.run (svc.run v xs).1 ys).2) := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih => simp [run, ih]

variable [DecidableEq In] [DecidableEq Out]

/-- Pending inputs take effect one after another, in as many internal steps of the spec as
there are of them. -/
theorem takes (svc : Service In Out S T) (xs : List In) :
    ∀ (t : Abs In Out S) (rest : Bag In), rest + ↑xs ≤ t.pending →
      ∃ t', svc.spec.lts.τSTr t t' ∧ t'.value = (svc.run t.value xs).1 ∧
        t'.outbox = t.outbox + ↑(svc.run t.value xs).2 ∧ rest ≤ t'.pending := by
  induction xs with
  | nil => exact fun t rest h => ⟨t, .refl, rfl, by simp, by simpa using h⟩
  | cons x xs ih =>
    intro t rest h
    rw [← Bag.cons_coe, Bag.add_cons] at h
    obtain ⟨t', ht', hvalue, houtbox, hrest⟩ := ih
      ⟨(svc.step t.value x).1, t.pending.erase x, t.outbox + (svc.step t.value x).2⟩ rest
      (by simpa using Bag.erase_le_erase x h)
    refine ⟨t', .head ⟨x, Bag.mem_of_le h (Bag.mem_cons_self _ _), rfl⟩ ht', hvalue, ?_,
      hrest⟩
    rw [houtbox, run, ← Bag.coe_add, Bag.add_assoc]

end Service

variable {σ : Signature} {sys : System σ} {S W : Type}

/--
Where a system holds what its service is doing: the input a message in flight carries that is
still to take effect (`pend`), the output one carries that is still to be handed over (`owe`),
and those that the actors' states or a witness `W` hold (`held`, `owing`). `value` says which
values of the service a state of the actors and the messages in flight, with the witness, may
be read as.
-/
structure Account (sys : System σ) (S W : Type) where
  /-- The input a message in flight carries that is still to take effect. -/
  pend : Envelope σ → Option σ.In := fun _ => none
  /-- The output a message in flight carries that is still to be handed over. -/
  owe : Envelope σ → Option σ.Out := fun _ => none
  /-- Inputs still to take effect that the actors' states or the witness hold. -/
  held : ((i : σ.Id) → sys.State i) → W → Bag σ.In := fun _ _ => 0
  /-- Outputs still to be handed over that the actors' states or the witness hold. -/
  owing : ((i : σ.Id) → sys.State i) → W → Bag σ.Out := fun _ _ => 0
  /-- The values of the service that the actors' states and the messages in flight may be
  read as, with the witness. -/
  value : ((i : σ.Id) → sys.State i) → List (Envelope σ) → W → S → Prop

namespace Account

variable (a : Account sys S W)

/-- Every input a state holds that is still to take effect. -/
def pending (c : SysState sys) (w : W) : Bag σ.In :=
  ↑(c.net.filterMap a.pend) + a.held c.state w

/-- Every output a state has waiting or holds. -/
def owed (c : SysState sys) (w : W) : Bag σ.Out :=
  ↑c.outbox + ↑(c.net.filterMap a.owe) + a.owing c.state w

/-- The spec's state `t` explains `c` with the witness `w`: its value is one the account allows,
it still has pending what `c` holds, and it still owes what `c` has waiting or holds. -/
structure Holds (c : SysState sys) (w : W) (t : Service.Abs σ.In σ.Out S) : Prop where
  /-- The value is one the account allows. -/
  value : a.value c.state c.net w t.value
  /-- The spec still has pending what `c` holds. -/
  pending : a.pending c w ≤ t.pending
  /-- The spec still owes what `c` has waiting or holds. -/
  owed : a.owed c w ≤ t.outbox

/-- The standard simulation: `t` explains `c` with some witness. -/
def Sim (c : SysState sys) (t : Service.Abs σ.In σ.Out S) : Prop :=
  ∃ w, a.Holds c w t

variable {T : Type} (svc : Service σ.In σ.Out S T)

/--
`c'` is `c` after a step that the inputs `xs` taking effect explain: from any value the account
allows of `c`, `xs` lead to one it allows of `c'`, `c'` holds, with `xs`, no more inputs than
`c` did, and owes no more than `c` did with the outputs of `xs`.
-/
def Moves (c c' : SysState sys) : Prop :=
  ∀ w v, a.value c.state c.net w v → ∃ w' xs, a.value c'.state c'.net w' (svc.run v xs).1 ∧
    a.pending c' w' + ↑xs ≤ a.pending c w ∧ a.owed c' w' ≤ a.owed c w + ↑(svc.run v xs).2

variable {a svc} {c c' : SysState sys}

/-- A step that `Moves` is answered by internal steps of the spec: its inputs taking effect. -/
theorem Holds.moves {w : W} {t : Service.Abs σ.In σ.Out S} (h : a.Holds c w t)
    (hm : a.Moves svc c c') : ∃ t', svc.spec.lts.τSTr t t' ∧ a.Sim c' t' := by
  obtain ⟨w', xs, hvalue, hpending, howed⟩ := hm w t.value h.value
  obtain ⟨t', ht', hvalue', houtbox', hrest⟩ :=
    Service.takes svc xs t (a.pending c' w') (hpending.trans h.pending)
  refine ⟨t', ht', w', hvalue' ▸ hvalue, hrest, howed.trans ?_⟩
  rw [houtbox']
  exact Bag.add_le_add h.owed Bag.le_rfl

variable (a svc) in
/--
`c'` is `c` after a step that passes the deadline `t`: from any value the account allows of
`c`, the inputs `xs` take effect, `t` is then armed, and its passing leads to a value the
account allows of `c'`; `c'` holds, with `xs`, no more inputs than `c` did, and owes no more
than `c` did with the outputs of `xs` and of the deadline passing.
-/
def Fires (t : T) (c c' : SysState sys) : Prop :=
  ∀ w v, a.value c.state c.net w v → ∃ w' xs, svc.armed (svc.run v xs).1 t = true ∧
    a.value c'.state c'.net w' (svc.fire (svc.run v xs).1 t).1 ∧
    a.pending c' w' + ↑xs ≤ a.pending c w ∧
    a.owed c' w' ≤ a.owed c w + ↑(svc.run v xs).2 + ↑(svc.fire (svc.run v xs).1 t).2

variable (a svc) in
/-- A step that passes the deadline `d` names: `Fires` when it names one, `Moves` when not. -/
def Passes : Option T → SysState sys → SysState sys → Prop
  | none, c, c' => a.Moves svc c c'
  | some t, c, c' => a.Fires svc t c c'

/-- A step that `Fires` is answered by its inputs taking effect, then the deadline passing. -/
theorem Holds.fires {w : W} {t₀ : Service.Abs σ.In σ.Out S} {t : T} (h : a.Holds c w t₀)
    (hf : a.Fires svc t c c') : ∃ t', svc.spec.lts.STr t₀ (some (.fire t)) t' ∧ a.Sim c' t' := by
  obtain ⟨w', xs, harmed, hvalue, hpending, howed⟩ := hf w t₀.value h.value
  obtain ⟨t₁, ht₁, hvalue₁, houtbox₁, hrest⟩ :=
    Service.takes svc xs t₀ (a.pending c' w') (hpending.trans h.pending)
  refine ⟨⟨(svc.fire t₁.value t).1, t₁.pending, t₁.outbox + (svc.fire t₁.value t).2⟩,
    .tr ht₁ ⟨by rwa [hvalue₁], rfl⟩ .refl, w', by rw [hvalue₁]; exact hvalue, hrest, ?_⟩
  refine howed.trans ?_
  rw [houtbox₁, hvalue₁]
  exact Bag.add_le_add (Bag.add_le_add h.owed Bag.le_rfl) Bag.le_rfl

/-- A step that `Passes` the deadline `d` names is answered by a step of the spec with that
label. -/
theorem Holds.passes {w : W} {t₀ : Service.Abs σ.In σ.Out S} {d : Option T} (h : a.Holds c w t₀)
    (hp : a.Passes svc d c c') :
    ∃ t', svc.spec.lts.STr t₀ (d.map Visible.fire) t' ∧ a.Sim c' t' := by
  cases d with
  | none =>
    obtain ⟨t', ht', h'⟩ := h.moves hp
    exact ⟨t', (LTS.sTr_τSTr_iff _).mpr ht', h'⟩
  | some t => exact h.fires hp

/-- A step at which nothing takes effect: the account allows the same values, and the state
after holds and owes no more. -/
theorem Moves.of_le
    (h : ∀ w v, a.value c.state c.net w v → ∃ w', a.value c'.state c'.net w' v ∧
      a.pending c' w' ≤ a.pending c w ∧ a.owed c' w' ≤ a.owed c w) : a.Moves svc c c' := by
  intro w v hv
  obtain ⟨w', hv', hp, ho⟩ := h w v hv
  exact ⟨w', [], hv', by simpa using hp, by simpa using ho⟩

/-- Losing messages and timers, when the account's value does not read what is lost. -/
theorem Moves.of_loses (hl : c'.Loses c)
    (hv : ∀ w v, a.value c.state c.net w v → a.value c'.state c'.net w v) : a.Moves svc c c' := by
  refine Moves.of_le fun w v h => ⟨w, hv w v h, ?_, ?_⟩
  · simp only [pending, hl.state]
    exact Bag.add_le_add (Bag.coe_le_coe_of_sublist (hl.net.filterMap _)) Bag.le_rfl
  · simp only [owed, hl.state, hl.outbox]
    exact Bag.add_le_add (Bag.add_le_add Bag.le_rfl (Bag.coe_le_coe_of_sublist (hl.net.filterMap _))) Bag.le_rfl

/-- An actor that moves and sends and outputs nothing, such as one that recovers, in a state
the account reads no differently. -/
theorem Moves.quiet {i : σ.Id} {s : sys.State i} {effs : List (Effect σ i)}
    (hvalue : ∀ w v, a.value c.state c.net w v → a.value (update c.state i s) c.net w v)
    (hsends : Effect.sends i effs = []) (hemits : Effect.emits effs = [])
    (hheld : ∀ w, a.held (update c.state i s) w = a.held c.state w := by intro; rfl)
    (howing : ∀ w, a.owing (update c.state i s) w = a.owing c.state w := by intro; rfl) :
    a.Moves svc c (c.grow i (s, effs)) := by
  refine Moves.of_le fun w v h => ⟨w, ?_, ?_, ?_⟩
  · simpa [SysState.grow, hsends] using hvalue w v h
  all_goals simp [SysState.grow, pending, owed, hsends, hemits, hheld, howing]

variable {e : Envelope σ} {r : sys.State e.dst × List (Effect σ e.dst)}

/-- An actor handles `e` and passes on what it carried: its sends carry the input `e` carried,
its outputs and sends the output `e` carried, and nothing takes effect. -/
theorem Moves.forward (he : e ∈ c.net)
    (hvalue : ∀ w v, a.value c.state c.net w v →
      a.value (update c.state e.dst r.1) (c.net.erase e ++ Effect.sends e.dst r.2) w v)
    (hpend : (Effect.sends e.dst r.2).filterMap a.pend = (a.pend e).toList)
    (howe : Effect.emits r.2 ++ (Effect.sends e.dst r.2).filterMap a.owe = (a.owe e).toList)
    (hheld : ∀ w, a.held (update c.state e.dst r.1) w = a.held c.state w := by intro; rfl)
    (howing : ∀ w, a.owing (update c.state e.dst r.1) w = a.owing c.state w := by intro; rfl) :
    a.Moves svc c (({ c with net := c.net.erase e }).grow e.dst r) := by
  refine Moves.of_le fun w v h => ⟨w, hvalue w v h, Bag.le_of_eq ?_, Bag.le_of_eq ?_⟩
  · simp only [pending, SysState.grow, hheld, List.filterMap_append, hpend,
      Bag.coe_eq_coe.mpr (filterMap_perm_erase he), ← Bag.coe_add]
    ac_rfl
  · simp only [owed, SysState.grow, howing, List.filterMap_append, ← howe,
      Bag.coe_eq_coe.mpr (filterMap_perm_erase he), ← Bag.coe_add]
    ac_rfl

/-- An actor handles `e`, and that is the input `x` that `e` carried taking effect: its sends
carry no input, and its outputs and sends carry the outputs of `x`. -/
theorem Moves.take (he : e ∈ c.net) {x : σ.In} (hx : a.pend e = some x) (hnone : a.owe e = none)
    (hvalue : ∀ w v, a.value c.state c.net w v →
      a.value (update c.state e.dst r.1) (c.net.erase e ++ Effect.sends e.dst r.2) w
        (svc.step v x).1)
    (hpend : (Effect.sends e.dst r.2).filterMap a.pend = [])
    (howe : ∀ w v, a.value c.state c.net w v →
      Effect.emits r.2 ++ (Effect.sends e.dst r.2).filterMap a.owe = (svc.step v x).2)
    (hheld : ∀ w, a.held (update c.state e.dst r.1) w = a.held c.state w := by intro; rfl)
    (howing : ∀ w, a.owing (update c.state e.dst r.1) w = a.owing c.state w := by intro; rfl) :
    a.Moves svc c (({ c with net := c.net.erase e }).grow e.dst r) := by
  intro w v h
  refine ⟨w, [x], by rw [Service.run_singleton]; exact hvalue w v h, Bag.le_of_eq ?_, Bag.le_of_eq ?_⟩
  · simp only [pending, SysState.grow, hheld, List.filterMap_append, hpend, List.append_nil,
      Bag.coe_eq_coe.mpr (filterMap_perm_erase he), hx, Option.toList_some,
      ← Bag.coe_add]
    ac_rfl
  · rw [Service.run_singleton, ← howe w v h]
    simp only [owed, SysState.grow, howing, List.filterMap_append,
      Bag.coe_eq_coe.mpr (filterMap_perm_erase he), hnone, Option.toList_none,
      List.nil_append, ← Bag.coe_add]
    ac_rfl

/--
Actor `i` moves from the states `state` to `r`, having been handed the input `x` and the output
`o` (what a message it handles carried), with the network going from `net` to `net'`: from any
value the account allows, some inputs `xs` take effect, and the inputs its sends carry, those
the state after holds and `xs` are at most `x` and what the state held; what it outputs, what
its sends carry and what the state after owes are at most `o`, what the state owed and the
outputs of `xs`. This is all an application shows of a step (`Moves.handle`, `Moves.grow`).
-/
def Handles (a : Account sys S W) (svc : Service σ.In σ.Out S T) (state : (i : σ.Id) → sys.State i) (net net' : List (Envelope σ)) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) (x : Option σ.In) (o : Option σ.Out) : Prop :=
  ∀ w v, a.value state net w v → ∃ w' xs, a.value (update state i r.1) net' w' (svc.run v xs).1 ∧
    ↑((Effect.sends i r.2).filterMap a.pend) + a.held (update state i r.1) w' + ↑xs ≤
      ↑x.toList + a.held state w ∧
    ↑(Effect.emits r.2) + ↑((Effect.sends i r.2).filterMap a.owe) + a.owing (update state i r.1) w' ≤
      ↑o.toList + a.owing state w + ↑(svc.run v xs).2

/-- An actor handles `e`: what that does is `Handles` with what `e` carried. -/
theorem Moves.handle (he : e ∈ c.net)
    (h : a.Handles svc c.state c.net (c.net.erase e ++ Effect.sends e.dst r.2) e.dst r (a.pend e)
      (a.owe e)) :
    a.Moves svc c (({ c with net := c.net.erase e }).grow e.dst r) := by
  intro w v hv
  obtain ⟨w', xs, hv', hp, ho⟩ := h w v hv
  refine ⟨w', xs, hv', ?_, ?_⟩
  · have := Bag.add_le_add_left hp ↑((c.net.erase e).filterMap a.pend)
    simp only [pending, SysState.grow, List.filterMap_append,
      Bag.coe_eq_coe.mpr (filterMap_perm_erase he), ← Bag.coe_add]
    exact Bag.le_congr this (by ac_rfl) (by ac_rfl)
  · have := Bag.add_le_add_left ho (↑c.outbox + ↑((c.net.erase e).filterMap a.owe))
    simp only [owed, SysState.grow, List.filterMap_append,
      Bag.coe_eq_coe.mpr (filterMap_perm_erase he), ← Bag.coe_add]
    exact Bag.le_congr this (by ac_rfl) (by ac_rfl)

/-- An actor moves with no message taken off the network (a timer, a recovery, a message handed
over a second time): `Handles` with nothing handed to it. -/
theorem Moves.grow {i : σ.Id} {r : sys.State i × List (Effect σ i)}
    (h : a.Handles svc c.state c.net (c.net ++ Effect.sends i r.2) i r none none) :
    a.Moves svc c (c.grow i r) := by
  intro w v hv
  obtain ⟨w', xs, hv', hp, ho⟩ := h w v hv
  refine ⟨w', xs, hv', ?_, ?_⟩
  · have := Bag.add_le_add_left (hp.trans_eq (Bag.zero_add _)) ↑(c.net.filterMap a.pend)
    simp only [pending, SysState.grow, List.filterMap_append, ← Bag.coe_add]
    exact Bag.le_congr this (by ac_rfl) (by ac_rfl)
  · have := Bag.add_le_add_left (ho.trans_eq (congrArg (· + _) (Bag.zero_add _)))
      (↑c.outbox + ↑(c.net.filterMap a.owe))
    simp only [owed, SysState.grow, List.filterMap_append, ← Bag.coe_add]
    exact Bag.le_congr this (by ac_rfl) (by ac_rfl)

/-- `Handles`, for a step that passes the deadline `t` after the inputs `xs` take effect: `t`
is then armed, and the outputs of its passing may be owed too. -/
def HandlesFire (a : Account sys S W) (svc : Service σ.In σ.Out S T)
    (state : (i : σ.Id) → sys.State i) (net net' : List (Envelope σ)) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) (x : Option σ.In) (o : Option σ.Out) (t : T) : Prop :=
  ∀ w v, a.value state net w v → ∃ w' xs, svc.armed (svc.run v xs).1 t = true ∧
    a.value (update state i r.1) net' w' (svc.fire (svc.run v xs).1 t).1 ∧
    ↑((Effect.sends i r.2).filterMap a.pend) + a.held (update state i r.1) w' + ↑xs ≤
      ↑x.toList + a.held state w ∧
    ↑(Effect.emits r.2) + ↑((Effect.sends i r.2).filterMap a.owe) + a.owing (update state i r.1) w' ≤
      ↑o.toList + a.owing state w + ↑(svc.run v xs).2 + ↑(svc.fire (svc.run v xs).1 t).2

/-- An actor handles `e` and passes the deadline `t`: what that does is `HandlesFire` with what
`e` carried. -/
theorem Fires.handle {t : T} (he : e ∈ c.net)
    (h : a.HandlesFire svc c.state c.net (c.net.erase e ++ Effect.sends e.dst r.2) e.dst r
      (a.pend e) (a.owe e) t) :
    a.Fires svc t c (({ c with net := c.net.erase e }).grow e.dst r) := by
  intro w v hv
  obtain ⟨w', xs, harmed, hv', hp, ho⟩ := h w v hv
  refine ⟨w', xs, harmed, hv', ?_, ?_⟩
  · have := Bag.add_le_add_left hp ↑((c.net.erase e).filterMap a.pend)
    simp only [pending, SysState.grow, List.filterMap_append,
      Bag.coe_eq_coe.mpr (filterMap_perm_erase he), ← Bag.coe_add]
    exact Bag.le_congr this (by ac_rfl) (by ac_rfl)
  · have := Bag.add_le_add_left ho (↑c.outbox + ↑((c.net.erase e).filterMap a.owe))
    simp only [owed, SysState.grow, List.filterMap_append,
      Bag.coe_eq_coe.mpr (filterMap_perm_erase he), ← Bag.coe_add]
    exact Bag.le_congr this (by ac_rfl) (by ac_rfl)

/-- An actor passes the deadline `t` with no message taken off the network (a timer, a message
handed over a second time): `HandlesFire` with nothing handed to it. -/
theorem Fires.grow {i : σ.Id} {r : sys.State i × List (Effect σ i)} {t : T}
    (h : a.HandlesFire svc c.state c.net (c.net ++ Effect.sends i r.2) i r none none t) :
    a.Fires svc t c (c.grow i r) := by
  intro w v hv
  obtain ⟨w', xs, harmed, hv', hp, ho⟩ := h w v hv
  refine ⟨w', xs, harmed, hv', ?_, ?_⟩
  · have := Bag.add_le_add_left (hp.trans_eq (Bag.zero_add _)) ↑(c.net.filterMap a.pend)
    simp only [pending, SysState.grow, List.filterMap_append, ← Bag.coe_add]
    exact Bag.le_congr this (by ac_rfl) (by ac_rfl)
  · have := Bag.add_le_add_left (ho.trans_eq (by rw [Option.toList_none, Bag.coe_nil, Bag.zero_add]))
      (↑c.outbox + ↑(c.net.filterMap a.owe))
    simp only [owed, SysState.grow, List.filterMap_append, ← Bag.coe_add]
    exact Bag.le_congr this (by ac_rfl) (by ac_rfl)

variable {env : EnvModel σ} {inv : SysState sys → Prop}

/--
A system implements its service with deadlines when every step of an actor `Moves`, or, where
it is a timer that `deadlines` names or a message handed over that `delivered` names, `Fires`
that deadline (`Passes`). The rest is as in `implements`.
-/
theorem implements_timed {svc : Service σ.In σ.Out S T} (a : Account sys S W)
    {deadlines delivered : Deadlines σ T}
    (hinv : sys.Invariant env inv)
    (init : ∃ w, a.Holds (SysState.init sys env) w ⟨svc.init, 0, 0⟩)
    (accept : ∀ x, a.pend ⟨none, (sys.accept x).1, (sys.accept x).2⟩ = some x ∧
      a.owe ⟨none, (sys.accept x).1, (sys.accept x).2⟩ = none)
    (input : ∀ c w v x, inv c → a.value c.state c.net w v →
      a.value c.state (c.net ++ [⟨none, (sys.accept x).1, (sys.accept x).2⟩]) w v)
    (deliver : ∀ c e, inv c → sys.Sent e → c.deliverable env e = true →
      a.Passes svc (delivered e.dst e.msg) c (({ c with net := c.net.erase e }).grow e.dst
        ((sys.actor e.dst).step (c.state e.dst) e.msg)))
    (duplicate : ∀ c e, inv c → sys.Sent e → c.deliverable env e = true →
      (env.link e.src e.dst).duplicating = true → a.Passes svc (delivered e.dst e.msg) c
        (c.grow e.dst ((sys.actor e.dst).step (c.state e.dst) e.msg)))
    (drop : ∀ c e, inv c → sys.Sent e → e ∈ c.net → (env.link e.src e.dst).lossy = true →
      a.Moves svc c { c with net := c.net.erase e })
    (down : ∀ c i, env.mayCrash i = true ∨ sys.Stops i → a.Moves svc c (c.down env i))
    (timeout : ∀ c i msg, inv c → sys.Armed i msg → msg ∈ c.timers i →
      a.Passes svc (deadlines i msg) c (c.grow i ((sys.actor i).step (c.state i) msg)))
    (recover : ∀ c i, inv c → a.Moves svc c (c.grow i ((sys.actor i).recover (c.state i)))) :
    sys.Implements env svc deadlines delivered := by
  have hsent := fun c e (hc : inv c ∧ sys.Traced c) he => hc.2.net e he
  refine System.Refines.of_timed_events (fun c hc => ⟨hinv c hc, System.traced sys env c hc⟩)
    a.Sim ⟨_, rfl, init⟩ (fun c t up timers ⟨w, h⟩ _ => ⟨w, h.value, h.pending, h.owed⟩) ?_ ?_
    (fun c t e hc ⟨_, h⟩ hd =>
      h.passes (deliver c e hc.1 (hsent c e hc (SysState.mem_of_deliverable hd)) hd))
    (fun c t e hc ⟨_, h⟩ hd hdup =>
      h.passes (duplicate c e hc.1 (hsent c e hc (SysState.mem_of_deliverable hd)) hd hdup))
    (fun c t e hc ⟨_, h⟩ hmem hlossy => h.moves (drop c e hc.1 (hsent c e hc hmem) hmem hlossy))
    (fun c t i ⟨_, h⟩ hi => h.moves (down c i hi))
    (fun c t i msg hc ⟨_, h⟩ hmem =>
      h.passes (timeout c i msg hc.1 (hc.2.timers i msg hmem) hmem))
    (fun c t i hc ⟨_, h⟩ => h.moves (recover c i hc.1))
  · rintro c t x ⟨hc, -⟩ ⟨w, h⟩
    obtain ⟨hpend, howe⟩ := accept x
    refine ⟨{ t with pending := x ::ₘ t.pending }, .single rfl, w, input c w _ x hc h.value, ?_, ?_⟩
    · have := Bag.cons_le_cons x h.pending
      simp only [pending, filterMap_concat, hpend, Option.toList_some, ← Bag.coe_add] at this ⊢
      rw [Bag.add_comm (↑(c.net.filterMap a.pend) : Bag σ.In), Bag.add_assoc]
      simpa using this
    · simpa [owed, filterMap_concat, howe] using h.owed
  · rintro c t out hc ⟨w, h⟩ hmem
    have hin : out ∈ (↑c.outbox : Bag σ.Out) := Bag.mem_coe.mpr hmem
    refine ⟨{ t with outbox := t.outbox.erase out },
      .single ⟨Bag.mem_of_le h.owed (Bag.mem_add.mpr (.inl (Bag.mem_add.mpr
        (.inl hin)))), rfl⟩, w, h.value, h.pending, ?_⟩
    have := Bag.erase_le_erase out h.owed
    rwa [owed, Bag.erase_add_left_pos _ (Bag.mem_add.mpr (.inl hin)),
      Bag.erase_add_left_pos _ hin, Bag.coe_erase] at this

/--
A system implements its service when every step of an actor `Moves`: an application gives the
account, that it holds initially, that an input is what its message to the system carries, and
the steps. A value that reads the messages in flight must also survive an input arriving, and
losses must keep the account; `Moves.of_loses` does that for a value that does not read what
is lost.
-/
theorem implements {svc : Service σ.In σ.Out S T} (a : Account sys S W)
    (hinv : sys.Invariant env inv)
    (init : ∃ w, a.Holds (SysState.init sys env) w ⟨svc.init, 0, 0⟩)
    (accept : ∀ x, a.pend ⟨none, (sys.accept x).1, (sys.accept x).2⟩ = some x ∧
      a.owe ⟨none, (sys.accept x).1, (sys.accept x).2⟩ = none)
    (input : ∀ c w v x, inv c → a.value c.state c.net w v →
      a.value c.state (c.net ++ [⟨none, (sys.accept x).1, (sys.accept x).2⟩]) w v)
    (deliver : ∀ c e, inv c → sys.Sent e → c.deliverable env e = true → a.Moves svc c
      (({ c with net := c.net.erase e }).grow e.dst ((sys.actor e.dst).step (c.state e.dst) e.msg)))
    (duplicate : ∀ c e, inv c → sys.Sent e → c.deliverable env e = true →
      (env.link e.src e.dst).duplicating = true →
        a.Moves svc c (c.grow e.dst ((sys.actor e.dst).step (c.state e.dst) e.msg)))
    (drop : ∀ c e, inv c → sys.Sent e → e ∈ c.net → (env.link e.src e.dst).lossy = true →
      a.Moves svc c { c with net := c.net.erase e })
    (down : ∀ c i, env.mayCrash i = true ∨ sys.Stops i → a.Moves svc c (c.down env i))
    (timeout : ∀ c i msg, inv c → sys.Armed i msg → msg ∈ c.timers i →
      a.Moves svc c (c.grow i ((sys.actor i).step (c.state i) msg)))
    (recover : ∀ c i, inv c → a.Moves svc c (c.grow i ((sys.actor i).recover (c.state i)))) :
    sys.Implements env svc :=
  a.implements_timed (deadlines := fun _ _ => none) (delivered := fun _ _ => none) hinv init
    accept input deliver duplicate drop down timeout recover

end Account

end Lanes
