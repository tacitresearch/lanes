/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Check.EquivDecide
public import Lanes.Check.SearchSound
public import Lanes.Check.System
public import Lanes.Check.WorldEquiv

/-!
# A PASS from `Check.system` is sound

`Scenario.Reachable` says which worlds a check covers, in terms of `SysState.step` alone: the
semantics, with inputs chosen by the driver, crashes within the budget and every world within
the constraint. `Check.system_sound` says that a complete PASS means every `always` property
holds in all of them.

The checker merges worlds that differ only in message order no actor can see (`World.Equiv`),
so the properties and the constraint must not see it either. `World.Equiv.eq_of_quiet` and
`World.Equiv.eq_of_perm` discharge that for properties that ignore messages in flight and
pending outputs, or look at them only up to order.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature} {sys : System σ} {D : Type}

/-- The events that involve neither the driver nor the crash budget. -/
def Event.isInternal : Event σ → Bool
  | .deliver _ | .duplicate _ | .drop _ | .timeout .. | .start _ => true
  | .input _ | .output _ | .crash _ => false

/--
The instance a check covers: the worlds the semantics reaches when the driver chooses the
inputs and sees the outputs, at most `maxCrashes` crashes happen and no world violates the
constraint.
-/
inductive Scenario.Reachable (sys : System σ) (sc : Scenario σ D)
    (constraint : World sys D → Bool) : World sys D → Prop
  | init : constraint (World.init sys sc) = true → Reachable sys sc constraint (World.init sys sc)
  | input {w : World sys D} {x : σ.In} {d : D} {c : SysState sys} :
    Reachable sys sc constraint w → (x, d) ∈ sc.driver.inputs w.driver →
    w.state.step sc.env (.input x) = some c →
    constraint { w with state := c, driver := d } = true →
    Reachable sys sc constraint { w with state := c, driver := d }
  | output {w : World sys D} {out : σ.Out} {c : SysState sys} :
    Reachable sys sc constraint w → w.state.step sc.env (.output out) = some c →
    constraint { w with state := c, driver := sc.driver.observe w.driver out } = true →
    Reachable sys sc constraint { w with state := c, driver := sc.driver.observe w.driver out }
  | crash {w : World sys D} {i : σ.Id} {c : SysState sys} :
    Reachable sys sc constraint w → w.crashes < sc.maxCrashes →
    w.state.step sc.env (.crash i) = some c →
    constraint { w with state := c, crashes := w.crashes + 1 } = true →
    Reachable sys sc constraint { w with state := c, crashes := w.crashes + 1 }
  | internal {w : World sys D} {ev : Event σ} {c : SysState sys} :
    Reachable sys sc constraint w → ev.isInternal = true → w.state.step sc.env ev = some c →
    constraint { w with state := c } = true → Reachable sys sc constraint { w with state := c }

theorem Scenario.Reachable.system {sc : Scenario σ D} {constraint : World sys D → Bool}
    {w : World sys D} (h : sc.Reachable sys constraint w) : sys.Reachable sc.env w.state := by
  induction h with
  | init => exact .init
  | input _ _ hstep _ ih | output _ hstep _ ih | crash _ _ hstep _ ih | internal _ _ hstep _ ih =>
    exact .step _ ih hstep

theorem World.mem_next_iff [Enum σ.Id] {sc : Scenario σ D} {w w' : World sys D} {ev : Event σ} :
    (ev, w') ∈ w.next sc ↔ ∃ c, w.state.step sc.env ev = some c ∧
      match ev with
      | .input x =>
        ∃ d, (x, d) ∈ sc.driver.inputs w.driver ∧ w' = { w with state := c, driver := d }
      | .output out => w' = { w with state := c, driver := sc.driver.observe w.driver out }
      | .crash _ =>
        w.crashes < sc.maxCrashes ∧ w' = { w with state := c, crashes := w.crashes + 1 }
      | _ => w' = { w with state := c } := by
  simp only [World.next, List.mem_append, List.mem_filterMap, SysState.compact_eq]
  constructor
  · rintro (⟨⟨ev₀, c⟩, hsucc, hsome⟩ | ⟨⟨x, d⟩, hinput, hsome⟩)
    · obtain ⟨hstep, hnotInput⟩ := SysState.mem_successors_iff.mp hsucc
      cases ev₀ with
      | input x => exact absurd rfl (hnotInput x)
      | crash i =>
        by_cases hbudget : w.crashes < sc.maxCrashes
        · simp only [hbudget, ite_true, Option.some.injEq, Prod.mk.injEq] at hsome
          obtain ⟨rfl, rfl⟩ := hsome
          exact ⟨c, hstep, hbudget, rfl⟩
        · simp [hbudget] at hsome
      | output out | deliver e | duplicate e | drop e | timeout i msg | start i =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨rfl, rfl⟩ := hsome
        exact ⟨c, hstep, rfl⟩
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hsome
      obtain ⟨c, hstep, rfl, rfl⟩ := hsome
      exact ⟨c, hstep, d, hinput, rfl⟩
  · rintro ⟨c, hstep, hw'⟩
    cases ev with
    | input x =>
      obtain ⟨d, hinput, rfl⟩ := hw'
      exact .inr ⟨(x, d), hinput, by simp [hstep]⟩
    | crash i =>
      obtain ⟨hbudget, rfl⟩ := hw'
      exact .inl ⟨(_, c), SysState.mem_successors_iff.mpr ⟨hstep, by simp⟩, by simp [hbudget]⟩
    | output out | deliver e | duplicate e | drop e | timeout i msg | start i =>
      subst hw'
      exact .inl ⟨(_, c), SysState.mem_successors_iff.mpr ⟨hstep, by simp⟩, rfl⟩

theorem Scenario.Reachable.model [Enum σ.Id] {sc : Scenario σ D}
    {constraint : World sys D → Bool} {w : World sys D} (h : sc.Reachable sys constraint w) :
    (Check.model sys sc).Reachable (fun n => constraint n.world) ⟨w⟩ := by
  induction h with
  | init hc => exact .init (by simp [Check.model]) hc
  | @input _ x d _ _ hinput hstep hc ih =>
    have hmem := (World.mem_next_iff (ev := .input x)).mpr ⟨_, hstep, d, hinput, rfl⟩
    exact .step ih (List.mem_map.mpr ⟨_, hmem, rfl⟩) hc
  | @output _ out _ _ hstep hc ih =>
    have hmem := (World.mem_next_iff (ev := .output out)).mpr ⟨_, hstep, rfl⟩
    exact .step ih (List.mem_map.mpr ⟨_, hmem, rfl⟩) hc
  | @crash _ i _ _ hbudget hstep hc ih =>
    have hmem := (World.mem_next_iff (ev := .crash i)).mpr ⟨_, hstep, hbudget, rfl⟩
    exact .step ih (List.mem_map.mpr ⟨_, hmem, rfl⟩) hc
  | @internal _ ev _ _ hev hstep hc ih =>
    have hmem := (World.mem_next_iff (ev := ev)).mpr ⟨_, hstep, by
      cases ev <;> first | rfl | exact absurd hev (by simp [Event.isInternal])⟩
    exact .step ih (List.mem_map.mpr ⟨_, hmem, rfl⟩) hc

theorem Scenario.Reachable.of_model [Enum σ.Id] {sc : Scenario σ D}
    {constraint : World sys D → Bool} {n : Check.Node sys sc.env D}
    (h : (Check.model sys sc).Reachable (fun n => constraint n.world) n) :
    sc.Reachable sys constraint n.world := by
  induction h with
  | init hinit hc =>
    obtain rfl : _ = Check.Node.mk _ := by simpa [Check.model] using hinit
    exact .init hc
  | step _ hnext hc ih =>
    obtain ⟨⟨ev, w'⟩, hmem, heq⟩ := List.mem_map.mp hnext
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨c, hstep, hw'⟩ := World.mem_next_iff.mp hmem
    cases ev with
    | input x =>
      obtain ⟨d, hinput, rfl⟩ := hw'
      exact .input ih hinput hstep hc
    | output out => subst hw'; exact .output ih hstep hc
    | crash i =>
      obtain ⟨hbudget, rfl⟩ := hw'
      exact .crash ih hbudget hstep hc
    | deliver e | duplicate e | drop e | timeout i msg | start i =>
      subst hw'
      exact .internal ih rfl hstep hc

/-- `Scenario.Reachable` is exactly what the checker's model reaches. -/
theorem Scenario.reachable_iff [Enum σ.Id] {sc : Scenario σ D} {constraint : World sys D → Bool}
    {w : World sys D} : sc.Reachable sys constraint w ↔
      (Check.model sys sc).Reachable (fun n => constraint n.world) ⟨w⟩ :=
  ⟨Reachable.model, Reachable.of_model (n := ⟨w⟩)⟩

theorem NetEquiv.toPerm {env : EnvModel σ} {a b : List (Envelope σ)} (h : NetEquiv env a b) :
    a.Perm b := by
  rw [List.perm_iff_count]
  intro e
  have hself : onLink e.src e.dst e = true := by simp [onLink]
  rw [← List.count_filter (l := a) hself, ← List.count_filter (l := b) hself]
  exact (h.perm e.src e.dst).count_eq e

theorem SysState.Equiv.hash_eq [σ.Inspect] [sys.Inspect] {env : EnvModel σ} {a b : SysState sys}
    (h : SysState.Equiv env a b) : a.hash = b.hash := by
  have hnet := h.net.toPerm.foldl_eq'
    (f := fun (h : UInt64) e => h + mixHash 11 (Hashable.hash e))
    (fun _ _ _ _ z => by rw [UInt64.add_assoc, UInt64.add_comm (mixHash _ _), UInt64.add_assoc]) 0
  have hout := h.outbox.foldl_eq'
    (f := fun (h : UInt64) o => h + mixHash 13 (Hashable.hash o))
    (fun _ _ _ _ z => by rw [UInt64.add_assoc, UInt64.add_comm (mixHash _ _), UInt64.add_assoc]) 0
  simp only [SysState.hash, h.state, h.up, h.timers, hnet, hout]

/-- `w` with no messages in flight and no pending outputs. -/
def World.quiet (w : World sys D) : World sys D :=
  { w with state := { w.state with net := [], outbox := [] } }

namespace World.Equiv

variable {env : EnvModel σ} {a b : World sys D} {α : Type}

theorem net_perm (h : World.Equiv env a b) : a.state.net.Perm b.state.net :=
  h.state.net.toPerm

/-- A property that looks at messages in flight and pending outputs only up to their order
cannot tell merged worlds apart. -/
theorem eq_of_perm {p : World sys D → α}
    (hp : ∀ (w : World sys D) (net : List (Envelope σ)) (outbox : List σ.Out),
      w.state.net.Perm net → w.state.outbox.Perm outbox →
      p w = p { w with state := { w.state with net, outbox } })
    (h : World.Equiv env a b) : p a = p b := by
  have hb : b =
      { a with state := { a.state with net := b.state.net, outbox := b.state.outbox } } := by
    obtain ⟨⟨hstate, hup, htimers, _, _⟩, hdriver, hcrashes⟩ := h
    obtain ⟨⟨_, _, _, _, _⟩, _, _⟩ := a
    obtain ⟨⟨_, _, _, _, _⟩, _, _⟩ := b
    simp only at hstate hup htimers hdriver hcrashes
    simp [hstate, hup, htimers, hdriver, hcrashes]
  rw [hb]
  exact hp a _ _ h.net_perm h.state.outbox

/-- A property that ignores messages in flight and pending outputs cannot tell merged worlds
apart. For a property of actor states, timers, the driver and the crash count, `hp` is
`fun _ => rfl`. -/
theorem eq_of_quiet {p : World sys D → α} (hp : ∀ w, p w = p w.quiet)
    (h : World.Equiv env a b) : p a = p b := by
  have hquiet : a.quiet = b.quiet := by
    simp only [World.quiet, h.state.state, h.state.up, h.state.timers, h.driver, h.crashes]
  rw [hp a, hp b, hquiet]

end World.Equiv

namespace Check

variable [σ.Inspect] [sys.Inspect] {env : EnvModel σ}

theorem Node.beq_iff [BEq D] [∀ i, LawfulBEq (sys.State i)] {a b : Node sys env D} :
    (a == b) = true ↔ a.world.crashes = b.world.crashes ∧ (a.world.driver == b.world.driver) = true
      ∧ SysState.Equiv env a.world.state b.world.state := by
  simp only [BEq.beq, Bool.and_eq_true, SysState.equiv_iff, and_assoc]
  simp

theorem Node.beq_iff_equiv [BEq D] [LawfulBEq D] [∀ i, LawfulBEq (sys.State i)]
    {a b : Node sys env D} : (a == b) = true ↔ World.Equiv env a.world b.world := by
  rw [Node.beq_iff, beq_iff_eq]
  exact ⟨fun ⟨hc, hd, hs⟩ => ⟨hs, hd, hc⟩, fun ⟨hs, hd, hc⟩ => ⟨hc, hd, hs⟩⟩

instance [BEq D] [EquivBEq D] [∀ i, LawfulBEq (sys.State i)] : EquivBEq (Node sys env D) where
  rfl := Node.beq_iff.mpr ⟨rfl, BEq.rfl, .refl env _⟩
  symm h :=
    have ⟨hc, hd, hs⟩ := Node.beq_iff.mp h
    Node.beq_iff.mpr ⟨hc.symm, BEq.symm hd, hs.symm⟩
  trans h₁ h₂ :=
    have ⟨hc₁, hd₁, hs₁⟩ := Node.beq_iff.mp h₁
    have ⟨hc₂, hd₂, hs₂⟩ := Node.beq_iff.mp h₂
    Node.beq_iff.mpr ⟨hc₁.trans hc₂, BEq.trans hd₁ hd₂, hs₁.trans hs₂⟩

instance [BEq D] [Hashable D] [LawfulHashable D] [∀ i, LawfulBEq (sys.State i)] :
    LawfulHashable (Node sys env D) where
  hash_eq a b h := by
    obtain ⟨hc, hd, hs⟩ := Node.beq_iff.mp h
    simp only [hash, hs.hash_eq, hc, LawfulHashable.hash_eq _ _ hd]

variable [BEq D] [Hashable D] [LawfulBEq D] [∀ i, LawfulBEq (sys.State i)]

/--
A complete PASS from `Check.system` is sound: every `always` property holds in every world of
the checked instance.

Actor states and the driver's state must compare with `==` exactly when they are equal. The
properties and the constraint must not tell merged worlds apart.
-/
theorem system_sound (sc : Scenario σ D) (props : List (Property (World sys D)))
    (opts : Options (World sys D))
    (hprops : ∀ p ∈ props, ∀ a b, World.Equiv sc.env a b → p.holds a = p.holds b)
    (hconstraint : ∀ a b, World.Equiv sc.env a b → opts.constraint a = opts.constraint b)
    (hfailure : (system sys sc props opts).failure = none)
    (hcomplete : (system sys sc props opts).complete = true)
    {name : String} {p : World sys D → Bool} (hp : .always name p ∈ props)
    {w : World sys D} (hw : sc.Reachable sys opts.constraint w) : p w = true := by
  simp only [system, Report.map, Option.map_eq_none_iff] at hfailure hcomplete
  refine search_sound (s := (⟨w⟩ : Node sys sc.env D)) (p := fun n => p n.world) ?_ hfailure
    hcomplete (List.mem_map.mpr ⟨_, hp, rfl⟩) hw.model
  refine ⟨fun a b hab l a' ha' => ?_, fun a b hab => hconstraint _ _ (Node.beq_iff_equiv.mp hab),
    fun q hq a b hab => ?_⟩
  · obtain ⟨⟨ev, w'⟩, hmem, heq⟩ := List.mem_map.mp ha'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨b', hb', hequiv⟩ := (Node.beq_iff_equiv.mp hab).next hmem
    exact ⟨ev, ⟨b'⟩, List.mem_map.mpr ⟨(ev, b'), hb', rfl⟩, Node.beq_iff_equiv.mpr hequiv⟩
  · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    cases q' <;> exact hprops _ hq' _ _ (Node.beq_iff_equiv.mp hab)

end Check

end Lanes
