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

The checker merges worlds that differ only in message order no actor can see, and in the driver's
state up to `==` (`World.Equiv`), so the properties and the constraint must not see either.
`World.Equiv.eq_of_quiet` and `World.Equiv.eq_of_perm` discharge that for properties that ignore
messages in flight and pending outputs, or look at them only up to order, when `==` on the
driver's state is equality; `World.Equiv.congr` is the general form.

`Check.system_sound_of_respects` is the theorem for a driver whose `==` is only an equivalence
that the driver respects (`Driver.Respects`), such as a monitored driver.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature} {sys : System σ} {D : Type}

/-- The events that involve neither the driver nor the crash budget. -/
def Event.isInternal : Event σ → Bool
  | .deliver _ | .duplicate _ | .drop _ | .start _ => true
  | .input _ | .output _ | .timeout .. | .crash _ => false

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
  | timeout {w : World sys D} {i : σ.Id} {msg : σ.Msg i} {c : SysState sys} :
    Reachable sys sc constraint w → w.state.step sc.env (.timeout i msg) = some c →
    constraint { w with state := c, driver := sc.driver.timeout w.driver i msg } = true →
    Reachable sys sc constraint { w with state := c, driver := sc.driver.timeout w.driver i msg }
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
  | input _ _ hstep _ ih | output _ hstep _ ih | timeout _ hstep _ ih | crash _ _ hstep _ ih
  | internal _ _ hstep _ ih =>
    exact .step _ ih hstep

theorem World.mem_next_iff [Enum σ.Id] {sc : Scenario σ D} {w w' : World sys D} {ev : Event σ} :
    (ev, w') ∈ w.next sc ↔ ∃ c, w.state.step sc.env ev = some c ∧
      match ev with
      | .input x =>
        ∃ d, (x, d) ∈ sc.driver.inputs w.driver ∧ w' = { w with state := c, driver := d }
      | .output out => w' = { w with state := c, driver := sc.driver.observe w.driver out }
      | .timeout i msg => w' = { w with state := c, driver := sc.driver.timeout w.driver i msg }
      | .crash _ =>
        w.crashes < sc.maxCrashes ∧ w' = { w with state := c, crashes := w.crashes + 1 }
      | _ => w' = { w with state := c } := by
  simp only [World.next, List.mem_append, List.mem_filterMap]
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

namespace Check

@[simp] theorem Node.of_world [Enum σ.Id] {env : EnvModel σ} (w : World sys D) :
    (Node.of w : Node sys env D).world = w := by
  simp [Node.of]

/-- A node is its world: the slots are computed from it. -/
theorem Node.eq_of_world [Enum σ.Id] {env : EnvModel σ} {a b : Node sys env D}
    (h : a.world = b.world) : a = b := by
  obtain ⟨_, _, ha⟩ := a
  obtain ⟨_, _, hb⟩ := b
  subst h ha hb
  rfl

theorem mem_model_init [Enum σ.Id] {sc : Scenario σ D} {n : Node sys sc.env D} :
    n ∈ (model sys sc).init ↔ n.world = World.init sys sc := by
  simp only [model, List.mem_singleton]
  exact ⟨fun h => h ▸ Node.of_world _, fun h => Node.eq_of_world (h.trans (Node.of_world _).symm)⟩

/-- The model's steps are the world's. -/
theorem mem_model_next [Enum σ.Id] {sc : Scenario σ D} {n n' : Node sys sc.env D}
    {ev : Event σ} : (ev, n') ∈ (model sys sc).next n ↔ (ev, n'.world) ∈ n.world.next sc := by
  simp only [model, List.mem_map]
  constructor
  · rintro ⟨⟨ev', w'⟩, hmem, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    simpa using hmem
  · exact fun h => ⟨_, h, Prod.ext rfl (Node.eq_of_world (Node.of_world _))⟩

end Check

theorem Scenario.Reachable.model_step [Enum σ.Id] {sc : Scenario σ D}
    {constraint : World sys D → Bool} {w w' : World sys D} {ev : Event σ}
    (h : (Check.model sys sc).Reachable (fun n => constraint n.world) (.of w))
    (hnext : (ev, w') ∈ w.next sc) (hc : constraint w' = true) :
    (Check.model sys sc).Reachable (fun n => constraint n.world) (.of w') :=
  .step h (Check.mem_model_next.mpr (by simpa using hnext)) (by simpa using hc)

theorem Scenario.Reachable.model [Enum σ.Id] {sc : Scenario σ D}
    {constraint : World sys D → Bool} {w : World sys D} (h : sc.Reachable sys constraint w) :
    (Check.model sys sc).Reachable (fun n => constraint n.world) (.of w) := by
  induction h with
  | init hc => exact .init (Check.mem_model_init.mpr (Check.Node.of_world _)) (by simpa using hc)
  | @input _ x d _ _ hinput hstep hc ih =>
    exact model_step ih ((World.mem_next_iff (ev := .input x)).mpr ⟨_, hstep, d, hinput, rfl⟩) hc
  | @output _ out _ _ hstep hc ih =>
    exact model_step ih ((World.mem_next_iff (ev := .output out)).mpr ⟨_, hstep, rfl⟩) hc
  | @timeout _ i msg _ _ hstep hc ih =>
    exact model_step ih ((World.mem_next_iff (ev := .timeout i msg)).mpr ⟨_, hstep, rfl⟩) hc
  | @crash _ i _ _ hbudget hstep hc ih =>
    exact model_step ih ((World.mem_next_iff (ev := .crash i)).mpr ⟨_, hstep, hbudget, rfl⟩) hc
  | @internal _ ev _ _ hev hstep hc ih =>
    exact model_step ih ((World.mem_next_iff (ev := ev)).mpr ⟨_, hstep, by
      cases ev <;> first | rfl | exact absurd hev (by simp [Event.isInternal])⟩) hc

theorem Scenario.Reachable.of_model [Enum σ.Id] {sc : Scenario σ D}
    {constraint : World sys D → Bool} {n : Check.Node sys sc.env D}
    (h : (Check.model sys sc).Reachable (fun n => constraint n.world) n) :
    sc.Reachable sys constraint n.world := by
  induction h with
  | init hinit hc =>
    rw [Check.mem_model_init.mp hinit] at hc ⊢
    exact .init hc
  | @step n n' ev _ hnext hc ih =>
    obtain ⟨c, hstep, hw'⟩ := World.mem_next_iff.mp (Check.mem_model_next.mp hnext)
    cases ev with
    | input x =>
      obtain ⟨d, hinput, hw'⟩ := hw'
      simp only [hw'] at hc ⊢
      exact .input ih hinput hstep hc
    | output out =>
      simp only [hw'] at hc ⊢
      exact .output ih hstep hc
    | timeout i msg =>
      simp only [hw'] at hc ⊢
      exact .timeout ih hstep hc
    | crash i =>
      obtain ⟨hbudget, hw'⟩ := hw'
      simp only [hw'] at hc ⊢
      exact .crash ih hbudget hstep hc
    | deliver e | duplicate e | drop e | start i =>
      simp only [hw'] at hc ⊢
      exact .internal ih rfl hstep hc

/-- `Scenario.Reachable` is exactly what the checker's model reaches. -/
theorem Scenario.reachable_iff [Enum σ.Id] {sc : Scenario σ D} {constraint : World sys D → Bool}
    {w : World sys D} : sc.Reachable sys constraint w ↔
      (Check.model sys sc).Reachable (fun n => constraint n.world) (.of w) :=
  ⟨Reachable.model, fun h => by simpa using Reachable.of_model h⟩

theorem SysState.Equiv.trafficHash_eq [σ.Inspect] {env : EnvModel σ} {a b : SysState sys}
    (h : SysState.Equiv env a b) : a.trafficHash = b.trafficHash := by
  have hnet := h.net.toPerm.foldl_eq'
    (f := fun (h : UInt64) e => h + mixHash 11 (Hashable.hash e))
    (fun _ _ _ _ z => by rw [UInt64.add_assoc, UInt64.add_comm (mixHash _ _), UInt64.add_assoc]) 0
  have hout := h.outbox.foldl_eq'
    (f := fun (h : UInt64) o => h + mixHash 13 (Hashable.hash o))
    (fun _ _ _ _ z => by rw [UInt64.add_assoc, UInt64.add_comm (mixHash _ _), UInt64.add_assoc]) 0
  simp only [SysState.trafficHash, hnet, hout]

theorem SysState.Equiv.hash_eq [σ.Inspect] [sys.Inspect] {env : EnvModel σ} {a b : SysState sys}
    (h : SysState.Equiv env a b) : a.hash = b.hash := by
  simp only [SysState.hash, h.state, h.up, h.timers, h.trafficHash_eq]

/-- `w` with no messages in flight and no pending outputs. -/
def World.quiet (w : World sys D) : World sys D :=
  { w with state := { w.state with net := [], outbox := [] } }

namespace World.Equiv

variable [BEq D] {env : EnvModel σ} {a b : World sys D} {α : Type}

theorem net_perm (h : World.Equiv env a b) : a.state.net.Perm b.state.net :=
  h.state.net.toPerm

/-- Merged worlds differ only in the order of messages in flight and of pending outputs, and in
the driver's state up to `==`. -/
theorem congr {p : World sys D → α}
    (hp : ∀ (w : World sys D) (net : List (Envelope σ)) (outbox : List σ.Out) (driver : D),
      w.state.net.Perm net → w.state.outbox.Perm outbox → (w.driver == driver) = true →
      p w = p { w with state := { w.state with net, outbox }, driver })
    (h : World.Equiv env a b) : p a = p b := by
  have hb : b = { a with state := { a.state with net := b.state.net, outbox := b.state.outbox },
                         driver := b.driver } := by
    obtain ⟨⟨hstate, hup, htimers, _, _⟩, _, hcrashes⟩ := h
    obtain ⟨⟨_, _, _, _, _⟩, _, _⟩ := a
    obtain ⟨⟨_, _, _, _, _⟩, _, _⟩ := b
    simp only at hstate hup htimers hcrashes
    simp [hstate, hup, htimers, hcrashes]
  rw [hb]
  exact hp a _ _ _ h.net_perm h.state.outbox h.driver

/-- A property that looks at messages in flight and pending outputs only up to their order
cannot tell merged worlds apart. -/
theorem eq_of_perm [LawfulBEq D] {p : World sys D → α}
    (hp : ∀ (w : World sys D) (net : List (Envelope σ)) (outbox : List σ.Out),
      w.state.net.Perm net → w.state.outbox.Perm outbox →
      p w = p { w with state := { w.state with net, outbox } })
    (h : World.Equiv env a b) : p a = p b :=
  h.congr fun w net outbox _ hnet houtbox hdriver =>
    eq_of_beq hdriver ▸ hp w net outbox hnet houtbox

/-- A property that ignores messages in flight and pending outputs cannot tell merged worlds
apart. For a property of actor states, timers, the driver and the crash count, `hp` is
`fun _ => rfl`. -/
theorem eq_of_quiet [LawfulBEq D] {p : World sys D → α} (hp : ∀ w, p w = p w.quiet)
    (h : World.Equiv env a b) : p a = p b := by
  have hquiet : a.quiet = b.quiet := by
    simp only [World.quiet, h.state.state, h.state.up, h.state.timers, eq_of_beq h.driver,
      h.crashes]
  rw [hp a, hp b, hquiet]

end World.Equiv

namespace Check

variable [σ.Inspect] [sys.Inspect] {env : EnvModel σ}

omit [σ.Inspect] [sys.Inspect] in
theorem Slot.same_of [∀ i, BEq (sys.State i)] (a b : SysState sys) (i : σ.Id) :
    (Slot.of a i).same (Slot.of b i) =
      (a.state i == b.state i && a.up i == b.up i && a.timers i == b.timers i) := by
  unfold Slot.same
  split
  · rfl
  · next h => exact absurd rfl h

omit [σ.Inspect] in
theorem Slot.allSame_iff [∀ i, LawfulBEq (sys.State i)] (a b : SysState sys) (l : List σ.Id) :
    Slot.allSame (l.map (Slot.of a)) (l.map (Slot.of b)) = true ↔
      ∀ i ∈ l, a.state i = b.state i ∧ a.up i = b.up i ∧ a.timers i = b.timers i := by
  induction l with
  | nil => simp [Slot.allSame]
  | cons i l ih => simp [Slot.allSame, Slot.same_of, ih, and_assoc]

theorem Node.beq_iff [BEq D] [∀ i, LawfulBEq (sys.State i)] {a b : Node sys env D} :
    (a == b) = true ↔ a.world.crashes = b.world.crashes ∧ (a.world.driver == b.world.driver) = true
      ∧ SysState.Equiv env a.world.state b.world.state := by
  change (a.world.crashes == b.world.crashes && a.world.driver == b.world.driver
    && Slot.allSame a.slots b.slots
    && SysState.netEquiv env a.world.state.net b.world.state.net
    && a.world.state.outbox.isPerm b.world.state.outbox) = true ↔ _
  rw [a.slots_eq, b.slots_eq]
  simp only [Bool.and_eq_true, beq_iff_eq, Slot.allSame_iff, netEquiv_iff, List.isPerm_iff,
    and_assoc]
  constructor
  · rintro ⟨hc, hd, hall, hnet, hout⟩
    exact ⟨hc, hd, funext fun i => (hall i (Enum.complete i)).1,
      funext fun i => (hall i (Enum.complete i)).2.1,
      funext fun i => (hall i (Enum.complete i)).2.2, hnet, hout⟩
  · rintro ⟨hc, hd, h⟩
    exact ⟨hc, hd, fun i _ => ⟨congrFun h.state i, congrFun h.up i, congrFun h.timers i⟩,
      h.net, h.outbox⟩

theorem Node.beq_iff_equiv [BEq D] [∀ i, LawfulBEq (sys.State i)] {a b : Node sys env D} :
    (a == b) = true ↔ World.Equiv env a.world b.world := by
  rw [Node.beq_iff]
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

/-- Nodes the checker merges have the same hash, so each is stored once and the count of
states is the count of worlds up to `World.Equiv`. Soundness does not need this. -/
instance [BEq D] [Hashable D] [LawfulHashable D] [∀ i, LawfulBEq (sys.State i)] :
    LawfulHashable (Node sys env D) where
  hash_eq a b h := by
    obtain ⟨hc, hd, hs⟩ := Node.beq_iff.mp h
    have hslots : a.slots = b.slots := by
      rw [a.slots_eq, b.slots_eq]
      congr 1
      funext i
      simp only [Slot.of, hs.state, hs.up, hs.timers]
    simp only [hash, hslots, hs.trafficHash_eq, hc, LawfulHashable.hash_eq _ _ hd]

variable [BEq D] [Hashable D] [∀ i, LawfulBEq (sys.State i)]

/--
A complete PASS from `Check.system` is sound: every `always` property holds in every world of
the checked instance.

Actor states must compare with `==` exactly when they are equal. On the driver's state `==` need
only be an equivalence that the driver respects. The properties and the constraint must not tell
merged worlds apart.
-/
theorem system_sound_of_respects [EquivBEq D] (sc : Scenario σ D)
    (hdriver : sc.driver.Respects) (props : List (Property (World sys D)))
    (opts : Options (World sys D))
    (hprops : ∀ p ∈ props, ∀ a b, World.Equiv sc.env a b → p.holds a = p.holds b)
    (hconstraint : ∀ a b, World.Equiv sc.env a b → opts.constraint a = opts.constraint b)
    (hfailure : (system sys sc props opts).failure = none)
    (hcomplete : (system sys sc props opts).complete = true)
    {name : String} {p : World sys D → Bool} (hp : .always name p ∈ props)
    {w : World sys D} (hw : sc.Reachable sys opts.constraint w) : p w = true := by
  simp only [system, Report.map, Option.map_eq_none_iff] at hfailure hcomplete
  have hsound := search_sound (s := (.of w : Node sys sc.env D)) (p := fun n => p n.world) ?_
    hfailure hcomplete (List.mem_map.mpr ⟨_, hp, rfl⟩) hw.model
  · simpa using hsound
  refine ⟨fun a b hab l a' ha' => ?_, fun a b hab => hconstraint _ _ (Node.beq_iff_equiv.mp hab),
    fun q hq a b hab => ?_⟩
  · obtain ⟨b', hb', hequiv⟩ := (Node.beq_iff_equiv.mp hab).next hdriver (mem_model_next.mp ha')
    exact ⟨l, .of b', mem_model_next.mpr (by simpa using hb'),
      Node.beq_iff_equiv.mpr (by simpa using hequiv)⟩
  · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    cases q' <;> exact hprops _ hq' _ _ (Node.beq_iff_equiv.mp hab)

/-- `system_sound_of_respects` for a driver whose state compares with `==` exactly when it is
equal, which every driver respects. -/
theorem system_sound [LawfulBEq D] (sc : Scenario σ D) (props : List (Property (World sys D)))
    (opts : Options (World sys D))
    (hprops : ∀ p ∈ props, ∀ a b, World.Equiv sc.env a b → p.holds a = p.holds b)
    (hconstraint : ∀ a b, World.Equiv sc.env a b → opts.constraint a = opts.constraint b)
    (hfailure : (system sys sc props opts).failure = none)
    (hcomplete : (system sys sc props opts).complete = true)
    {name : String} {p : World sys D → Bool} (hp : .always name p ∈ props)
    {w : World sys D} (hw : sc.Reachable sys opts.constraint w) : p w = true :=
  system_sound_of_respects sc (.of_lawful _) props opts hprops hconstraint hfailure hcomplete hp hw

end Check

/-! Reported traces are runs of the semantics. -/

theorem World.step_of_mem_next [Enum σ.Id] {sc : Scenario σ D} {w w' : World sys D}
    {ev : Event σ} (h : (ev, w') ∈ w.next sc) : w.state.step sc.env ev = some w'.state := by
  obtain ⟨c, hstep, hw⟩ := World.mem_next_iff.mp h
  rw [hstep]
  cases ev with
  | input x => obtain ⟨d, _, rfl⟩ := hw; rfl
  | crash i => obtain ⟨_, rfl⟩ := hw; rfl
  | output out | deliver e | duplicate e | drop e | timeout i msg | start i => subst hw; rfl

namespace Check

theorem Trace.last_cons {S L : Type} (s : S) (step : L × S) (rest : List (L × S)) :
    (Trace.mk s (step :: rest)).last = (Trace.mk step.2 rest).last := by
  cases rest with
  | nil => rfl
  | cons next rest =>
    simp only [Trace.last, List.getLast?_cons_cons]
    cases h : (next :: rest).getLast? with
    | none => simp at h
    | some last => rfl

theorem Trace.last_map {S S' L : Type} (f : S → S') (t : Trace S L) :
    (t.map f).last = f t.last := by
  obtain ⟨init, steps⟩ := t
  induction steps generalizing init with
  | nil => rfl
  | cons step rest ih =>
    have := ih step.2
    simp only [Trace.map, List.map_cons] at this ⊢
    rw [Trace.last_cons, Trace.last_cons]
    exact this

theorem Trace.labels_map {S S' L : Type} (f : S → S') (t : Trace S L) :
    (t.map f).labels = t.labels := by
  simp [Trace.map, Trace.labels, List.map_map, Function.comp_def]

theorem run_of_steps [Enum σ.Id] {sc : Scenario σ D} (n : Node sys sc.env D)
    (steps : List (Event σ × Node sys sc.env D)) (h : (model sys sc).Steps n steps) :
    n.world.state.run sc.env (steps.map (·.1)) = some (Trace.mk n steps).last.world.state := by
  induction steps generalizing n with
  | nil => rfl
  | cons step rest ih =>
    obtain ⟨hmem, hrest⟩ := h
    rw [Trace.last_cons, List.map_cons, SysState.run,
      World.step_of_mem_next (mem_model_next.mp hmem)]
    exact ih _ hrest

/--
A violation `Check.system` reports is real: the events of its trace are a run of the semantics
from the initial state, and the named property is false in the state they reach. Nothing is
assumed about the equality or the hashes used to merge states.
-/
theorem system_violated [σ.Inspect] [sys.Inspect] [BEq D] [Hashable D] (sc : Scenario σ D)
    (props : List (Property (World sys D))) (opts : Options (World sys D)) {name : String}
    {t : Trace (World sys D) (Event σ)}
    (h : (system sys sc props opts).failure = some (.violated name t)) :
    (SysState.init sys sc.env).run sc.env t.labels = some t.last.state ∧
      ∃ p, .always name p ∈ props ∧ p t.last = false := by
  simp only [system, Report.map, Option.map_eq_some_iff] at h
  obtain ⟨failure, hsearch, hmap⟩ := h
  cases failure with
  | deadlock t₀ => simp at hmap
  | unreached names => simp at hmap
  | violated name₀ t₀ =>
    simp only [Failure.violated.injEq] at hmap
    obtain ⟨rfl, rfl⟩ := hmap
    obtain ⟨⟨hinit, hsteps⟩, _, p', hp', hfalse⟩ := search_violated hsearch
    obtain ⟨prop, hprop, hprop'⟩ := List.mem_map.mp hp'
    rw [Trace.last_map, Trace.labels_map]
    have hstart : t₀.init.world.state = SysState.init sys sc.env := by
      rw [mem_model_init.mp hinit]
      rfl
    refine ⟨?_, ?_⟩
    · rw [← hstart]
      exact run_of_steps t₀.init t₀.steps hsteps
    · cases prop with
      | sometimes n q => simp at hprop'
      | always n q =>
        simp only [Property.always.injEq] at hprop'
        obtain ⟨rfl, rfl⟩ := hprop'
        exact ⟨q, hprop, hfalse⟩

end Check

/-! The runs of an instance, with their events: what a refinement check is about. -/

/-- `Scenario.Reachable` with the events kept: the runs a check covers, each with the world it
ends in. -/
inductive Scenario.Run [Enum σ.Id] (sys : System σ) (sc : Scenario σ D)
    (constraint : World sys D → Bool) : List (Event σ) → World sys D → Prop
  | init : constraint (World.init sys sc) = true → Run sys sc constraint [] (World.init sys sc)
  | step {events : List (Event σ)} {w w' : World sys D} {ev : Event σ} :
    Run sys sc constraint events w → (ev, w') ∈ w.next sc → constraint w' = true →
    Run sys sc constraint (events ++ [ev]) w'

namespace Scenario

variable [Enum σ.Id] {sc : Scenario σ D} {constraint : World sys D → Bool} {w : World sys D}
  {events : List (Event σ)}

theorem Run.reachable (h : sc.Run sys constraint events w) : sc.Reachable sys constraint w := by
  induction h with
  | init hc => exact .init hc
  | step _ hnext hc ih =>
    simpa using Reachable.of_model (Reachable.model_step ih.model hnext hc)

/-- The events of a run are a run of the semantics from the initial state. -/
theorem Run.run (h : sc.Run sys constraint events w) :
    (SysState.init sys sc.env).run sc.env events = some w.state := by
  induction h with
  | init => rfl
  | step _ hnext _ ih =>
    rw [SysState.run_append, ih]
    simp [SysState.run, World.step_of_mem_next hnext]

theorem reachable_iff_exists_run :
    sc.Reachable sys constraint w ↔ ∃ events, sc.Run sys constraint events w := by
  refine ⟨fun h => ?_, fun ⟨_, h⟩ => h.reachable⟩
  suffices hmodel : ∀ n, (Check.model sys sc).Reachable (fun n => constraint n.world) n →
      ∃ events, sc.Run sys constraint events n.world from by simpa using hmodel (.of w) h.model
  intro n hn
  induction hn with
  | init hinit hc =>
    rw [Check.mem_model_init.mp hinit] at hc ⊢
    exact ⟨[], .init hc⟩
  | step _ hnext hc ih =>
    obtain ⟨events, hrun⟩ := ih
    exact ⟨_, .step hrun (Check.mem_model_next.mp hnext) hc⟩

end Scenario

end Lanes
