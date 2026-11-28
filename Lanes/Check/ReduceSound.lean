/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Check.Reduce
public import Lanes.Check.SystemSound

/-!
# A pass of a reduced model is a pass of the model

`Model.Reduction` is what `canon` must satisfy: each state is related to its representative by
`rel`, an equivalence that the constraint and the properties respect, and a simulation of the
model. Then the reduced model and the model reach the same states up to `rel`
(`Model.Reduction.reachable`, `Model.Reduction.of_reduced`), and:

- `search_reduce_sound`: a complete pass of the reduced search means every `always` property
  holds in every reachable state of the model. A refinement check (`Check.refines`) is an
  `always` property, so it is covered.
- `search_reduce_deadlock_free`: with deadlock checking on, no reachable state of the model is
  stuck.
- `search_reduce_violated`, `search_reduce_deadlock`, `search_reduce_witness`: what the reduced
  search reports is true of a reachable state of the model, related to the one reported.
- `search_reduce_unreached`: a `sometimes` property reported unreached is false in every
  reachable state of the model.
- `systemReduced_sound`: the same for `Check.systemReduced`, given a `World.Reduction`.
-/

@[expose] public section

namespace Lanes.Check

variable {S L : Type}

/-- `canon` is a sound reduction of `m` under `rel`: each state is related to its
representative, `rel` is an equivalence that the constraint and the properties respect, and
whatever step one state takes, a related state takes a step to a related state. -/
structure Model.Reduction (m : Model S L) (constraint : S → Bool) (props : List (Property S))
    (canon : S → S) (rel : S → S → Prop) : Prop where
  canon : ∀ s, rel s (canon s)
  symm : ∀ {a b}, rel a b → rel b a
  trans : ∀ {a b c}, rel a b → rel b c → rel a c
  next : ∀ {a b}, rel a b → ∀ l a', (l, a') ∈ m.next a →
    ∃ l' b', (l', b') ∈ m.next b ∧ rel a' b'
  constraint : ∀ {a b}, rel a b → constraint a = constraint b
  prop : ∀ p ∈ props, ∀ {a b}, rel a b → p.holds a = p.holds b

namespace Model

variable {m : Model S L} {constraint : S → Bool} {props : List (Property S)} {canon : S → S}
  {rel : S → S → Prop}

theorem mem_reduce_init {s : S} : s ∈ (m.reduce canon).init ↔ ∃ a ∈ m.init, canon a = s :=
  List.mem_map

theorem mem_reduce_next {s t : S} {l : L} :
    (l, t) ∈ (m.reduce canon).next s ↔ ∃ u, (l, u) ∈ m.next s ∧ canon u = t := by
  simp only [reduce, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨l', u⟩, hu, rfl, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(l, u), hu, rfl, rfl⟩

/-- Every reachable state of the model is related to a reachable state of the reduced model. -/
theorem Reduction.reachable (h : m.Reduction constraint props canon rel) {a : S}
    (ha : m.Reachable constraint a) : ∃ b, (m.reduce canon).Reachable constraint b ∧ rel a b := by
  induction ha with
  | init ha hc =>
    exact ⟨_, .init (mem_reduce_init.mpr ⟨_, ha, rfl⟩) (h.constraint (h.canon _) ▸ hc),
      h.canon _⟩
  | @step a a' l _ hstep hc ih =>
    obtain ⟨b, hb, hab⟩ := ih
    obtain ⟨l', b', hb', hab'⟩ := h.next hab l a' hstep
    have hrel := h.trans hab' (h.canon b')
    exact ⟨canon b', .step hb (mem_reduce_next.mpr ⟨b', hb', rfl⟩) (h.constraint hrel ▸ hc), hrel⟩

/-- Every reachable state of the reduced model is related to a reachable state of the model. -/
theorem Reduction.of_reduced (h : m.Reduction constraint props canon rel) {b : S}
    (hb : (m.reduce canon).Reachable constraint b) : ∃ a, m.Reachable constraint a ∧ rel b a := by
  induction hb with
  | init hb hc =>
    obtain ⟨a, ha, rfl⟩ := mem_reduce_init.mp hb
    exact ⟨a, .init ha (h.constraint (h.canon a) ▸ hc), h.symm (h.canon a)⟩
  | @step b b' l _ hstep hc ih =>
    obtain ⟨a, ha, hba⟩ := ih
    obtain ⟨u, hu, rfl⟩ := mem_reduce_next.mp hstep
    obtain ⟨l', a', ha', hua'⟩ := h.next hba l u hu
    have hrel := h.trans (h.symm (h.canon u)) hua'
    exact ⟨a', .step ha ha' ((h.constraint hrel).symm ▸ hc), hrel⟩

/-- The reduced model respects `==` when the model does and `canon` keeps `==` states `==`. -/
theorem Respects.reduce [BEq S] (hm : m.Respects constraint props)
    (hcanon : ∀ a b, (a == b) = true → (canon a == canon b) = true) :
    (m.reduce canon).Respects constraint props where
  next a b hab l a' ha' := by
    obtain ⟨u, hu, rfl⟩ := mem_reduce_next.mp ha'
    obtain ⟨l', b', hb', hub'⟩ := hm.next a b hab l u hu
    exact ⟨l', canon b', mem_reduce_next.mpr ⟨b', hb', rfl⟩, hcanon _ _ hub'⟩
  constraint := hm.constraint
  prop := hm.prop

end Model

variable [BEq S] [Hashable S] {m : Model S L} {props : List (Property S)} {opts : Options S}
  {labelName : L → String} {actions : List String} {canon : S → S} {rel : S → S → Prop}

/-- A complete pass of the reduced search is a pass of the model: every `always` property holds
in every state the model reaches within the constraint. -/
theorem search_reduce_sound [EquivBEq S] (h : m.Reduction opts.constraint props canon rel)
    (hm : (m.reduce canon).Respects opts.constraint props)
    (hfailure : (search (m.reduce canon) props opts labelName actions).failure = none)
    (hcomplete : (search (m.reduce canon) props opts labelName actions).complete = true)
    {name : String} {p : S → Bool} (hp : .always name p ∈ props) {s : S}
    (hs : m.Reachable opts.constraint s) : p s = true := by
  obtain ⟨b, hb, hsb⟩ := h.reachable hs
  rw [show p s = p b from h.prop _ hp hsb]
  exact search_sound hm hfailure hcomplete hp hb

/-- A violation the reduced search reports is one of the model: some state it reaches within
the constraint, related to the one reported, violates the property. -/
theorem search_reduce_violated (h : m.Reduction opts.constraint props canon rel) {name : String}
    {t : Trace S L}
    (hv : (search (m.reduce canon) props opts labelName actions).failure = some (.violated name t)) :
    ∃ s, m.Reachable opts.constraint s ∧ rel t.last s ∧
      ∃ p, .always name p ∈ props ∧ p s = false := by
  obtain ⟨-, hreach, p, hp, hfalse⟩ := search_violated hv
  obtain ⟨s, hs, hts⟩ := h.of_reduced hreach
  exact ⟨s, hs, hts, p, hp, (show p s = p t.last from (h.prop _ hp hts).symm) ▸ hfalse⟩

/-- A witness the reduced search reports is one of the model. -/
theorem search_reduce_witness (h : m.Reduction opts.constraint props canon rel) {name : String}
    {t : Trace S L} (hw : (name, t) ∈ (search (m.reduce canon) props opts labelName actions).witnesses) :
    ∃ s, m.Reachable opts.constraint s ∧ rel t.last s ∧
      ∃ p, .sometimes name p ∈ props ∧ p s = true := by
  obtain ⟨-, hreach, p, hp, htrue⟩ := search_witness hw
  obtain ⟨s, hs, hts⟩ := h.of_reduced hreach
  exact ⟨s, hs, hts, p, hp, (show p s = p t.last from (h.prop _ hp hts).symm) ▸ htrue⟩

/-- A complete reduced search that reports `sometimes` properties unreached names one that is
false in every state the model reaches within the constraint. -/
theorem search_reduce_unreached [EquivBEq S] (h : m.Reduction opts.constraint props canon rel)
    (hm : (m.reduce canon).Respects opts.constraint props) {names : List String}
    (hfailure : (search (m.reduce canon) props opts labelName actions).failure =
      some (.unreached names))
    (hcomplete : (search (m.reduce canon) props opts labelName actions).complete = true) :
    ∃ name p, name ∈ names ∧ .sometimes name p ∈ props ∧
      ∀ s, m.Reachable opts.constraint s → p s = false := by
  obtain ⟨name, p, hname, hp, hfalse⟩ := search_unreached_exists hm hfailure hcomplete
  refine ⟨name, p, hname, hp, fun s hs => ?_⟩
  obtain ⟨b, hb, hsb⟩ := h.reachable hs
  rw [show p s = p b from h.prop _ hp hsb]
  exact hfalse b hb

/-- A deadlock the reduced search reports is one of the model: a state it reaches within the
constraint, not terminal, whose every successor is outside the constraint. -/
theorem search_reduce_deadlock (h : m.Reduction opts.constraint props canon rel)
    (hterminal : ∀ {a b}, rel a b → opts.terminal a = opts.terminal b) {t : Trace S L}
    (hd : (search (m.reduce canon) props opts labelName actions).failure = some (.deadlock t)) :
    ∃ s, m.Reachable opts.constraint s ∧ rel t.last s ∧
      (∀ l s', (l, s') ∈ m.next s → opts.constraint s' = false) ∧ opts.terminal s = false := by
  obtain ⟨-, hreach, hstuck, hnot⟩ := search_deadlock hd
  obtain ⟨s, hs, hts⟩ := h.of_reduced hreach
  refine ⟨s, hs, hts, fun l s' hs' => ?_, (hterminal hts).symm.trans hnot⟩
  obtain ⟨l', u, hu, hs'u⟩ := h.next (h.symm hts) l s' hs'
  rw [h.constraint (h.trans hs'u (h.canon u))]
  exact hstuck l' _ (Model.mem_reduce_next.mpr ⟨u, hu, rfl⟩)

/-- A complete pass of the reduced search with deadlock checking on leaves no deadlock in the
model: every state it reaches within the constraint is terminal or has a successor within the
constraint. -/
theorem search_reduce_deadlock_free [EquivBEq S] (h : m.Reduction opts.constraint props canon rel)
    (hm : (m.reduce canon).Respects opts.constraint props)
    (hterminal : ∀ {a b}, rel a b → opts.terminal a = opts.terminal b)
    (hbeq : ∀ a b, (a == b) = true → opts.terminal a = opts.terminal b)
    (hcheck : opts.checkDeadlock = true)
    (hfailure : (search (m.reduce canon) props opts labelName actions).failure = none)
    (hcomplete : (search (m.reduce canon) props opts labelName actions).complete = true) {s : S}
    (hs : m.Reachable opts.constraint s) :
    opts.terminal s = true ∨ ∃ l s', (l, s') ∈ m.next s ∧ opts.constraint s' = true := by
  obtain ⟨b, hb, hsb⟩ := h.reachable hs
  rcases search_deadlock_free hm hbeq hcheck hfailure hcomplete hb with hterm | ⟨l, t, ht, hc⟩
  · exact .inl ((hterminal hsb).trans hterm)
  · obtain ⟨u, hu, rfl⟩ := Model.mem_reduce_next.mp ht
    obtain ⟨l', s', hs', hus'⟩ := h.next (h.symm hsb) l u hu
    exact .inr ⟨l', s', hs', (h.constraint (h.trans (h.symm (h.canon u)) hus')) ▸ hc⟩

/-! `Check.systemReduced` -/

variable {σ : Signature} {sys : System σ} {D : Type}

/-- `canon` is a sound reduction of a scenario's worlds under `rel`: `Model.Reduction` stated of
`World.next`. -/
structure World.Reduction [Enum σ.Id] (sc : Scenario σ D) (constraint : World sys D → Bool)
    (props : List (Property (World sys D))) (canon : World sys D → World sys D)
    (rel : World sys D → World sys D → Prop) : Prop where
  canon : ∀ w, rel w (canon w)
  symm : ∀ {a b}, rel a b → rel b a
  trans : ∀ {a b c}, rel a b → rel b c → rel a c
  next : ∀ {a b}, rel a b → ∀ ev a', (ev, a') ∈ a.next sc →
    ∃ ev' b', (ev', b') ∈ b.next sc ∧ rel a' b'
  constraint : ∀ {a b}, rel a b → constraint a = constraint b
  prop : ∀ p ∈ props, ∀ {a b}, rel a b → p.holds a = p.holds b

theorem World.Reduction.model [Enum σ.Id] {sc : Scenario σ D}
    {constraint : World sys D → Bool} {props : List (Property (World sys D))}
    {canon : World sys D → World sys D} {rel : World sys D → World sys D → Prop}
    (h : World.Reduction sc constraint props canon rel) :
    (model sys sc).Reduction (fun n => constraint n.world) (Node.props props)
      (fun n => .of (canon n.world)) (fun a b => rel a.world b.world) where
  canon n := by simpa using h.canon n.world
  symm := h.symm
  trans := h.trans
  next {a b} hab l a' ha' := by
    obtain ⟨ev', b', hb', hab'⟩ := h.next hab l a'.world (mem_model_next.mp ha')
    exact ⟨ev', .of b', mem_model_next.mpr (by simpa using hb'), by simpa using hab'⟩
  constraint hab := h.constraint hab
  prop p hp {a b} hab := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    cases q <;> exact h.prop _ hq hab

/-- A relation on the driver's states that the driver cannot see: related states offer the same
inputs, to related states, and stay related after an output, a timer or a delivery.
`Driver.Respects` is the case of `==`. -/
structure _root_.Lanes.Driver.Simulation (driver : Driver σ D) (R : D → D → Prop) : Prop where
  inputs : ∀ a b, R a b → ∀ x a', (x, a') ∈ driver.inputs a →
    ∃ b', (x, b') ∈ driver.inputs b ∧ R a' b'
  observe : ∀ a b out, R a b → R (driver.observe a out) (driver.observe b out)
  timeout : ∀ a b i msg, R a b → R (driver.timeout a i msg) (driver.timeout b i msg)
  deliver : ∀ a b i msg, R a b → R (driver.deliver a i msg) (driver.deliver b i msg)

/-- Worlds that differ only in the driver's state, by a relation the driver cannot see. -/
def World.SameUpTo (R : D → D → Prop) (a b : World sys D) : Prop :=
  a.state = b.state ∧ R a.driver b.driver ∧ a.crashes = b.crashes ∧ a.restarts = b.restarts

theorem World.SameUpTo.next [Enum σ.Id] {sc : Scenario σ D} {R : D → D → Prop}
    (hsim : sc.driver.Simulation R) {a b a' : World sys D} {ev : Event σ}
    (h : World.SameUpTo R a b) (hmem : (ev, a') ∈ a.next sc) :
    ∃ b', (ev, b') ∈ b.next sc ∧ World.SameUpTo R a' b' := by
  obtain ⟨hstate, hdriver, hcrashes, hrestarts⟩ := h
  obtain ⟨c, hstep, hw'⟩ := World.mem_next_iff.mp hmem
  rw [hstate] at hstep
  cases ev with
  | input x =>
    obtain ⟨d, hinput, rfl⟩ := hw'
    obtain ⟨d', hinput', hd⟩ := hsim.inputs _ _ hdriver x d hinput
    exact ⟨{ b with state := c, driver := d' }, World.mem_next_iff.mpr ⟨c, hstep, d', hinput', rfl⟩,
      rfl, hd, hcrashes, hrestarts⟩
  | output out =>
    subst hw'
    exact ⟨_, World.mem_next_iff.mpr ⟨c, hstep, rfl⟩, rfl, hsim.observe _ _ out hdriver, hcrashes,
      hrestarts⟩
  | timeout i msg =>
    subst hw'
    exact ⟨_, World.mem_next_iff.mpr ⟨c, hstep, rfl⟩, rfl, hsim.timeout _ _ i msg hdriver,
      hcrashes, hrestarts⟩
  | deliver e =>
    subst hw'
    exact ⟨_, World.mem_next_iff.mpr ⟨c, hstep, rfl⟩, rfl,
      hsim.deliver _ _ e.dst e.msg hdriver, hcrashes, hrestarts⟩
  | duplicate e =>
    subst hw'
    exact ⟨_, World.mem_next_iff.mpr ⟨c, hstep, rfl⟩, rfl,
      hsim.deliver _ _ e.dst e.msg hdriver, hcrashes, hrestarts⟩
  | crash i =>
    obtain ⟨hbudget, rfl⟩ := hw'
    exact ⟨_, World.mem_next_iff.mpr ⟨c, hstep, hcrashes ▸ hbudget, rfl⟩, rfl, hdriver,
      by simp [hcrashes], hrestarts⟩
  | restart =>
    obtain ⟨hbudget, rfl⟩ := hw'
    exact ⟨_, World.mem_next_iff.mpr ⟨c, hstep, hrestarts ▸ hbudget, rfl⟩, rfl, hdriver,
      hcrashes, by simp [hrestarts]⟩
  | tick m =>
    obtain ⟨hm, hlater, rfl⟩ := hw'
    exact ⟨_, World.mem_next_iff.mpr ⟨c, hstep, hm, hstate ▸ hlater, rfl⟩, rfl, hdriver, hcrashes,
      hrestarts⟩
  | drop e | start i =>
    subst hw'
    exact ⟨_, World.mem_next_iff.mpr ⟨c, hstep, rfl⟩, rfl, hdriver, hcrashes, hrestarts⟩

/-- Putting the driver's state in a canonical form is a reduction, when the form is related to
the state by an equivalence the driver, the constraint and the properties cannot see. A list
the driver uses as a set, kept sorted, is the usual case. -/
theorem World.Reduction.ofDriver [Enum σ.Id] {sc : Scenario σ D}
    {constraint : World sys D → Bool} {props : List (Property (World sys D))} (canon : D → D)
    {R : D → D → Prop} (hsim : sc.driver.Simulation R) (hcanon : ∀ d, R d (canon d))
    (hsymm : ∀ {a b}, R a b → R b a) (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (hconstraint : ∀ {a b}, World.SameUpTo R a b → constraint a = constraint b)
    (hprops : ∀ p ∈ props, ∀ {a b}, World.SameUpTo R a b → p.holds a = p.holds b) :
    World.Reduction sc constraint props (fun w => { w with driver := canon w.driver })
      (World.SameUpTo R) where
  canon w := ⟨rfl, hcanon w.driver, rfl, rfl⟩
  symm h := ⟨h.1.symm, hsymm h.2.1, h.2.2.1.symm, h.2.2.2.symm⟩
  trans h h' := ⟨h.1.trans h'.1, htrans h.2.1 h'.2.1, h.2.2.1.trans h'.2.2.1,
    h.2.2.2.trans h'.2.2.2⟩
  next h ev _ hmem := by
    obtain ⟨b', hb', hrel⟩ := h.next hsim hmem
    exact ⟨ev, b', hb', hrel⟩
  constraint := hconstraint
  prop := hprops

variable [σ.Inspect] [sys.Inspect] [BEq D] [Hashable D] [∀ i, LawfulBEq (sys.State i)]

/--
A complete PASS from `Check.systemReduced` is a PASS of `Check.system`: every `always` property
holds in every world of the checked instance.

Besides what `system_sound_of_respects` asks, `canon` must be a `World.Reduction` and keep
equivalent worlds equivalent.
-/
theorem systemReduced_sound [EquivBEq D] (sc : Scenario σ D) (hdriver : sc.driver.Respects)
    (canon : World sys D → World sys D) {rel : World sys D → World sys D → Prop}
    (props : List (Property (World sys D))) (opts : Options (World sys D))
    (hred : World.Reduction sc opts.constraint props canon rel)
    (hcanon : ∀ a b, World.Equiv sc.env a b → World.Equiv sc.env (canon a) (canon b))
    (hprops : ∀ p ∈ props, ∀ a b, World.Equiv sc.env a b → p.holds a = p.holds b)
    (hconstraint : ∀ a b, World.Equiv sc.env a b → opts.constraint a = opts.constraint b)
    (hfailure : (systemReduced sys sc canon props opts).failure = none)
    (hcomplete : (systemReduced sys sc canon props opts).complete = true)
    {name : String} {p : World sys D → Bool} (hp : .always name p ∈ props)
    {w : World sys D} (hw : sc.Reachable sys opts.constraint w) : p w = true := by
  simp only [systemReduced, Report.map, Option.map_eq_none_iff] at hfailure hcomplete
  have hm := (model_respects sc hdriver props opts hprops hconstraint).reduce
    (canon := fun n => .of (canon n.world)) fun a b hab =>
      Node.beq_iff_equiv.mpr (by simpa using hcanon _ _ (Node.beq_iff_equiv.mp hab))
  have hsound := search_reduce_sound (s := (.of w : Node sys sc.env D))
    (p := fun n => p n.world) hred.model hm hfailure hcomplete (List.mem_map.mpr ⟨_, hp, rfl⟩)
    hw.model
  simpa using hsound

end Lanes.Check
