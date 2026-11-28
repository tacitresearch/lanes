/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Semantics.Service

/-!
# A system that implements a service has a sequential history

`System.Implements` is a weak simulation, so each run of the system has a run of `Service.spec`
with the same inputs and outputs. This file reads that run as a sequential history: one list of
acts of the service, each an input taking effect or a deadline passing, played one at a time
from `init`. Every output the system hands over is an output of one act of the list, and an
input takes effect only after it arrives. So a statement proved of the service's functions and
every sequence of them holds of the outputs of every run of the system.

The history respects real time: an output handed over at position `i` of a run comes from an act
before `cut (i + 1)`, and an input that arrives at position `p` takes effect at `cut p` or later,
where `cut` is monotone. So if an output is handed over before an input arrives, what that output
answered took effect before the input did. This is the order linearizability asks for.
A deadline passes in the history exactly in the block `cut p` to `cut (p + 1)` of the position
`p` at which the run shows it, so what the service's functions say between two deadlines holds
between the positions at which they pass.

## Main definitions

- `Service.Act`, `Service.play`: an act of a service, and the value after a list of them.
- `Service.Produces`: an output is one of the act at a position of a history.

## Main statements

- `System.Implements.history`: every run of a system that implements a service has a history
  that explains its outputs, in real-time order.
- `System.Implements.produced`: so every output is that of an input that arrived before it, or of
  a deadline, from a value the service reaches.
-/

@[expose] public section

namespace Lanes

variable {In Out S T : Type}

namespace Service

/-- What takes effect in the sequential service: an input, or a deadline passing. -/
inductive Act (In T : Type) where
  /-- An input takes effect. -/
  | take (x : In)
  /-- A deadline passes. -/
  | fire (t : T)

/-- What one act does to a value: the new value and the outputs. -/
def act (svc : Service In Out S T) (v : S) : Act In T → S × List Out
  | .take x => svc.step v x
  | .fire t => svc.fire v t

/-- The value after a list of acts, played one at a time from `v`. -/
def play (svc : Service In Out S T) (v : S) (acts : List (Act In T)) : S :=
  acts.foldl (fun v a => (svc.act v a).1) v

/-- `o` is an output of the act at position `k` of `acts`, played from `init`. -/
def Produces (svc : Service In Out S T) (acts : List (Act In T)) (k : Nat) (o : Out) : Prop :=
  ∃ a, acts[k]? = some a ∧ o ∈ (svc.act (svc.play svc.init (acts.take k)) a).2

variable {svc : Service In Out S T}

/-- Playing one act more is that act on the value before it. -/
theorem play_concat (v : S) (acts : List (Act In T)) (a : Act In T) :
    svc.play v (acts ++ [a]) = (svc.act (svc.play v acts) a).1 := by
  simp [play, List.foldl_append]

/-- Playing two lists of acts is playing the second from where the first ends. -/
theorem play_append (v : S) (acts more : List (Act In T)) :
    svc.play v (acts ++ more) = svc.play (svc.play v acts) more := by
  simp [play, List.foldl_append]

/-- What an act of a history produces, it produces in any longer history. -/
theorem Produces.append {acts : List (Act In T)} {k : Nat} {o : Out} (h : svc.Produces acts k o)
    (more : List (Act In T)) : svc.Produces (acts ++ more) k o := by
  obtain ⟨a, ha, ho⟩ := h
  have hk : k < acts.length := (List.getElem?_eq_some_iff.mp ha).1
  refine ⟨a, by rw [List.getElem?_append_left hk, ha], ?_⟩
  rwa [List.take_append_of_le_length (Nat.le_of_lt hk)]

/-- An output of the last act of a history is produced at its position. -/
theorem produces_last {acts : List (Act In T)} {a : Act In T} {o : Out}
    (h : o ∈ (svc.act (svc.play svc.init acts) a).2) : svc.Produces (acts ++ [a]) acts.length o :=
  ⟨a, by simp, by simpa using h⟩

/-- A state of `Service.spec` explained by a history `acts`: its value is the history played,
every pending input is one of `A`, and every output waiting is produced by an act of the
history. -/
structure Follows (svc : Service In Out S T) (A : In → Prop) (acts : List (Act In T))
    (a : Abs In Out S) : Prop where
  /-- The value is the history played from `init`. -/
  value : a.value = svc.play svc.init acts
  /-- Every pending input is one of `A`. -/
  pending : ∀ x ∈ a.pending, A x
  /-- Every output waiting is produced by an act of the history. -/
  outbox : ∀ o ∈ a.outbox, ∃ k, svc.Produces acts k o

namespace Follows

variable {A : In → Prop} {acts : List (Act In T)} {a b : Abs In Out S}

/-- The initial state is explained by the empty history. -/
theorem init : svc.Follows A [] ⟨svc.init, 0, 0⟩ :=
  ⟨rfl, by simp, by simp⟩

/-- A weaker set of inputs explains what a stronger one does. -/
theorem mono (h : svc.Follows A acts a) {A' : In → Prop} (hA : ∀ x, A x → A' x) :
    svc.Follows A' acts a :=
  ⟨h.value, fun x hx => hA x (h.pending x hx), h.outbox⟩

/-- An input that takes effect is one more act of the history. -/
theorem take [DecidableEq In] (h : svc.Follows A acts a) {x : In} (_ : x ∈ a.pending) :
    svc.Follows A (acts ++ [.take x])
      ⟨(svc.step a.value x).1, a.pending.erase x, a.outbox + (svc.step a.value x).2⟩ := by
  refine ⟨?_, fun y hy => h.pending y (Bag.mem_of_mem_erase hy), fun o ho => ?_⟩
  · rw [play_concat, ← h.value]
    rfl
  · rcases Bag.mem_add.mp ho with ho | ho
    · obtain ⟨k, hk⟩ := h.outbox o ho
      exact ⟨k, hk.append _⟩
    · refine ⟨acts.length, produces_last ?_⟩
      rw [← h.value]
      exact ho

/-- A deadline that passes is one more act of the history. -/
theorem fire (h : svc.Follows A acts a) (t : T) :
    svc.Follows A (acts ++ [.fire t])
      ⟨(svc.fire a.value t).1, a.pending, a.outbox + (svc.fire a.value t).2⟩ := by
  refine ⟨?_, h.pending, fun o ho => ?_⟩
  · rw [play_concat, ← h.value]
    rfl
  · rcases Bag.mem_add.mp ho with ho | ho
    · obtain ⟨k, hk⟩ := h.outbox o ho
      exact ⟨k, hk.append _⟩
    · refine ⟨acts.length, produces_last ?_⟩
      rw [← h.value]
      exact ho

variable [DecidableEq In] [DecidableEq Out]

/-- Internal steps of the spec take pending inputs effect, each one more act of the history. -/
theorem τSTr (h : svc.Follows A acts a) (htr : svc.spec.lts.τSTr a b) :
    ∃ E, (∀ x, .take x ∈ E → A x) ∧ (∀ t, .fire t ∉ E) ∧ svc.Follows A (acts ++ E) b := by
  induction htr with
  | refl => exact ⟨[], by simp, by simp, by simpa using h⟩
  | tail _ hstep ih =>
    obtain ⟨E, hE, hF, h'⟩ := ih
    obtain ⟨x, hx, rfl⟩ := hstep
    refine ⟨E ++ [.take x], fun y hy => ?_, fun t ht => ?_, by simpa using h'.take hx⟩
    · rcases List.mem_append.mp hy with hy | hy
      · exact hE y hy
      · cases List.mem_singleton.mp hy
        exact h'.pending x hx
    · rcases List.mem_append.mp ht with ht | ht
      · exact hF t ht
      · cases List.mem_singleton.mp ht

/-- One step of the spec, internal or visible: an internal step or a deadline is one more act;
an input arriving is one more input explained; an output handed over is produced. -/
theorem tr (h : svc.Follows A acts a) {μ : Option (Visible In Out T)}
    (htr : svc.spec.Tr a μ b) :
    ∃ E, (∀ x, .take x ∈ E → A x) ∧
      svc.Follows (fun y => A y ∨ μ = some (.input y)) (acts ++ E) b ∧
      (∀ o, μ = some (.output o) → ∃ k, svc.Produces (acts ++ E) k o) ∧
      ∀ t, .fire t ∈ E ↔ μ = some (.fire t) := by
  rcases μ with _ | (x | o | t)
  · obtain ⟨x, hx, rfl⟩ := htr
    refine ⟨[.take x], ?_, (h.take hx).mono fun y hy => .inl hy, by simp, by simp⟩
    intro y hy
    cases List.mem_singleton.mp hy
    exact h.pending x hx
  · have hb : b = { a with pending := x ::ₘ a.pending } := htr
    subst hb
    refine ⟨[], by simp, ⟨by simpa using h.value, fun y hy => ?_, by simpa using h.outbox⟩,
      by simp, by simp⟩
    rcases Bag.mem_cons.mp hy with rfl | hy
    · exact .inr rfl
    · exact .inl (h.pending y hy)
  · obtain ⟨ho, hb⟩ : o ∈ a.outbox ∧ b = { a with outbox := a.outbox.erase o } := htr
    subst hb
    refine ⟨[], by simp, ⟨by simpa using h.value, fun y hy => .inl (h.pending y hy),
      fun o' ho' => by simpa using h.outbox o' (Bag.mem_of_mem_erase ho')⟩, ?_, by simp⟩
    rintro o' ⟨⟩
    simpa using h.outbox o ho
  · obtain ⟨-, hb⟩ : svc.armed a.value t = true ∧
        b = ⟨(svc.fire a.value t).1, a.pending, a.outbox + (svc.fire a.value t).2⟩ := htr
    subst hb
    exact ⟨[.fire t], by simp, (h.fire t).mono fun y hy => .inl hy, by simp,
      fun _ => by simp [eq_comm]⟩

/-- A saturated step of the spec: internal steps, one step, internal steps. -/
theorem sTr (h : svc.Follows A acts a) {μ : Option (Visible In Out T)}
    (htr : svc.spec.lts.STr a μ b) :
    ∃ E, (∀ x, .take x ∈ E → A x ∨ μ = some (.input x)) ∧
      svc.Follows (fun y => A y ∨ μ = some (.input y)) (acts ++ E) b ∧
      (∀ o, μ = some (.output o) → ∃ k, svc.Produces (acts ++ E) k o) ∧
      ∀ t, .fire t ∈ E ↔ μ = some (.fire t) := by
  cases htr with
  | refl =>
    refine ⟨[], by simp, ?_, by rintro o ⟨⟩, fun t => by simp⟩
    simpa using h.mono (A' := fun y => A y ∨ (HasTau.τ : Option (Visible In Out T)) = some (.input y))
      fun y hy => Or.inl hy
  | tr h₁ h₂ h₃ =>
    obtain ⟨E₁, hE₁, hF₁, f₁⟩ := h.τSTr h₁
    obtain ⟨E₂, hE₂, f₂, ho, hF₂⟩ := f₁.tr h₂
    obtain ⟨E₃, hE₃, hF₃, f₃⟩ := f₂.τSTr h₃
    refine ⟨E₁ ++ E₂ ++ E₃, fun x hx => ?_, by simpa using f₃, fun o hμ => ?_, fun t => ?_⟩
    · rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact .inl (hE₁ x hx)
        · exact .inl (hE₂ x hx)
      · exact hE₃ x hx
    · obtain ⟨k, hk⟩ := ho o hμ
      exact ⟨k, by simpa using hk.append E₃⟩
    · simp only [List.mem_append, hF₁ t, hF₃ t, false_or, or_false, hF₂ t]

end Follows

end Service

variable {σ : Signature} {sys : System σ} {env : EnvModel σ}
  {svc : Service σ.In σ.Out S T} {deadlines delivered : Deadlines σ T}

namespace System.Implements

/-- What explains a prefix `pre` of a run: a history and a monotone `cut` such that every input
of the history arrived at a position `p` with `cut p` at most its place, every output of `pre`
at position `i` comes from an act before `cut (i + 1)`, and a deadline passes in the history
exactly where it passes in the run: in the block `cut p` to `cut (p + 1)` of the position `p`
where `deadlines` or `delivered` shows it. -/
structure Explains (svc : Service σ.In σ.Out S T) (deadlines delivered : Deadlines σ T)
    (pre : List (Event σ)) (acts : List (Service.Act σ.In T)) (cut : Nat → Nat) : Prop where
  /-- `cut` is monotone. -/
  mono : ∀ i j, i ≤ j → cut i ≤ cut j
  /-- Every input takes effect after it arrives. -/
  taken : ∀ k (x : σ.In), acts[k]? = some (.take x) → ∃ p, pre[p]? = some (.input x) ∧ cut p ≤ k
  /-- Every output handed over comes from an act before the next position. -/
  shown : ∀ i (o : σ.Out), pre[i]? = some (.output o) → ∃ k < cut (i + 1), svc.Produces acts k o
  /-- Every deadline that passes in the history passes in the run, in the block of its
  position. -/
  fired : ∀ k (t : T), acts[k]? = some (.fire t) → ∃ p,
    (pre[p]?).bind (Event.timed deadlines delivered) = some (.fire t) ∧ cut p ≤ k ∧ k < cut (p + 1)
  /-- Every deadline that passes in the run passes in the history, in the block of its
  position. -/
  fires : ∀ p (t : T), (pre[p]?).bind (Event.timed deadlines delivered) = some (.fire t) →
    ∃ k, acts[k]? = some (.fire t) ∧ cut p ≤ k ∧ k < cut (p + 1)

/-- The loop of `history`: a run from a state the simulation relates to one the history
explains goes on being explained. -/
private theorem explain {rel : SysState sys → Service.Abs σ.In σ.Out S → Prop}
    (hstep : ∀ c t, rel c t → ∀ ev c', (sys.sem env).Tr c ev c' →
      ∃ t', svc.spec.lts.STr t (ev.timed deadlines delivered) t' ∧ rel c' t') :
    ∀ (evs pre : List (Event σ)) (c c' : SysState sys) (t : Service.Abs σ.In σ.Out S)
      (acts : List (Service.Act σ.In T)) (cut : Nat → Nat),
      rel c t → svc.Follows (fun (x : σ.In) => ∃ p : Nat, pre[p]? = some (Event.input x)) acts t →
      Explains svc deadlines delivered pre acts cut → (∀ i, pre.length ≤ i → cut i = acts.length) →
      c.run env evs = some c' →
      ∃ acts' cut', Explains svc deadlines delivered (pre ++ evs) acts' cut'
  | [], pre, c, c', t, acts, cut, _, _, hex, _, _ => ⟨acts, cut, by simpa using hex⟩
  | ev :: evs, pre, c, c', t, acts, cut, hrel, hf, hex, hcut, hrun => by
    simp only [SysState.run] at hrun
    cases hc₁ : c.step env ev with
    | none => simp [hc₁] at hrun
    | some c₁ =>
      rw [hc₁, Option.bind_some] at hrun
      obtain ⟨t₁, ht₁, hrel₁⟩ := hstep c t hrel ev c₁ hc₁
      obtain ⟨E, hE, hf₁, ho, hF⟩ := hf.sTr ht₁
      let pre₁ := pre ++ [ev]
      let acts₁ := acts ++ E
      let cut₁ : Nat → Nat := fun i => if i ≤ pre.length then cut i else acts₁.length
      have hpre (p : Nat) (x : σ.In) (hp : pre[p]? = some (.input x)) : pre₁[p]? = some (.input x) := by
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hp).1, hp]
      have hinput (x : σ.In) (hx : ev.timed deadlines delivered = some (.input x)) : ev = .input x := by
        cases ev <;> simp_all [Event.timed]
      have harrived (x : σ.In) (hx : (∃ p : Nat, pre[p]? = some (Event.input x)) ∨
          ev.timed deadlines delivered = some (.input x)) :
          ∃ p : Nat, pre₁[p]? = some (Event.input x) ∧ p ≤ pre.length := by
        rcases hx with ⟨p, hp⟩ | hx
        · exact ⟨p, hpre p x hp, Nat.le_of_lt (List.getElem?_eq_some_iff.mp hp).1⟩
        · exact ⟨pre.length, by simp [pre₁, hinput x hx], Nat.le_refl _⟩
      have hcutle (p : Nat) (hp : p ≤ pre.length) : cut₁ p ≤ acts.length := by
        simp only [cut₁, hp, ↓reduceIte]
        rw [← hcut pre.length (Nat.le_refl _)]
        exact hex.mono p _ hp
      have hex₁ : Explains svc deadlines delivered pre₁ acts₁ cut₁ := by
        refine ⟨fun i j hij => ?_, fun k x hk => ?_, fun i o hi => ?_, fun k t hk => ?_,
          fun p t hp => ?_⟩
        · simp only [cut₁]
          split <;> split
          · exact hex.mono i j hij
          · next hi _ =>
            have := hex.mono i _ hi
            rw [hcut pre.length (Nat.le_refl _)] at this
            exact Nat.le_trans this (by simp [acts₁])
          · omega
          · exact Nat.le_refl _
        · by_cases hkl : k < acts.length
          · rw [List.getElem?_append_left hkl] at hk
            obtain ⟨p, hp, hcp⟩ := hex.taken k x hk
            refine ⟨p, hpre p x hp, ?_⟩
            have hpl := (List.getElem?_eq_some_iff.mp hp).1
            simpa [cut₁, Nat.le_of_lt hpl] using hcp
          · rw [List.getElem?_append_right (by omega)] at hk
            obtain ⟨p, hp, hpl⟩ := harrived x (hE x (List.mem_of_getElem? hk))
            exact ⟨p, hp, Nat.le_trans (hcutle p hpl) (by omega)⟩
        · by_cases hil : i < pre.length
          · rw [List.getElem?_append_left hil] at hi
            obtain ⟨k, hk, hp⟩ := hex.shown i o hi
            exact ⟨k, by simpa [cut₁, Nat.succ_le_of_lt hil] using hk, hp.append E⟩
          · have hieq : i = pre.length := by
              have := (List.getElem?_eq_some_iff.mp hi).1
              simp only [pre₁, List.length_append, List.length_singleton] at this
              omega
            subst hieq
            simp only [pre₁, List.getElem?_concat_length, Option.some.injEq] at hi
            subst hi
            obtain ⟨k, hk⟩ := ho o rfl
            have hlt : k < acts₁.length := by
              obtain ⟨a, ha, -⟩ := hk
              exact (List.getElem?_eq_some_iff.mp ha).1
            exact ⟨k, by simpa [cut₁, Nat.add_one_le_iff] using hlt, hk⟩
        · have hk₁ : k < acts₁.length := (List.getElem?_eq_some_iff.mp hk).1
          by_cases hkl : k < acts.length
          · rw [List.getElem?_append_left hkl] at hk
            obtain ⟨p, hp, hcp, hkp⟩ := hex.fired k t hk
            have hpl : p < pre.length := by
              cases hq : pre[p]? with
              | none => simp [hq] at hp
              | some _ => exact (List.getElem?_eq_some_iff.mp hq).1
            refine ⟨p, by rw [List.getElem?_append_left hpl]; exact hp, ?_, ?_⟩
            · simpa [cut₁, Nat.le_of_lt hpl] using hcp
            · simpa [cut₁, Nat.succ_le_of_lt hpl] using hkp
          · rw [List.getElem?_append_right (by omega)] at hk
            have hμ := (hF t).mp (List.mem_of_getElem? hk)
            refine ⟨pre.length, ?_, ?_, by simpa [cut₁, Nat.add_one_le_iff] using hk₁⟩
            · simp only [pre₁, List.getElem?_concat_length, Option.bind_some]
              exact hμ
            simp only [cut₁, Nat.le_refl, ↓reduceIte]
            rw [hcut pre.length (Nat.le_refl _)]
            omega
        · by_cases hpl : p < pre.length
          · rw [List.getElem?_append_left hpl] at hp
            obtain ⟨k, hk, hcp, hkp⟩ := hex.fires p t hp
            have hkl : k < acts.length := by
              have := hex.mono (p + 1) pre.length hpl
              rw [hcut pre.length (Nat.le_refl _)] at this
              omega
            refine ⟨k, by rw [List.getElem?_append_left hkl]; exact hk, ?_, ?_⟩
            · simpa [cut₁, Nat.le_of_lt hpl] using hcp
            · simpa [cut₁, Nat.succ_le_of_lt hpl] using hkp
          · have hpe : p = pre.length := by
              have : p < pre₁.length := by
                cases hq : pre₁[p]? with
                | none => simp [hq] at hp
                | some _ => exact (List.getElem?_eq_some_iff.mp hq).1
              simp only [pre₁, List.length_append, List.length_singleton] at this
              omega
            subst hpe
            simp only [pre₁, List.getElem?_concat_length, Option.bind_some] at hp
            obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ((hF t).mpr hp)
            have hjl : j < E.length := (List.getElem?_eq_some_iff.mp hj).1
            refine ⟨acts.length + j, ?_, ?_, ?_⟩
            · rw [List.getElem?_append_right (by omega)]
              simpa using hj
            · simp only [cut₁, Nat.le_refl, ↓reduceIte]
              rw [hcut pre.length (Nat.le_refl _)]
              omega
            · simp [cut₁, acts₁, Nat.add_one_le_iff]
              omega
      have hf₂ : svc.Follows (fun (x : σ.In) => ∃ p : Nat, pre₁[p]? = some (Event.input x)) acts₁ t₁ :=
        hf₁.mono fun x hx => (harrived x hx).elim fun p ⟨hp, _⟩ => ⟨p, hp⟩
      have hcut₁ (i : Nat) (hi : pre₁.length ≤ i) : cut₁ i = acts₁.length := by
        have : ¬ i ≤ pre.length := by simp [pre₁] at hi; omega
        simp [cut₁, this]
      obtain ⟨acts', cut', hex'⟩ := explain hstep evs pre₁ c₁ c' t₁ acts₁ cut₁ hrel₁ hf₂ hex₁ hcut₁ hrun
      exact ⟨acts', cut', by simpa [pre₁] using hex'⟩

/-- Every run of a system that implements a service has a sequential history of the service
that explains it in real-time order: every input of the history arrived at a position `p` with
`cut p` at most its place, and every output handed over at position `i` is produced by an act
before `cut (i + 1)`, with `cut` monotone. -/
theorem history (h : sys.Implements env svc deadlines delivered) {evs : List (Event σ)}
    {c : SysState sys} (hrun : (SysState.init sys env).run env evs = some c) :
    ∃ (acts : List (Service.Act σ.In T)) (cut : Nat → Nat),
      Explains svc deadlines delivered evs acts cut := by
  obtain ⟨rel, hinit, hstep⟩ := h
  obtain ⟨t, rfl, hrel⟩ := hinit _ rfl
  simpa using explain hstep evs [] _ c _ [] (fun _ => 0) hrel Service.Follows.init
    ⟨fun _ _ _ => Nat.le_refl _, by simp, by simp, by simp, by simp⟩ (fun _ _ => rfl) hrun

/-- Every output of every run of a system that implements a service is an output of an input
that arrived before it, or of a deadline, from a value that a sequence of the service's acts
reaches. -/
theorem produced (h : sys.Implements env svc deadlines delivered) {evs : List (Event σ)}
    {c : SysState sys} (hrun : (SysState.init sys env).run env evs = some c) {i : Nat} {o : σ.Out}
    (hi : evs[i]? = some (.output o)) :
    ∃ acts a, o ∈ (svc.act (svc.play svc.init acts) a).2 ∧
      ∀ x, a = .take x → ∃ p < i, evs[p]? = some (.input x) := by
  obtain ⟨acts, cut, hex⟩ := history h hrun
  obtain ⟨k, hk, a, ha, ho⟩ := hex.shown i o hi
  refine ⟨acts.take k, a, ho, ?_⟩
  rintro x rfl
  obtain ⟨p, hp, hcp⟩ := hex.taken k x ha
  refine ⟨p, ?_, hp⟩
  rcases Nat.lt_trichotomy p i with hpi | rfl | hpi
  · exact hpi
  · rw [hi] at hp
    cases hp
  · have := hex.mono (i + 1) p hpi
    omega

end System.Implements

end Lanes
