/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Join
public import Lanes.Actors.KernelSound
public import Lanes.Actors.Monotone

/-!
# What survives a join

`SysState.left` is a state of `a.join b w` seen from `a`: its actors, its timers, the messages
on their way to it and the outputs that are its own. `System.Reachable.left` proves that every
reachable state of the join, seen from `a`, is a reachable state of `a` alone, under
`EnvModel.left`. So whatever is proved of `a` for every environment holds of `a` inside any join
(`System.Invariant.join_left`).

Seen from `a`, a message from `b` is an input. Inputs of `a` alone all travel on one link, so
that link is modelled as the most permissive one, `Link.network`.
-/

@[expose] public section

namespace Lanes

variable {σ τ : Signature}

namespace Envelope

/-- A message to an actor of the left system, as that system sees it: a sender that is not one
of its own actors is the outside. -/
def left? : Envelope (joinSig σ τ) → Option (Envelope σ)
  | ⟨src, .inl i, msg⟩ => some ⟨src.bind Sum.getLeft?, i, msg⟩
  | ⟨_, .inr _, _⟩ => none

def right? : Envelope (joinSig σ τ) → Option (Envelope τ)
  | ⟨src, .inr j, msg⟩ => some ⟨src.bind Sum.getRight?, j, msg⟩
  | ⟨_, .inl _, _⟩ => none

end Envelope

namespace EnvModel

def left (env : EnvModel (joinSig σ τ)) : EnvModel σ where
  link
    | some s, d => env.link (some (.inl s)) (.inl d)
    | none, _ => Link.network
  mayCrash i := env.mayCrash (.inl i)
  restarts i := env.restarts (.inl i)

def right (env : EnvModel (joinSig σ τ)) : EnvModel τ where
  link
    | some s, d => env.link (some (.inr s)) (.inr d)
    | none, _ => Link.network
  mayCrash j := env.mayCrash (.inr j)
  restarts j := env.restarts (.inr j)

end EnvModel

variable {a : System σ} {b : System τ} {w : Wiring σ τ}

namespace SysState

def left (c : SysState (a.join b w)) : SysState a where
  state i := c.state (.inl i)
  up i := c.up (.inl i)
  net := c.net.filterMap Envelope.left?
  timers i := c.timers (.inl i)
  outbox := c.outbox.filterMap Sum.getLeft?

def right (c : SysState (a.join b w)) : SysState b where
  state j := c.state (.inr j)
  up j := c.up (.inr j)
  net := c.net.filterMap Envelope.right?
  timers j := c.timers (.inr j)
  outbox := c.outbox.filterMap Sum.getRight?

end SysState

end Lanes

end

public section

namespace Lanes

private theorem update_update {ι : Type} [DecidableEq ι] {β : ι → Type} (f : (i : ι) → β i)
    (i : ι) (v v' : β i) : update (update f i v) i v' = update f i v' := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

private theorem update_inl {α β : Type} [DecidableEq α] [DecidableEq β] {γ : α ⊕ β → Type}
    (f : (x : α ⊕ β) → γ x) (i : α) (v : γ (.inl i)) :
    (fun k => update f (.inl i) v (.inl k)) = update (β := fun k => γ (.inl k)) (fun k => f (.inl k)) i v := by
  funext k
  by_cases h : k = i
  · subst h; simp
  · rw [update_of_ne _ _ h, update_of_ne _ _ (by simpa using h)]

private theorem update_inr_inl {α β : Type} [DecidableEq α] [DecidableEq β] {γ : α ⊕ β → Type}
    (f : (x : α ⊕ β) → γ x) (j : β) (v : γ (.inr j)) (k : α) :
    update f (.inr j) v (.inl k) = f (.inl k) :=
  update_of_ne _ _ (by simp)

private theorem filterMap_erase {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → Option β}
    {a : α} {b : β} (h : ∀ x, f x = some b ↔ x = a) (l : List α) :
    (l.erase a).filterMap f = (l.filterMap f).erase b := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : x = a
    · subst hx
      simp [(h x).mpr rfl]
    · cases hfx : f x with
      | none => simp [hx, hfx, ih]
      | some y =>
        have hy : y ≠ b := fun hyb => hx ((h x).mp (hyb ▸ hfx))
        simp [hx, hfx, ih, hy]

private theorem filterMap_erase_of_none {α β : Type} [DecidableEq α] {f : α → Option β} {a : α}
    (h : f a = none) (l : List α) : (l.erase a).filterMap f = l.filterMap f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : x = a
    · subst hx
      simp [h]
    · cases hfx : f x <;> simp [hx, hfx, ih]

private theorem filterMap_filter_of_none {α β : Type} {f : α → Option β} {p : α → Bool}
    (h : ∀ x, p x = false → f x = none) (l : List α) :
    (l.filter p).filterMap f = l.filterMap f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases hp : p x with
    | true => cases hfx : f x <;> simp [hp, hfx, ih]
    | false => simp [hp, ih, h x hp]

private theorem filter_erase {α : Type} [DecidableEq α] (p : α → Bool) (l : List α) {a : α}
    (h : p a = true) : (l.filter p).erase a = (l.erase a).filter p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : x = a
    · subst hx
      simp [h]
    · cases hp : p x <;> simp [hx, hp, ih]

namespace Effect

variable {σ : Signature} {i : σ.Id}

/-- An actor's timers after its effects. -/
def retime (effs : List (Effect σ i)) (timers : List (σ.Msg i)) : List (σ.Msg i) :=
  effs.foldl (fun timers eff =>
    match eff with
    | .after _ msg => if msg ∈ timers then timers else timers ++ [msg]
    | .cancel msg => timers.erase msg
    | _ => timers) timers

end Effect

namespace SysState

section General

variable {σ : Signature} {sys : System σ} {env : EnvModel σ}

theorem performAll_eq (c : SysState sys) (i : σ.Id) (effs : List (Effect σ i)) :
    c.performAll i effs = { c with
      net := c.net ++ Effect.sends i effs
      timers := update c.timers i (Effect.retime effs (c.timers i))
      outbox := c.outbox ++ Effect.emits effs } := by
  induction effs generalizing c with
  | nil => simp [Effect.sends, Effect.emits, Effect.retime]
  | cons eff effs ih =>
    rw [performAll_cons, ih]
    cases eff <;>
      simp [perform, Effect.sends, Effect.emits, Effect.retime, List.append_assoc, update_update]

/-- A step in full: the new state and what the effects add, then the actor taken down if one
of them is `stop`. -/
theorem settle_eq (env : EnvModel σ) (c : SysState sys) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) :
    c.settle env i r =
      if r.2.any Effect.isStop then
        ({ c with
          state := update c.state i r.1
          net := c.net ++ Effect.sends i r.2
          timers := update c.timers i (Effect.retime r.2 (c.timers i))
          outbox := c.outbox ++ Effect.emits r.2 } : SysState sys).down env i
      else
        { c with
          state := update c.state i r.1
          net := c.net ++ Effect.sends i r.2
          timers := update c.timers i (Effect.retime r.2 (c.timers i))
          outbox := c.outbox ++ Effect.emits r.2 } := by
  simp only [settle, performAll_eq]

/-- An actor's step does not look at the messages in flight: one that stays in flight could as
well be lost after the step as before it. -/
theorem settle_erase (c : SysState sys) (i : σ.Id) (r : sys.State i × List (Effect σ i))
    {e : Envelope σ} (hmem : e ∈ c.net) (hlossy : (env.link e.src e.dst).lossy = true) :
    e ∈ (c.settle env i r).net ∧
      ({ c with net := c.net.erase e } : SysState sys).settle env i r =
        { c.settle env i r with net := (c.settle env i r).net.erase e } := by
  simp only [settle_eq]
  split
  · simp only [down]
    refine ⟨by simp [hmem, hlossy], ?_⟩
    rw [filter_erase _ _ (by simp [hlossy]), List.erase_append_left _ hmem]
  · exact ⟨by simp [hmem], by rw [List.erase_append_left _ hmem]⟩

theorem run_inputs (env : EnvModel σ) (c : SysState sys) (xs : List σ.In) :
    c.run env (xs.map .input) = some { c with
      net := c.net ++ xs.map fun x => ⟨none, (sys.accept x).1, (sys.accept x).2⟩ } := by
  induction xs generalizing c with
  | nil => simp [run]
  | cons x xs ih => simp [run, step, ih, List.append_assoc]

/-- Handing over the outputs that are not `kept`, when none of them waits behind an equal one
that is kept. -/
theorem run_outputs_filter (env : EnvModel σ) (c : SysState sys) (kept : σ.Out → Bool)
    (pre outs : List σ.Out) (hpre : ∀ out ∈ pre, kept out = true) :
    ({ c with outbox := pre ++ outs } : SysState sys).run env
        ((outs.filter (!kept ·)).map .output)
      = some { c with outbox := pre ++ outs.filter kept } := by
  induction outs generalizing pre with
  | nil => simp [run]
  | cons out outs ih =>
    cases hout : kept out with
    | true =>
      have h := ih (pre ++ [out]) (by
        intro o ho
        rcases List.mem_append.mp ho with ho | ho
        · exact hpre o ho
        · simp only [List.mem_singleton] at ho
          exact ho ▸ hout)
      simpa [hout, List.append_assoc] using h
    | false =>
      have hnot : out ∉ pre := fun h => by simp [hpre out h] at hout
      simp only [List.filter_cons, hout, Bool.not_false, ↓reduceIte, List.map_cons, run]
      rw [step_output.mpr ⟨by simp, rfl⟩]
      simp only [Option.bind_some, List.erase_append_right _ hnot, List.erase_cons_head]
      simpa [hout] using ih pre hpre

end General

end SysState

/-- `l` with some of the messages from outside left out. -/
private inductive Thin {σ : Signature} : List (Envelope σ) → List (Envelope σ) → Prop
  | nil : Thin [] []
  | keep (e : Envelope σ) {l l' : List (Envelope σ)} : Thin l l' → Thin (e :: l) (e :: l')
  | skip {e : Envelope σ} {l l' : List (Envelope σ)} : e.src = none → Thin l l' → Thin l (e :: l')

namespace Thin

variable {σ : Signature}

private theorem refl : ∀ l : List (Envelope σ), Thin l l
  | [] => .nil
  | e :: l => .keep e (refl l)

private theorem append {l₁ l₁' l₂ l₂' : List (Envelope σ)} (h₁ : Thin l₁ l₁') (h₂ : Thin l₂ l₂') :
    Thin (l₁ ++ l₂) (l₁' ++ l₂') := by
  induction h₁ with
  | nil => exact h₂
  | keep e _ ih => exact .keep e ih
  | skip he _ ih => exact .skip he ih

private theorem of_append {l₁' l₂' : List (Envelope σ)} :
    ∀ {l}, Thin l (l₁' ++ l₂') → ∃ l₁ l₂, l = l₁ ++ l₂ ∧ Thin l₁ l₁' ∧ Thin l₂ l₂' := by
  induction l₁' with
  | nil => exact fun {l} h => ⟨[], l, rfl, .nil, h⟩
  | cons e l₁' ih =>
    intro l h
    cases h with
    | keep _ h =>
      obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := ih h
      exact ⟨e :: l₁, l₂, rfl, .keep e h₁, h₂⟩
    | skip he h =>
      obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := ih h
      exact ⟨l₁, l₂, rfl, .skip he h₁, h₂⟩

private theorem eq_of_inside {l l' : List (Envelope σ)} (h : Thin l l')
    (hl : ∀ e ∈ l', e.src ≠ none) : l = l' := by
  induction h with
  | nil => rfl
  | keep e _ ih => rw [ih fun e he => hl e (List.mem_cons_of_mem _ he)]
  | skip he _ _ => exact absurd he (hl _ List.mem_cons_self)

private theorem of_map {α : Type} {f : α → Envelope σ} {xs : List α} :
    ∀ {l}, Thin l (xs.map f) → ∃ ys : List α, l = ys.map f := by
  induction xs with
  | nil =>
    intro l h
    cases h
    exact ⟨[], rfl⟩
  | cons x xs ih =>
    intro l h
    cases h with
    | keep _ h =>
      obtain ⟨ys, rfl⟩ := ih h
      exact ⟨x :: ys, rfl⟩
    | skip _ h => exact ih h

private theorem mem {l l' : List (Envelope σ)} (h : Thin l l') {e : Envelope σ} (he : e ∈ l')
    (hsrc : e.src ≠ none) : e ∈ l := by
  induction h with
  | nil => exact he
  | keep x _ ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih he)
  | skip hx _ ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact absurd hx hsrc
    · exact ih he

private theorem find? {l l' : List (Envelope σ)} (h : Thin l l') {p : Envelope σ → Bool}
    (hp : ∀ e, p e = true → e.src ≠ none) : l.find? p = l'.find? p := by
  induction h with
  | nil => rfl
  | keep e _ ih => simp [List.find?_cons, ih]
  | @skip e _ _ he _ ih =>
    have hpe : p e = false := by
      cases hpe : p e with
      | false => rfl
      | true => exact absurd he (hp e hpe)
    simp [hpe, ih]

/-- A message between actors that left `l'` was in every thinning of `l'`. -/
private theorem unerase {u : Envelope σ} (hsrc : u.src ≠ none) :
    ∀ {l' l : List (Envelope σ)}, u ∈ l' → Thin l (l'.erase u) →
      ∃ n, Thin n l' ∧ n.erase u = l ∧ u ∈ n := by
  intro l'
  induction l' with
  | nil => exact fun hu => absurd hu (by simp)
  | cons x l' ih =>
    intro l hu h
    by_cases hx : x = u
    · subst hx
      rw [List.erase_cons_head] at h
      exact ⟨x :: l, .keep x h, by simp, by simp⟩
    · have hu' : u ∈ l' := (List.mem_cons.mp hu).resolve_left fun h => hx h.symm
      rw [List.erase_cons_tail (by simpa using hx)] at h
      cases h with
      | keep _ h =>
        obtain ⟨n, hn, rfl, hmem⟩ := ih hu' h
        exact ⟨x :: n, .keep x hn, by simp [hx], List.mem_cons_of_mem _ hmem⟩
      | skip hsrc' h =>
        obtain ⟨n, hn, rfl, hmem⟩ := ih hu' h
        exact ⟨n, .skip hsrc' hn, rfl, hmem⟩

/-- A message from outside that a thinning of `l'` lacks can be put back where it was. -/
private theorem insert {u : Envelope σ} :
    ∀ {l' l : List (Envelope σ)}, u ∈ l' → u ∉ l → Thin l l' →
      ∃ n, Thin n l' ∧ n.erase u = l ∧ u ∈ n := by
  intro l'
  induction l' with
  | nil => exact fun hu => absurd hu (by simp)
  | cons x l' ih =>
    intro l hu hnot h
    cases h with
    | keep _ h =>
      have hx : x ≠ u := fun hx => hnot (hx ▸ List.mem_cons_self)
      have hu' : u ∈ l' := (List.mem_cons.mp hu).resolve_left fun h => hx h.symm
      obtain ⟨n, hn, rfl, hmem⟩ := ih hu' (fun h => hnot (List.mem_cons_of_mem _ h)) h
      exact ⟨x :: n, .keep x hn, by simp [hx], List.mem_cons_of_mem _ hmem⟩
    | skip hsrc' h =>
      by_cases hx : x = u
      · subst hx
        exact ⟨x :: l, .keep x h, by simp, by simp⟩
      · have hu' : u ∈ l' := (List.mem_cons.mp hu).resolve_left fun h => hx h.symm
        obtain ⟨n, hn, rfl, hmem⟩ := ih hu' hnot h
        exact ⟨n, .skip hsrc' hn, rfl, hmem⟩

private theorem of_filterMap_erase {α : Type} [DecidableEq α] {f : α → Option (Envelope σ)} {a : α}
    (ha : ∀ u, f a = some u → u.src = none) :
    ∀ (l : List α) {n}, Thin n ((l.erase a).filterMap f) → Thin n (l.filterMap f) := by
  intro l
  induction l with
  | nil => exact fun h => h
  | cons x l ih =>
    intro n h
    by_cases hx : x = a
    · subst hx
      rw [List.erase_cons_head] at h
      cases hfx : f x with
      | none => simpa [hfx] using h
      | some u =>
        rw [List.filterMap_cons_some hfx]
        exact .skip (ha u hfx) h
    · rw [List.erase_cons_tail (by simpa using hx)] at h
      cases hfx : f x with
      | none =>
        rw [List.filterMap_cons_none hfx] at h ⊢
        exact ih h
      | some v =>
        rw [List.filterMap_cons_some hfx] at h ⊢
        cases h with
        | keep _ h => exact .keep v (ih h)
        | skip hv h => exact .skip hv (ih h)

/-- Taking an actor down in the join drops what taking it down alone drops, and messages from
outside besides. -/
private theorem of_filter {α : Type} {f : α → Option (Envelope σ)} {p : α → Bool}
    {q : Envelope σ → Bool} (hout : ∀ u, u.src = none → q u = true)
    (hin : ∀ x u, f x = some u → u.src ≠ none → q u = p x) :
    ∀ (l : List α) {n}, Thin n ((l.filter p).filterMap f) →
      ∃ m, Thin m (l.filterMap f) ∧ m.filter q = n := by
  intro l
  induction l with
  | nil =>
    intro n h
    cases h
    exact ⟨[], .nil, rfl⟩
  | cons x l ih =>
    intro n h
    cases hfx : f x with
    | none =>
      rw [List.filterMap_cons_none hfx]
      rw [List.filter_cons] at h
      split at h
      · rw [List.filterMap_cons_none hfx] at h
        exact ih h
      · exact ih h
    | some u =>
      rw [List.filterMap_cons_some hfx]
      cases hp : p x with
      | false =>
        rw [List.filter_cons_of_neg (by simp [hp])] at h
        obtain ⟨m, hm, rfl⟩ := ih h
        by_cases hsrc : u.src = none
        · exact ⟨m, .skip hsrc hm, rfl⟩
        · have hq : q u = false := (hin x u hfx hsrc).trans hp
          exact ⟨u :: m, .keep u hm, by rw [List.filter_cons_of_neg (by simp [hq])]⟩
      | true =>
        rw [List.filter_cons_of_pos hp, List.filterMap_cons_some hfx] at h
        cases h with
        | keep _ h =>
          obtain ⟨m, hm, rfl⟩ := ih h
          have hq : q u = true := by
            by_cases hsrc : u.src = none
            · exact hout u hsrc
            · exact (hin x u hfx hsrc).trans hp
          exact ⟨u :: m, .keep u hm, by rw [List.filter_cons_of_pos hq]⟩
        | skip hs h =>
          obtain ⟨m, hm, rfl⟩ := ih h
          exact ⟨m, .skip hs hm, rfl⟩

end Thin

section Left

variable {σ τ : Signature} {a : System σ} {b : System τ} {w : Wiring σ τ}
  {env : EnvModel (joinSig σ τ)}

private theorem Envelope.left?_eq_inside {s i : σ.Id} {msg : σ.Msg i}
    (e : Envelope (joinSig σ τ)) :
    e.left? = some ⟨some s, i, msg⟩ ↔ e = ⟨some (.inl s), .inl i, msg⟩ := by
  constructor
  · intro h
    obtain ⟨src, i' | j, msg'⟩ := e
    · simp only [Envelope.left?, Option.some.injEq, Envelope.mk.injEq] at h
      obtain ⟨hsrc, rfl, hmsg⟩ := h
      cases hmsg
      rcases src with _ | s' | j
      · simp at hsrc
      · simp only [Option.bind_some, Sum.getLeft?_inl, Option.some.injEq] at hsrc
        rw [hsrc]
      · simp at hsrc
    · simp [Envelope.left?] at h
  · rintro rfl
    rfl

namespace Wiring

variable {i : σ.Id} {j : τ.Id}

private theorem sends_left (effs : List (Effect σ i)) :
    (Effect.sends (σ := joinSig σ τ) (.inl i) (effs.flatMap fun eff => [w.left b eff])).filterMap
      Envelope.left? = Effect.sends i effs := by
  induction effs with
  | nil => rfl
  | cons eff effs ih =>
    have head : (Effect.sends (σ := joinSig σ τ) (.inl i) [w.left b eff]).filterMap
        Envelope.left? = Effect.sends i [eff] := by
      cases eff with
      | emit out => cases h : w.toRight out <;> simp [Effect.sends, Wiring.left, h, Envelope.left?]
      | _ => simp [Effect.sends, Wiring.left, Envelope.left?]
    rw [List.flatMap_cons, show eff :: effs = [eff] ++ effs from rfl]
    simp only [Effect.sends, List.filterMap_append] at head ih ⊢
    rw [head, ih]

private theorem emits_left (effs : List (Effect σ i)) :
    (Effect.emits (effs.flatMap fun eff => [w.left b eff])).filterMap Sum.getLeft?
      = (Effect.emits effs).filter fun out => (w.toRight out).isNone := by
  induction effs with
  | nil => rfl
  | cons eff effs ih =>
    have head : (Effect.emits [w.left b eff]).filterMap Sum.getLeft?
        = (Effect.emits [eff]).filter fun out => (w.toRight out).isNone := by
      cases eff with
      | emit out => cases h : w.toRight out <;> simp [Effect.emits, Wiring.left, h]
      | _ => simp [Effect.emits, Wiring.left]
    rw [List.flatMap_cons, show eff :: effs = [eff] ++ effs from rfl]
    simp only [Effect.emits, List.filterMap_append, List.filter_append] at head ih ⊢
    rw [head, ih]

private theorem retime_left (effs : List (Effect σ i)) (timers : List (σ.Msg i)) :
    Effect.retime (σ := joinSig σ τ) (i := .inl i) (effs.flatMap fun eff => [w.left b eff]) timers
      = Effect.retime effs timers := by
  induction effs generalizing timers with
  | nil => rfl
  | cons eff effs ih =>
    have head : Effect.retime (σ := joinSig σ τ) (i := .inl i) [w.left b eff] timers
        = Effect.retime [eff] timers := by
      cases eff with
      | emit out => cases h : w.toRight out <;> simp [Effect.retime, Wiring.left, h]
      | _ => simp [Effect.retime, Wiring.left]
    rw [List.flatMap_cons, show eff :: effs = [eff] ++ effs from rfl]
    simp only [Effect.retime, List.foldl_append] at head ih ⊢
    rw [head, ih]

private theorem isStop_left (effs : List (Effect σ i)) :
    (effs.flatMap fun eff => [w.left b eff]).any Effect.isStop = effs.any Effect.isStop := by
  induction effs with
  | nil => rfl
  | cons eff effs ih =>
    have head : (w.left b eff).isStop = eff.isStop := by
      cases eff with
      | emit out => cases h : w.toRight out <;> simp [Effect.isStop, Wiring.left, h]
      | _ => simp [Effect.isStop, Wiring.left]
    rw [List.flatMap_cons, List.any_append, List.any_cons, ih]
    simp [head]

private theorem sends_right_left (effs : List (Effect τ j)) :
    (Effect.sends (σ := joinSig σ τ) (.inr j) (effs.flatMap fun eff => [w.right a eff])).filterMap
      Envelope.left?
      = ((Effect.emits effs).filterMap w.toLeft).map fun x =>
          ⟨none, (a.accept x).1, (a.accept x).2⟩ := by
  induction effs with
  | nil => rfl
  | cons eff effs ih =>
    have head : (Effect.sends (σ := joinSig σ τ) (.inr j) [w.right a eff]).filterMap
        Envelope.left?
        = ((Effect.emits [eff]).filterMap w.toLeft).map fun x =>
            ⟨none, (a.accept x).1, (a.accept x).2⟩ := by
      cases eff with
      | emit out =>
        cases h : w.toLeft out <;>
          simp [Effect.sends, Effect.emits, Wiring.right, h, Envelope.left?]
      | _ => simp [Effect.sends, Effect.emits, Wiring.right, Envelope.left?]
    rw [List.flatMap_cons, show eff :: effs = [eff] ++ effs from rfl]
    simp only [Effect.sends, Effect.emits, List.filterMap_append, List.map_append] at head ih ⊢
    rw [head, ih]

private theorem emits_right_left (effs : List (Effect τ j)) :
    (Effect.emits (effs.flatMap fun eff => [w.right a eff])).filterMap Sum.getLeft?
      = ([] : List σ.Out) := by
  induction effs with
  | nil => rfl
  | cons eff effs ih =>
    have head : (Effect.emits [w.right a eff]).filterMap Sum.getLeft? = ([] : List σ.Out) := by
      cases eff with
      | emit out => cases h : w.toLeft out <;> simp [Effect.emits, Wiring.right, h]
      | _ => simp [Effect.emits, Wiring.right]
    rw [List.flatMap_cons]
    simp only [Effect.emits, List.filterMap_append] at head ih ⊢
    rw [head, ih]
    rfl

end Wiring

namespace SysState

private theorem thin_down {i : σ.Id} (l : List (Envelope (joinSig σ τ))) {n : List (Envelope σ)}
    (h : Thin n ((l.filter fun e => decide (e.dst ≠ .inl i)
      || (env.link e.src e.dst).lossy).filterMap Envelope.left?)) :
    ∃ m, Thin m (l.filterMap Envelope.left?) ∧
      m.filter (fun e => decide (e.dst ≠ i) || (env.left.link e.src e.dst).lossy) = n :=
  Thin.of_filter (fun u hu => by simp [hu, EnvModel.left, Link.network])
    (fun e u he hu => by
      obtain ⟨src, k | j, msg⟩ := e
      · simp only [Envelope.left?, Option.some.injEq] at he
        subst he
        rcases src with _ | s | j
        · simp at hu
        · simp [EnvModel.left]
        · simp at hu
      · simp [Envelope.left?] at he) l h

private theorem left?_of_dropped {j : τ.Id} (e : Envelope (joinSig σ τ))
    (h : (decide (e.dst ≠ .inr j) || (env.link e.src e.dst).lossy) = false) : e.left? = none := by
  obtain ⟨src, k | j', msg⟩ := e
  · simp at h
  · rfl

private theorem left_settle (c : SysState (a.join b w)) (i : σ.Id)
    (r : a.State i × List (Effect σ i)) :
    (c.settle env (.inl i) (r.1, r.2.flatMap fun eff => [w.left b eff])).left =
      if r.2.any Effect.isStop then
        { state := update c.left.state i r.1
          up := update c.left.up i false
          net := ((c.net ++ Effect.sends (σ := joinSig σ τ) (.inl i)
            (r.2.flatMap fun eff => [w.left b eff])).filter fun e =>
              decide (e.dst ≠ .inl i) || (env.link e.src e.dst).lossy).filterMap Envelope.left?
          timers := update c.left.timers i []
          outbox := c.left.outbox ++ (Effect.emits r.2).filter fun out => (w.toRight out).isNone }
      else
        { state := update c.left.state i r.1
          up := c.left.up
          net := c.left.net ++ Effect.sends i r.2
          timers := update c.left.timers i (Effect.retime r.2 (c.left.timers i))
          outbox := c.left.outbox ++ (Effect.emits r.2).filter fun out => (w.toRight out).isNone } := by
  rw [settle_eq]
  simp only [Wiring.isStop_left]
  split
  · apply SysState.ext'
    · exact update_inl c.state i r.1
    · exact update_inl c.up i false
    · rfl
    · simp only [left, down, update_update]
      exact update_inl c.timers i []
    · simp [left, down, Wiring.emits_left]
  · apply SysState.ext'
    · exact update_inl c.state i r.1
    · rfl
    · simp [left, Wiring.sends_left]
    · simp only [left, Wiring.retime_left]
      exact update_inl c.timers i _
    · simp [left, Wiring.emits_left]

/-- A step of an actor of `a` in the join is the same step of `a` alone, from a state that
never received the messages from outside that the join is about to drop. -/
private theorem settle_left (c : SysState (a.join b w)) (i : σ.Id)
    (r : a.State i × List (Effect σ i)) {n' : List (Envelope σ)}
    (h : Thin n' (c.settle env (.inl i) (r.1, r.2.flatMap fun eff => [w.left b eff])).left.net) :
    ∃ n, Thin n c.left.net ∧ ∀ outbox,
      ({ c.left with net := n, outbox := outbox } : SysState a).settle env.left i r =
        { (c.settle env (.inl i) (r.1, r.2.flatMap fun eff => [w.left b eff])).left with
          net := n', outbox := outbox ++ Effect.emits r.2 } := by
  rw [left_settle] at h ⊢
  have inside : ∀ e ∈ Effect.sends i r.2, e.src ≠ none := fun e he => by
    simp [(Effect.mem_sends.mp he).1]
  by_cases hstop : r.2.any Effect.isStop = true
  · simp only [hstop, ↓reduceIte] at h ⊢
    obtain ⟨m, hm, rfl⟩ := thin_down _ h
    rw [List.filterMap_append, Wiring.sends_left] at hm
    obtain ⟨n, s, rfl, hn, hs⟩ := hm.of_append
    obtain rfl := hs.eq_of_inside inside
    refine ⟨n, hn, fun outbox => ?_⟩
    rw [settle_eq]
    simp only [hstop, ↓reduceIte, down, update_update]
  · simp only [hstop, Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨n, s, rfl, hn, hs⟩ := h.of_append
    obtain rfl := hs.eq_of_inside inside
    refine ⟨n, hn, fun outbox => ?_⟩
    rw [settle_eq]
    simp only [hstop, Bool.false_eq_true, ↓reduceIte]

private theorem left_settle_inr (c : SysState (a.join b w)) (j : τ.Id)
    (r : b.State j × List (Effect τ j)) :
    (c.settle env (.inr j) (r.1, r.2.flatMap fun eff => [w.right a eff])).left =
      { c.left with
        net := c.left.net ++ ((Effect.emits r.2).filterMap w.toLeft).map fun x =>
          ⟨none, (a.accept x).1, (a.accept x).2⟩ } := by
  have hnet : (c.net ++ Effect.sends (σ := joinSig σ τ) (.inr j)
      (r.2.flatMap fun eff => [w.right a eff])).filterMap Envelope.left?
      = c.left.net ++ ((Effect.emits r.2).filterMap w.toLeft).map fun x =>
        ⟨none, (a.accept x).1, (a.accept x).2⟩ := by
    rw [List.filterMap_append, Wiring.sends_right_left]
    rfl
  have houtbox : (c.outbox ++ Effect.emits (r.2.flatMap fun eff => [w.right a eff])).filterMap
      Sum.getLeft? = c.left.outbox := by
    rw [List.filterMap_append, Wiring.emits_right_left, List.append_nil]
    rfl
  rw [settle_eq]
  split
  · apply SysState.ext'
    · funext k
      exact update_inr_inl c.state j r.1 k
    · funext k
      exact update_inr_inl c.up j false k
    · simp only [left, down]
      rw [filterMap_filter_of_none left?_of_dropped, hnet]
      rfl
    · funext k
      simp only [left, down]
      rw [update_inr_inl, update_inr_inl]
    · exact houtbox
  · apply SysState.ext'
    · funext k
      exact update_inr_inl c.state j r.1 k
    · rfl
    · exact hnet
    · funext k
      simp only [left]
      rw [update_inr_inl]
    · exact houtbox

private theorem deliverable_left {c : SysState (a.join b w)} {s i : σ.Id} {msg : σ.Msg i}
    {n : List (Envelope σ)} (hn : Thin n c.left.net)
    (h : c.deliverable env ⟨some (.inl s), .inl i, msg⟩ = true) :
    ({ c.left with net := n } : SysState a).deliverable env.left ⟨some s, i, msg⟩ = true := by
  have hlink : env.left.link (some s) i = env.link (some (.inl s)) (.inl i) := rfl
  simp only [deliverable, hlink] at h ⊢
  split at h
  · next hord =>
    simp only [hord, ↓reduceIte]
    have hsame : (fun e : Envelope (joinSig σ τ) =>
        e.left?.any (Envelope.sameLink ⟨some s, i, msg⟩))
        = Envelope.sameLink (⟨some (.inl s), .inl i, msg⟩ : Envelope (joinSig σ τ)) := by
      funext e
      obtain ⟨src, k | j, m⟩ := e
      · rcases src with _ | s' | j' <;> simp [Envelope.left?, Envelope.sameLink]
      · simp [Envelope.left?, Envelope.sameLink]
    have hfind : n.find? (Envelope.sameLink ⟨some s, i, msg⟩) = some ⟨some s, i, msg⟩ := by
      rw [hn.find? fun e he => by
        simp only [Envelope.sameLink, Bool.and_eq_true, decide_eq_true_eq] at he
        simp [← he.1]]
      show (c.net.filterMap Envelope.left?).find? _ = _
      rw [List.find?_filterMap, hsame, (by simpa using h :
        c.net.find? (Envelope.sameLink (⟨some (.inl s), .inl i, msg⟩ : Envelope (joinSig σ τ)))
          = some _)]
      rfl
    simp [hfind]
  · next hord =>
    simp only [hord]
    have hmem : (⟨some s, i, msg⟩ : Envelope σ) ∈ c.left.net :=
      List.mem_filterMap.mpr ⟨_, by simpa using h, rfl⟩
    simpa using hn.mem hmem (by simp)

end SysState

/-- What the induction carries, of a join seen from `a`: with any of the messages from outside
left out it is a state `a` reaches alone, and no output waits that the wiring routes to `b`. -/
private structure Seen (env : EnvModel (joinSig σ τ)) (w : Wiring σ τ) (c : SysState a) : Prop where
  reach : ∀ n, Thin n c.net → a.Reachable env.left { c with net := n }
  tidy : ∀ out ∈ c.outbox, w.toRight out = none

namespace Seen

private theorem inputs {c : SysState a} (hc : Seen env w c) (xs : List σ.In) :
    Seen env w { c with
      net := c.net ++ xs.map fun x => ⟨none, (a.accept x).1, (a.accept x).2⟩ } := by
  refine ⟨fun n hn => ?_, hc.tidy⟩
  obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := hn.of_append
  obtain ⟨ys, rfl⟩ := h₂.of_map
  exact (hc.reach n₁ h₁).run (SysState.run_inputs env.left _ ys)

/-- A message from outside is handled whether or not `a` alone still has it in flight: it is
duplicated if so, and otherwise it is the one message put back and delivered. -/
private theorem handle_outside {c : SysState a} (hc : Seen env w c) {u : Envelope σ}
    (hu : u ∈ c.net) (hsrc : u.src = none) (hup : c.up u.dst = true) {n : List (Envelope σ)}
    (hn : Thin n c.net) :
    a.Reachable env.left (({ c with net := n } : SysState a).handle env.left u.dst u.msg) := by
  have hlink : env.left.link u.src u.dst = Link.network := by
    rw [hsrc]
    rfl
  by_cases hmem : u ∈ n
  · exact (hc.reach n hn).step (.duplicate u) (SysState.step_duplicate.mpr
      ⟨hup, by rw [hlink]; rfl, by simp [SysState.deliverable, hlink, Link.network, hmem], rfl⟩)
  · obtain ⟨m, hm, rfl, hmm⟩ := Thin.insert hu hmem hn
    exact (hc.reach m hm).step (.deliver u) (SysState.step_deliver.mpr
      ⟨hup, by simp [SysState.deliverable, hlink, Link.network, hmm], rfl⟩)

private theorem settle {c : SysState (a.join b w)}
    (htidy : ∀ out ∈ c.left.outbox, w.toRight out = none) (i : σ.Id)
    (r : a.State i × List (Effect σ i))
    (hreach : ∀ n, Thin n c.left.net →
      a.Reachable env.left (({ c.left with net := n } : SysState a).settle env.left i r)) :
    Seen env w (c.settle env (.inl i) (r.1, r.2.flatMap fun eff => [w.left b eff])).left := by
  have houtbox : (c.settle env (.inl i) (r.1, r.2.flatMap fun eff => [w.left b eff])).left.outbox
      = c.left.outbox ++ (Effect.emits r.2).filter fun out => (w.toRight out).isNone := by
    rw [SysState.left_settle]
    split <;> rfl
  refine ⟨fun n' hn' => ?_, fun out hout => ?_⟩
  · obtain ⟨n, hn, heq⟩ := SysState.settle_left c i r hn'
    have hrun := SysState.run_outputs_filter env.left
      ({ (c.settle env (.inl i) (r.1, r.2.flatMap fun eff => [w.left b eff])).left with
        net := n' } : SysState a)
      (fun out => (w.toRight out).isNone) c.left.outbox (Effect.emits r.2)
      (fun out hout => by simp [htidy out hout])
    rw [← houtbox] at hrun
    exact ((heq c.left.outbox) ▸ hreach n hn).run hrun
  · rw [houtbox] at hout
    rcases List.mem_append.mp hout with hout | hout
    · exact htidy out hout
    · simpa using (List.mem_filter.mp hout).2

private theorem settle_inr {c : SysState (a.join b w)} (hc : Seen env w c.left) (j : τ.Id)
    (r : b.State j × List (Effect τ j)) :
    Seen env w (c.settle env (.inr j) (r.1, r.2.flatMap fun eff => [w.right a eff])).left := by
  rw [SysState.left_settle_inr]
  exact hc.inputs _

private theorem start_inr {c : SysState (a.join b w)} (hc : Seen env w c.left) (j : τ.Id) :
    Seen env w (c.startActor env (.inr j)).left := by
  have hleft : ({ c with up := update c.up (.inr j) true } : SysState (a.join b w)).left
      = c.left :=
    SysState.ext' rfl (funext fun k => update_inr_inl c.up j true k) rfl rfl rfl
  exact settle_inr (c := { c with up := update c.up (.inr j) true }) (hleft ▸ hc) j
    ((b.actor j).recover (c.state (.inr j)))

private theorem step {c c' : SysState (a.join b w)} {ev : Event (joinSig σ τ)}
    (hc : Seen env w c.left) (hstep : c.step env ev = some c') : Seen env w c'.left := by
  cases ev with
  | input x =>
    obtain rfl := SysState.step_input.mp hstep
    cases x with
    | inl x =>
      have hleft : ({ c with net := c.net ++ [⟨none, .inl (a.accept x).1, (a.accept x).2⟩] } :
          SysState (a.join b w)).left = { c.left with
            net := c.left.net ++ [x].map fun x => ⟨none, (a.accept x).1, (a.accept x).2⟩ } := by
        simp [SysState.left, Envelope.left?]
      exact hleft ▸ hc.inputs [x]
    | inr y =>
      have hleft : ({ c with net := c.net ++ [⟨none, .inr (b.accept y).1, (b.accept y).2⟩] } :
          SysState (a.join b w)).left = c.left := by
        simp [SysState.left, Envelope.left?]
      exact hleft ▸ hc
  | deliver e =>
    obtain ⟨hup, hdel, rfl⟩ := SysState.step_deliver.mp hstep
    obtain ⟨src, i | j, msg⟩ := e
    · refine settle (c := { c with net := c.net.erase ⟨src, .inl i, msg⟩ }) hc.tidy i
        ((a.actor i).step (c.state (.inl i)) msg) fun n hn => ?_
      have hmem := SysState.mem_of_deliverable hdel
      have outside : src.bind Sum.getLeft? = none →
          a.Reachable env.left (({ c.left with net := n } : SysState a).settle env.left i
            ((a.actor i).step (c.state (.inl i)) msg)) := fun hsrc =>
        hc.handle_outside (u := ⟨src.bind Sum.getLeft?, i, msg⟩)
          (List.mem_filterMap.mpr ⟨_, hmem, rfl⟩) hsrc hup
          (Thin.of_filterMap_erase (fun u hu => by
            simp only [Envelope.left?, Option.some.injEq] at hu
            rw [← hu]
            exact hsrc) c.net hn)
      rcases src with _ | s | j'
      · exact outside rfl
      · have herase : (c.net.erase ⟨some (.inl s), .inl i, msg⟩).filterMap Envelope.left?
            = c.left.net.erase ⟨some s, i, msg⟩ :=
          filterMap_erase (fun e' => Envelope.left?_eq_inside e') c.net
        obtain ⟨m, hm, rfl, hmm⟩ := Thin.unerase (u := ⟨some s, i, msg⟩) (l' := c.left.net)
          (by simp) (List.mem_filterMap.mpr ⟨_, hmem, rfl⟩) ((congrArg (Thin n) herase).mp hn)
        exact (hc.reach m hm).step (.deliver ⟨some s, i, msg⟩) (SysState.step_deliver.mpr
          ⟨hup, SysState.deliverable_left hm hdel, rfl⟩)
      · exact outside rfl
    · have hleft : ({ c with net := c.net.erase ⟨src, .inr j, msg⟩ } :
          SysState (a.join b w)).left = c.left :=
        SysState.ext' rfl rfl (filterMap_erase_of_none rfl c.net) rfl rfl
      exact settle_inr (c := { c with net := c.net.erase ⟨src, .inr j, msg⟩ }) (hleft ▸ hc) j
        ((b.actor j).step (c.state (.inr j)) msg)
  | duplicate e =>
    obtain ⟨hup, hdup, hdel, rfl⟩ := SysState.step_duplicate.mp hstep
    obtain ⟨src, i | j, msg⟩ := e
    · refine settle (c := c) hc.tidy i ((a.actor i).step (c.state (.inl i)) msg) fun n hn => ?_
      have outside : src.bind Sum.getLeft? = none →
          a.Reachable env.left (({ c.left with net := n } : SysState a).settle env.left i
            ((a.actor i).step (c.state (.inl i)) msg)) := fun hsrc =>
        hc.handle_outside (u := ⟨src.bind Sum.getLeft?, i, msg⟩)
          (List.mem_filterMap.mpr ⟨_, SysState.mem_of_deliverable hdel, rfl⟩) hsrc hup hn
      rcases src with _ | s | j'
      · exact outside rfl
      · exact (hc.reach n hn).step (.duplicate ⟨some s, i, msg⟩) (SysState.step_duplicate.mpr
          ⟨hup, hdup, SysState.deliverable_left hn hdel, rfl⟩)
      · exact outside rfl
    · exact settle_inr hc j ((b.actor j).step (c.state (.inr j)) msg)
  | drop e =>
    obtain ⟨hlossy, hmem, rfl⟩ := SysState.step_drop.mp hstep
    obtain ⟨src, i | j, msg⟩ := e
    · have outside : src.bind Sum.getLeft? = none →
          Seen env w ({ c with net := c.net.erase ⟨src, .inl i, msg⟩ } :
            SysState (a.join b w)).left := fun hsrc =>
        ⟨fun n hn => hc.reach n (Thin.of_filterMap_erase (fun u hu => by
          simp only [Envelope.left?, Option.some.injEq] at hu
          rw [← hu]
          exact hsrc) c.net hn), hc.tidy⟩
      rcases src with _ | s | j'
      · exact outside rfl
      · refine ⟨fun n hn => ?_, hc.tidy⟩
        have herase : (c.net.erase ⟨some (.inl s), .inl i, msg⟩).filterMap Envelope.left?
            = c.left.net.erase ⟨some s, i, msg⟩ :=
          filterMap_erase (fun e' => Envelope.left?_eq_inside e') c.net
        obtain ⟨m, hm, rfl, hmm⟩ := Thin.unerase (u := ⟨some s, i, msg⟩) (l' := c.left.net)
          (by simp) (List.mem_filterMap.mpr ⟨_, hmem, rfl⟩) ((congrArg (Thin n) herase).mp hn)
        exact (hc.reach m hm).step (.drop ⟨some s, i, msg⟩)
          (SysState.step_drop.mpr ⟨hlossy, hmm, rfl⟩)
      · exact outside rfl
    · have hleft : ({ c with net := c.net.erase ⟨src, .inr j, msg⟩ } :
          SysState (a.join b w)).left = c.left :=
        SysState.ext' rfl rfl (filterMap_erase_of_none rfl c.net) rfl rfl
      exact hleft ▸ hc
  | timeout i msg =>
    obtain ⟨hup, hmem, rfl⟩ := SysState.step_timeout.mp hstep
    cases i with
    | inl i =>
      have hleft : ({ c with timers := update c.timers (.inl i) ((c.timers (.inl i)).erase msg) } :
          SysState (a.join b w)).left
          = { c.left with timers := update c.left.timers i ((c.left.timers i).erase msg) } :=
        SysState.ext' rfl rfl rfl (update_inl c.timers i _) rfl
      refine settle
        (c := { c with timers := update c.timers (.inl i) ((c.timers (.inl i)).erase msg) })
        hc.tidy i ((a.actor i).step (c.state (.inl i)) msg) fun n hn => ?_
      rw [hleft]
      exact (hc.reach n hn).step (.timeout i msg) (SysState.step_timeout.mpr ⟨hup, hmem, rfl⟩)
    | inr j =>
      have hleft : ({ c with timers := update c.timers (.inr j) ((c.timers (.inr j)).erase msg) } :
          SysState (a.join b w)).left = c.left :=
        SysState.ext' rfl rfl rfl (funext fun k => update_inr_inl c.timers j ((c.timers (.inr j)).erase msg) k) rfl
      exact settle_inr
        (c := { c with timers := update c.timers (.inr j) ((c.timers (.inr j)).erase msg) })
        (hleft ▸ hc) j ((b.actor j).step (c.state (.inr j)) msg)
  | output out =>
    obtain ⟨hmem, rfl⟩ := SysState.step_output.mp hstep
    cases out with
    | inl out =>
      have houtbox := filterMap_erase (f := Sum.getLeft?) (a := (.inl out : σ.Out ⊕ τ.Out))
        (b := out) (fun x => by cases x <;> simp) c.outbox
      refine ⟨fun n hn => ?_, fun o ho =>
        hc.tidy o (List.mem_of_mem_erase ((congrArg (o ∈ ·) houtbox).mp ho))⟩
      exact (congrArg (fun outbox =>
        a.Reachable env.left ({ c.left with net := n, outbox := outbox } : SysState a)) houtbox).mpr
        ((hc.reach n hn).step (.output out) (SysState.step_output.mpr
          ⟨List.mem_filterMap.mpr ⟨_, hmem, rfl⟩, rfl⟩))
    | inr out =>
      have houtbox := filterMap_erase_of_none (f := Sum.getLeft? (α := σ.Out))
        (a := (.inr out : σ.Out ⊕ τ.Out)) rfl c.outbox
      refine ⟨fun n hn => ?_, fun o ho =>
        hc.tidy o ((congrArg (o ∈ ·) houtbox).mp ho)⟩
      exact (congrArg (fun outbox =>
        a.Reachable env.left ({ c.left with net := n, outbox := outbox } : SysState a)) houtbox).mpr
        (hc.reach n hn)
  | crash i =>
    obtain ⟨hup, hcrash, rfl⟩ := SysState.step_crash.mp hstep
    cases i with
    | inl i =>
      refine ⟨fun n hn => ?_, hc.tidy⟩
      obtain ⟨m, hm, rfl⟩ := SysState.thin_down c.net hn
      have hdown : ({ (c.down env (.inl i)).left with
          net := m.filter fun e => decide (e.dst ≠ i) || (env.left.link e.src e.dst).lossy } :
            SysState a) = ({ c.left with net := m } : SysState a).down env.left i :=
        SysState.ext' rfl (update_inl c.up i false) rfl (update_inl c.timers i []) rfl
      exact (hc.reach m hm).step (.crash i) (SysState.step_crash.mpr ⟨hup, hcrash, hdown⟩)
    | inr j =>
      have hleft : (c.down env (.inr j)).left = c.left :=
        SysState.ext' rfl (funext fun k => update_inr_inl c.up j false k)
          (filterMap_filter_of_none SysState.left?_of_dropped c.net)
          (funext fun k => update_inr_inl c.timers j [] k) rfl
      exact hleft ▸ hc
  | start i =>
    obtain ⟨hup, hmail, rfl⟩ := SysState.step_start.mp hstep
    cases i with
    | inl i =>
      have hleft : ({ c with up := update c.up (.inl i) true } : SysState (a.join b w)).left
          = { c.left with up := update c.left.up i true } :=
        SysState.ext' rfl (update_inl c.up i true) rfl rfl rfl
      refine settle (c := { c with up := update c.up (.inl i) true }) hc.tidy i
        ((a.actor i).recover (c.state (.inl i))) fun n hn => ?_
      rw [hleft]
      by_cases hmail' : ({ c.left with net := n } : SysState a).hasMail i = true
          ∨ env.left.restarts i = true
      · exact (hc.reach n hn).step (.start i) (SysState.step_start.mpr ⟨hup, hmail', rfl⟩)
      · have hjoin : c.hasMail (.inl i) = true := hmail.resolve_right fun h => hmail' (.inr h)
        obtain ⟨e, he, hdst⟩ : ∃ e ∈ c.net, e.dst = .inl i := by
          simpa [SysState.hasMail] using hjoin
        obtain ⟨src, k | j, msg⟩ := e
        · obtain rfl : k = i := by simpa using hdst
          have hu : (⟨src.bind Sum.getLeft?, k, msg⟩ : Envelope σ) ∈ c.left.net :=
            List.mem_filterMap.mpr ⟨_, he, rfl⟩
          have hun : (⟨src.bind Sum.getLeft?, k, msg⟩ : Envelope σ) ∉ n := fun h =>
            hmail' (.inl (by simpa [SysState.hasMail] using ⟨_, h, rfl⟩))
          have hsrc : src.bind Sum.getLeft? = none :=
            Classical.byContradiction fun h => hun (hn.mem hu h)
          obtain ⟨m, hm, rfl, hmm⟩ := Thin.insert hu hun hn
          have hlossy : (env.left.link (src.bind Sum.getLeft?) k).lossy = true := by
            rw [hsrc]
            rfl
          obtain ⟨hkept, heq⟩ := SysState.settle_erase (env := env.left)
            ({ c.left with net := m, up := update c.left.up k true } : SysState a) k
            ((a.actor k).recover (c.state (.inl k))) hmm hlossy
          have hstart := (hc.reach m hm).step (.start k) (SysState.step_start.mpr
            ⟨hup, .inl (by simpa [SysState.hasMail] using ⟨_, hmm, rfl⟩), rfl⟩)
          exact heq ▸ hstart.step (.drop _) (SysState.step_drop.mpr ⟨hlossy, hkept, rfl⟩)
        · simp at hdst
    | inr j => exact start_inr hc j

/-- Booting the actors of `a` in the join is booting `a` alone, with the outputs wired to `b`
still waiting. -/
private theorem boot (l : List σ.Id) :
    ∀ (c : SysState (a.join b w)) {n' : List (Envelope σ)},
      Thin n' (l.foldl (fun c i => c.startActor env (.inl i)) c).left.net →
      ∃ n, Thin n c.left.net ∧ ∀ outbox,
        outbox.filter (fun out => (w.toRight out).isNone) = c.left.outbox →
        ∃ outbox', outbox'.filter (fun out => (w.toRight out).isNone)
            = (l.foldl (fun c i => c.startActor env (.inl i)) c).left.outbox ∧
          l.foldl (fun c i => c.startActor env.left i)
              ({ c.left with net := n, outbox := outbox } : SysState a)
            = { (l.foldl (fun c i => c.startActor env (.inl i)) c).left with
                net := n', outbox := outbox' } := by
  induction l with
  | nil => exact fun c n' h => ⟨n', h, fun outbox ho => ⟨outbox, ho, rfl⟩⟩
  | cons i l ih =>
    intro c n' h
    obtain ⟨n₁, hn₁, h₁⟩ := ih (c.startActor env (.inl i)) h
    obtain ⟨n, hn, h₀⟩ := SysState.settle_left (env := env)
      ({ c with up := update c.up (.inl i) true }) i ((a.actor i).recover (c.state (.inl i))) hn₁
    have hleft : ({ c with up := update c.up (.inl i) true } : SysState (a.join b w)).left
        = { c.left with up := update c.left.up i true } :=
      SysState.ext' rfl (update_inl c.up i true) rfl rfl rfl
    have houtbox : (c.startActor env (.inl i)).left.outbox
        = c.left.outbox ++ (Effect.emits ((a.actor i).recover (c.state (.inl i))).2).filter
          fun out => (w.toRight out).isNone := by
      show (SysState.settle env ({ c with up := update c.up (.inl i) true }) (.inl i)
        (((a.actor i).recover (c.state (.inl i))).1,
          ((a.actor i).recover (c.state (.inl i))).2.flatMap fun eff => [w.left b eff])).left.outbox
        = _
      rw [SysState.left_settle]
      split <;> rfl
    refine ⟨n, hn, fun outbox ho => ?_⟩
    obtain ⟨outbox', ho', h'⟩ := h₁ (outbox ++ Effect.emits ((a.actor i).recover (c.state (.inl i))).2)
      (by rw [List.filter_append, ho, houtbox])
    refine ⟨outbox', ho', ?_⟩
    rw [List.foldl_cons, List.foldl_cons, ← h']
    congr 1
    have h₂ := h₀ outbox
    rw [hleft] at h₂
    exact h₂

private theorem init (env : EnvModel (joinSig σ τ)) :
    Seen env w (SysState.init (a.join b w) env).left := by
  have hfold : SysState.init (a.join b w) env
      = b.boot.foldl (fun c j => c.startActor env (.inr j))
        (a.boot.foldl (fun c i => c.startActor env (.inl i)) (SysState.blank (a.join b w))) := by
    simp [SysState.init, List.foldl_append, List.foldl_map]
  have hright : ∀ (l : List τ.Id) (c : SysState (a.join b w)), Seen env w c.left →
      Seen env w (l.foldl (fun c j => c.startActor env (.inr j)) c).left := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons j l ih => exact fun c hc => ih _ (start_inr hc j)
  rw [hfold]
  apply hright
  have hboot : ∀ n', Thin n' (a.boot.foldl (fun c i => c.startActor env (.inl i))
      (SysState.blank (a.join b w))).left.net →
      ∃ outbox', outbox'.filter (fun out => (w.toRight out).isNone)
          = (a.boot.foldl (fun c i => c.startActor env (.inl i))
            (SysState.blank (a.join b w))).left.outbox ∧
        SysState.init a env.left = { (a.boot.foldl (fun c i => c.startActor env (.inl i))
          (SysState.blank (a.join b w))).left with net := n', outbox := outbox' } := by
    intro n' hn'
    obtain ⟨n, hn, h⟩ := boot a.boot (SysState.blank (a.join b w)) hn'
    obtain rfl : n = [] := by
      cases hn
      rfl
    exact h [] rfl
  refine ⟨fun n' hn' => ?_, fun out hout => ?_⟩
  · obtain ⟨outbox', ho', heq⟩ := hboot n' hn'
    have hrun := SysState.run_outputs_filter env.left
      ({ (a.boot.foldl (fun c i => c.startActor env (.inl i))
        (SysState.blank (a.join b w))).left with net := n' } : SysState a)
      (fun out => (w.toRight out).isNone) [] outbox' (by simp)
    simp only [List.nil_append, ho'] at hrun
    exact (heq ▸ System.Reachable.init).run hrun
  · obtain ⟨outbox', ho', -⟩ := hboot _ (Thin.refl _)
    rw [← ho'] at hout
    simpa using (List.mem_filter.mp hout).2

end Seen

variable {c : SysState (a.join b w)}

/-- Every reachable state of a join, seen from its left system, is a state that system reaches
alone, when its inputs may be lost, repeated and reordered. -/
theorem System.Reachable.left (h : (a.join b w).Reachable env c) : a.Reachable env.left c.left := by
  have hseen : Seen env w c.left := by
    induction h with
    | init => exact Seen.init env
    | step ev _ hstep ih => exact ih.step hstep
  exact hseen.reach _ (Thin.refl _)

/-- What is proved of a system alone, with a network link from outside, holds of it in every
join. -/
theorem System.Invariant.join_left {P : SysState a → Prop} (h : a.Invariant env.left P) :
    (a.join b w).Invariant env fun c => P c.left :=
  fun _ hc => h _ hc.left

theorem System.Invariant.join_left_state {Q : ((i : σ.Id) → a.State i) → Prop}
    (h : ∀ env, a.Invariant env fun c => Q c.state) :
    (a.join b w).Invariant env fun c => Q fun i => c.state (.inl i) :=
  fun _ hc => h env.left _ hc.left

end Left

end Lanes
