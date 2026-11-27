/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Join
public import Lanes.Proof.Deed
public import Lanes.Core.Run
public import Lanes.Proof.Equiv
public import Lanes.Core.FairScheduler

/-!
# What survives a join

`SysState.left` is a state of `a.join b w` seen from `a`: its actors, its timers, the messages
on their way to it and the outputs that are its own. `System.Reachable.left` proves that every
reachable state of the join, seen from `a`, is a reachable state of `a` alone, under
`EnvModel.left`. So whatever is proved of `a` for every environment holds of `a` inside any join
(`System.Invariant.join_left`).

`SysState.run_left` is the same of runs: a run of the join, seen from `a`, is a run of `a` alone
in which the actors handle the same messages and the same outputs are handed over, in the same
order (`Deed`). So a statement that counts what `a` does, proved of every run of `a` alone, holds
of `a` inside any join. What the two runs do not share is the inputs: alone, `a` may be put in a
message fewer times than the join delivers it, since its link from outside duplicates.

Seen from `a`, a message from `b` is an input. Inputs of `a` alone all travel on one link, so
that link is modelled as the most permissive one, `Link.network`.

One event of the join is zero or more events of `a` alone, but not always the same ones in the
same order: two equal inputs from different senders are two messages in the join and one kind
of message alone, and the join may take the newer first. So the proof carries, for every state
of the join, every way of leaving out messages from outside (`Thin`): alone, `a` never receives
a message the join is going to remove out of turn.

`SysState.step_swap` exchanges the two sides of a join, which gives the same for `b`
(`System.Reachable.right`) up to one difference. `a` boots first, so what its boot sends `b` is
in flight before the first messages of `b` itself, and alone `b` receives inputs only after it
has booted. Seen from `b` the join is therefore a state of `b` alone up to `SysState.Equiv`, the
order of messages on different links, and exactly one when the boot of `a` sends `b` nothing
(`System.Reachable.right_of_quiet_boot`).

Without the messages from outside in flight (`SysState.thinLeft`, `SysState.thinRight`), each
step of the join is a run of either side alone (`SysState.exists_block`,
`SysState.exists_blockRight`), from where that side alone starts (`SysState.init_thinLeft`,
`SysState.init_thinRight`). For `b` this is exact: what the boot of `a` sends it is from outside.
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

/-- The join seen from `a` with the messages from outside in flight left out: what `a` alone
reaches when each message from outside is put in just before the join delivers it. -/
def SysState.thinLeft (c : SysState (a.join b w)) : SysState a :=
  { c.left with net := c.left.net.filter fun e => e.src.isSome }

/-- The event of `a` alone that meets the obligation an event of the join meets, if any. -/
def Event.left? : Event (joinSig σ τ) → Option (Event σ)
  | .deliver e => e.left?.map .deliver
  | .timeout (.inl i) msg => some (.timeout i msg)
  | .start (.inl i) => some (.start i)
  | .output (.inl out) => some (.output out)
  | _ => none

/-- What an event of a join shows the left system doing. -/
def Event.leftDeed : Event (joinSig σ τ) → Option (Deed σ)
  | .deliver ⟨_, .inl i, msg⟩ | .duplicate ⟨_, .inl i, msg⟩ => some (.handle i msg)
  | .timeout (.inl i) msg => some (.handle i msg)
  | .output (.inl out) => some (.output out)
  | _ => none

/-- What an event of the left system alone shows that the join shows too. Alone, an output the
wiring routes to the other system is handed over; in the join it is a message. -/
def Wiring.shown (w : Wiring σ τ) (ev : Event σ) : Option (Deed σ) :=
  ev.deed.filter fun
    | .output out => (w.toRight out).isNone
    | .handle .. => true

/-- The join seen from `b` with the messages from outside in flight left out. The messages from
`a` are from outside too, those its boot sent before `b` booted among them. -/
def SysState.thinRight (c : SysState (a.join b w)) : SysState b :=
  { c.right with net := c.right.net.filter fun e => e.src.isSome }

/-- The event of `b` alone that meets the obligation an event of the join meets, if any. -/
def Event.right? : Event (joinSig σ τ) → Option (Event τ)
  | .deliver e => e.right?.map .deliver
  | .timeout (.inr j) msg => some (.timeout j msg)
  | .start (.inr j) => some (.start j)
  | .output (.inr out) => some (.output out)
  | _ => none

/-- What an event of a join shows the right system doing. -/
def Event.rightDeed : Event (joinSig σ τ) → Option (Deed τ)
  | .deliver ⟨_, .inr j, msg⟩ | .duplicate ⟨_, .inr j, msg⟩ => some (.handle j msg)
  | .timeout (.inr j) msg => some (.handle j msg)
  | .output (.inr out) => some (.output out)
  | _ => none

/-- What an event of the right system alone shows that the join shows too. -/
def Wiring.shownRight (w : Wiring σ τ) (ev : Event τ) : Option (Deed τ) :=
  ev.deed.filter fun
    | .output out => (w.toLeft out).isNone
    | .handle .. => true

end Lanes

end

public section

namespace Lanes

private theorem update_inl {α β : Type} [DecidableEq α] [DecidableEq β] {γ : α ⊕ β → Type}
    (f : (x : α ⊕ β) → γ x) (i : α) (v : γ (.inl i)) :
    (fun k => update f (.inl i) v (.inl k))
      = update (β := fun k => γ (.inl k)) (fun k => f (.inl k)) i v := by
  funext k
  by_cases h : k = i
  · subst h; simp
  · rw [update_of_ne _ _ h, update_of_ne _ _ (by simpa using h)]

private theorem update_inr_inl {α β : Type} [DecidableEq α] [DecidableEq β] {γ : α ⊕ β → Type}
    (f : (x : α ⊕ β) → γ x) (j : β) (v : γ (.inr j)) (k : α) :
    update f (.inr j) v (.inl k) = f (.inl k) :=
  update_of_ne _ _ (by simp)

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

private theorem subset {l l' : List (Envelope σ)} (h : Thin l l') {e : Envelope σ} (he : e ∈ l) :
    e ∈ l' := by
  induction h with
  | nil => exact he
  | keep x _ ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih he)
  | skip _ _ ih => exact List.mem_cons_of_mem _ (ih he)

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

theorem sends_left (effs : List (Effect σ i)) :
    (Effect.sends (σ := joinSig σ τ) (.inl i) (effs.flatMap fun eff => [w.left b eff])).filterMap
      Envelope.left? = Effect.sends i effs := by
  simp only [Effect.sends, ← List.map_eq_flatMap, List.filterMap_map, List.filterMap_filterMap]
  congr 1
  funext eff
  cases eff with
  | emit out => cases h : w.toRight out <;> simp [Wiring.left, h, Envelope.left?]
  | _ => simp [Wiring.left, Envelope.left?]

theorem emits_left (effs : List (Effect σ i)) :
    (Effect.emits (effs.flatMap fun eff => [w.left b eff])).filterMap Sum.getLeft?
      = (Effect.emits effs).filter fun out => (w.toRight out).isNone := by
  simp only [Effect.emits, ← List.map_eq_flatMap, List.filterMap_map, List.filterMap_filterMap,
    List.filter_filterMap]
  congr 1
  funext eff
  cases eff with
  | emit out => cases h : w.toRight out <;> simp [Wiring.left, h, Option.filter]
  | _ => simp [Wiring.left]

theorem retime_left (effs : List (Effect σ i)) (timers : List (σ.Msg i)) :
    Effect.retime (σ := joinSig σ τ) (i := .inl i) (effs.flatMap fun eff => [w.left b eff]) timers
      = Effect.retime effs timers := by
  simp only [Effect.retime, ← List.map_eq_flatMap, List.foldl_map]
  congr 1
  funext timers eff
  cases eff with
  | emit out => cases h : w.toRight out <;> simp [Wiring.left, h]
  | _ => simp [Wiring.left]

theorem isStop_left (effs : List (Effect σ i)) :
    (effs.flatMap fun eff => [w.left b eff]).any Effect.isStop = effs.any Effect.isStop :=
  Effect.any_isStop_flatMap (fun eff => by
    cases eff with
    | emit out => cases h : w.toRight out <;> simp [Effect.isStop, Wiring.left, h]
    | _ => simp [Effect.isStop, Wiring.left]) effs

theorem sends_right_left (effs : List (Effect τ j)) :
    (Effect.sends (σ := joinSig σ τ) (.inr j) (effs.flatMap fun eff => [w.right a eff])).filterMap
      Envelope.left?
      = ((Effect.emits effs).filterMap w.toLeft).map fun x =>
          ⟨none, (a.accept x).1, (a.accept x).2⟩ := by
  simp only [Effect.sends, Effect.emits, ← List.map_eq_flatMap, List.filterMap_map,
    List.filterMap_filterMap, List.map_filterMap]
  congr 1
  funext eff
  cases eff with
  | emit out => cases h : w.toLeft out <;> simp [Wiring.right, h, Envelope.left?]
  | _ => simp [Wiring.right, Envelope.left?]

theorem emits_right_left (effs : List (Effect τ j)) :
    (Effect.emits (effs.flatMap fun eff => [w.right a eff])).filterMap Sum.getLeft?
      = ([] : List σ.Out) := by
  simp only [Effect.emits, ← List.map_eq_flatMap, List.filterMap_map, List.filterMap_filterMap,
    List.filterMap_eq_nil_iff]
  intro eff _
  cases eff with
  | emit out => cases h : w.toLeft out <;> simp [Wiring.right, h]
  | _ => simp [Wiring.right]

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

theorem left_settle (c : SysState (a.join b w)) (i : σ.Id)
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
          outbox := c.left.outbox ++ (Effect.emits r.2).filter fun out =>
            (w.toRight out).isNone } := by
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

theorem left_settle_inr (c : SysState (a.join b w)) (j : τ.Id)
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
left out it is a state `a` reaches alone, and no output waits that the wiring routes to `b`.
`R t` is "reaches alone, showing `t`": by a run with those deeds for the system that boots
first, and reachable up to the order of messages on different links for the other. -/
private structure Seen (env : EnvModel (joinSig σ τ)) (w : Wiring σ τ)
    (R : List (Deed σ) → SysState a → Prop) (t : List (Deed σ)) (c : SysState a) : Prop where
  closed : ∀ {t : List (Deed σ)} {x x' : SysState a} (ev : Event σ), R t x →
    x.step env.left ev = some x' → R (t ++ (w.shown ev).toList) x'
  reach : ∀ n, Thin n c.net → R t { c with net := n }
  tidy : ∀ out ∈ c.outbox, w.toRight out = none

/-- A run of events that show nothing. -/
private theorem run_closed {env : EnvModel σ} {R : List (Deed σ) → SysState a → Prop}
    (closed : ∀ {t : List (Deed σ)} {x x' : SysState a} (ev : Event σ), R t x →
      x.step env ev = some x' → R (t ++ (w.shown ev).toList) x') :
    ∀ {evs : List (Event σ)} {t : List (Deed σ)} {x x' : SysState a},
      (∀ ev ∈ evs, w.shown ev = none) → R t x → x.run env evs = some x' → R t x' := by
  intro evs
  induction evs with
  | nil =>
    intro t x x' _ hx hrun
    simp only [SysState.run, Option.some.injEq] at hrun
    exact hrun ▸ hx
  | cons ev evs ih =>
    intro t x x' hquiet hx hrun
    simp only [SysState.run] at hrun
    cases hstep : x.step env ev with
    | none => simp [hstep] at hrun
    | some x₁ =>
      have hx₁ := closed ev hx hstep
      rw [hquiet ev List.mem_cons_self, Option.toList_none, List.append_nil] at hx₁
      exact ih (fun ev' h => hquiet ev' (List.mem_cons_of_mem _ h)) hx₁
        (by simpa [hstep] using hrun)

private theorem shown_inputs (xs : List σ.In) :
    ∀ ev ∈ xs.map (Event.input (σ := σ)), w.shown ev = none := by
  intro ev hev
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hev
  rfl

private theorem shown_wired (outs : List σ.Out) :
    ∀ ev ∈ (outs.filter fun out => !(w.toRight out).isNone).map (Event.output (σ := σ)),
      w.shown ev = none := by
  intro ev hev
  obtain ⟨out, hout, rfl⟩ := List.mem_map.mp hev
  have hwired := (List.mem_filter.mp hout).2
  simp only [Bool.not_eq_true'] at hwired
  simp [Wiring.shown, Event.deed, hwired]

/-- Reached alone by a run that shows `t`. -/
private def Shows (a : System σ) (env : EnvModel σ) (w : Wiring σ τ) (t : List (Deed σ))
    (c : SysState a) : Prop :=
  ∃ evs, (SysState.init a env).run env evs = some c ∧ evs.filterMap w.shown = t

private theorem Shows.step {env : EnvModel σ} {t : List (Deed σ)} {x x' : SysState a}
    (ev : Event σ) (h : Shows a env w t x) (hstep : x.step env ev = some x') :
    Shows a env w (t ++ (w.shown ev).toList) x' := by
  obtain ⟨evs, hrun, rfl⟩ := h
  exact ⟨evs ++ [ev], by simp [SysState.run_append, hrun, SysState.run, hstep],
    filterMap_concat _ _ _⟩

namespace Seen

variable {R : List (Deed σ) → SysState a → Prop} {t : List (Deed σ)}

/-- One event of `a` alone that shows nothing. -/
private theorem quiet {c : SysState a} (hc : Seen env w R t c) {t' : List (Deed σ)}
    {x x' : SysState a} (ev : Event σ) (hquiet : w.shown ev = none) (hx : R t' x)
    (hstep : x.step env.left ev = some x') : R t' x' := by
  have h := hc.closed ev hx hstep
  rwa [hquiet, Option.toList_none, List.append_nil] at h

private theorem still {c : SysState a} (hc : Seen env w R t c) : Seen env w R (t ++ []) c :=
  (List.append_nil t).symm ▸ hc

private theorem inputs {c : SysState a} (hc : Seen env w R t c) (xs : List σ.In) :
    Seen env w R t { c with
      net := c.net ++ xs.map fun x => ⟨none, (a.accept x).1, (a.accept x).2⟩ } := by
  refine ⟨hc.closed, fun n hn => ?_, hc.tidy⟩
  obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := hn.of_append
  obtain ⟨ys, rfl⟩ := h₂.of_map
  exact run_closed hc.closed (shown_inputs ys) (hc.reach n₁ h₁)
    (SysState.run_inputs env.left _ ys)

/-- A message from outside is handled whether or not `a` alone still has it in flight: it is
duplicated if so, and otherwise it is the one message put back and delivered. -/
private theorem handle_outside {c : SysState a} (hc : Seen env w R t c) {u : Envelope σ}
    (hu : u ∈ c.net) (hsrc : u.src = none) (hup : c.up u.dst = true) {n : List (Envelope σ)}
    (hn : Thin n c.net) :
    R (t ++ [.handle u.dst u.msg])
      (({ c with net := n } : SysState a).handle env.left u.dst u.msg) := by
  have hlink : env.left.link u.src u.dst = Link.network := by
    rw [hsrc]
    rfl
  by_cases hmem : u ∈ n
  · exact hc.closed (.duplicate u) (hc.reach n hn) (SysState.step_duplicate.mpr
      ⟨hup, by rw [hlink]; rfl, by simp [SysState.deliverable, hlink, Link.network, hmem], rfl⟩)
  · obtain ⟨m, hm, rfl, hmm⟩ := Thin.insert hu hmem hn
    exact hc.closed (.deliver u) (hc.reach m hm) (SysState.step_deliver.mpr
      ⟨hup, by simp [SysState.deliverable, hlink, Link.network, hmm], rfl⟩)

private theorem settle {c : SysState (a.join b w)}
    (closed : ∀ {t : List (Deed σ)} {x x' : SysState a} (ev : Event σ), R t x →
      x.step env.left ev = some x' → R (t ++ (w.shown ev).toList) x')
    (htidy : ∀ out ∈ c.left.outbox, w.toRight out = none) (i : σ.Id)
    (r : a.State i × List (Effect σ i))
    (hreach : ∀ n, Thin n c.left.net →
      R t (({ c.left with net := n } : SysState a).settle env.left i r)) :
    Seen env w R t (c.settle env (.inl i) (r.1, r.2.flatMap fun eff => [w.left b eff])).left := by
  have houtbox : (c.settle env (.inl i) (r.1, r.2.flatMap fun eff => [w.left b eff])).left.outbox
      = c.left.outbox ++ (Effect.emits r.2).filter fun out => (w.toRight out).isNone := by
    rw [SysState.left_settle]
    split <;> rfl
  refine ⟨closed, fun n' hn' => ?_, fun out hout => ?_⟩
  · obtain ⟨n, hn, heq⟩ := SysState.settle_left c i r hn'
    have hrun := SysState.run_outputs_filter env.left
      ({ (c.settle env (.inl i) (r.1, r.2.flatMap fun eff => [w.left b eff])).left with
        net := n' } : SysState a)
      (fun out => (w.toRight out).isNone) c.left.outbox (Effect.emits r.2)
      (fun out hout => by simp [htidy out hout])
    rw [← houtbox] at hrun
    exact run_closed closed (shown_wired _) ((heq c.left.outbox) ▸ hreach n hn) hrun
  · rw [houtbox] at hout
    rcases List.mem_append.mp hout with hout | hout
    · exact htidy out hout
    · simpa using (List.mem_filter.mp hout).2

private theorem settle_inr {c : SysState (a.join b w)} (hc : Seen env w R t c.left) (j : τ.Id)
    (r : b.State j × List (Effect τ j)) :
    Seen env w R t (c.settle env (.inr j) (r.1, r.2.flatMap fun eff => [w.right a eff])).left := by
  rw [SysState.left_settle_inr]
  exact hc.inputs _

private theorem start_inr {c : SysState (a.join b w)} (hc : Seen env w R t c.left) (j : τ.Id) :
    Seen env w R t (c.startActor env (.inr j)).left := by
  have hleft : ({ c with up := update c.up (.inr j) true } : SysState (a.join b w)).left
      = c.left :=
    SysState.ext' rfl (funext fun k => update_inr_inl c.up j true k) rfl rfl rfl
  exact settle_inr (c := { c with up := update c.up (.inr j) true }) (hleft ▸ hc) j
    ((b.actor j).recover (c.state (.inr j)))

private theorem step_input {c c' : SysState (a.join b w)} {x : σ.In ⊕ τ.In}
    (hc : Seen env w R t c.left) (hstep : c.step env (.input x) = some c') :
    Seen env w R t c'.left := by
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

private theorem step_deliver {c c' : SysState (a.join b w)} {e : Envelope (joinSig σ τ)}
    (hc : Seen env w R t c.left) (hstep : c.step env (.deliver e) = some c') :
    Seen env w R (t ++ (Event.deliver e).leftDeed.toList) c'.left := by
  obtain ⟨hup, hdel, rfl⟩ := SysState.step_deliver.mp hstep
  obtain ⟨src, i | j, msg⟩ := e
  · refine settle (c := { c with net := c.net.erase ⟨src, .inl i, msg⟩ }) hc.closed hc.tidy i
      ((a.actor i).step (c.state (.inl i)) msg) fun n hn => ?_
    have hmem := SysState.mem_of_deliverable hdel
    have outside : src.bind Sum.getLeft? = none →
        R (t ++ [.handle i msg]) (({ c.left with net := n } : SysState a).settle env.left i
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
      exact hc.closed (.deliver ⟨some s, i, msg⟩) (hc.reach m hm) (SysState.step_deliver.mpr
        ⟨hup, SysState.deliverable_left hm hdel, rfl⟩)
    · exact outside rfl
  · have hleft : ({ c with net := c.net.erase ⟨src, .inr j, msg⟩ } :
        SysState (a.join b w)).left = c.left :=
      SysState.ext' rfl rfl (filterMap_erase_of_none rfl c.net) rfl rfl
    exact (settle_inr (c := { c with net := c.net.erase ⟨src, .inr j, msg⟩ }) (hleft ▸ hc) j
      ((b.actor j).step (c.state (.inr j)) msg)).still

private theorem step_duplicate {c c' : SysState (a.join b w)} {e : Envelope (joinSig σ τ)}
    (hc : Seen env w R t c.left) (hstep : c.step env (.duplicate e) = some c') :
    Seen env w R (t ++ (Event.duplicate e).leftDeed.toList) c'.left := by
  obtain ⟨hup, hdup, hdel, rfl⟩ := SysState.step_duplicate.mp hstep
  obtain ⟨src, i | j, msg⟩ := e
  · refine settle (c := c) hc.closed hc.tidy i ((a.actor i).step (c.state (.inl i)) msg)
      fun n hn => ?_
    have outside : src.bind Sum.getLeft? = none →
        R (t ++ [.handle i msg]) (({ c.left with net := n } : SysState a).settle env.left i
          ((a.actor i).step (c.state (.inl i)) msg)) := fun hsrc =>
      hc.handle_outside (u := ⟨src.bind Sum.getLeft?, i, msg⟩)
        (List.mem_filterMap.mpr ⟨_, SysState.mem_of_deliverable hdel, rfl⟩) hsrc hup hn
    rcases src with _ | s | j'
    · exact outside rfl
    · exact hc.closed (.duplicate ⟨some s, i, msg⟩) (hc.reach n hn) (SysState.step_duplicate.mpr
        ⟨hup, hdup, SysState.deliverable_left hn hdel, rfl⟩)
    · exact outside rfl
  · exact (settle_inr hc j ((b.actor j).step (c.state (.inr j)) msg)).still

private theorem step_drop {c c' : SysState (a.join b w)} {e : Envelope (joinSig σ τ)}
    (hc : Seen env w R t c.left) (hstep : c.step env (.drop e) = some c') :
    Seen env w R t c'.left := by
  obtain ⟨hlossy, hmem, rfl⟩ := SysState.step_drop.mp hstep
  obtain ⟨src, i | j, msg⟩ := e
  · have outside : src.bind Sum.getLeft? = none →
        Seen env w R t ({ c with net := c.net.erase ⟨src, .inl i, msg⟩ } :
          SysState (a.join b w)).left := fun hsrc =>
      ⟨hc.closed, fun n hn => hc.reach n (Thin.of_filterMap_erase (fun u hu => by
        simp only [Envelope.left?, Option.some.injEq] at hu
        rw [← hu]
        exact hsrc) c.net hn), hc.tidy⟩
    rcases src with _ | s | j'
    · exact outside rfl
    · refine ⟨hc.closed, fun n hn => ?_, hc.tidy⟩
      have herase : (c.net.erase ⟨some (.inl s), .inl i, msg⟩).filterMap Envelope.left?
          = c.left.net.erase ⟨some s, i, msg⟩ :=
        filterMap_erase (fun e' => Envelope.left?_eq_inside e') c.net
      obtain ⟨m, hm, rfl, hmm⟩ := Thin.unerase (u := ⟨some s, i, msg⟩) (l' := c.left.net)
        (by simp) (List.mem_filterMap.mpr ⟨_, hmem, rfl⟩) ((congrArg (Thin n) herase).mp hn)
      exact hc.quiet (.drop ⟨some s, i, msg⟩) rfl (hc.reach m hm)
        (SysState.step_drop.mpr ⟨hlossy, hmm, rfl⟩)
    · exact outside rfl
  · have hleft : ({ c with net := c.net.erase ⟨src, .inr j, msg⟩ } :
        SysState (a.join b w)).left = c.left :=
      SysState.ext' rfl rfl (filterMap_erase_of_none rfl c.net) rfl rfl
    exact hleft ▸ hc

private theorem step_timeout {c c' : SysState (a.join b w)} {i : σ.Id ⊕ τ.Id}
    {msg : (joinSig σ τ).Msg i}
    (hc : Seen env w R t c.left) (hstep : c.step env (.timeout i msg) = some c') :
    Seen env w R (t ++ (Event.timeout i msg).leftDeed.toList) c'.left := by
  obtain ⟨hup, hmem, rfl⟩ := SysState.step_timeout.mp hstep
  cases i with
  | inl i =>
    have hleft : ({ c with timers := update c.timers (.inl i) ((c.timers (.inl i)).erase msg) } :
        SysState (a.join b w)).left
        = { c.left with timers := update c.left.timers i ((c.left.timers i).erase msg) } :=
      SysState.ext' rfl rfl rfl (update_inl c.timers i _) rfl
    refine settle
      (c := { c with timers := update c.timers (.inl i) ((c.timers (.inl i)).erase msg) })
      hc.closed hc.tidy i ((a.actor i).step (c.state (.inl i)) msg) fun n hn => ?_
    rw [hleft]
    exact hc.closed (.timeout i msg) (hc.reach n hn) (SysState.step_timeout.mpr ⟨hup, hmem, rfl⟩)
  | inr j =>
    have hleft : ({ c with timers := update c.timers (.inr j) ((c.timers (.inr j)).erase msg) } :
        SysState (a.join b w)).left = c.left :=
      SysState.ext' rfl rfl rfl
        (funext fun k => update_inr_inl c.timers j ((c.timers (.inr j)).erase msg) k) rfl
    exact (settle_inr
      (c := { c with timers := update c.timers (.inr j) ((c.timers (.inr j)).erase msg) })
      (hleft ▸ hc) j ((b.actor j).step (c.state (.inr j)) msg)).still

private theorem step_output {c c' : SysState (a.join b w)} {out : σ.Out ⊕ τ.Out}
    (hc : Seen env w R t c.left) (hstep : c.step env (.output out) = some c') :
    Seen env w R (t ++ (Event.output out).leftDeed.toList) c'.left := by
  obtain ⟨hmem, rfl⟩ := SysState.step_output.mp hstep
  cases out with
  | inl out =>
    have houtbox := filterMap_erase (f := Sum.getLeft?) (a := (.inl out : σ.Out ⊕ τ.Out))
      (b := out) (fun x => by cases x <;> simp) c.outbox
    have hleft : out ∈ c.left.outbox := List.mem_filterMap.mpr ⟨_, hmem, rfl⟩
    have hshown : w.shown (.output out) = some (.output out) := by
      simp [Wiring.shown, Event.deed, hc.tidy out hleft]
    refine ⟨hc.closed, fun n hn => ?_, fun o ho =>
      hc.tidy o (List.mem_of_mem_erase ((congrArg (o ∈ ·) houtbox).mp ho))⟩
    have hstep := hc.closed (.output out) (hc.reach n hn) (SysState.step_output.mpr ⟨hleft, rfl⟩)
    rw [hshown] at hstep
    exact (congrArg (fun outbox =>
      R (t ++ [.output out]) ({ c.left with net := n, outbox := outbox } : SysState a))
        houtbox).mpr hstep
  | inr out =>
    have houtbox := filterMap_erase_of_none (f := Sum.getLeft? (α := σ.Out))
      (a := (.inr out : σ.Out ⊕ τ.Out)) rfl c.outbox
    refine still ⟨hc.closed, fun n hn => ?_, fun o ho =>
      hc.tidy o ((congrArg (o ∈ ·) houtbox).mp ho)⟩
    exact (congrArg (fun outbox =>
      R t ({ c.left with net := n, outbox := outbox } : SysState a)) houtbox).mpr
      (hc.reach n hn)

private theorem step_crash {c c' : SysState (a.join b w)} {i : σ.Id ⊕ τ.Id}
    (hc : Seen env w R t c.left) (hstep : c.step env (.crash i) = some c') :
    Seen env w R t c'.left := by
  obtain ⟨hup, hcrash, rfl⟩ := SysState.step_crash.mp hstep
  cases i with
  | inl i =>
    refine ⟨hc.closed, fun n hn => ?_, hc.tidy⟩
    obtain ⟨m, hm, rfl⟩ := SysState.thin_down c.net hn
    have hdown : ({ (c.down env (.inl i)).left with
        net := m.filter fun e => decide (e.dst ≠ i) || (env.left.link e.src e.dst).lossy } :
          SysState a) = ({ c.left with net := m } : SysState a).down env.left i :=
      SysState.ext' rfl (update_inl c.up i false) rfl (update_inl c.timers i []) rfl
    exact hc.quiet (.crash i) rfl (hc.reach m hm)
      (SysState.step_crash.mpr ⟨hup, hcrash, hdown⟩)
  | inr j =>
    have hleft : (c.down env (.inr j)).left = c.left :=
      SysState.ext' rfl (funext fun k => update_inr_inl c.up j false k)
        (filterMap_filter_of_none SysState.left?_of_dropped c.net)
        (funext fun k => update_inr_inl c.timers j [] k) rfl
    exact hleft ▸ hc

private theorem step_start {c c' : SysState (a.join b w)} {i : σ.Id ⊕ τ.Id}
    (hc : Seen env w R t c.left) (hstep : c.step env (.start i) = some c') :
    Seen env w R t c'.left := by
  obtain ⟨hup, hmail, rfl⟩ := SysState.step_start.mp hstep
  cases i with
  | inl i =>
    have hleft : ({ c with up := update c.up (.inl i) true } : SysState (a.join b w)).left
        = { c.left with up := update c.left.up i true } :=
      SysState.ext' rfl (update_inl c.up i true) rfl rfl rfl
    refine settle (c := { c with up := update c.up (.inl i) true }) hc.closed hc.tidy i
      ((a.actor i).recover (c.state (.inl i))) fun n hn => ?_
    rw [hleft]
    by_cases hmail' : ({ c.left with net := n } : SysState a).hasMail i = true
        ∨ env.left.restarts i = true
    · exact hc.quiet (.start i) rfl (hc.reach n hn)
        (SysState.step_start.mpr ⟨hup, hmail', rfl⟩)
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
        have hstart := hc.quiet (.start k) rfl (hc.reach m hm) (SysState.step_start.mpr
          ⟨hup, .inl (by simpa [SysState.hasMail] using ⟨_, hmm, rfl⟩), rfl⟩)
        exact heq ▸ hc.quiet (.drop _) rfl hstart (SysState.step_drop.mpr ⟨hlossy, hkept, rfl⟩)
      · simp at hdst
  | inr j => exact start_inr hc j

private theorem step {c c' : SysState (a.join b w)} {ev : Event (joinSig σ τ)}
    (hc : Seen env w R t c.left) (hstep : c.step env ev = some c') :
    Seen env w R (t ++ ev.leftDeed.toList) c'.left := by
  cases ev with
  | input x => exact (hc.step_input hstep).still
  | deliver e => exact hc.step_deliver hstep
  | duplicate e => exact hc.step_duplicate hstep
  | drop e => exact (hc.step_drop hstep).still
  | timeout i msg => exact hc.step_timeout hstep
  | output out => exact hc.step_output hstep
  | crash i => exact (hc.step_crash hstep).still
  | start i => exact (hc.step_start hstep).still

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
    obtain ⟨outbox', ho', h'⟩ :=
      h₁ (outbox ++ Effect.emits ((a.actor i).recover (c.state (.inl i))).2)
        (by rw [List.filter_append, ho, houtbox])
    refine ⟨outbox', ho', ?_⟩
    rw [List.foldl_cons, List.foldl_cons, ← h']
    congr 1
    have h₂ := h₀ outbox
    rw [hleft] at h₂
    exact h₂

/-- Booting `a` in a join in which nothing has reached `a` yet. -/
private theorem init_from (c₀ : SysState (a.join b w)) (hc₀ : c₀.left = SysState.blank a) :
    Seen env w (Shows a env.left w) []
      (a.boot.foldl (fun c i => c.startActor env (.inl i)) c₀).left := by
  have hboot : ∀ n', Thin n' (a.boot.foldl (fun c i => c.startActor env (.inl i)) c₀).left.net →
      ∃ outbox', outbox'.filter (fun out => (w.toRight out).isNone)
          = (a.boot.foldl (fun c i => c.startActor env (.inl i)) c₀).left.outbox ∧
        SysState.init a env.left = { (a.boot.foldl (fun c i => c.startActor env (.inl i)) c₀).left
          with net := n', outbox := outbox' } := by
    intro n' hn'
    obtain ⟨n, hn, h⟩ := boot a.boot c₀ hn'
    rw [hc₀] at hn h
    obtain rfl : n = [] := by
      cases hn
      rfl
    exact h [] rfl
  refine ⟨fun ev h hstep => h.step ev hstep, fun n' hn' => ?_, fun out hout => ?_⟩
  · obtain ⟨outbox', ho', heq⟩ := hboot n' hn'
    have hrun := SysState.run_outputs_filter env.left
      ({ (a.boot.foldl (fun c i => c.startActor env (.inl i)) c₀).left with net := n' } :
        SysState a)
      (fun out => (w.toRight out).isNone) [] outbox' (by simp)
    simp only [List.nil_append, ho'] at hrun
    have hinit : Shows a env.left w [] (SysState.init a env.left) := ⟨[], rfl, rfl⟩
    exact run_closed (fun ev h hstep => h.step ev hstep) (shown_wired outbox') (heq ▸ hinit) hrun
  · obtain ⟨outbox', ho', -⟩ := hboot _ (Thin.refl _)
    rw [← ho'] at hout
    simpa using (List.mem_filter.mp hout).2

private theorem init (env : EnvModel (joinSig σ τ)) :
    Seen env w (Shows a env.left w) [] (SysState.init (a.join b w) env).left := by
  have hfold : SysState.init (a.join b w) env
      = b.boot.foldl (fun c j => c.startActor env (.inr j))
        (a.boot.foldl (fun c i => c.startActor env (.inl i)) (SysState.blank (a.join b w))) := by
    simp [SysState.init, List.foldl_append, List.foldl_map]
  have hright : ∀ (l : List τ.Id) (c : SysState (a.join b w)),
      Seen env w (Shows a env.left w) [] c.left →
      Seen env w (Shows a env.left w) []
        (l.foldl (fun c j => c.startActor env (.inr j)) c).left := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons j l ih => exact fun c hc => ih _ (start_inr hc j)
  rw [hfold]
  exact hright _ _ (init_from _ rfl)

end Seen

variable {c : SysState (a.join b w)}

/-- Every run of a join, seen from its left system, is a run of that system alone, when its
inputs may be lost, repeated and reordered, and the two runs show the same: the actors of the
left system handle the same messages and the same outputs are handed over, in the same order.
The outputs the wiring routes to the other system are handed over too in the run alone, and
are not shown. -/
theorem SysState.run_left {evs : List (Event (joinSig σ τ))}
    (h : (SysState.init (a.join b w) env).run env evs = some c) :
    ∃ evs' : List (Event σ), (SysState.init a env.left).run env.left evs' = some c.left
      ∧ evs'.filterMap w.shown = evs.filterMap Event.leftDeed := by
  have hseen : Seen env w (Shows a env.left w) (evs.filterMap Event.leftDeed) c.left := by
    refine System.Reachable.run_induction (P := fun evs c =>
      Seen env w (Shows a env.left w) (evs.filterMap Event.leftDeed) c.left) .init h
      (Seen.init env) ?_
    intro evs c₁ ev c₂ _ hseen hstep
    exact filterMap_concat Event.leftDeed evs ev ▸ hseen.step hstep
  exact hseen.reach _ (Thin.refl _)

/-- Every reachable state of a join, seen from its left system, is a state that system reaches
alone, when its inputs may be lost, repeated and reordered. -/
theorem System.Reachable.left (h : (a.join b w).Reachable env c) : a.Reachable env.left c.left := by
  have hseen : ∃ t, Seen env w (Shows a env.left w) t c.left := by
    induction h with
    | init => exact ⟨_, Seen.init env⟩
    | step ev _ hstep ih => exact ih.elim fun t h => ⟨_, h.step hstep⟩
  obtain ⟨t, hseen⟩ := hseen
  obtain ⟨evs, hrun, -⟩ := hseen.reach _ (Thin.refl _)
  exact System.Reachable.init.run hrun

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

section Swap

variable {σ τ : Signature} {a : System σ} {b : System τ} {w : Wiring σ τ}
  {env : EnvModel (joinSig σ τ)}

private theorem swap_inj {α β : Type} {x y : α ⊕ β} : x.swap = y.swap ↔ x = y :=
  ⟨fun h => by simpa using congrArg Sum.swap h, fun h => h ▸ rfl⟩

private def Wiring.swap (w : Wiring σ τ) : Wiring τ σ where
  toRight := w.toLeft
  toLeft := w.toRight

private def Envelope.swap : Envelope (joinSig σ τ) → Envelope (joinSig τ σ)
  | ⟨src, .inl i, msg⟩ => ⟨src.map Sum.swap, .inr i, msg⟩
  | ⟨src, .inr j, msg⟩ => ⟨src.map Sum.swap, .inl j, msg⟩

private def Effect.swap :
    {x : σ.Id ⊕ τ.Id} → Effect (joinSig σ τ) x → Effect (joinSig τ σ) x.swap
  | _, .send (.inl t) msg => .send (.inr t) msg
  | _, .send (.inr t) msg => .send (.inl t) msg
  | _, .emit out => .emit out.swap
  | .inl _, .after delay_ms msg => .after delay_ms msg
  | .inr _, .after delay_ms msg => .after delay_ms msg
  | .inl _, .cancel msg => .cancel msg
  | .inr _, .cancel msg => .cancel msg
  | _, .stop => .stop

private def EnvModel.swap (env : EnvModel (joinSig σ τ)) : EnvModel (joinSig τ σ) where
  link src dst := env.link (src.map Sum.swap) dst.swap
  mayCrash x := env.mayCrash x.swap
  restarts x := env.restarts x.swap

private def Event.swap : Event (joinSig σ τ) → Event (joinSig τ σ)
  | .input x => .input x.swap
  | .deliver e => .deliver e.swap
  | .duplicate e => .duplicate e.swap
  | .drop e => .drop e.swap
  | .timeout (.inl i) msg => .timeout (.inr i) msg
  | .timeout (.inr j) msg => .timeout (.inl j) msg
  | .output out => .output out.swap
  | .crash x => .crash x.swap
  | .start x => .start x.swap

namespace Envelope

private theorem swap_dst (e : Envelope (joinSig σ τ)) : e.swap.dst = e.dst.swap := by
  obtain ⟨src, i | j, msg⟩ := e <;> rfl

private theorem swap_src (e : Envelope (joinSig σ τ)) : e.swap.src = e.src.map Sum.swap := by
  obtain ⟨src, i | j, msg⟩ := e <;> rfl

private theorem swap_inj {e e' : Envelope (joinSig σ τ)} (h : e.swap = e'.swap) : e = e' := by
  have hsrc : ∀ {s s' : Option (σ.Id ⊕ τ.Id)}, s.map Sum.swap = s'.map Sum.swap → s = s' :=
    fun h => by simpa [Option.map_map] using congrArg (Option.map Sum.swap) h
  obtain ⟨src, i | j, msg⟩ := e <;> obtain ⟨src', i' | j', msg'⟩ := e' <;>
    simp only [swap, Envelope.mk.injEq, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq, false_and,
      and_false] at h
  · obtain ⟨h₁, rfl, h₃⟩ := h
    cases h₃
    rw [hsrc h₁]
  · obtain ⟨h₁, rfl, h₃⟩ := h
    cases h₃
    rw [hsrc h₁]

private theorem swap_sameLink (e x : Envelope (joinSig σ τ)) :
    e.swap.sameLink x.swap = e.sameLink x := by
  simp only [sameLink, swap_dst, swap_src]
  congr 1
  · exact decide_eq_decide.mpr
      ⟨fun h => by simpa [Option.map_map] using congrArg (Option.map Sum.swap) h, fun h => h ▸ rfl⟩
  · exact decide_eq_decide.mpr Lanes.swap_inj

end Envelope

private theorem EnvModel.swap_link (env : EnvModel (joinSig σ τ)) (e : Envelope (joinSig σ τ)) :
    env.swap.link e.swap.src e.swap.dst = env.link e.src e.dst := by
  simp [EnvModel.swap, Envelope.swap_dst, Envelope.swap_src, Option.map_map]

private theorem Effect.swap_isStop {x : σ.Id ⊕ τ.Id} (eff : Effect (joinSig σ τ) x) :
    eff.swap.isStop = eff.isStop := by
  cases x <;> cases eff <;> first | rfl | (rename_i to msg; cases to <;> rfl)

namespace Wiring

private theorem left_swap {i : σ.Id} (effs : List (Effect σ i)) :
    (effs.flatMap fun eff => [w.left b eff]).map Effect.swap
      = effs.flatMap fun eff => [w.swap.right b eff] := by
  rw [List.map_flatMap]
  congr 1
  funext eff
  cases eff with
  | emit out =>
    simp only [Wiring.left, Wiring.right, Wiring.swap, List.map_cons, List.map_nil]
    cases w.toRight out <;> rfl
  | _ => rfl

private theorem right_swap {j : τ.Id} (effs : List (Effect τ j)) :
    (effs.flatMap fun eff => [w.right a eff]).map Effect.swap
      = effs.flatMap fun eff => [w.swap.left a eff] := by
  rw [List.map_flatMap]
  congr 1
  funext eff
  cases eff with
  | emit out =>
    simp only [Wiring.left, Wiring.right, Wiring.swap, List.map_cons, List.map_nil]
    cases w.toLeft out <;> rfl
  | _ => rfl

end Wiring

namespace SysState

private def swapAt : (x : σ.Id ⊕ τ.Id) → JoinState a b x → JoinState b a x.swap
  | .inl _, s => s
  | .inr _, s => s

/-- The join with its two sides exchanged. -/
private def swap (c : SysState (a.join b w)) : SysState (b.join a w.swap) where
  state := fun
    | .inl j => c.state (.inr j)
    | .inr i => c.state (.inl i)
  up x := c.up x.swap
  net := c.net.map Envelope.swap
  timers := fun
    | .inl j => c.timers (.inr j)
    | .inr i => c.timers (.inl i)
  outbox := c.outbox.map Sum.swap

private theorem swap_update_state (f : (x : σ.Id ⊕ τ.Id) → JoinState a b x) (x : σ.Id ⊕ τ.Id)
    (v : JoinState a b x) :
    (fun y : τ.Id ⊕ σ.Id => match y with
      | .inl j => update f x v (.inr j)
      | .inr i => update f x v (.inl i) : (y : τ.Id ⊕ σ.Id) → JoinState b a y)
      = update (fun y : τ.Id ⊕ σ.Id => match y with
        | .inl j => f (.inr j)
        | .inr i => f (.inl i) : (y : τ.Id ⊕ σ.Id) → JoinState b a y) x.swap (swapAt x v) := by
  funext y
  rcases x with i | j <;> rcases y with j' | i'
  · simp [update]
  · by_cases h : i' = i
    · subst h
      simp [swapAt]
    · simp [update, h]
  · by_cases h : j' = j
    · subst h
      simp [swapAt]
    · simp [update, h]
  · simp [update]

private theorem swap_update_up (f : σ.Id ⊕ τ.Id → Bool) (x : σ.Id ⊕ τ.Id) (v : Bool) :
    (fun y : τ.Id ⊕ σ.Id => update f x v y.swap) = update (fun y => f y.swap) x.swap v := by
  funext y
  by_cases h : y = x.swap
  · subst h
    cases x <;> simp
  · rw [update_of_ne _ _ h, update_of_ne _ _ (fun h' => h (by simp [← h']))]

private theorem swap_update_timers (f : (x : σ.Id ⊕ τ.Id) → List (JoinMsg σ τ x))
    (i : σ.Id) (v : List (σ.Msg i)) :
    (fun y : τ.Id ⊕ σ.Id => match y with
      | .inl j => update f (.inl i) v (.inr j)
      | .inr k => update f (.inl i) v (.inl k) : (y : τ.Id ⊕ σ.Id) → List (JoinMsg τ σ y))
      = update (fun y : τ.Id ⊕ σ.Id => match y with
        | .inl j => f (.inr j)
        | .inr k => f (.inl k) : (y : τ.Id ⊕ σ.Id) → List (JoinMsg τ σ y)) (.inr i) v := by
  funext y
  rcases y with j | k
  · rw [update_of_ne _ _ (by simp)]
    exact update_of_ne _ _ (by simp)
  · by_cases h : k = i
    · subst h
      simp
    · rw [update_of_ne _ _ (by simpa using h)]
      exact update_of_ne _ _ (by simpa using h)

private theorem swap_update_timers' (f : (x : σ.Id ⊕ τ.Id) → List (JoinMsg σ τ x))
    (j : τ.Id) (v : List (τ.Msg j)) :
    (fun y : τ.Id ⊕ σ.Id => match y with
      | .inl k => update f (.inr j) v (.inr k)
      | .inr i => update f (.inr j) v (.inl i) : (y : τ.Id ⊕ σ.Id) → List (JoinMsg τ σ y))
      = update (fun y : τ.Id ⊕ σ.Id => match y with
        | .inl k => f (.inr k)
        | .inr i => f (.inl i) : (y : τ.Id ⊕ σ.Id) → List (JoinMsg τ σ y)) (.inl j) v := by
  funext y
  rcases y with k | i
  · by_cases h : k = j
    · subst h
      simp
    · rw [update_of_ne _ _ (by simpa using h)]
      exact update_of_ne _ _ (by simpa using h)
  · rw [update_of_ne _ _ (by simp)]
    exact update_of_ne _ _ (by simp)

private theorem perform_swap (c : SysState (a.join b w)) (x : σ.Id ⊕ τ.Id)
    (eff : Effect (joinSig σ τ) x) : (c.perform x eff).swap = c.swap.perform x.swap eff.swap := by
  rcases x with i | j
  · cases eff with
    | send to msg => cases to <;> simp [perform, swap, Effect.swap, Envelope.swap]
    | emit out => simp [perform, swap, Effect.swap]
    | after delay_ms msg =>
      exact SysState.ext' rfl rfl rfl (swap_update_timers c.timers i _) rfl
    | cancel msg => exact SysState.ext' rfl rfl rfl (swap_update_timers c.timers i _) rfl
    | stop => rfl
  · cases eff with
    | send to msg => cases to <;> simp [perform, swap, Effect.swap, Envelope.swap]
    | emit out => simp [perform, swap, Effect.swap]
    | after delay_ms msg =>
      exact SysState.ext' rfl rfl rfl (swap_update_timers' c.timers j _) rfl
    | cancel msg => exact SysState.ext' rfl rfl rfl (swap_update_timers' c.timers j _) rfl
    | stop => rfl

private theorem performAll_swap (c : SysState (a.join b w)) (x : σ.Id ⊕ τ.Id)
    (effs : List (Effect (joinSig σ τ) x)) :
    (c.performAll x effs).swap = c.swap.performAll x.swap (effs.map Effect.swap) := by
  induction effs generalizing c with
  | nil => rfl
  | cons eff effs ih => rw [performAll_cons, ih, perform_swap, List.map_cons, performAll_cons]

private theorem down_swap (c : SysState (a.join b w)) (x : σ.Id ⊕ τ.Id) :
    (c.down env x).swap = c.swap.down env.swap x.swap := by
  have hnet : (c.net.filter fun e => decide (e.dst ≠ x) || (env.link e.src e.dst).lossy).map
      Envelope.swap = (c.net.map Envelope.swap).filter fun e =>
        decide (e.dst ≠ x.swap) || (env.swap.link e.src e.dst).lossy := by
    rw [List.filter_map]
    congr 2
    funext e
    show _ = (decide (e.swap.dst ≠ x.swap) || (env.swap.link e.swap.src e.swap.dst).lossy)
    rw [EnvModel.swap_link, Envelope.swap_dst]
    simp [Lanes.swap_inj]
  rcases x with i | j
  · exact SysState.ext' rfl (swap_update_up c.up (.inl i) false) hnet
      (swap_update_timers c.timers i []) rfl
  · exact SysState.ext' rfl (swap_update_up c.up (.inr j) false) hnet
      (swap_update_timers' c.timers j []) rfl

private theorem settle_swap (c : SysState (a.join b w)) (x : σ.Id ⊕ τ.Id)
    (r : JoinState a b x × List (Effect (joinSig σ τ) x)) :
    (c.settle env x r).swap
      = c.swap.settle env.swap x.swap (swapAt x r.1, r.2.map Effect.swap) := by
  have hstop : (r.2.map Effect.swap).any Effect.isStop = r.2.any Effect.isStop :=
    Effect.any_isStop_map Effect.swap_isStop r.2
  have hstate : ({ c with state := update c.state x r.1 } : SysState (a.join b w)).swap
      = { c.swap with state := update c.swap.state x.swap (swapAt x r.1) } :=
    SysState.ext' (swap_update_state c.state x r.1) rfl rfl rfl rfl
  simp only [settle, hstop]
  split
  · rw [down_swap, performAll_swap, hstate]
  · rw [performAll_swap, hstate]

private theorem handle_swap_inl (c : SysState (a.join b w)) (i : σ.Id) (msg : σ.Msg i) :
    (c.handle env (.inl i) msg).swap = c.swap.handle env.swap (.inr i) msg := by
  exact (settle_swap c (.inl i) (((a.join b w).actor (.inl i)).step (c.state (.inl i)) msg)).trans
    (congrArg (fun effs => c.swap.settle env.swap (.inr i)
        (((a.actor i).step (c.state (.inl i)) msg).1, effs))
      (Wiring.left_swap (w := w) (b := b) ((a.actor i).step (c.state (.inl i)) msg).2))

private theorem handle_swap_inr (c : SysState (a.join b w)) (j : τ.Id) (msg : τ.Msg j) :
    (c.handle env (.inr j) msg).swap = c.swap.handle env.swap (.inl j) msg := by
  exact (settle_swap c (.inr j) (((a.join b w).actor (.inr j)).step (c.state (.inr j)) msg)).trans
    (congrArg (fun effs => c.swap.settle env.swap (.inl j)
        (((b.actor j).step (c.state (.inr j)) msg).1, effs))
      (Wiring.right_swap (w := w) (a := a) ((b.actor j).step (c.state (.inr j)) msg).2))

private theorem startActor_swap (c : SysState (a.join b w)) (x : σ.Id ⊕ τ.Id) :
    (c.startActor env x).swap = c.swap.startActor env.swap x.swap := by
  have hup : ({ c with up := update c.up x true } : SysState (a.join b w)).swap
      = { c.swap with up := update c.swap.up x.swap true } :=
    SysState.ext' rfl (swap_update_up c.up x true) rfl rfl rfl
  rcases x with i | j
  · refine (settle_swap _ (.inl i)
      (((a.join b w).actor (.inl i)).recover (c.state (.inl i)))).trans ?_
    rw [hup]
    exact congrArg (fun effs => SysState.settle env.swap
        ({ c.swap with up := update c.swap.up (.inr i) true } : SysState (b.join a w.swap)) (.inr i)
        (((a.actor i).recover (c.state (.inl i))).1, effs))
      (Wiring.left_swap (w := w) (b := b) ((a.actor i).recover (c.state (.inl i))).2)
  · refine (settle_swap _ (.inr j)
      (((a.join b w).actor (.inr j)).recover (c.state (.inr j)))).trans ?_
    rw [hup]
    exact congrArg (fun effs => SysState.settle env.swap
        ({ c.swap with up := update c.swap.up (.inl j) true } : SysState (b.join a w.swap)) (.inl j)
        (((b.actor j).recover (c.state (.inr j))).1, effs))
      (Wiring.right_swap (w := w) (a := a) ((b.actor j).recover (c.state (.inr j))).2)

private theorem deliverable_swap (c : SysState (a.join b w)) (e : Envelope (joinSig σ τ)) :
    c.swap.deliverable env.swap e.swap = c.deliverable env e := by
  have hsame : Envelope.sameLink e.swap ∘ Envelope.swap = Envelope.sameLink e := by
    funext x
    exact Envelope.swap_sameLink e x
  simp only [deliverable, EnvModel.swap_link, swap, List.find?_map, hsame]
  split
  · cases c.net.find? e.sameLink with
    | none => rfl
    | some x =>
      simp only [Option.map_some]
      exact Bool.eq_iff_iff.mpr ⟨fun h => by simpa using Envelope.swap_inj (by simpa using h),
        fun h => by simpa using congrArg Envelope.swap (by simpa using h : x = e)⟩
  · exact Bool.eq_iff_iff.mpr ⟨fun h => by
        obtain ⟨x, hx, hxe⟩ := List.mem_map.mp (by simpa using h)
        simpa [← Envelope.swap_inj hxe] using hx,
      fun h => by simpa using List.mem_map_of_mem (f := Envelope.swap) (by simpa using h)⟩

private theorem hasMail_swap (c : SysState (a.join b w)) (x : σ.Id ⊕ τ.Id) :
    c.swap.hasMail x.swap = c.hasMail x := by
  simp only [hasMail, swap, List.any_map]
  congr 1
  funext e
  simp [Envelope.swap_dst, Lanes.swap_inj]

/-- A join and the join with its sides exchanged take the same steps. -/
private theorem step_swap {c c' : SysState (a.join b w)} {ev : Event (joinSig σ τ)}
    (h : c.step env ev = some c') : c.swap.step env.swap ev.swap = some c'.swap := by
  have herase : ∀ e : Envelope (joinSig σ τ),
      ({ c with net := c.net.erase e } : SysState (a.join b w)).swap
        = { c.swap with net := c.swap.net.erase e.swap } := fun e =>
    SysState.ext' rfl rfl (map_erase fun _ _ => Envelope.swap_inj) rfl rfl
  cases ev with
  | input x =>
    obtain rfl := step_input.mp h
    refine step_input.mpr (SysState.ext' rfl rfl ?_ rfl rfl)
    cases x <;> simp [swap, Envelope.swap]
  | deliver e =>
    obtain ⟨hup, hdel, rfl⟩ := step_deliver.mp h
    refine step_deliver.mpr ⟨by rw [Envelope.swap_dst]; simpa [swap] using hup,
      (deliverable_swap c e).trans hdel, ?_⟩
    rw [← herase]
    obtain ⟨src, i | j, msg⟩ := e
    · exact handle_swap_inl _ i msg
    · exact handle_swap_inr _ j msg
  | duplicate e =>
    obtain ⟨hup, hdup, hdel, rfl⟩ := step_duplicate.mp h
    refine step_duplicate.mpr ⟨by rw [Envelope.swap_dst]; simpa [swap] using hup,
      by rw [EnvModel.swap_link]; exact hdup, (deliverable_swap c e).trans hdel, ?_⟩
    obtain ⟨src, i | j, msg⟩ := e
    · exact handle_swap_inl _ i msg
    · exact handle_swap_inr _ j msg
  | drop e =>
    obtain ⟨hlossy, hmem, rfl⟩ := step_drop.mp h
    exact step_drop.mpr
      ⟨by rw [EnvModel.swap_link]; exact hlossy, List.mem_map_of_mem hmem, herase e⟩
  | timeout x msg =>
    obtain ⟨hup, hmem, rfl⟩ := step_timeout.mp h
    rcases x with i | j
    · refine step_timeout.mpr ⟨hup, hmem, ?_⟩
      refine (handle_swap_inl _ i msg).trans ?_
      congr 1
      exact SysState.ext' rfl rfl rfl (swap_update_timers c.timers i _) rfl
    · refine step_timeout.mpr ⟨hup, hmem, ?_⟩
      refine (handle_swap_inr _ j msg).trans ?_
      congr 1
      exact SysState.ext' rfl rfl rfl (swap_update_timers' c.timers j _) rfl
  | output out =>
    obtain ⟨hmem, rfl⟩ := step_output.mp h
    exact step_output.mpr ⟨List.mem_map_of_mem hmem,
      SysState.ext' rfl rfl rfl rfl (map_erase fun _ _ => Lanes.swap_inj.mp)⟩
  | crash x =>
    obtain ⟨hup, hcrash, rfl⟩ := step_crash.mp h
    exact step_crash.mpr ⟨by simpa [swap] using hup, by simpa [EnvModel.swap] using hcrash,
      down_swap c x⟩
  | start x =>
    obtain ⟨hup, hmail, rfl⟩ := step_start.mp h
    exact step_start.mpr ⟨by simpa [swap] using hup,
      hmail.imp (fun h => (hasMail_swap c x).trans h) (fun h => by simpa [EnvModel.swap] using h),
      startActor_swap c x⟩

private theorem blank_swap :
    (SysState.blank (a.join b w)).swap = SysState.blank (b.join a w.swap) :=
  SysState.ext' (funext fun y => by cases y <;> rfl) rfl rfl (funext fun y => by cases y <;> rfl)
    rfl

private theorem init_swap (env : EnvModel (joinSig σ τ)) :
    (SysState.init (a.join b w) env).swap
      = b.boot.foldl (fun c j => c.startActor env.swap (.inl j))
        (a.boot.foldl (fun c i => c.startActor env.swap (.inr i))
          (SysState.blank (b.join a w.swap))) := by
  have hfold : ∀ (l : List (σ.Id ⊕ τ.Id)) (c : SysState (a.join b w)),
      (l.foldl (fun c x => c.startActor env x) c).swap
        = l.foldl (fun c x => c.startActor env.swap x.swap) c.swap := fun l c =>
    (List.foldl_hom swap fun c x => (startActor_swap c x).symm).symm
  show (List.foldl (fun c x => c.startActor env x) (SysState.blank (a.join b w))
    (a.boot.map .inl ++ b.boot.map .inr)).swap = _
  rw [hfold, blank_swap, List.foldl_append, List.foldl_map, List.foldl_map]
  rfl

private theorem swap_left (c : SysState (a.join b w)) : c.swap.left = c.right := by
  refine SysState.ext' rfl rfl ?_ rfl ?_
  · show (c.net.map Envelope.swap).filterMap Envelope.left? = c.net.filterMap Envelope.right?
    rw [List.filterMap_map]
    congr 1
    funext e
    obtain ⟨src, i | j, msg⟩ := e
    · rfl
    · rcases src with _ | s | s <;> rfl
  · show (c.outbox.map Sum.swap).filterMap Sum.getLeft? = c.outbox.filterMap Sum.getRight?
    rw [List.filterMap_map]
    congr 1
    funext out
    cases out <;> rfl

end SysState

private theorem EnvModel.swap_left (env : EnvModel (joinSig σ τ)) : env.swap.left = env.right := by
  simp only [EnvModel.left, EnvModel.right, EnvModel.swap, EnvModel.mk.injEq]
  refine ⟨?_, rfl, rfl⟩
  funext src dst
  cases src <;> rfl

end Swap

section Right

namespace SysState

variable {σ : Signature} {sys : System σ} {env : EnvModel σ}

/-- An actor's start does not look at the messages in flight. -/
private theorem startActor_prefix (c : SysState sys) (i : σ.Id) {pre : List (Envelope σ)}
    (hpre : ∀ e ∈ pre, (env.link e.src e.dst).lossy = true) :
    ({ c with net := pre ++ c.net } : SysState sys).startActor env i
      = { c.startActor env i with net := pre ++ (c.startActor env i).net } := by
  have hkept : pre.filter (fun e => decide (e.dst ≠ i) || (env.link e.src e.dst).lossy) = pre :=
    List.filter_eq_self.mpr fun e he => by simp [hpre e he]
  simp only [startActor, settle_eq]
  split
  · simp only [down, List.append_assoc, List.filter_append, hkept]
  · simp only [List.append_assoc]

private theorem boot_prefix (l : List σ.Id) {pre : List (Envelope σ)}
    (hpre : ∀ e ∈ pre, (env.link e.src e.dst).lossy = true) :
    ∀ c : SysState sys,
      l.foldl (fun c i => c.startActor env i) ({ c with net := pre ++ c.net } : SysState sys)
        = { l.foldl (fun c i => c.startActor env i) c with
            net := pre ++ (l.foldl (fun c i => c.startActor env i) c).net } := by
  induction l with
  | nil => exact fun _ => rfl
  | cons i l ih =>
    intro c
    rw [List.foldl_cons, startActor_prefix c i hpre]
    exact ih (c.startActor env i)

/-- Messages from outside on an unordered link sit as well before the others as after them. -/
private theorem equiv_rotate (c : SysState sys) {pre : List (Envelope σ)}
    (hsrc : ∀ e ∈ pre, e.src = none) (hord : ∀ dst, (env.link none dst).ordered = false) :
    SysState.Equiv env ({ c with net := c.net ++ pre } : SysState sys)
      { c with net := pre ++ c.net } := by
  refine ⟨rfl, rfl, rfl, ⟨fun src dst => ?_, fun src dst hordered => ?_⟩, .refl _⟩
  · simp only [List.filter_append]
    exact List.perm_append_comm
  · have hnone : pre.filter (onLink src dst) = [] := by
      rw [List.filter_eq_nil_iff]
      intro e he hon
      simp only [onLink, Bool.and_eq_true, decide_eq_true_eq] at hon
      rw [← hon.1, hsrc e he, hord dst] at hordered
      exact absurd hordered (by simp)
    simp only [List.filter_append, hnone, List.append_nil, List.nil_append]

end SysState

variable {σ τ : Signature} {a : System σ} {b : System τ} {w : Wiring σ τ}
  {env : EnvModel (joinSig σ τ)}

namespace Seen

private theorem boot_inr (l : List τ.Id) :
    ∀ c : SysState (a.join b w), ∃ xs : List σ.In,
      (l.foldl (fun c j => c.startActor env (.inr j)) c).left
        = { c.left with
            net := c.left.net ++ xs.map fun x => ⟨none, (a.accept x).1, (a.accept x).2⟩ } := by
  induction l with
  | nil => exact fun c => ⟨[], by simp⟩
  | cons j l ih =>
    intro c
    have hleft : ({ c with up := update c.up (.inr j) true } : SysState (a.join b w)).left
        = c.left :=
      SysState.ext' rfl (funext fun k => update_inr_inl c.up j true k) rfl rfl rfl
    have hstart := SysState.left_settle_inr (env := env)
      ({ c with up := update c.up (.inr j) true }) j ((b.actor j).recover (c.state (.inr j)))
    rw [hleft] at hstart
    have hstart : (c.startActor env (.inr j)).left = _ := hstart
    obtain ⟨xs, hxs⟩ := ih (c.startActor env (.inr j))
    refine ⟨(Effect.emits ((b.actor j).recover (c.state (.inr j))).2).filterMap w.toLeft ++ xs, ?_⟩
    rw [List.foldl_cons, hxs, hstart]
    simp [List.append_assoc]

/-- The system that boots second: the other's boot has already sent it inputs, which it alone
can only receive after its own boot. Its messages then sit in another order. -/
private theorem init_late (env : EnvModel (joinSig σ τ)) :
    Seen env w (fun _ => System.Near a env.left) []
      (a.boot.foldl (fun c i => c.startActor env (.inl i))
        (b.boot.foldl (fun c j => c.startActor env (.inr j))
          (SysState.blank (a.join b w)))).left := by
  obtain ⟨xs, hxs⟩ := boot_inr (env := env) b.boot (SysState.blank (a.join b w))
  have hnear : ∀ n', Thin n' (a.boot.foldl (fun c i => c.startActor env (.inl i))
      (b.boot.foldl (fun c j => c.startActor env (.inr j))
        (SysState.blank (a.join b w)))).left.net →
      ∃ outbox', outbox'.filter (fun out => (w.toRight out).isNone)
          = (a.boot.foldl (fun c i => c.startActor env (.inl i))
            (b.boot.foldl (fun c j => c.startActor env (.inr j))
              (SysState.blank (a.join b w)))).left.outbox ∧
        System.Near a env.left { (a.boot.foldl (fun c i => c.startActor env (.inl i))
          (b.boot.foldl (fun c j => c.startActor env (.inr j))
            (SysState.blank (a.join b w)))).left with net := n', outbox := outbox' } := by
    intro n' hn'
    obtain ⟨n, hn, h⟩ := boot a.boot _ hn'
    rw [hxs] at hn h
    obtain ⟨ys, rfl⟩ : ∃ ys : List σ.In,
        n = ys.map fun x => ⟨none, (a.accept x).1, (a.accept x).2⟩ := by
      have hn : Thin n (xs.map fun x => (⟨none, (a.accept x).1, (a.accept x).2⟩ : Envelope σ)) := hn
      exact hn.of_map
    obtain ⟨outbox', ho', heq⟩ := h [] rfl
    refine ⟨outbox', ho', ?_⟩
    rw [← heq]
    have hpre : ∀ e ∈ ys.map fun x => (⟨none, (a.accept x).1, (a.accept x).2⟩ : Envelope σ),
        e.src = none := by
      intro e he
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
      rfl
    have hboot := SysState.boot_prefix (env := env.left) a.boot (pre := ys.map fun x =>
      (⟨none, (a.accept x).1, (a.accept x).2⟩ : Envelope σ))
      (fun e he => by rw [hpre e he]; rfl) (SysState.blank a)
    have hnil : ({ SysState.blank a with net := ys.map fun x =>
          (⟨none, (a.accept x).1, (a.accept x).2⟩ : Envelope σ) } : SysState a)
        = { SysState.blank a with net := (ys.map fun x =>
          (⟨none, (a.accept x).1, (a.accept x).2⟩ : Envelope σ)) ++ (SysState.blank a).net } :=
      SysState.ext' rfl rfl (List.append_nil _).symm rfl rfl
    have hfold : a.boot.foldl (fun c i => c.startActor env.left i)
        ({ SysState.blank a with net := ys.map fun x =>
          (⟨none, (a.accept x).1, (a.accept x).2⟩ : Envelope σ) } : SysState a)
        = { SysState.init a env.left with
            net := (ys.map fun x => (⟨none, (a.accept x).1, (a.accept x).2⟩ : Envelope σ))
              ++ (SysState.init a env.left).net } :=
      (congrArg (fun c : SysState a => a.boot.foldl (fun c i => c.startActor env.left i) c)
        hnil).trans hboot
    refine ⟨_, System.Reachable.init.run (SysState.run_inputs env.left _ ys), ?_⟩
    exact (congrArg (SysState.Equiv env.left _) hfold).mpr
      (SysState.equiv_rotate (env := env.left) (SysState.init a env.left) hpre fun _ => rfl)
  refine ⟨fun ev h hstep => System.Near.step ev h hstep, fun n' hn' => ?_, fun out hout => ?_⟩
  · obtain ⟨outbox', ho', hnear'⟩ := hnear n' hn'
    have hrun := SysState.run_outputs_filter env.left
      ({ (a.boot.foldl (fun c i => c.startActor env (.inl i))
        (b.boot.foldl (fun c j => c.startActor env (.inr j))
          (SysState.blank (a.join b w)))).left with net := n' } : SysState a)
      (fun out => (w.toRight out).isNone) [] outbox' (by simp)
    simp only [List.nil_append, ho'] at hrun
    exact run_closed (w := w) (R := fun _ => System.Near a env.left) (t := [])
      (fun ev h hstep => System.Near.step ev h hstep) (shown_wired outbox') hnear' hrun
  · obtain ⟨outbox', ho', -⟩ := hnear _ (Thin.refl _)
    rw [← ho'] at hout
    simpa using (List.mem_filter.mp hout).2

end Seen

variable {c : SysState (a.join b w)}

/-- Every reachable state of a join, seen from its right system, is a state that system reaches
alone, up to the order of messages on different links. The order can differ because the left
system boots first: what its boot sends is in flight before the right system's own first
messages, and alone the right system receives inputs only once it has booted. -/
private theorem System.Reachable.seen_swap (h : (a.join b w).Reachable env c) :
    ∃ t, Seen env.swap w.swap (fun _ => System.Near b env.swap.left) t c.swap.left := by
  induction h with
  | init =>
    rw [SysState.init_swap]
    exact ⟨_, Seen.init_late env.swap⟩
  | step ev _ hstep ih => exact ih.elim fun t h => ⟨_, h.step (SysState.step_swap hstep)⟩

theorem System.Reachable.right (h : (a.join b w).Reachable env c) :
    ∃ c', b.Reachable env.right c' ∧ SysState.Equiv env.right c' c.right := by
  obtain ⟨t, hseen⟩ := h.seen_swap
  have hnear : System.Near b env.swap.left c.swap.left := hseen.reach _ (Thin.refl _)
  rw [EnvModel.swap_left] at hnear
  exact SysState.swap_left c ▸ hnear

/-- No output that the wiring routes to `a` waits in the join. -/
theorem System.Reachable.right_unwired (h : (a.join b w).Reachable env c) :
    ∀ out ∈ c.right.outbox, w.toLeft out = none := by
  obtain ⟨t, hseen⟩ := h.seen_swap
  exact SysState.swap_left c ▸ hseen.tidy

/-- The right system is seen exactly as it is alone when the boot of the left system sends it
nothing. -/
theorem System.Reachable.right_of_quiet_boot
    (hquiet : ∀ i ∈ a.boot, ∀ s out, .emit out ∈ ((a.actor i).recover s).2 → w.toRight out = none)
    (h : (a.join b w).Reachable env c) : b.Reachable env.right c.right := by
  have hblank : ∀ (l : List σ.Id) (c₀ : SysState (b.join a w.swap)), (∀ i ∈ l, i ∈ a.boot) →
      (l.foldl (fun c i => c.startActor env.swap (.inr i)) c₀).left = c₀.left := by
    intro l
    induction l with
    | nil => exact fun _ _ => rfl
    | cons i l ih =>
      intro c₀ hl
      have hleft : ({ c₀ with up := update c₀.up (.inr i) true } :
          SysState (b.join a w.swap)).left = c₀.left :=
        SysState.ext' rfl (funext fun k => update_inr_inl c₀.up i true k) rfl rfl rfl
      have hstart : (c₀.startActor env.swap (.inr i)).left = _ :=
        SysState.left_settle_inr (env := env.swap) ({ c₀ with up := update c₀.up (.inr i) true }) i
          ((a.actor i).recover (c₀.state (.inr i)))
      have hnone : (Effect.emits ((a.actor i).recover (c₀.state (.inr i))).2).filterMap
          w.swap.toLeft = [] := by
        rw [List.filterMap_eq_nil_iff]
        intro out hout
        simp only [Effect.emits, List.mem_filterMap] at hout
        obtain ⟨eff, heff, hout⟩ := hout
        cases eff <;> simp only [Option.some.injEq, reduceCtorEq] at hout
        exact hquiet i (hl i List.mem_cons_self) _ out (hout ▸ heff)
      rw [List.foldl_cons, ih _ fun k hk => hl k (List.mem_cons_of_mem _ hk), hstart, hnone, hleft]
      simp
  have hseen : ∃ t, Seen env.swap w.swap (Shows b env.swap.left w.swap) t c.swap.left := by
    induction h with
    | init =>
      rw [SysState.init_swap]
      exact ⟨_, Seen.init_from _ (hblank a.boot _ fun _ h => h)⟩
    | step ev _ hstep ih => exact ih.elim fun t h => ⟨_, h.step (SysState.step_swap hstep)⟩
  obtain ⟨t, hseen⟩ := hseen
  obtain ⟨evs, hrun, -⟩ := hseen.reach _ (Thin.refl _)
  have hreach : b.Reachable env.swap.left c.swap.left := System.Reachable.init.run hrun
  rw [EnvModel.swap_left] at hreach
  exact SysState.swap_left c ▸ hreach

/-- What is proved of a system alone, with a network link from outside, holds of it on the
right of every join, if it does not depend on the order of messages on different links. -/
theorem System.Invariant.join_right {P : SysState b → Prop} (h : b.Invariant env.right P)
    (hP : ∀ c c', SysState.Equiv env.right c c' → P c → P c') :
    (a.join b w).Invariant env fun c => P c.right := fun _ hc =>
  let ⟨c', hc', hequiv⟩ := hc.right
  hP c' _ hequiv (h c' hc')

theorem System.Invariant.join_right_state {Q : ((j : τ.Id) → b.State j) → Prop}
    (h : ∀ env, b.Invariant env fun c => Q c.state) :
    (a.join b w).Invariant env fun c => Q fun j => c.state (.inr j) := by
  intro c hc
  obtain ⟨c', hc', hequiv⟩ := hc.right
  have hQ : Q c'.state := h env.right c' hc'
  rw [hequiv.state] at hQ
  exact hQ

end Right

section Thinned

/-! Seen from `a` without the messages from outside, a run of the join is a run of `a` alone
step by step: each step of the join is a short run of `a` (`Wiring.Block`) from the view before
it to the view after it. -/

variable {σ τ : Signature} {a : System σ} {b : System τ} {w : Wiring σ τ}
  {env : EnvModel (joinSig σ τ)} {c c' : SysState (a.join b w)}

private theorem Thin.inside (l : List (Envelope σ)) : Thin (l.filter fun e => e.src.isSome) l := by
  induction l with
  | nil => exact .nil
  | cons e l ih =>
    cases h : e.src with
    | none =>
      rw [List.filter_cons_of_neg (by simp [h])]
      exact .skip h ih
    | some s =>
      rw [List.filter_cons_of_pos (by simp [h])]
      exact .keep e ih

/-- No output that the wiring routes to `b` waits in the join. -/
theorem System.Reachable.left_unwired (h : (a.join b w).Reachable env c) :
    ∀ out ∈ c.left.outbox, w.toRight out = none := by
  have hseen : ∃ t, Seen env w (Shows a env.left w) t c.left := by
    induction h with
    | init => exact ⟨_, Seen.init env⟩
    | step ev _ hstep ih => exact ih.elim fun t h => ⟨_, h.step hstep⟩
  obtain ⟨t, hseen⟩ := hseen
  exact hseen.tidy

/-- What a step of the join needs of `c` to be a run of `a` alone: no output waits that the
wiring routes to `b`, and every message from outside to `a` is an input `a` accepts. A reachable
state of the join has it, and so has the join with its sides exchanged, which is not reachable. -/
private structure Tidy (w : Wiring σ τ) (c : SysState (a.join b w)) : Prop where
  unwired : ∀ out ∈ c.left.outbox, w.toRight out = none
  accepted : ∀ u ∈ c.left.net, u.src = none →
    ∃ x, (⟨none, (a.accept x).1, (a.accept x).2⟩ : Envelope σ) = u

private theorem Tidy.of_reachable (hc : (a.join b w).Reachable env c) : Tidy w c :=
  ⟨hc.left_unwired, fun _ hu hsrc => hc.left.accepted hu hsrc⟩

/-- The outputs of `effs` that the wiring routes to `b`, handed over. -/
def Wiring.wired (w : Wiring σ τ) {i : σ.Id} (effs : List (Effect σ i)) : List (Event σ) :=
  ((Effect.emits effs).filter fun out => !(w.toRight out).isNone).map .output

namespace SysState

private theorem thinLeft_erase_outside (e : Envelope (joinSig σ τ))
    (he : ∀ u, e.left? = some u → u.src = none) :
    ({ c with net := c.net.erase e } : SysState (a.join b w)).thinLeft = c.thinLeft := by
  refine SysState.ext' rfl rfl ?_ rfl rfl
  show ((c.net.erase e).filterMap Envelope.left?).filter _
    = (c.net.filterMap Envelope.left?).filter _
  rw [List.filter_filterMap, List.filter_filterMap, filterMap_erase_of_none]
  cases h : e.left? with
  | none => rfl
  | some u => simp [he u h]

private theorem thinLeft_erase_inside {s i : σ.Id} {msg : σ.Msg i} :
    ({ c with net := c.net.erase ⟨some (.inl s), .inl i, msg⟩ } : SysState (a.join b w)).thinLeft
      = { c.thinLeft with net := c.thinLeft.net.erase ⟨some s, i, msg⟩ } := by
  refine SysState.ext' rfl rfl ?_ rfl rfl
  show ((c.net.erase _).filterMap Envelope.left?).filter _
    = ((c.net.filterMap Envelope.left?).filter _).erase _
  rw [filterMap_erase (fun e' => Envelope.left?_eq_inside e') c.net, filter_erase_of_pos _ _ rfl]

private theorem thinLeft_append_outside (l : List (Envelope (joinSig σ τ)))
    (c : SysState (a.join b w)) (hl : ∀ e ∈ l, ∀ u, e.left? = some u → u.src = none) :
    ({ c with net := c.net ++ l } : SysState (a.join b w)).thinLeft = c.thinLeft := by
  refine SysState.ext' rfl rfl ?_ rfl rfl
  show ((c.net ++ l).filterMap Envelope.left?).filter _ = (c.net.filterMap Envelope.left?).filter _
  rw [List.filterMap_append, List.filter_append, List.append_right_eq_self, List.filter_eq_nil_iff]
  intro u hu
  obtain ⟨e, he, heu⟩ := List.mem_filterMap.mp hu
  simp [hl e he u heu]

private theorem inside_down (i : σ.Id) (l : List (Envelope (joinSig σ τ))) :
    ((l.filter fun e => decide (e.dst ≠ .inl i) || (env.link e.src e.dst).lossy).filterMap
        Envelope.left?).filter (fun e => e.src.isSome)
      = ((l.filterMap Envelope.left?).filter fun e => e.src.isSome).filter
          fun e => decide (e.dst ≠ i) || (env.left.link e.src e.dst).lossy := by
  rw [List.filter_filterMap, List.filterMap_filter, List.filter_filterMap, List.filter_filterMap]
  congr 1
  funext e
  obtain ⟨src, k | j, msg⟩ := e
  · rcases src with _ | s | j'
    · simp [Envelope.left?, Option.filter]
    · simp only [Envelope.left?, Option.bind_some, Sum.getLeft?_inl]
      simp [Option.filter, EnvModel.left]
    · simp [Envelope.left?, Option.filter]
  · simp [Envelope.left?]

private theorem thinLeft_down (i : σ.Id) :
    (c.down env (.inl i)).thinLeft = c.thinLeft.down env.left i :=
  SysState.ext' rfl (update_inl c.up i false) (inside_down i c.net) (update_inl c.timers i []) rfl

/-- A step of an actor of `a` in the join, seen without the messages from outside, is the same
step of `a` alone, followed by handing over the outputs the wiring routes to `b`. -/
private theorem thinLeft_settle (c : SysState (a.join b w)) (i : σ.Id)
    (r : a.State i × List (Effect σ i)) (htidy : ∀ out ∈ c.left.outbox, w.toRight out = none) :
    (c.thinLeft.settle env.left i r).run env.left (w.wired r.2)
      = some (c.settle env (.inl i) (r.1, r.2.flatMap fun eff => [w.left b eff])).thinLeft := by
  have inside : (Effect.sends i r.2).filter (fun e => e.src.isSome) = Effect.sends i r.2 :=
    List.filter_eq_self.mpr fun e he => by simp [(Effect.mem_sends.mp he).1]
  have hsettle : c.thinLeft.settle env.left i r =
      { (c.settle env (.inl i) (r.1, r.2.flatMap fun eff => [w.left b eff])).thinLeft with
        outbox := c.left.outbox ++ Effect.emits r.2 } := by
    rw [settle_eq]
    unfold thinLeft
    rw [left_settle]
    split
    · refine SysState.ext' rfl rfl ?_ ?_ rfl
      · show (c.thinLeft.net ++ Effect.sends i r.2).filter _ = _
        rw [inside_down, List.filterMap_append, Wiring.sends_left,
          List.filter_append (p := fun e : Envelope σ => e.src.isSome), inside]
        rfl
      · simp only [down, update_update]
    · refine SysState.ext' rfl rfl ?_ rfl rfl
      show c.thinLeft.net ++ Effect.sends i r.2 = _
      rw [List.filter_append (p := fun e : Envelope σ => e.src.isSome), inside]
      rfl
  rw [hsettle]
  have hrun := SysState.run_outputs_filter env.left
    { (c.settle env (.inl i) (r.1, r.2.flatMap fun eff => [w.left b eff])).thinLeft with
      outbox := c.left.outbox ++ Effect.emits r.2 }
    (fun out => (w.toRight out).isNone) c.left.outbox (Effect.emits r.2)
    (fun out hout => by simp [htidy out hout])
  refine hrun.trans (congrArg some (SysState.ext' rfl rfl rfl rfl ?_))
  show c.left.outbox ++ _
    = (c.settle env (.inl i) (r.1, r.2.flatMap fun eff => [w.left b eff])).left.outbox
  rw [left_settle]
  split <;> rfl

private theorem thinLeft_settle_inr (c : SysState (a.join b w)) (j : τ.Id)
    (r : b.State j × List (Effect τ j)) :
    (c.settle env (.inr j) (r.1, r.2.flatMap fun eff => [w.right a eff])).thinLeft
      = c.thinLeft := by
  unfold thinLeft
  rw [left_settle_inr]
  refine SysState.ext' rfl rfl ?_ rfl rfl
  show (c.left.net ++ _).filter _ = c.left.net.filter _
  rw [List.filter_append, List.append_right_eq_self, List.filter_eq_nil_iff]
  intro u hu
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hu
  simp

private theorem thinLeft_start_inr (c : SysState (a.join b w)) (j : τ.Id) :
    (c.startActor env (.inr j)).thinLeft = c.thinLeft := by
  have hleft : ({ c with up := update c.up (.inr j) true } : SysState (a.join b w)).thinLeft
      = c.thinLeft :=
    SysState.ext' rfl (funext fun k => update_inr_inl c.up j true k) rfl rfl rfl
  exact (thinLeft_settle_inr (c := { c with up := update c.up (.inr j) true }) j
    ((b.actor j).recover (c.state (.inr j)))).trans hleft

/-- A message between actors of `a` that is deliverable without the messages from outside is
deliverable in the join. -/
theorem deliverable_of_thinLeft {e : Envelope σ}
    (h : c.thinLeft.deliverable env.left e = true) :
    ∃ s, e.src = some s ∧ c.deliverable env ⟨some (.inl s), .inl e.dst, e.msg⟩ = true := by
  have hmem := mem_of_deliverable h
  obtain ⟨hleft, hsrc⟩ := List.mem_filter.mp hmem
  obtain ⟨src, i, msg⟩ := e
  obtain ⟨s, rfl⟩ := Option.isSome_iff_exists.mp hsrc
  refine ⟨s, rfl, ?_⟩
  have hlink : env.left.link (some s) i = env.link (some (.inl s)) (.inl i) := rfl
  simp only [deliverable, hlink] at h ⊢
  split at h
  · next hord =>
    simp only [hord, ↓reduceIte]
    have hsame : (fun e : Envelope (joinSig σ τ) =>
        (e.left?.filter fun e => e.src.isSome).any (Envelope.sameLink ⟨some s, i, msg⟩))
        = Envelope.sameLink (⟨some (.inl s), .inl i, msg⟩ : Envelope (joinSig σ τ)) := by
      funext e
      obtain ⟨src, k | j, m⟩ := e
      · rcases src with _ | s' | j' <;> simp [Envelope.left?, Envelope.sameLink, Option.filter]
      · simp [Envelope.left?, Envelope.sameLink]
    have hfind : c.thinLeft.net.find? (Envelope.sameLink ⟨some s, i, msg⟩)
        = some ⟨some s, i, msg⟩ := by simpa using h
    change ((c.net.filterMap Envelope.left?).filter _).find? _ = _ at hfind
    rw [List.filter_filterMap, List.find?_filterMap, hsame] at hfind
    cases hE : c.net.find?
        (Envelope.sameLink (⟨some (.inl s), .inl i, msg⟩ : Envelope (joinSig σ τ))) with
    | none => simp [hE] at hfind
    | some E =>
      rw [hE, Option.bind_some] at hfind
      have hEu : E.left? = some ⟨some s, i, msg⟩ := by
        cases hl : E.left? with
        | none => simp [hl] at hfind
        | some u =>
          rw [hl] at hfind
          simp only [Option.filter] at hfind
          split at hfind <;> simp_all
      simp [(Envelope.left?_eq_inside E).mp hEu]
  · next hord =>
    simp only [hord] at h ⊢
    obtain ⟨E, hE, hEu⟩ := List.mem_filterMap.mp hleft
    simpa [(Envelope.left?_eq_inside E).mp hEu] using hE

theorem hasMail_of_thinLeft {i : σ.Id} (h : c.thinLeft.hasMail i = true) :
    c.hasMail (.inl i) = true := by
  simp only [hasMail, List.any_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨E, hE, hEu⟩ := List.mem_filterMap.mp (List.mem_filter.mp hu).1
  refine ⟨E, hE, ?_⟩
  obtain ⟨src, k | j, msg⟩ := E
  · simp only [Envelope.left?, Option.some.injEq] at hEu
    rw [← hEu]
  · simp [Envelope.left?] at hEu

end SysState

private theorem mem_timeouts_left {i i' : σ.Id} {msg : σ.Msg i'} (effs : List (Effect σ i))
    (h : Event.timeout (σ := joinSig σ τ) (.inl i') msg ∈
      Effect.timeouts (σ := joinSig σ τ) (.inl i) (effs.flatMap fun eff => [w.left b eff])) :
    Event.timeout i' msg ∈ Effect.timeouts i effs := by
  simp only [Effect.timeouts, List.mem_filterMap, List.mem_flatMap, List.mem_singleton] at h ⊢
  obtain ⟨_, ⟨eff, heff, rfl⟩, h⟩ := h
  refine ⟨eff, heff, ?_⟩
  cases eff with
  | after d m =>
    simp only [Wiring.left, Option.some.injEq, Event.timeout.injEq, Sum.inl.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp [eq_of_heq h]
  | emit out => cases hw : w.toRight out <;> simp [Wiring.left, hw] at h
  | _ => simp [Wiring.left] at h

private theorem not_mem_timeouts_inr {i : σ.Id} {j : τ.Id} {msg : σ.Msg i}
    (effs : List (Effect (joinSig σ τ) (.inr j))) :
    Event.timeout (σ := joinSig σ τ) (.inl i) msg ∉
      Effect.timeouts (σ := joinSig σ τ) (.inr j) effs := by
  simp only [Effect.timeouts, List.mem_filterMap, not_exists, not_and]
  intro eff _
  cases eff <;> simp

/-- What `a` alone does for a step `ev` of the join from `c` to `c'`, seen without the messages
from outside: a run between the two views that shows what `ev` shows of `a`, takes the
obligation `ev` meets, arms the timers of `a` that `ev` arms, and passes only through states
whose actors are as in `c` or as in `c'`. -/
structure Wiring.Block (w : Wiring σ τ) (env : EnvModel (joinSig σ τ))
    (c c' : SysState (a.join b w)) (ev : Event (joinSig σ τ)) (evs : List (Event σ)) : Prop where
  run : c.thinLeft.run env.left evs = some c'.thinLeft
  shown : evs.filterMap w.shown = ev.leftDeed.toList
  taken : ∀ e, ev.left? = some e → e ∈ evs
  arms : ∀ i msg, Event.timeout (σ := joinSig σ τ) (.inl i) msg ∈ c.arms ev →
    ∃ j, ∃ hj : j < evs.length, ∃ d,
    c.thinLeft.run env.left (evs.take j) = some d ∧ Event.timeout i msg ∈ d.arms evs[j]
  near : ∀ j d, c.thinLeft.run env.left (evs.take j) = some d →
    (d.state = c.left.state ∧ d.up = c.left.up) ∨ (d.state = c'.left.state ∧ d.up = c'.left.up)

namespace Wiring.Block

private theorem nil {ev : Event (joinSig σ τ)} (hthin : c'.thinLeft = c.thinLeft)
    (hdeed : ev.leftDeed = none) (hleft : ev.left? = none)
    (harms : ∀ i msg, Event.timeout (σ := joinSig σ τ) (.inl i) msg ∉ c.arms ev) :
    Wiring.Block w env c c' ev [] where
  run := by rw [hthin]; rfl
  shown := by rw [hdeed]; rfl
  taken e h := by simp [hleft] at h
  arms i msg h := absurd h (harms i msg)
  near j d h := by
    simp only [List.take_nil, SysState.run, Option.some.injEq] at h
    exact .inl (h ▸ ⟨rfl, rfl⟩)

private theorem single {ev : Event (joinSig σ τ)} {e : Event σ}
    (hstep : c.thinLeft.step env.left e = some c'.thinLeft)
    (hshown : (w.shown e).toList = ev.leftDeed.toList)
    (htaken : ∀ e', ev.left? = some e' → e' = e)
    (harms : ∀ i msg, Event.timeout (σ := joinSig σ τ) (.inl i) msg ∉ c.arms ev) :
    Wiring.Block w env c c' ev [e] where
  run := by simp [SysState.run, hstep]
  shown := by rw [filterMap_cons_toList, List.filterMap_nil, List.append_nil, hshown]
  taken e' h := by simp [htaken e' h]
  arms i msg h := absurd h (harms i msg)
  near j d h := by
    cases j with
    | zero =>
      simp only [List.take_zero, SysState.run, Option.some.injEq] at h
      exact .inl (h ▸ ⟨rfl, rfl⟩)
    | succ j =>
      simp only [List.take_succ_cons, List.take_nil, SysState.run, hstep, Option.bind_some,
        Option.some.injEq] at h
      exact .inr (h ▸ ⟨rfl, rfl⟩)

private theorem handle {ev : Event (joinSig σ τ)} {c₁ : SysState (a.join b w)} {i : σ.Id}
    {r : a.State i × List (Effect σ i)} {pre mid : List (Event σ)} {main : Event σ}
    {x : SysState a} (hpre : c.thinLeft.run env.left pre = some x)
    (hpreq : ∀ e ∈ pre, e.quiet = true)
    (hmain : x.run env.left (main :: mid) = some (c₁.thinLeft.settle env.left i r))
    (hmidq : ∀ e ∈ mid, e.quiet = true)
    (hc' : c' = c₁.settle env (.inl i) (r.1, r.2.flatMap fun eff => [w.left b eff]))
    (htidy : ∀ out ∈ c₁.left.outbox, w.toRight out = none)
    (hshown : (pre ++ main :: mid).filterMap w.shown = ev.leftDeed.toList)
    (htaken : ∀ e, ev.left? = some e → e = main)
    (harms : ∀ i' msg, Event.timeout (σ := joinSig σ τ) (.inl i') msg ∈ c.arms ev →
      Event.timeout i' msg ∈ x.arms main) :
    Wiring.Block w env c c' ev (pre ++ main :: (mid ++ w.wired r.2)) := by
  have hwired : ∀ e ∈ w.wired r.2, e.quiet = true := by
    intro e he
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp he
    rfl
  obtain ⟨y, hy, hymid⟩ : ∃ y, x.step env.left main = some y ∧
      y.run env.left mid = some (c₁.thinLeft.settle env.left i r) := by
    simp only [SysState.run] at hmain
    cases hstep : x.step env.left main with
    | none => simp [hstep] at hmain
    | some y => exact ⟨y, rfl, by simpa [hstep] using hmain⟩
  have hy' : y.run env.left (mid ++ w.wired r.2) = some c'.thinLeft := by
    rw [SysState.run_append, hymid, Option.bind_some, hc', SysState.thinLeft_settle c₁ i r htidy]
  have hrun : c.thinLeft.run env.left (pre ++ main :: (mid ++ w.wired r.2))
      = some c'.thinLeft := by
    rw [SysState.run_append, hpre, Option.bind_some]
    simp only [SysState.run, hy, Option.bind_some, hy']
  have hyc := SysState.run_quiet
    (fun e he => (List.mem_append.mp he).elim (hmidq e) (hwired e)) hy'
  refine ⟨hrun, ?_, fun e h => by simp [htaken e h], fun i' msg h => ?_, fun j d h => ?_⟩
  · have hw : (w.wired r.2).filterMap w.shown = [] := List.filterMap_eq_nil_iff.mpr (shown_wired _)
    rw [← List.cons_append, ← List.append_assoc, List.filterMap_append, hshown, hw,
      List.append_nil]
  · exact ⟨pre.length, by simp, x, by simpa using hpre, by simpa using harms i' msg h⟩
  · by_cases hj : j ≤ pre.length
    · rw [List.take_append_of_le_length hj] at h
      have := SysState.run_quiet (fun e he => hpreq e (List.mem_of_mem_take he)) h
      exact .inl ⟨this.1, this.2.1⟩
    · obtain ⟨k, rfl⟩ : ∃ k, j = pre.length + (k + 1) := ⟨j - pre.length - 1, by omega⟩
      rw [List.take_append, List.take_of_length_le (by omega), SysState.run_append, hpre,
        Option.bind_some, show pre.length + (k + 1) - pre.length = k + 1 by omega,
        List.take_succ_cons, SysState.run, hy, Option.bind_some] at h
      have hd := SysState.run_quiet (fun e he =>
        (List.mem_append.mp (List.mem_of_mem_take he)).elim (hmidq e) (hwired e)) h
      exact .inr ⟨hd.1.trans hyc.1.symm, hd.2.1.trans hyc.2.1.symm⟩

end Wiring.Block

namespace SysState

/-- A message from outside to an actor of `a`, put in from outside alone. -/
private theorem put_outside (hc : Tidy w c) {u : Envelope σ}
    (hu : u ∈ c.left.net) (hsrc : u.src = none) :
    ∃ x, c.thinLeft.run env.left [.input x] = some { c.thinLeft with net := c.thinLeft.net ++ [u] }
      ∧ u ∉ c.thinLeft.net := by
  obtain ⟨x, hx⟩ := hc.accepted _ hu hsrc
  refine ⟨x, ?_, fun h => ?_⟩
  · have hin := (step_input (c := c.thinLeft) (env := env.left) (x := x)).mpr rfl
    rw [hx] at hin
    simp only [run, hin, Option.bind_some]
  · have := (List.mem_filter.mp h).2
    rw [hsrc] at this
    cases this

private theorem inside_main {c₁ : SysState (a.join b w)} {i : σ.Id}
    {r : a.State i × List (Effect σ i)} {main : Event σ} {ev : Event (joinSig σ τ)}
    (hc : Tidy w c)
    (hmain : c.thinLeft.step env.left main = some (c₁.thinLeft.settle env.left i r))
    (hc' : c' = c₁.settle env (.inl i) (r.1, r.2.flatMap fun eff => [w.left b eff]))
    (houtbox : c₁.outbox = c.outbox) (hshown : (w.shown main).toList = ev.leftDeed.toList)
    (htaken : ∀ e, ev.left? = some e → e = main)
    (harms : ∀ i' msg, Event.timeout (σ := joinSig σ τ) (.inl i') msg ∈ c.arms ev →
      Event.timeout i' msg ∈ c.thinLeft.arms main) :
    ∃ evs, Wiring.Block w env c c' ev evs :=
  ⟨_, Wiring.Block.handle (pre := []) (mid := []) rfl (by simp)
    (by simp [run, hmain]) (by simp) hc'
    (fun out hout => hc.unwired out (by simpa [SysState.left, houtbox] using hout))
    (by simpa [filterMap_cons_toList] using hshown) htaken harms⟩

private theorem outside_main {c₁ : SysState (a.join b w)} {i : σ.Id} {msg : σ.Msg i}
    {ev : Event (joinSig σ τ)} (hc : Tidy w c)
    (hu : (⟨none, i, msg⟩ : Envelope σ) ∈ c.left.net) (hup : c.up (.inl i) = true)
    (hc₁ : c₁.thinLeft = c.thinLeft)
    (hc' : c' = c₁.settle env (.inl i) (((a.actor i).step (c.state (.inl i)) msg).1,
      ((a.actor i).step (c.state (.inl i)) msg).2.flatMap fun eff => [w.left b eff]))
    (houtbox : c₁.outbox = c.outbox) (hshown : ev.leftDeed = some (.handle i msg))
    (htaken : ∀ e, ev.left? = some e → e = .deliver ⟨none, i, msg⟩)
    (harms : ∀ i' m, Event.timeout (σ := joinSig σ τ) (.inl i') m ∈ c.arms ev →
      Event.timeout i' m ∈ Effect.timeouts i ((a.actor i).step (c.state (.inl i)) msg).2) :
    ∃ evs, Wiring.Block w env c c' ev evs := by
  obtain ⟨x, hx, hnot⟩ := put_outside hc hu rfl
  have hlink : env.left.link none i = Link.network := rfl
  have hdeliver : ({ c.thinLeft with net := c.thinLeft.net ++ [⟨none, i, msg⟩] } : SysState a).step
      env.left (.deliver ⟨none, i, msg⟩)
        = some (c₁.thinLeft.settle env.left i ((a.actor i).step (c.state (.inl i)) msg)) := by
    refine step_deliver.mpr ⟨hup, by simp [deliverable, hlink, Link.network], ?_⟩
    rw [hc₁, List.erase_append_right _ hnot, List.erase_cons_head, List.append_nil]
    rfl
  exact ⟨_, Wiring.Block.handle (c₁ := c₁) (r := (a.actor i).step (c.state (.inl i)) msg)
    (pre := [.input x]) (mid := []) hx (by simp [Event.quiet]) (by simp [run, hdeliver])
    (by simp) hc'
    (fun out hout => hc.unwired out (by simpa [SysState.left, houtbox] using hout))
    (by rw [hshown]; rfl) htaken harms⟩

private theorem block_deliver (hc : Tidy w c) {e : Envelope (joinSig σ τ)}
    (hstep : c.step env (.deliver e) = some c') :
    ∃ evs, Wiring.Block w env c c' (.deliver e) evs := by
  obtain ⟨hup, hdel, rfl⟩ := step_deliver.mp hstep
  have hmem := mem_of_deliverable hdel
  obtain ⟨src, i | j, msg⟩ := e
  · have harms (x : SysState a) (hx : x.state = c.left.state) (src' : Option σ.Id) (i' : σ.Id)
        (m : σ.Msg i') (h : Event.timeout (σ := joinSig σ τ) (.inl i') m ∈
          c.arms (.deliver ⟨src, .inl i, msg⟩)) :
        Event.timeout i' m ∈ x.arms (.deliver ⟨src', i, msg⟩) := by
      simp only [arms, hx]
      exact mem_timeouts_left _ h
    have outside (hsrc : src.bind Sum.getLeft? = none) :
        ∃ evs, Wiring.Block w env c (({ c with net := c.net.erase ⟨src, .inl i, msg⟩ } :
          SysState (a.join b w)).handle env (.inl i) msg) (.deliver ⟨src, .inl i, msg⟩) evs :=
      outside_main hc (hsrc ▸ List.mem_filterMap.mpr ⟨_, hmem, rfl⟩) hup
        (thinLeft_erase_outside _ fun u hu => by simp [Envelope.left?, hsrc] at hu; rw [← hu])
        rfl rfl rfl (fun e h => by simpa [Event.left?, Envelope.left?, hsrc, eq_comm] using h)
        fun i' m h => harms c.left rfl none i' m h
    rcases src with _ | s | j'
    · exact outside rfl
    · have hdel' : c.thinLeft.deliverable env.left ⟨some s, i, msg⟩ = true :=
        deliverable_left (Thin.inside _) hdel
      exact inside_main hc (step_deliver (c := c.thinLeft) (env := env.left)
          (e := ⟨some s, i, msg⟩) |>.mpr ⟨hup, hdel', by rw [← thinLeft_erase_inside]; rfl⟩)
        rfl rfl rfl (fun e h => by simpa [Event.left?, Envelope.left?, eq_comm] using h)
        fun i' m h => harms _ rfl _ i' m h
    · exact outside rfl
  · refine ⟨[], .nil ?_ rfl rfl fun i' m => not_mem_timeouts_inr _⟩
    exact (thinLeft_settle_inr _ j ((b.actor j).step (c.state (.inr j)) msg)).trans
      (thinLeft_erase_outside _ (by simp [Envelope.left?]))

private theorem block_duplicate (hc : Tidy w c) {e : Envelope (joinSig σ τ)}
    (hstep : c.step env (.duplicate e) = some c') :
    ∃ evs, Wiring.Block w env c c' (.duplicate e) evs := by
  obtain ⟨hup, hdup, hdel, rfl⟩ := step_duplicate.mp hstep
  have hmem := mem_of_deliverable hdel
  obtain ⟨src, i | j, msg⟩ := e
  · have harms (x : SysState a) (hx : x.state = c.left.state) (e : Event σ)
        (he : x.arms e = Effect.timeouts i ((a.actor i).step (x.state i) msg).2) (i' : σ.Id)
        (m : σ.Msg i') (h : Event.timeout (σ := joinSig σ τ) (.inl i') m ∈
          c.arms (.duplicate ⟨src, .inl i, msg⟩)) :
        Event.timeout i' m ∈ x.arms e := by
      rw [he, hx]
      exact mem_timeouts_left _ h
    have outside (hsrc : src.bind Sum.getLeft? = none) :
        ∃ evs, Wiring.Block w env c (c.handle env (.inl i) msg) (.duplicate ⟨src, .inl i, msg⟩)
          evs :=
      outside_main hc (hsrc ▸ List.mem_filterMap.mpr ⟨_, hmem, rfl⟩) hup rfl rfl rfl rfl
        (fun e h => by simp [Event.left?] at h)
        fun i' m h => harms c.left rfl (.deliver ⟨none, i, msg⟩) rfl i' m h
    rcases src with _ | s | j'
    · exact outside rfl
    · have hdel' : c.thinLeft.deliverable env.left ⟨some s, i, msg⟩ = true :=
        deliverable_left (Thin.inside _) hdel
      exact inside_main (c₁ := c) hc (step_duplicate (c := c.thinLeft) (env := env.left)
          (e := ⟨some s, i, msg⟩) |>.mpr ⟨hup, hdup, hdel', rfl⟩)
        rfl rfl rfl (fun e h => by simp [Event.left?] at h)
        fun i' m h => harms c.thinLeft rfl (.duplicate ⟨some s, i, msg⟩) rfl i' m h
    · exact outside rfl
  · exact ⟨[], .nil (thinLeft_settle_inr _ j ((b.actor j).step (c.state (.inr j)) msg)) rfl rfl
      fun i' m => not_mem_timeouts_inr _⟩

private theorem block_drop {e : Envelope (joinSig σ τ)} (hstep : c.step env (.drop e) = some c') :
    ∃ evs, Wiring.Block w env c c' (.drop e) evs := by
  obtain ⟨hlossy, hmem, rfl⟩ := step_drop.mp hstep
  have hnone : ∀ i msg, Event.timeout (σ := joinSig σ τ) (.inl i) msg ∉ c.arms (.drop e) :=
    fun _ _ h => by simp [arms] at h
  obtain ⟨src, i | j, msg⟩ := e
  · have outside (hsrc : src.bind Sum.getLeft? = none) :
        ∃ evs, Wiring.Block w env c { c with net := c.net.erase ⟨src, .inl i, msg⟩ }
          (.drop ⟨src, .inl i, msg⟩) evs :=
      ⟨[], .nil (thinLeft_erase_outside _ fun u hu => by
        simp [Envelope.left?, hsrc] at hu; rw [← hu]) rfl rfl hnone⟩
    rcases src with _ | s | j'
    · exact outside rfl
    · refine ⟨_, .single (e := .drop ⟨some s, i, msg⟩) ?_ rfl
        (fun e h => by simp [Event.left?] at h)
        hnone⟩
      exact step_drop.mpr ⟨hlossy, List.mem_filter.mpr ⟨List.mem_filterMap.mpr ⟨_, hmem, rfl⟩, rfl⟩,
        thinLeft_erase_inside⟩
    · exact outside rfl
  · exact ⟨[], .nil (thinLeft_erase_outside _ (by simp [Envelope.left?])) rfl rfl hnone⟩

private theorem block_timeout (hc : Tidy w c) {i : σ.Id ⊕ τ.Id}
    {msg : (joinSig σ τ).Msg i} (hstep : c.step env (.timeout i msg) = some c') :
    ∃ evs, Wiring.Block w env c c' (.timeout i msg) evs := by
  obtain ⟨hup, hmem, rfl⟩ := step_timeout.mp hstep
  cases i with
  | inl i =>
    have hthin : ({ c with timers := update c.timers (.inl i) ((c.timers (.inl i)).erase msg) } :
        SysState (a.join b w)).thinLeft
        = { c.thinLeft with
            timers := update c.thinLeft.timers i ((c.thinLeft.timers i).erase msg) } :=
      SysState.ext' rfl rfl rfl (update_inl c.timers i _) rfl
    exact inside_main hc (step_timeout (c := c.thinLeft) (env := env.left) |>.mpr
        ⟨hup, hmem, by rw [hthin]; rfl⟩) rfl rfl rfl
      (fun e h => by simpa [Event.left?, eq_comm] using h) fun i' m h => mem_timeouts_left _ h
  | inr j =>
    have hthin : ({ c with timers := update c.timers (.inr j) ((c.timers (.inr j)).erase msg) } :
        SysState (a.join b w)).thinLeft = c.thinLeft :=
      SysState.ext' rfl rfl rfl
        (funext fun k => update_inr_inl c.timers j ((c.timers (.inr j)).erase msg) k) rfl
    exact ⟨[], .nil
      ((thinLeft_settle_inr _ j ((b.actor j).step (c.state (.inr j)) msg)).trans hthin)
      rfl rfl
      fun i' m => not_mem_timeouts_inr _⟩

private theorem block_output (hc : Tidy w c) {out : σ.Out ⊕ τ.Out}
    (hstep : c.step env (.output out) = some c') :
    ∃ evs, Wiring.Block w env c c' (.output out) evs := by
  obtain ⟨hmem, rfl⟩ := step_output.mp hstep
  have hnone : ∀ i msg, Event.timeout (σ := joinSig σ τ) (.inl i) msg ∉ c.arms (.output out) :=
    fun _ _ h => by simp [arms] at h
  cases out with
  | inl out =>
    have hleft : out ∈ c.thinLeft.outbox := List.mem_filterMap.mpr ⟨_, hmem, rfl⟩
    have houtbox := filterMap_erase (f := Sum.getLeft?) (a := (.inl out : σ.Out ⊕ τ.Out))
      (b := out) (fun x => by cases x <;> simp) c.outbox
    refine ⟨_, .single (e := .output out) (step_output.mpr ⟨hleft, ?_⟩) ?_
      (fun e h => by simpa [Event.left?, eq_comm] using h) hnone⟩
    · exact SysState.ext' rfl rfl rfl rfl houtbox
    · simp [Wiring.shown, Event.deed, Event.leftDeed, hc.unwired out hleft, Option.filter]
  | inr out =>
    exact ⟨[], .nil (SysState.ext' rfl rfl rfl rfl (filterMap_erase_of_none rfl c.outbox)) rfl rfl
      hnone⟩

private theorem block_crash {i : σ.Id ⊕ τ.Id} (hstep : c.step env (.crash i) = some c') :
    ∃ evs, Wiring.Block w env c c' (.crash i) evs := by
  obtain ⟨hup, hcrash, rfl⟩ := step_crash.mp hstep
  have hnone : ∀ i' msg, Event.timeout (σ := joinSig σ τ) (.inl i') msg ∉ c.arms (.crash i) :=
    fun _ _ h => by simp [arms] at h
  cases i with
  | inl i =>
    exact ⟨_, .single (e := .crash i) (step_crash.mpr ⟨hup, hcrash, thinLeft_down i⟩) rfl
      (fun e h => by simp [Event.left?] at h) hnone⟩
  | inr j =>
    have hleft : (c.down env (.inr j)).left = c.left :=
      SysState.ext' rfl (funext fun k => update_inr_inl c.up j false k)
        (filterMap_filter_of_none SysState.left?_of_dropped c.net)
        (funext fun k => update_inr_inl c.timers j [] k) rfl
    refine ⟨[], .nil ?_ rfl rfl hnone⟩
    unfold thinLeft
    rw [hleft]

private theorem block_start (hc : Tidy w c) {i : σ.Id ⊕ τ.Id}
    (hstep : c.step env (.start i) = some c') :
    ∃ evs, Wiring.Block w env c c' (.start i) evs := by
  obtain ⟨hdown, hmail, rfl⟩ := step_start.mp hstep
  cases i with
  | inl i =>
    have hthin : ({ c with up := update c.up (.inl i) true } : SysState (a.join b w)).thinLeft
        = { c.thinLeft with up := update c.thinLeft.up i true } :=
      SysState.ext' rfl (update_inl c.up i true) rfl rfl rfl
    by_cases hmail' : c.thinLeft.hasMail i = true ∨ env.left.restarts i = true
    · exact inside_main hc (step_start (c := c.thinLeft) (env := env.left) |>.mpr
          ⟨hdown, hmail', by rw [hthin]; rfl⟩) rfl rfl rfl
        (fun e h => by simpa [Event.left?, eq_comm] using h) fun i' m h => mem_timeouts_left _ h
    · have hjoin : c.hasMail (.inl i) = true := hmail.resolve_right fun h => hmail' (.inr h)
      obtain ⟨e, he, hdst⟩ : ∃ e ∈ c.net, e.dst = .inl i := by
        simpa [SysState.hasMail] using hjoin
      obtain ⟨src, k | j, msg⟩ := e
      · obtain rfl : k = i := by simpa using hdst
        have hu : (⟨src.bind Sum.getLeft?, k, msg⟩ : Envelope σ) ∈ c.left.net :=
          List.mem_filterMap.mpr ⟨_, he, rfl⟩
        have hsrc : src.bind Sum.getLeft? = none := by
          cases hb : src.bind Sum.getLeft? with
          | none => rfl
          | some s' =>
            refine absurd (.inl ?_) hmail'
            simp only [hasMail, List.any_eq_true, decide_eq_true_eq]
            rw [hb] at hu
            exact ⟨_, List.mem_filter.mpr ⟨hu, rfl⟩, rfl⟩
        rw [hsrc] at hu
        obtain ⟨x, hx, hnot⟩ := put_outside hc hu rfl
        have hlossy : (env.left.link none k).lossy = true := rfl
        let x' : SysState a :=
          { c.thinLeft with
            net := c.thinLeft.net ++ [⟨none, k, msg⟩]
            up := update c.thinLeft.up k true }
        obtain ⟨hkept, heq⟩ := SysState.settle_erase (env := env.left) x' k
          ((a.actor k).recover (c.state (.inl k))) (e := ⟨none, k, msg⟩) (by simp [x']) hlossy
        have hx' : ({ x' with net := x'.net.erase ⟨none, k, msg⟩ } : SysState a)
            = ({ c with up := update c.up (.inl k) true } : SysState (a.join b w)).thinLeft := by
          rw [hthin]
          simp [x', List.erase_append_right _ hnot]
        have hmain : ({ c.thinLeft with net := c.thinLeft.net ++ [⟨none, k, msg⟩] } :
            SysState a).run env.left [.start k, .drop ⟨none, k, msg⟩]
            = some (({ c with up := update c.up (.inl k) true } :
              SysState (a.join b w)).thinLeft.settle env.left k
                ((a.actor k).recover (c.state (.inl k)))) := by
          have hstart : ({ c.thinLeft with net := c.thinLeft.net ++ [⟨none, k, msg⟩] } :
              SysState a).step env.left (.start k) = some (x'.settle env.left k
                ((a.actor k).recover (c.state (.inl k)))) :=
            step_start.mpr ⟨hdown, .inl (by simp [hasMail]), rfl⟩
          rw [← hx', heq]
          simp only [run, hstart, Option.bind_some, step_drop.mpr ⟨hlossy, hkept, rfl⟩]
        exact ⟨_, Wiring.Block.handle (pre := [.input x]) (mid := [.drop ⟨none, k, msg⟩]) hx
          (by simp [Event.quiet]) hmain (by simp [Event.quiet]) rfl hc.unwired rfl
          (fun e h => by simpa [Event.left?, eq_comm] using h)
          fun i' m h => mem_timeouts_left _ h⟩
      · simp at hdst
  | inr j =>
    exact ⟨[], .nil (thinLeft_start_inr c j) rfl rfl fun i' m => not_mem_timeouts_inr _⟩

private theorem exists_block_of (hc : Tidy w c) {ev : Event (joinSig σ τ)}
    (hstep : c.step env ev = some c') : ∃ evs, Wiring.Block w env c c' ev evs := by
  cases ev with
  | input x =>
    obtain rfl := step_input.mp hstep
    refine ⟨[], .nil ?_ rfl rfl fun _ _ h => by simp [arms] at h⟩
    cases x <;> exact thinLeft_append_outside _ _ (by simp [Envelope.left?])
  | deliver e => exact block_deliver hc hstep
  | duplicate e => exact block_duplicate hc hstep
  | drop e => exact block_drop hstep
  | timeout i msg => exact block_timeout hc hstep
  | output out => exact block_output hc hstep
  | crash i => exact block_crash hstep
  | start i => exact block_start hc hstep

/-- Every step of the join from a reachable state is a run of `a` alone between the views
without the messages from outside. -/
theorem exists_block (hc : (a.join b w).Reachable env c) {ev : Event (joinSig σ τ)}
    (hstep : c.step env ev = some c') : ∃ evs, Wiring.Block w env c c' ev evs :=
  exists_block_of (Tidy.of_reachable hc) hstep

/-- The join starts, seen from `a` without the messages from outside, where `a` alone starts
once it has handed over the outputs the wiring routes to `b`. -/
theorem init_thinLeft (env : EnvModel (joinSig σ τ)) :
    ∃ evs, (SysState.init a env.left).run env.left evs
        = some (SysState.init (a.join b w) env).thinLeft
      ∧ ∀ ev ∈ evs, ev.quiet = true ∧ w.shown ev = none := by
  have hfold : SysState.init (a.join b w) env
      = b.boot.foldl (fun c j => c.startActor env (.inr j))
        (a.boot.foldl (fun c i => c.startActor env (.inl i)) (SysState.blank (a.join b w))) := by
    simp [SysState.init, List.foldl_append, List.foldl_map]
  obtain ⟨xs, hxs⟩ := Seen.boot_inr (env := env) b.boot
    (a.boot.foldl (fun c i => c.startActor env (.inl i)) (SysState.blank (a.join b w)))
  obtain ⟨n, hn, h⟩ := Seen.boot (env := env) a.boot (SysState.blank (a.join b w))
    (Thin.inside _)
  obtain rfl : n = [] := by
    cases hn
    rfl
  obtain ⟨outbox', ho', heq⟩ := h [] rfl
  have hinit : SysState.init a env.left = { (a.boot.foldl (fun c i => c.startActor env (.inl i))
      (SysState.blank (a.join b w))).thinLeft with outbox := [] ++ outbox' } := heq
  have hB : (b.boot.foldl (fun c j => c.startActor env (.inr j))
      (a.boot.foldl (fun c i => c.startActor env (.inl i)) (SysState.blank (a.join b w)))).thinLeft
      = (a.boot.foldl (fun c i => c.startActor env (.inl i))
        (SysState.blank (a.join b w))).thinLeft := by
    unfold thinLeft
    rw [hxs]
    refine SysState.ext' rfl rfl ?_ rfl rfl
    show List.filter _ (_ ++ _) = List.filter _ _
    rw [List.filter_append, List.append_right_eq_self, List.filter_eq_nil_iff]
    intro u hu
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hu
    simp
  refine ⟨(outbox'.filter fun out => !(w.toRight out).isNone).map .output, ?_, fun ev hev => ?_⟩
  · rw [hinit, SysState.run_outputs_filter _ _ _ [] outbox' (by simp), List.nil_append, ho', hfold,
      hB]
    rfl
  · obtain ⟨out, hout, rfl⟩ := List.mem_map.mp hev
    exact ⟨rfl, shown_wired outbox' _ hev⟩

end SysState

end Thinned

section ThinnedRight

/-! Seen from `b` without the messages from outside, a run of the join is a run of `b` alone
step by step too. The join with its sides exchanged takes the same steps (`SysState.step_swap`),
and a step of a join is a run of its left system from any state with no wired output waiting
and only accepted inputs from outside, which a reachable state of the join has on both sides. The
boot of `a` is out of the way: what it sends `b` is from outside, so the view leaves it out. -/

variable {σ τ : Signature} {a : System σ} {b : System τ} {w : Wiring σ τ}
  {env : EnvModel (joinSig σ τ)} {c c' : SysState (a.join b w)}

private theorem SysState.swap_thinLeft (c : SysState (a.join b w)) :
    c.swap.thinLeft = c.thinRight := by
  unfold SysState.thinLeft SysState.thinRight
  rw [SysState.swap_left]

private theorem Wiring.swap_shown (w : Wiring σ τ) : w.swap.shown = w.shownRight := by
  funext ev
  unfold Wiring.shown Wiring.shownRight
  congr 1

private theorem Event.left?_swap (ev : Event (joinSig σ τ)) : ev.swap.left? = ev.right? := by
  cases ev with
  | deliver e =>
    obtain ⟨src, i | j, msg⟩ := e
    · rfl
    · rcases src with _ | s | s <;> rfl
  | timeout x msg => rcases x with i | j <;> rfl
  | start x => rcases x with i | j <;> rfl
  | output out => rcases out with o | o <;> rfl
  | _ => rfl

private theorem Event.leftDeed_swap (ev : Event (joinSig σ τ)) :
    ev.swap.leftDeed = ev.rightDeed := by
  cases ev with
  | deliver e | duplicate e => obtain ⟨src, i | j, msg⟩ := e <;> rfl
  | timeout x msg => rcases x with i | j <;> rfl
  | output out => rcases out with o | o <;> rfl
  | _ => rfl

private theorem Effect.timeouts_swap {x : σ.Id ⊕ τ.Id} (effs : List (Effect (joinSig σ τ) x)) :
    Effect.timeouts x.swap (effs.map Effect.swap) = (Effect.timeouts x effs).map Event.swap := by
  simp only [Effect.timeouts, List.filterMap_map, List.map_filterMap]
  congr 1
  funext eff
  rcases x with i | j <;> cases eff <;> first | rfl | (rename_i to msg; cases to <;> rfl)

private theorem SysState.arms_swap (c : SysState (a.join b w)) (ev : Event (joinSig σ τ)) :
    c.swap.arms ev.swap = (c.arms ev).map Event.swap := by
  have hl (i : σ.Id) (effs : List (Effect σ i)) :
      Effect.timeouts (σ := joinSig τ σ) (.inr i) (effs.flatMap fun eff => [w.swap.right b eff])
        = (Effect.timeouts (σ := joinSig σ τ) (.inl i)
          (effs.flatMap fun eff => [w.left b eff])).map Event.swap := by
    rw [← Wiring.left_swap]
    exact Effect.timeouts_swap (x := .inl i) _
  have hr (j : τ.Id) (effs : List (Effect τ j)) :
      Effect.timeouts (σ := joinSig τ σ) (.inl j) (effs.flatMap fun eff => [w.swap.left a eff])
        = (Effect.timeouts (σ := joinSig σ τ) (.inr j)
          (effs.flatMap fun eff => [w.right a eff])).map Event.swap := by
    rw [← Wiring.right_swap]
    exact Effect.timeouts_swap (x := .inr j) _
  cases ev with
  | deliver e | duplicate e =>
    obtain ⟨src, i | j, msg⟩ := e
    · exact hl i _
    · exact hr j _
  | timeout x msg =>
    rcases x with i | j
    · exact hl i _
    · exact hr j _
  | start x =>
    rcases x with i | j
    · exact hl i _
    · exact hr j _
  | _ => rfl

/-- The join with its sides exchanged meets what a step needs of a state on its left, though it
is not reachable. -/
private theorem Tidy.swap (hc : (a.join b w).Reachable env c) : Tidy w.swap c.swap := by
  refine ⟨fun out hout => ?_, fun u hu hsrc => ?_⟩
  · rw [SysState.swap_left] at hout
    exact hc.right_unwired out hout
  · rw [SysState.swap_left] at hu
    obtain ⟨c₁, hc₁, hequiv⟩ := hc.right
    exact hc₁.accepted ((hequiv.net.mem_iff u).mpr hu) hsrc

namespace SysState

/-- A message between actors of `b` that is deliverable without the messages from outside is
deliverable in the join. -/
theorem deliverable_of_thinRight {e : Envelope τ}
    (h : c.thinRight.deliverable env.right e = true) :
    ∃ s, e.src = some s ∧ c.deliverable env ⟨some (.inr s), .inr e.dst, e.msg⟩ = true := by
  rw [← swap_thinLeft, ← EnvModel.swap_left] at h
  obtain ⟨s, hs, hdel⟩ := deliverable_of_thinLeft h
  exact ⟨s, hs, (deliverable_swap c ⟨some (.inr s), .inr e.dst, e.msg⟩).symm.trans hdel⟩

theorem hasMail_of_thinRight {j : τ.Id} (h : c.thinRight.hasMail j = true) :
    c.hasMail (.inr j) = true := by
  rw [← swap_thinLeft] at h
  exact (hasMail_swap c (.inr j)).symm.trans (hasMail_of_thinLeft h)

end SysState

/-- What `b` alone does for a step `ev` of the join from `c` to `c'`, seen without the messages
from outside: `Wiring.Block` for the right system. -/
structure Wiring.BlockRight (w : Wiring σ τ) (env : EnvModel (joinSig σ τ))
    (c c' : SysState (a.join b w)) (ev : Event (joinSig σ τ)) (evs : List (Event τ)) : Prop where
  run : c.thinRight.run env.right evs = some c'.thinRight
  shown : evs.filterMap w.shownRight = ev.rightDeed.toList
  taken : ∀ e, ev.right? = some e → e ∈ evs
  arms : ∀ j msg, Event.timeout (σ := joinSig σ τ) (.inr j) msg ∈ c.arms ev →
    ∃ k, ∃ hk : k < evs.length, ∃ d,
    c.thinRight.run env.right (evs.take k) = some d ∧ Event.timeout j msg ∈ d.arms evs[k]
  near : ∀ k d, c.thinRight.run env.right (evs.take k) = some d →
    (d.state = c.right.state ∧ d.up = c.right.up) ∨ (d.state = c'.right.state ∧ d.up = c'.right.up)

namespace SysState

/-- Every step of the join from a reachable state is a run of `b` alone between the views
without the messages from outside. -/
theorem exists_blockRight (hc : (a.join b w).Reachable env c) {ev : Event (joinSig σ τ)}
    (hstep : c.step env ev = some c') : ∃ evs, Wiring.BlockRight w env c c' ev evs := by
  obtain ⟨evs, hb⟩ := exists_block_of (Tidy.swap hc) (step_swap hstep)
  have hrun := hb.run
  have hshown := hb.shown
  rw [swap_thinLeft, swap_thinLeft, EnvModel.swap_left] at hrun
  rw [Wiring.swap_shown, Event.leftDeed_swap] at hshown
  refine ⟨evs, hrun, hshown, fun e he => hb.taken e ((Event.left?_swap ev).trans he),
    fun j msg h => ?_, fun k d h => ?_⟩
  · have harms := hb.arms j msg (by rw [arms_swap]; exact List.mem_map_of_mem h)
    rwa [swap_thinLeft, EnvModel.swap_left] at harms
  · have hnear := hb.near k d (by rwa [swap_thinLeft, EnvModel.swap_left])
    rwa [swap_left, swap_left] at hnear

/-- Booting the actors of `a` in a join where nothing but messages from outside has reached
them is, seen without those messages, booting `a` alone and handing over the outputs the wiring
routes to `b`. -/
private theorem boot_thinLeft (env : EnvModel (joinSig σ τ)) (c₀ : SysState (a.join b w))
    (hc₀ : c₀.thinLeft = SysState.blank a) :
    ∃ evs, (SysState.init a env.left).run env.left evs
        = some (a.boot.foldl (fun c i => c.startActor env (.inl i)) c₀).thinLeft
      ∧ ∀ ev ∈ evs, ev.quiet = true ∧ w.shown ev = none := by
  obtain ⟨n, hn, h⟩ := Seen.boot (env := env) a.boot c₀ (Thin.inside _)
  obtain ⟨outbox', ho', heq⟩ := h [] (congrArg SysState.outbox hc₀).symm
  have hnet : c₀.left.net.filter (fun e => e.src.isSome) = [] := congrArg SysState.net hc₀
  have hsrc : ∀ e ∈ n, e.src = none := by
    intro e he
    cases hs : e.src with
    | none => rfl
    | some s =>
      have hmem : e ∈ c₀.left.net.filter fun e => e.src.isSome :=
        List.mem_filter.mpr ⟨hn.subset he, by simp [hs]⟩
      rw [hnet] at hmem
      cases hmem
  have hstate := congrArg SysState.state hc₀
  have hup := congrArg SysState.up hc₀
  have htimers := congrArg SysState.timers hc₀
  have hblank : ({ c₀.left with net := n, outbox := [] } : SysState a)
      = { SysState.blank a with net := n ++ (SysState.blank a).net } :=
    SysState.ext' hstate hup (List.append_nil n).symm htimers rfl
  rw [hblank, boot_prefix (env := env.left) a.boot (fun e he => by rw [hsrc e he]; rfl)] at heq
  obtain rfl : n = [] := by
    cases n with
    | nil => rfl
    | cons e n =>
      have h1 := congrArg SysState.net heq
      simp only [List.cons_append] at h1
      have hmem : e ∈ (a.boot.foldl (fun c i => c.startActor env (.inl i)) c₀).left.net.filter
          fun e => e.src.isSome := by
        rw [← h1]
        exact List.mem_cons_self
      have := (List.mem_filter.mp hmem).2
      rw [hsrc e List.mem_cons_self] at this
      cases this
  have hinit : SysState.init a env.left = { (a.boot.foldl (fun c i => c.startActor env (.inl i))
      c₀).thinLeft with outbox := [] ++ outbox' } :=
    (SysState.ext' rfl rfl (List.nil_append _).symm rfl rfl).trans heq
  refine ⟨(outbox'.filter fun out => !(w.toRight out).isNone).map .output, ?_, fun ev hev => ?_⟩
  · rw [hinit, SysState.run_outputs_filter _ _ _ [] outbox' (by simp), List.nil_append, ho']
    rfl
  · obtain ⟨out, hout, rfl⟩ := List.mem_map.mp hev
    exact ⟨rfl, shown_wired outbox' _ hev⟩

/-- The join starts, seen from `b` without the messages from outside, where `b` alone starts
once it has handed over the outputs the wiring routes to `a`. What the boot of `a` sent `b` is
from outside, so the view does not have it. -/
theorem init_thinRight (env : EnvModel (joinSig σ τ)) :
    ∃ evs, (SysState.init b env.right).run env.right evs
        = some (SysState.init (a.join b w) env).thinRight
      ∧ ∀ ev ∈ evs, ev.quiet = true ∧ w.shownRight ev = none := by
  have h₀ : (a.boot.foldl (fun c i => c.startActor env.swap (.inr i))
      (SysState.blank (b.join a w.swap))).thinLeft = SysState.blank b := by
    obtain ⟨xs, hxs⟩ := Seen.boot_inr (env := env.swap) a.boot (SysState.blank (b.join a w.swap))
    unfold thinLeft
    rw [hxs]
    refine SysState.ext' rfl rfl ?_ rfl rfl
    show List.filter _ ([] ++ _) = []
    rw [List.filter_eq_nil_iff]
    intro u hu
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp (by simpa using hu)
    simp
  obtain ⟨evs, hrun, hquiet⟩ := boot_thinLeft env.swap _ h₀
  rw [← init_swap, swap_thinLeft, EnvModel.swap_left] at hrun
  rw [Wiring.swap_shown] at hquiet
  exact ⟨evs, hrun, hquiet⟩

end SysState

end ThinnedRight

end Lanes
