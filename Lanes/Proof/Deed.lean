/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Step
public import Lanes.Proof.List

/-!
# What a run shows a system doing

A `Deed` is what an event shows of the system itself: an actor handles a message, or an output
is handed over. Inputs, losses, crashes and starts are the environment's. Deeds are what a run
of a system put together keeps of a run of one of its parts (`SysState.run_left`), so a
statement that counts deeds is one a part can be proved to satisfy alone.

`System.handled_le_put` is the counting fact that needs the links: a kind of message that no
actor sends and no timer carries is handled no more often than it is put in from outside, when
the links it arrives on do not duplicate.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

inductive Deed (σ : Signature) where
  | handle (i : σ.Id) (msg : σ.Msg i)
  | output (out : σ.Out)

def Event.deed : Event σ → Option (Deed σ)
  | .deliver e | .duplicate e => some (.handle e.dst e.msg)
  | .timeout i msg => some (.handle i msg)
  | .output out => some (.output out)
  | .input _ | .drop _ | .crash _ | .start _ | .restart | .tick _ => none

def deeds (events : List (Event σ)) : List (Deed σ) :=
  events.filterMap Event.deed

/-- A kind of message, such as "a request with this id for the gate". -/
abbrev Kind (σ : Signature) : Type := (i : σ.Id) → σ.Msg i → Bool

def Deed.handles (p : Kind σ) : Deed σ → Bool
  | .handle i msg => p i msg
  | .output _ => false

/-- How often `events` show an actor handling a message of the kind `p`. -/
def handled (p : Kind σ) (events : List (Event σ)) : Nat :=
  (deeds events).countP (Deed.handles p)

/-- How often `events` put a message of the kind `p` in from outside. -/
def put (sys : System σ) (p : Kind σ) (events : List (Event σ)) : Nat :=
  events.countP fun
    | .input x => p (sys.accept x).1 (sys.accept x).2
    | _ => false

/-- Nothing in `effs` sends or arms a message of the kind `p`. -/
def Effect.Avoids (p : Kind σ) {i : σ.Id} (effs : List (Effect σ i)) : Prop :=
  (∀ to msg, .send to msg ∈ effs → p to msg = false)
    ∧ ∀ delay_ms msg, .after delay_ms msg ∈ effs → p i msg = false

/-- No actor of `sys` ever sends or arms a message of the kind `p`. -/
structure System.OnlyPut (sys : System σ) (p : Kind σ) : Prop where
  step : ∀ i ctx s msg, Effect.Avoids p ((sys.actor i).stepAt ctx s msg).2
  recover : ∀ i t s, Effect.Avoids p ((sys.actor i).recoverAt t s).2

end Lanes

end

public section

namespace Lanes

variable {σ : Signature} {sys : System σ} {env : EnvModel σ} {p : Kind σ}

/-- Handing an output over takes exactly that one output from those waiting. -/
theorem SysState.countP_outbox_of_output {c c' : SysState sys} {out : σ.Out} (q : σ.Out → Bool)
    (hstep : c.step env (.output out) = some c') :
    c'.outbox.countP q + (q out).toNat = c.outbox.countP q := by
  obtain ⟨hout, rfl⟩ := SysState.step_output.mp hstep
  exact countP_erase_add q hout

/-- At most `n` messages of the kind are in flight, each from outside, and none is a timer. -/
private structure Unsent (p : Kind σ) (n : Nat) (c : SysState sys) : Prop where
  atMost : c.net.countP (fun e => p e.dst e.msg) ≤ n
  fromOutside : ∀ e ∈ c.net, p e.dst e.msg = true → e.src = none
  noTimer : ∀ i, ∀ msg ∈ c.timers i, p i msg = false

namespace Unsent

variable {n : Nat} {c c' : SysState sys}

private theorem of_le (h : Unsent p n c) (hnet : c'.net.Sublist c.net)
    (htimers : ∀ i, ∀ msg ∈ c'.timers i, msg ∈ c.timers i) : Unsent p n c' where
  atMost := Nat.le_trans hnet.countP_le h.atMost
  fromOutside e he := h.fromOutside e (hnet.subset he)
  noTimer i msg hmsg := h.noTimer i msg (htimers i msg hmsg)

private theorem perform (h : Unsent p n c) {i : σ.Id} {effs : List (Effect σ i)}
    (havoids : Effect.Avoids p effs) {eff : Effect σ i} (heff : eff ∈ effs) :
    Unsent p n (c.perform i eff) := by
  cases eff with
  | send to msg =>
    have hp := havoids.1 to msg heff
    refine ⟨by simpa [SysState.perform, hp] using h.atMost, fun e he hpe => ?_, h.noTimer⟩
    rcases List.mem_append.mp he with he | he
    · exact h.fromOutside e he hpe
    · obtain rfl := List.mem_singleton.mp he
      simp [hp] at hpe
  | after delay_ms msg =>
    have hp := havoids.2 delay_ms msg heff
    refine ⟨h.atMost, h.fromOutside, fun j m hm => ?_⟩
    by_cases hj : j = i
    · subst hj
      simp only [SysState.perform, update_self] at hm
      split at hm
      · exact h.noTimer j m hm
      · rcases List.mem_append.mp hm with hm | hm
        · exact h.noTimer j m hm
        · exact List.mem_singleton.mp hm ▸ hp
    · exact h.noTimer j m (by simpa [SysState.perform, hj] using hm)
  | cancel msg =>
    refine h.of_le (List.Sublist.refl _) fun j m hm => ?_
    by_cases hj : j = i
    · subst hj
      exact List.mem_of_mem_erase (by simpa [SysState.perform] using hm)
    · simpa [SysState.perform, hj] using hm
  | emit out => exact h.of_le (List.Sublist.refl _) fun _ _ hm => hm
  | stop => exact h.of_le (List.Sublist.refl _) fun _ _ hm => hm

private theorem down (h : Unsent p n c) (i : σ.Id) : Unsent p n (c.down env i) := by
  refine h.of_le List.filter_sublist fun j m hm => ?_
  by_cases hj : j = i
  · subst hj
    simp [SysState.down] at hm
  · simpa [SysState.down, hj] using hm

private theorem settle (h : Unsent p n c) (i : σ.Id) {r : sys.State i × List (Effect σ i)}
    (havoids : Effect.Avoids p r.2) : Unsent p n (c.settle env i r) :=
  SysState.settle_induction (h.of_le (List.Sublist.refl _) fun _ _ hm => hm)
    (fun _ _ heff hc => hc.perform havoids heff) fun _ hc => hc.down i

private theorem start (h : Unsent p n c) (honly : sys.OnlyPut p) (i : σ.Id) :
    Unsent p n (c.startActor env i) :=
  settle (c := { c with up := update c.up i true })
    (h.of_le (List.Sublist.refl _) fun _ _ hm => hm) i (honly.recover i _ _)

private theorem erase (h : Unsent p n c) {e : Envelope σ} (he : e ∈ c.net) :
    ∃ m, m + (p e.dst e.msg).toNat = n ∧ Unsent p m { c with net := c.net.erase e } := by
  have hcount := countP_erase_add (fun e => p e.dst e.msg) he
  have hatMost := h.atMost
  exact ⟨n - (p e.dst e.msg).toNat, by omega, by simp only; omega,
    fun e' he' => h.fromOutside e' (List.mem_of_mem_erase he'), h.noTimer⟩

end Unsent

private theorem handled_snoc (p : Kind σ) (events : List (Event σ)) (ev : Event σ) :
    handled p (events ++ [ev]) = handled p events + match ev.deed with
      | some deed => (deed.handles p).toNat
      | none => 0 := by
  simp only [handled, deeds, List.filterMap_append, List.countP_append]
  cases h : ev.deed with
  | none => simp [h]
  | some deed => cases hp : deed.handles p <;> simp [h, hp]

private theorem put_snoc (p : Kind σ) (events : List (Event σ)) (ev : Event σ) :
    put sys p (events ++ [ev]) = put sys p events + match ev with
      | .input x => (p (sys.accept x).1 (sys.accept x).2).toNat
      | _ => 0 := by
  simp only [put, List.countP_append]
  cases ev <;> simp [List.countP_cons]
  split <;> simp_all

/-- A kind of message that only the outside sends is handled no more often than it is put in,
when the links it arrives on do not duplicate. Actors may crash, restart and stop, the process
may restart, and every link may lose and reorder. -/
theorem System.handled_le_put (honly : sys.OnlyPut p)
    (hlink : ∀ i msg, p i msg = true → (env.link none i).duplicating = false)
    {events : List (Event σ)} {c : SysState sys}
    (hrun : (SysState.init sys env).run env events = some c) :
    handled p events ≤ put sys p events := by
  suffices h : ∃ n, handled p events + n ≤ put sys p events ∧ Unsent p n c by
    obtain ⟨n, hle, -⟩ := h
    omega
  have hinit : Unsent p 0 (SysState.init sys env) :=
    SysState.init_induction
      ⟨by simp [SysState.blank], by simp [SysState.blank], by simp [SysState.blank]⟩
      fun c i h => h.start honly i
  refine System.Reachable.run_induction
    (P := fun events c => ∃ n, handled p events + n ≤ put sys p events ∧ Unsent p n c)
    .init hrun ⟨0, by simp [handled, deeds, put], hinit⟩ ?_
  rintro evs c₁ ev c₂ - ⟨n, hle, hunsent⟩ hstep
  rw [handled_snoc, put_snoc]
  cases ev with
  | input x =>
    obtain rfl := SysState.step_input.mp hstep
    refine ⟨n + (p (sys.accept x).1 (sys.accept x).2).toNat, by simp only [Event.deed]; omega,
      ?_, fun e he hpe => ?_, hunsent.noTimer⟩
    · have := hunsent.atMost
      cases hp : p (sys.accept x).1 (sys.accept x).2 <;> simp [hp] <;> omega
    · rcases List.mem_append.mp he with he | he
      · exact hunsent.fromOutside e he hpe
      · exact List.mem_singleton.mp he ▸ rfl
  | deliver e =>
    obtain ⟨_, hdeliverable, rfl⟩ := SysState.step_deliver.mp hstep
    obtain ⟨m, rfl, hm⟩ := hunsent.erase (SysState.mem_of_deliverable hdeliverable)
    exact ⟨m, by simp only [Event.deed, Deed.handles]; omega, hm.settle e.dst (honly.step ..)⟩
  | duplicate e =>
    obtain ⟨_, hduplicating, hdeliverable, rfl⟩ := SysState.step_duplicate.mp hstep
    have hp : p e.dst e.msg = false := by
      cases hp : p e.dst e.msg with
      | false => rfl
      | true =>
        rw [hunsent.fromOutside e (SysState.mem_of_deliverable hdeliverable) hp,
          hlink e.dst e.msg hp] at hduplicating
        cases hduplicating
    exact ⟨n, by simp only [Event.deed, Deed.handles, hp]; simpa using hle,
      hunsent.settle e.dst (honly.step ..)⟩
  | drop e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_drop.mp hstep
    exact ⟨n, by simpa [Event.deed] using hle,
      hunsent.of_le List.erase_sublist fun _ _ hm => hm⟩
  | timeout i msg =>
    obtain ⟨_, hmem, rfl⟩ := SysState.step_timeout.mp hstep
    have hp := hunsent.noTimer i msg hmem
    refine ⟨n, by simp only [Event.deed, Deed.handles, hp]; simpa using hle,
      Unsent.settle (c := { c₁ with timers := update c₁.timers i ((c₁.timers i).erase msg) })
        (hunsent.of_le (List.Sublist.refl _) fun j m hm => ?_) i (honly.step ..)⟩
    by_cases hj : j = i
    · subst hj
      exact List.mem_of_mem_erase (by simpa using hm)
    · simpa [hj] using hm
  | output out =>
    obtain ⟨_, rfl⟩ := SysState.step_output.mp hstep
    exact ⟨n, by simpa [Event.deed, Deed.handles] using hle,
      hunsent.of_le (List.Sublist.refl _) fun _ _ hm => hm⟩
  | crash i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_crash.mp hstep
    exact ⟨n, by simpa [Event.deed] using hle, hunsent.down i⟩
  | start i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
    exact ⟨n, by simpa [Event.deed] using hle, hunsent.start honly i⟩
  | restart =>
    obtain ⟨_, rfl⟩ := SysState.step_restart.mp hstep
    exact ⟨0, by simp only [Event.deed]; omega, hinit⟩
  | tick m =>
    obtain rfl := SysState.step_tick.mp hstep
    exact ⟨n, by simpa [Event.deed] using hle,
      hunsent.of_le (List.Sublist.refl _) fun _ _ hm => hm⟩

end Lanes
