import Lanes.Semantics
import Rookery.System
import Rookery.Proofs.Limits

/-!
# The system is its spec

What is proved of `Board.handle` and `Board.fire` is proved of what runs:

- `board_invariant`: every board the actor reaches, in every run of the system under every
  environment model, is within the bounds of `Config`, has fresh ids, and its memo remembers no
  read and no secret;
- `implements`: the system implements its spec with deadlines, for every configuration and every
  environment in which the link from the outside to the board does not hand a request over twice
  and the process does not restart: requests may be lost and reordered, the board may crash any
  number of times, and its timers are the spec's deadlines passing. A restart puts the board back
  at its initial state while the spec keeps its value, so it is not allowed; the bounds of
  `board_invariant` hold across restarts all the same.

The relation is the plainest there is: the spec's value is the board's state, the spec still has
pending every request on its way to the board, and still owes every response not yet handed
over. A request takes effect when the board handles it; a timer that fires is its deadline
passing, which is always armed in the spec; a crash keeps the state and loses timers, which the
relation does not read.
-/

set_option linter.unusedSectionVars false

namespace Rookery

open Lanes

variable {N C : Type} [DecidableEq N] [DecidableEq C]

/-- The board's own effects are timers: armed for a deadline, or cancelled. -/
def IsTimer (e : Lanes.Effect (sig N C) ()) : Prop :=
  (∃ delay d, e = .after delay (.deadline d)) ∨ ∃ d, e = .cancel (.deadline d)

theorem isTimer_timerEffects (config : Config) (n : N) (timers : Timers) :
    ∀ e ∈ (timerEffects config n timers : List (Effect (sig N C) ())), IsTimer e := by
  intro e he
  simp only [timerEffects, List.mem_append, List.mem_map] at he
  rcases he with ((he | he) | he) | ⟨s, _, rfl⟩
  · split at he
    · simp only [List.mem_singleton] at he; exact .inl ⟨_, _, he⟩
    · cases he
  · split at he
    · cases hl : config.lockout_ms with
      | none => simp [hl] at he
      | some d => simp only [hl, Option.map_some, Option.toList_some, List.mem_singleton] at he
                  exact .inl ⟨_, _, he⟩
    · cases he
  · split at he
    · simp only [List.mem_singleton] at he; exact .inl ⟨_, _, he⟩
    · cases he
  · exact .inr ⟨_, rfl⟩

theorem isTimer_rearm (config : Config) (b : Board N C) :
    ∀ e ∈ (rearm config b : List (Effect (sig N C) ())), IsTimer e := by
  intro e he
  simp only [rearm, List.mem_flatMap] at he
  obtain ⟨⟨n, p⟩, _, he⟩ := he
  simp only [rearmOne, List.mem_append] at he
  rcases he with he | he
  · exact isTimer_timerEffects config n _ e he
  · split at he
    · obtain ⟨s, _, rfl⟩ := List.mem_map.mp he
      exact .inl ⟨_, _, rfl⟩
    · cases he

theorem sends_of_timers {effs : List (Effect (sig N C) ())} (h : ∀ e ∈ effs, IsTimer e) :
    Effect.sends (σ := sig N C) () effs = [] := by
  refine List.filterMap_eq_nil_iff.mpr fun e he => ?_
  rcases h e he with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> rfl

theorem emits_of_timers {effs : List (Effect (sig N C) ())} (h : ∀ e ∈ effs, IsTimer e) :
    Effect.emits effs = [] := by
  refine List.filterMap_eq_nil_iff.mpr fun e he => ?_
  rcases h e he with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> rfl

variable (config : Config)

theorem board_step_request (b : Board N C) (r : Request N C) :
    (board config).step b (.request r) = ((b.handle config r).1,
      .emit ⟨r.req, (b.handle config r).2.1, r.json⟩ :: timerEffects config r.name (b.handle config r).2.2) :=
  rfl

theorem step_request (b : Board N C) (r : Request N C) :
    Effect.sends (σ := sig N C) () ((board config).step b (.request r)).2 = [] ∧
      Effect.emits ((board config).step b (.request r)).2 = [⟨r.req, (b.handle config r).2.1, r.json⟩] := by
  have ht := isTimer_timerEffects (C := C) config r.name (b.handle config r).2.2
  have hs := sends_of_timers ht
  have he := emits_of_timers ht
  rw [board_step_request]
  simp only [Effect.sends, Effect.emits, List.filterMap_cons] at hs he ⊢
  exact ⟨hs, by rw [he]⟩

/-- Every timer the board arms is a deadline. -/
theorem armed_deadline {i : Unit} {msg : (sig N C).Msg i} (h : (system N C config).Armed i msg) :
    ∃ d, msg = .deadline d := by
  have of_timer : ∀ {effs : List (Effect (sig N C) ())}, (∀ e ∈ effs, IsTimer e) →
      ∀ {delay}, Effect.after delay msg ∈ effs → ∃ d, msg = .deadline d := by
    intro effs h delay he
    rcases h _ he with ⟨_, d, he'⟩ | ⟨_, he'⟩
    · cases he'; exact ⟨d, rfl⟩
    · cases he'
  cases h with
  | step s m he =>
    cases m with
    | request r =>
      simp only [system, board, List.mem_cons, reduceCtorEq, false_or] at he
      exact of_timer (isTimer_timerEffects config r.name _) he
    | deadline d => simp [system, board] at he
  | recover s he => exact of_timer (isTimer_rearm config s) he

/-- Every message on its way to the board is a request from the outside. -/
theorem sent_request {e : Envelope (sig N C)} (h : (system N C config).Sent e) :
    ∃ r, e = ⟨none, (), .request r⟩ := by
  cases h with
  | accept r => exact ⟨r, rfl⟩
  | step s m he =>
    cases m with
    | request r => rw [(step_request config s r).1] at he; cases he
    | deadline d => simp [system, board, Effect.sends] at he
  | recover s he =>
    rw [show (((system N C config).actor ()).recover s).2 = rearm config s from rfl,
      sends_of_timers (isTimer_rearm config s)] at he
    cases he

/-! ## The board's invariant -/

/-- Within the bounds, with fresh ids, and a memo that remembers no read and no secret. -/
def Sound (b : Board N C) : Prop :=
  b.Bounded config ∧ b.Fresh ∧ b.Quiet

theorem board_inductive :
    (board (N := N) (C := C) config).Inductive (Sound (N := N) (C := C) config) where
  init := ⟨Board.bounded_init config, Board.fresh_init, Board.quiet_init⟩
  step b msg h := by
    cases msg with
    | request r => exact ⟨h.1.handle config r, h.2.1.handle config r, h.2.2.handle config r⟩
    | deadline d => exact ⟨h.1.fire config d, h.2.1.fire d, h.2.2.fire d⟩
  recover _ h := h

/-- In every state of every run, under every environment model, the board is sound. -/
theorem board_invariant (env : EnvModel (sig N C)) :
    (system N C config).Invariant env fun c => Sound config (c.state ()) :=
  System.invariant_of_actor (system N C config) () (board_inductive config).invariant env

/-! ## Refinement -/

def requests (net : List (Envelope (sig N C))) : List (Request N C) :=
  net.filterMap fun e => match e.msg with
    | .request r => some r
    | .deadline _ => none

/-- The spec's value is the board, it has pending every request in flight and owes every
response waiting. -/
def Rel (c : SysState (system N C config))
    (t : Service.Abs (Request N C) (Response N) (Board N C)) : Prop :=
  t.value = c.state () ∧ (↑(requests c.net) : Bag (Request N C)) ≤ t.pending ∧
    (↑c.outbox : Bag (Response N)) ≤ t.outbox

theorem requests_le_of_sublist {l l' : List (Envelope (sig N C))} (h : l'.Sublist l) :
    (↑(requests l') : Bag (Request N C)) ≤ ↑(requests l) :=
  Bag.coe_le_coe_of_sublist (h.filterMap _)

/-- The system implements its spec, deadlines and all, in every environment whose link from the
outside to the board does not duplicate and where the process does not restart. -/
theorem implements (env : EnvModel (sig N C)) (henv : (env.link none ()).duplicating = false)
    (hrestart : env.mayRestart = false) :
    (system N C config).Implements env (spec N C config) deadlines := by
  refine System.Refines.of_events (System.traced _ env) (Rel config) ⟨_, rfl, ?_⟩
    (fun c t _ _ h _ => h) ?input ?output ?deliver ?duplicate ?drop ?down ?timeout ?recover
    (fun h => absurd h (by simp [hrestart]))
  · exact ⟨rfl, by simp [requests, SysState.init, SysState.blank],
      by simp [SysState.init, SysState.blank]⟩
  case input =>
    rintro c t x - ⟨hv, hp, ho⟩
    refine ⟨{ t with pending := x ::ₘ t.pending }, .single rfl, hv, ?_, ho⟩
    simp only [requests, filterMap_concat, Option.toList_some, ← Bag.coe_add]
    rw [Bag.add_comm, Bag.coe_singleton, Bag.singleton_add]
    exact Bag.cons_le_cons x hp
  case output =>
    rintro c t out - ⟨hv, hp, ho⟩ hmem
    have hin : out ∈ (↑c.outbox : Bag (Response N)) := Bag.mem_coe.mpr hmem
    refine ⟨{ t with outbox := t.outbox.erase out }, .single ⟨Bag.mem_of_le ho hin, rfl⟩,
      hv, hp, ?_⟩
    rw [← Bag.coe_erase]
    exact Bag.erase_le_erase out ho
  case deliver =>
    rintro c t e hc ⟨hv, hp, ho⟩ hd
    have he := SysState.mem_of_deliverable hd
    obtain ⟨r, rfl⟩ := sent_request config (hc.net _ he)
    have hpend : r ∈ t.pending := by
      refine Bag.mem_of_le hp (Bag.mem_coe.mpr ?_)
      exact List.mem_filterMap.mpr ⟨_, he, rfl⟩
    refine ⟨_, .single ⟨r, hpend, rfl⟩, ?_, ?_, ?_⟩
    · simp [SysState.grow, hv, spec, system, board]
    · have hs := (step_request config (c.state ()) r).1
      simp only [SysState.grow, system] at hs ⊢
      rw [hs, List.append_nil]
      have hperm := Bag.coe_eq_coe.mpr
        (filterMap_perm_erase (f := fun e : Envelope (sig N C) => match e.msg with
          | .request r => some r
          | .deadline _ => none) he)
      have : (↑(requests c.net) : Bag (Request N C)) = r ::ₘ ↑(requests (c.net.erase ⟨none, (), .request r⟩)) := by
        simpa [requests] using hperm
      rw [this] at hp
      have := Bag.erase_le_erase r hp
      simpa using this
    · have hs := (step_request config (c.state ()) r).2
      simp only [SysState.grow, system] at hs ⊢
      rw [hs, ← Bag.coe_add, hv]
      exact Bag.add_le_add ho (Bag.le_of_eq rfl)
  case duplicate =>
    rintro c t e hc - hd hdup
    obtain ⟨r, rfl⟩ := sent_request config (hc.net _ (SysState.mem_of_deliverable hd))
    simp [henv] at hdup
  case drop =>
    rintro c t e - ⟨hv, hp, ho⟩ - -
    exact ⟨t, .refl, hv, (requests_le_of_sublist List.erase_sublist).trans hp, ho⟩
  case down =>
    rintro c t i ⟨hv, hp, ho⟩ -
    exact ⟨t, .refl, hv, (requests_le_of_sublist List.filter_sublist).trans hp, ho⟩
  case timeout =>
    rintro c t i msg hc ⟨hv, hp, ho⟩ hmem
    obtain ⟨d, rfl⟩ := armed_deadline config (hc.timers () _ hmem)
    refine ⟨⟨t.value.fire d, t.pending, t.outbox + 0⟩, .single ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · simp [SysState.grow, hv, system, board]
    · simpa [SysState.grow, system, board, Effect.sends] using hp
    · simpa [SysState.grow, system, board, Effect.emits] using ho
  case recover =>
    rintro c t i - ⟨hv, hp, ho⟩
    have ht := isTimer_rearm config (c.state ())
    refine ⟨t, .refl, ?_, ?_, ?_⟩
    · simp [SysState.grow, hv, system, board]
    · simp only [SysState.grow, system, board]
      rw [sends_of_timers ht, List.append_nil]
      exact hp
    · simp only [SysState.grow, system, board]
      rw [emits_of_timers ht, List.append_nil]
      exact ho

end Rookery
