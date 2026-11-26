import Ledger.System

/-!
What the user actors guarantee: the ledger is asked to serve user `n` only by `user n`, so a
user id never comes from a request; and no user holds more sessions or failures than the
configuration allows.
-/

namespace Ledger

open Lanes

variable {N C : Type} [DecidableEq N] [DecidableEq C]

theorem not_send_timerEffects (config : Config N) (self : N) (timers : Timers)
    {to : Id N} {m : Msg N C to} : Effect.send to m ∉ timerEffects (C := C) config self timers := by
  simp only [timerEffects, List.mem_append, List.mem_map, not_or]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · split
    · cases config.lockout_ms <;> simp
    · simp
  · split <;> simp
  · simp

theorem not_send_rearm (config : Config N) (self : N) (u : Option (Profile C))
    {to : Id N} {m : Msg N C to} : Effect.send to m ∉ rearm config self u := by
  cases u with
  | none => simp [rearm]
  | some p =>
    simp only [rearm, List.mem_append, not_or]
    refine ⟨not_send_timerEffects config self _, ?_⟩
    split <;> simp

/-- A user actor asks the ledger to serve only itself. -/
theorem serve_sent_by_owner (config : Config N) (answering : Answering) (i : Id N)
    (s : (system N C config answering).State i) (msg : Msg N C i) {req : ReqId} {owner : N}
    {op : Op} (h : Effect.send Id.ledger (LedgerMsg.serve req owner op)
      ∈ (((system N C config answering).actor i).step s msg).2) : i = .user owner := by
  cases i with
  | ledger =>
    cases msg <;> simp [system, ledger] at h
  | user n =>
    cases msg with
    | ask r q =>
      simp only [system, user, List.mem_cons] at h
      rcases h with h | h
      · generalize (User.decide config n r s q).2.1 = v at h
        cases v with
        | reply rep => cases answering <;> simp [tell] at h
        | serve op' =>
          simp only [tell, Effect.send.injEq, heq_eq_eq, LedgerMsg.serve.injEq] at h
          rw [h.2.2.1]
      · exact absurd h (not_send_timerEffects config n _)
    | unlock | expire => simp [system, user] at h

/-- Every request to serve user `owner` on its way to the ledger was sent by `user owner`, in
every state of every run under every environment model. -/
theorem serve_from_owner (config : Config N) (answering : Answering) (env : EnvModel (sig N C)) :
    (system N C config answering).Invariant env fun c =>
      ∀ src req owner op, (⟨src, Id.ledger, LedgerMsg.serve req owner op⟩ : Envelope (sig N C))
        ∈ c.net → src = some (Id.user owner) := by
  refine System.Monotone.invariant ?_ env
  refine
    { blank := by simp [SysState.blank]
      below := fun c c' h hbelow src req owner op hm => h src req owner op (hbelow.net _ hm)
      input := fun c x h src req owner op hm => ?_
      step := fun c i msg h _ src req owner op hm => ?_
      recover := fun c i h src req owner op hm => ?_ }
  · rcases List.mem_append.mp hm with hm | hm
    · exact h src req owner op hm
    · simp only [List.mem_singleton, Envelope.mk.injEq] at hm
      exact absurd hm.2.1 (by simp)
  · rcases SysState.mem_grow_net.mp hm with hm | ⟨hsrc, hsend⟩
    · exact h src req owner op hm
    · simp only at hsrc
      rw [hsrc, serve_sent_by_owner config answering i _ msg hsend]
  · rcases SysState.mem_grow_net.mp hm with hm | ⟨hsrc, hsend⟩
    · exact h src req owner op hm
    · exfalso
      cases i with
      | ledger => simp [system, ledger] at hsend
      | user n => exact not_send_rearm config n _ hsend

/-- A user has at most `maxSessions` sessions and `maxFailures` failures counted, and is locked
when it has that many. -/
def Bounded (config : Config N) (u : Option (Profile C)) : Prop :=
  ∀ p, u = some p → p.sessions.ids.length ≤ config.maxSessions
    ∧ Auth.Attempts.Bounded config.maxFailures p.attempts

omit [DecidableEq N] [DecidableEq C] in
theorem bounded_close {config : Config N} {p : Profile C} (h : Bounded config (some p))
    (session : Sid) : Bounded config (some { p with sessions := p.sessions.close session }) := by
  intro q hq
  cases hq
  obtain ⟨hs, ha⟩ := h p rfl
  exact ⟨Nat.le_trans (List.length_erase_le ..) hs, ha⟩

omit [DecidableEq N] in
theorem bounded_decide (config : Config N) (self : N) (req : ReqId) {u : Option (Profile C)}
    (h : Bounded config u) (ask : Ask C) : Bounded config (User.decide config self req u ask).1 := by
  cases u with
  | none =>
    cases ask with
    | signUp c =>
      intro p hp
      cases hp
      exact ⟨Nat.zero_le _, by simp [Auth.Attempts.Bounded, Auth.Attempts.none]; omega⟩
    | logIn | act => intro p hp; cases hp
  | some p =>
    cases ask with
    | signUp => exact h
    | logIn c =>
      simp only [User.decide, User.logIn]
      split
      · exact h
      · split
        · intro q hq
          cases hq
          exact ⟨Auth.Sessions.length_start_le .., Auth.Attempts.bounded_succeed ..⟩
        · intro q hq
          cases hq
          exact ⟨(h p rfl).1, Auth.Attempts.bounded_fail ..⟩
    | act session op =>
      simp only [User.decide]
      split
      · cases op with
        | logOut => exact bounded_close h session
        | _ => exact h
      · exact h

theorem user_bounded (config : Config N) (answering : Answering) (self : N) :
    (user (C := C) config answering self).Invariant (Bounded config) :=
  Actor.Inductive.invariant
    { init := fun _ hp => nomatch hp
      step := fun u msg h => by
        cases msg with
        | ask req q => exact bounded_decide config self req h q
        | unlock =>
          intro q hq
          cases u with
          | none => cases hq
          | some p =>
            cases hq
            exact ⟨(h p rfl).1, by simp [Auth.Attempts.Bounded, Auth.Attempts.unlock,
              Auth.Attempts.none]; omega⟩
        | expire session =>
          cases u with
          | none => intro q hq; cases hq
          | some p => exact bounded_close h session
      recover := fun _ h => h }

end Ledger
