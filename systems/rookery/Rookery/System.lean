import Rookery.Spec

/-!
# Rookery as actors

One actor, `board`, holds the whole `Board` and runs the spec's own functions: a request is
`Board.handle`, a deadline passing is `Board.fire`. What the actor adds is time: it arms a timer
for each deadline a request starts (`timerEffects`), cancels the timer of a session that ends,
and as it recovers from a crash arms again the timers its state needs (`rearm`). A timer that
fires is the spec's deadline passing (`deadlines`).

Why one actor, and not one per account, per post or per timeline, is in the README: every
claim of the spec is about one atomic owner, and every deadline passes where the requests it
bears on are served.
-/

namespace Rookery

open Lanes

lanes_data inductive Msg (N C : Type) where
  | request (r : Request N C)
  | deadline (d : Deadline N)
  deriving DecidableEq, Repr, Hashable, Codable

abbrev sig (N C : Type) [DecidableEq N] [DecidableEq C] : Signature where
  Id := Unit
  Msg _ := Msg N C
  In := Request N C
  Out := Response N

variable {N C : Type} [DecidableEq N] [DecidableEq C]

def timerEffects (config : Config) (n : N) (timers : Timers) : List (Effect (sig N C) ()) :=
  (if timers.window then [.after config.window_ms (.deadline (.window n))] else [])
    ++ (if timers.locked then
        (config.lockout_ms.map fun d => .after d (.deadline (.unlock n))).toList
      else [])
    ++ (match config.session_ms, timers.opened with
      | some d, some session => [.after d (.deadline (.expire n session))]
      | _, _ => [])
    ++ timers.closed.map fun session => .cancel (.deadline (.expire n session))

/-- The timers an account's record needs: its window, its lock and its sessions. A crash loses
timers, so this is armed again at every start, with each delay in full: a window or a session
that spans a crash lasts longer, never shorter. -/
def rearmOne (config : Config) (n : N) (p : Profile N C) : List (Effect (sig N C) ()) :=
  timerEffects config n { window := p.window != 0, locked := p.attempts.locked }
    ++ (match config.session_ms with
      | some d => p.sessions.ids.map fun session => .after d (.deadline (.expire n session))
      | none => [])

def rearm (config : Config) (b : Board N C) : List (Effect (sig N C) ()) :=
  b.accounts.flatMap fun (n, p) => rearmOne config n p

def board (config : Config) : (sig N C).Actor () (Board N C) where
  init := {}
  step b
    | .request r =>
      let (b', reply, timers) := b.handle config r
      (b', .emit ⟨r.req, reply⟩ :: timerEffects config r.name timers)
    | .deadline d => (b.fire d, [])
  recover b := (b, rearm config b)

abbrev system (N C : Type) [DecidableEq N] [DecidableEq C] (config : Config) :
    System (sig N C) where
  State _ := Board N C
  actor _ := board config
  accept r := ⟨(), .request r⟩

/-- The board's timers are the spec's deadlines. -/
def deadlines : Deadlines (sig N C) (Deadline N)
  | (), .deadline d => some d
  | (), .request _ => none

end Rookery
