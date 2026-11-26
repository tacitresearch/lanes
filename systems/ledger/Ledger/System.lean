import Ledger.Spec

/-!
# The ledger as actors

One actor per user name, `user n`, holds that user's record: credential, failed attempts and
sessions. One actor, `ledger`, holds the book. A request goes to the user it names, which
decides it (`User.decide`) and tells the ledger: either the reply, or the operation to serve as
that user. The ledger answers every request.

That the ledger answers even what the user decided is what makes the system the spec: a user's
requests reach the ledger in the order the user decided them, so each takes effect, as the
spec has it, when the ledger handles it. A log-out answered by the user itself would return
while a transfer of the same session is still on its way, and a view asked after the log-out
could miss it; `Answering.fromUser` builds that system, and the checker finds the run
(`Check.lean`). The README says why the book is one actor.
-/

namespace Ledger

open Lanes

lanes_data inductive Id (N : Type) where
  | user (name : N)
  | ledger
  deriving DecidableEq, Repr, Hashable, Codable, Enum

lanes_data inductive UserMsg (C : Type) where
  | ask (req : ReqId) (question : Ask C)
  | unlock
  | expire (session : Sid)
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive LedgerMsg (N : Type) where
  | answer (req : ReqId) (reply : Reply N)
  /-- Sent only by `user owner` (`Ledger.Proofs`). -/
  | serve (req : ReqId) (owner : N) (op : Op)
  deriving DecidableEq, Repr, Hashable, Codable

abbrev Msg (N C : Type) : Id N → Type
  | .user _ => UserMsg C
  | .ledger => LedgerMsg N

instance {N C : Type} [DecidableEq N] [DecidableEq C] : ∀ i, DecidableEq (Msg N C i) := by
  instance_by_cases

abbrev sig (N C : Type) [DecidableEq N] [DecidableEq C] : Signature where
  Id := Id N
  Msg := Msg N C
  In := Request N C
  Out := Response N

/-- Who answers a request a user decided. Only `viaLedger` is the spec. -/
inductive Answering where
  | viaLedger
  | fromUser
  deriving DecidableEq, Repr

variable {N C : Type} [DecidableEq N] [DecidableEq C]

def timerEffects (config : Config N) (self : N) (timers : Timers) :
    List (Effect (sig N C) (.user self)) :=
  (if timers.locked then (config.lockout_ms.map fun d => .after d .unlock).toList else [])
    ++ (match config.session_ms, timers.opened with
      | some d, some session => [.after d (.expire session)]
      | _, _ => [])
    ++ timers.closed.map fun session => .cancel (.expire session)

def tell (answering : Answering) (self : N) (req : ReqId) :
    Verdict N → Effect (sig N C) (.user self)
  | .reply r =>
    match answering with
    | .viaLedger => .send .ledger (.answer req r)
    | .fromUser => .emit ⟨req, r⟩
  | .serve op => .send .ledger (.serve req self op)

/-- A user's timers are the spec's deadlines; the ledger has none. -/
def deadlines : Deadlines (sig N C) (Deadline N)
  | .user n, .unlock => some (.unlock n)
  | .user n, .expire session => some (.expire n session)
  | .user _, .ask .. => none
  | .ledger, _ => none

/-- A user's record survives a restart; its timers are armed again. -/
def rearm (config : Config N) (self : N) : Option (Profile C) → List (Effect (sig N C) (.user self))
  | none => []
  | some p =>
    timerEffects config self { locked := p.attempts.locked }
      ++ (match config.session_ms with
        | some d => p.sessions.ids.map fun session => .after d (.expire session)
        | none => [])

def user (config : Config N) (answering : Answering) (self : N) :
    (sig N C).Actor (.user self) (Option (Profile C)) where
  init := none
  step u
    | .ask req ask =>
      let (u, verdict, timers) := User.decide config self req u ask
      (u, tell answering self req verdict :: timerEffects config self timers)
    | .unlock => (User.unlock u, [])
    | .expire session => (User.expire session u, [])
  recover u := (u, rearm config self u)

def ledger (config : Config N) : (sig N C).Actor .ledger (Book N) where
  init := .empty
  step b
    | .answer req reply => (b, [.emit ⟨req, reply⟩])
    | .serve req owner op =>
      let (b, reply) := b.serve config owner req op
      (b, [.emit ⟨req, reply⟩])
  recover b := (b, [])

abbrev system (N C : Type) [DecidableEq N] [DecidableEq C] (config : Config N)
    (answering : Answering := .viaLedger) : System (sig N C) where
  State
    | .user _ => Option (Profile C)
    | .ledger => Book N
  actor
    | .user n => user config answering n
    | .ledger => ledger config
  accept r := ⟨.user r.name, .ask r.req r.ask⟩

end Ledger
