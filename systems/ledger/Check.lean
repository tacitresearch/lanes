import Ledger

/-!
# Model checks

Two users, `0` the administrator and `1`, two accounts each, with a right credential and a wrong
one. Each scenario is a list of requests, each sent once the requests it lists have been
answered, as a user who waits for a page does; the rest race. The monitor checks every
response, and every lock lifting and session ending, against the spec (`Ledger.spec`), and
every state is checked against the safety properties of `Ledger.Spec` and of the actors.

`ledgerCheck` prints each report and fails if one is not as expected. `ledgerCheck timed-crash`
runs the scenario with timers and a crash anywhere, which `lake test` leaves out for its size.
-/

namespace Ledger.Check

open Lanes

abbrev N := Fin 2
abbrev C := Fin 2

def right : C := 0
def wrong : C := 1

instance : ∀ i, Repr (Msg N C i) := by instance_by_cases
instance : ∀ i, Hashable (Msg N C i) := by instance_by_cases
instance : (sig N C).Inspect := {}
instance (config : Config N) (answering : Answering) : (system N C config answering).Inspect := by
  instance_by_cases

/-- A request and the requests whose answers it waits for. -/
abbrev Script := List (Request N C × List ReqId)

def clients (script : Script) : Driver (sig N C) (Waiting (Request N C)) :=
  Driver.after (fun out => some out.req) script

abbrev World' (config : Config N) (answering : Answering) :=
  World (system N C config answering)
    (Waiting (Request N C) × Check.Monitor (Request N C) (Response N) (SpecState N C))

def untimed : Config N :=
  { admin := 0, maxAccounts := 2, maxSessions := 2, maxFailures := 2, lockout_ms := none,
    session_ms := none }

/-- Who made each request of a script. -/
def viewer (script : Script) (req : ReqId) : Option N :=
  (script.find? (·.1.req == req)).map (·.1.name)

def isAudit (script : Script) (req : ReqId) : Bool :=
  script.any fun (x, _) => x.req == req && match x with
    | .act _ _ _ .audit => true
    | _ => false

section Properties

variable {config : Config N} {answering : Answering}

def book (w : World' config answering) : Book N := w.state.state .ledger

def profile (w : World' config answering) (n : N) : Option (Profile C) := w.state.state (.user n)

def props (config : Config N) (answering : Answering) (script : Script) :
    List (Check.Property (World' config answering)) :=
  [ Check.refines "every response is one the spec allows",
    .always "money is conserved in each currency" fun w =>
      (book w).conserved .eur && (book w).conserved .usd,
    .always "no account below zero unless it may be" fun w => (book w).noOverdraft,
    .always "the entries of each transfer sum to zero" fun w => (book w).paired,
    .always "each balance is the sum of its entries" fun w => (book w).cached,
    .always "a user sees only their own records" fun w =>
      w.state.outbox.all fun r =>
        isAudit script r.req || match viewer script r.req with
          | some n => r.reply.onlyOf (book w) n
          | none => false,
    .always "only user n asks the ledger to serve n" fun w =>
      w.state.net.all fun e => match e.dst, e.msg with
        | .ledger, .serve _ owner _ => e.src == some (.user owner)
        | _, _ => true,
    .always "sessions and failures stay within their bounds" fun w =>
      [0, 1].all fun n => (profile w n).all fun p =>
        p.sessions.ids.length ≤ config.maxSessions && p.attempts.failures ≤ config.maxFailures ]

end Properties

def check (config : Config N) (answering : Answering) (script : Script)
    (witnesses : List (Check.Property (World' config answering)))
    (env : EnvModel (sig N C) := {}) (maxCrashes : Nat := 0) :=
  Check.system (system N C config answering)
    { env, maxCrashes, driver := (spec N C config).monitored (clients script) deadlines }
    (props config answering script ++ witnesses)

/-- Links between actors that reorder: what several shards joined by TCP give. -/
def reordering : EnvModel (sig N C) where
  link src _ := if src.isSome then Link.unordered else Link.reliable

/-- Any actor may crash; it comes back with its state, as a shard does from its journal. -/
def crashing : EnvModel (sig N C) where
  mayCrash _ := true

/-- What `Ledger.implements` allows: requests lost and reordered on their way in, and any actor
crashing; the links from the users to the ledger are reliable. -/
def lossyIn : EnvModel (sig N C) where
  link src _ := if src.isSome then Link.reliable else { ordered := false, lossy := true }
  mayCrash _ := true

/-- Links from the users to the ledger that lose messages, which `Ledger.implements` does not
allow: the checker finds nothing, and the proof does not cover it. -/
def lossyToLedger : EnvModel (sig N C) where
  link src _ := if src.isSome then { lossy := true } else Link.reliable

def timed' : Config N :=
  { untimed with lockout_ms := some 1000, session_ms := some 1000 }

/-! ## Scenarios -/

def signUp (req : ReqId) (n : N) : Request N C := .signUp req n right
def logIn (req : ReqId) (n : N) (c : C := right) : Request N C := .logIn req n c
def act (req : ReqId) (n : N) (session : Sid) (op : Op) : Request N C := .act req n session op

/-- Both sign up and log in; the administrator opens an account that may go below zero and one
that may not; `1` opens one in each currency. -/
def setup : Script :=
  [ (signUp 1 0, []), (signUp 2 1, []), (logIn 3 0, [1]), (logIn 4 1, [2]),
    (act 5 0 3 (.openAccount .eur true), [3]), (act 6 0 3 (.openAccount .eur false), [5]),
    (act 7 1 4 (.openAccount .eur false), [6, 4]), (act 8 1 4 (.openAccount .usd false), [7]) ]

/-- The administrator pays `1`; then they pay each other at once, which the administrator can
afford only if `1`'s payment lands first; then `1` tries to pay across currencies, and both look
while the administrator reads the audit. -/
def transfers : Script :=
  setup ++
  [ (act 9 0 3 (.transfer 0 2 5), [8]),
    (act 10 1 4 (.transfer 2 1 3), [9]),
    (act 11 0 3 (.transfer 1 2 2), [9]),
    (act 12 1 4 (.transfer 2 3 1), [10, 11]),
    (act 13 1 4 .entries, [12]),
    (act 14 0 3 .audit, [12]) ]

/-- A transfer and a log-out of the same session race, and `1` looks once the log-out is
answered. -/
def logOutRace : Script :=
  setup ++
  [ (act 9 0 3 (.transfer 0 2 5), [8]),
    (act 10 0 3 .logOut, [8]),
    (act 11 1 4 .accounts, [10]) ]

/-- Two wrong credentials lock `1`'s account, which keeps the session it had; a third log-in of
the administrator evicts the oldest; a session is no key to another user, and `1` may neither
open an account that goes below zero nor see the audit. -/
def abuse : Script :=
  [ (signUp 1 0, []), (signUp 2 1, [1]), (logIn 3 1, [2]), (logIn 4 1 wrong, [3]),
    (logIn 5 1 wrong, [4]), (logIn 6 1, [5]), (logIn 7 0, [6]), (logIn 8 0, [7]),
    (logIn 9 0, [8]), (act 10 0 7 .accounts, [9]), (act 11 0 3 .accounts, [10]),
    (act 12 1 3 (.openAccount .eur true), [11]), (act 13 1 3 .audit, [11]), (signUp 14 0, [11]) ]

/-- The administrator pays `1` while `1` asks for its accounts, and `1`'s session may end at any
moment. -/
def expiryRace : Script :=
  setup ++ [(act 9 0 3 (.transfer 0 2 5), [8]), (act 10 1 4 .accounts, [8])]

def answered (w : World' config answering) (req : ReqId) (reply : Reply N) : Bool :=
  w.state.outbox.any fun r => r.req == req && r.reply == reply

def transfersWitnesses : List (Check.Property (World' untimed .viaLedger)) :=
  [ .sometimes "money reaches the other user" fun w => answered w 9 .transferred,
    .sometimes "both pay each other" fun w => answered w 10 .transferred && answered w 11 .transferred,
    .sometimes "a payment finds too little" fun w => answered w 11 (.invalid .insufficient),
    .sometimes "a payment across currencies is refused" fun w =>
      answered w 12 (.invalid .currencies),
    .sometimes "the audit sees six entries" fun w =>
      w.state.outbox.any fun r => r.req == 14 && match r.reply with
        | .entries list => list.length == 6
        | _ => false ]

def raceWitnesses (answering : Answering) : List (Check.Property (World' untimed answering)) :=
  [ .sometimes "the transfer lands before the log-out" fun w =>
      answered w 9 .transferred && answered w 10 .loggedOut,
    .sometimes "the log-out shuts the transfer out" fun w => answered w 9 .noSession ]

def abuseWitnesses : List (Check.Property (World' untimed .viaLedger)) :=
  [ .sometimes "two wrong credentials lock the account" fun w => answered w 6 .locked,
    .sometimes "the oldest session is gone" fun w => answered w 10 .noSession,
    .sometimes "a session is no key to another user" fun w => answered w 11 .noSession,
    .sometimes "only the administrator's accounts may go below zero" fun w =>
      answered w 12 .forbidden,
    .sometimes "only the administrator sees the audit" fun w => answered w 13 .forbidden,
    .sometimes "a name is taken once" fun w => answered w 14 .nameTaken ]

/-! ## The bridge, without a socket -/

namespace Bridge

open Ledger.Web Lanes.Http

def admin : Name := ⟨"admin", rfl⟩

def settings : Settings :=
  { key := .of "test key".toUTF8, password := { iterations := 2, pepper := "pepper".toUTF8 }
    origin := "http://127.0.0.1:8080", secure := false, admin }

def alice : Name := ⟨"alice", rfl⟩

def token : String := sessionToken settings alice 7

def post (path : String) (fields : List (String × String)) (cookie : Option String := some token) :
    Http.Request :=
  { method := .post, path := [path]
    headers := (cookie.map fun c => [("cookie", s!"{sessionCookie}={c}")]).getD []
    body := ("&".intercalate (fields.map fun (k, v) => s!"{k}={v}")).toUTF8 }

def csrf : String := Auth.formToken settings.key token

def same : Except Http.Response In → Except Http.Response In → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

def tests : List (String × Bool) :=
  let transfer := [("src", "1"), ("dst", "2"), ("amount", "5"), ("csrf", csrf)]
  [ ("bridge: a session's cookie makes an act of its user, whatever the form says",
      same (decode settings 9 (post "transfer" (transfer ++ [("name", "bob")])))
        (.ok (.act 9 alice 7 (.transfer 1 2 5)))),
    ("bridge: a cookie whose payload names another user does not verify",
      let forged := (Auth.tag settings.key "session" "7.alice") ++ ".7.bob"
      same (decode settings 9 (post "transfer" transfer forged)) (.error notLoggedIn)),
    ("bridge: a form token of another session is refused",
      same (decode settings 9 (post "transfer" ((transfer.take 3) ++
        [("csrf", Auth.formToken settings.key (sessionToken settings alice 8))])))
        (.error forbidden)),
    ("bridge: a password enters the system only as its digest",
      same (decode settings 9 (post "login" [("name", "alice"), ("password", "longenough")] none))
        (.ok (.logIn 9 alice (settings.password.digest "alice" "longenough")))),
    ("bridge: a short password is refused before it reaches the system",
      match decode settings 9 (post "signup" [("name", "alice"), ("password", "short")] none) with
      | .error r => r.status == 400
      | .ok _ => false) ]

end Bridge

def timedWitnesses : List (Check.Property (World' timed' .viaLedger)) :=
  [ .sometimes "a lock lifts" fun w => answered w 6 (.loggedIn 1 6),
    .sometimes "a lock holds" fun w => answered w 6 .locked,
    .sometimes "a session ends on its own" fun w => answered w 12 .noSession,
    .sometimes "a session lasts" fun w => answered w 12 .forbidden ]

/-- A user that decides a log-in as if the account were open: a lockout that does not lock,
though failures are counted and the lock's timer is armed. -/
def ignoreLock : UserMsg C → Option (Profile C) → Option (Profile C)
  | .ask _ (.logIn _), some p => some { p with attempts := { p.attempts with locked := false } }
  | _, u => u

abbrev leaky (config : Config N) : System (sig N C) where
  State
    | .user _ => Option (Profile C)
    | .ledger => Book N
  actor
    | .user n =>
      let honest := user config .viaLedger n
      { honest with step := fun u msg => honest.step (ignoreLock msg u) msg }
    | .ledger => ledger config
  accept r := ⟨.user r.name, .ask r.req r.ask⟩

instance (config : Config N) : (leaky config).Inspect := by instance_by_cases

def checkLeaky :=
  Check.system (leaky timed')
    { driver := (spec N C timed').monitored (clients abuse) deadlines }
    [Check.refines "every response is one the spec allows"]

def timed {sys : System (sig N C)} [sys.Inspect] {D : Type} (name : String)
    (ok : Check.Report (World sys D) (Event (sig N C)) → Bool)
    (report : Unit → Check.Report (World sys D) (Event (sig N C))) : IO Bool := do
  let start ← IO.monoMsNow
  let r := report ()
  let passed := ok r
  let ms := (← IO.monoMsNow) - start
  IO.println s!"== {name}: {if passed then "as expected" else "NOT AS EXPECTED"} ({ms} ms)"
  IO.println r.renderSystem
  (← IO.getStdout).flush
  return passed

def main (args : List String) : IO UInt32 := do
  let all := args.isEmpty
  let mut results := #[]
  if all || args.contains "race" then
    results := results.push (← timed "a log-out racing a transfer" (fun r => r.ok && r.complete)
      fun _ => check untimed .viaLedger logOutRace (raceWitnesses .viaLedger))
    results := results.push (← timed "the same, answered by the user: the checker finds the stale view"
      (fun r => match r.failure with
        | some (.violated "every response is one the spec allows" _) => true
        | _ => false)
      fun _ => check untimed .fromUser logOutRace (raceWitnesses .fromUser))
  if all || args.contains "abuse" then
    results := results.push (← timed "locks, evictions and refusals" (fun r => r.ok && r.complete)
      fun _ => check untimed .viaLedger abuse abuseWitnesses)
    results := results.push (← timed "with timers: sessions end and locks lift at any moment"
      (fun r => r.ok && r.complete)
      fun _ => check timed' .viaLedger abuse timedWitnesses)
    results := results.push (← timed "the same, with a lockout that does not lock"
      (fun r => match r.failure with
        | some (.violated "every response is one the spec allows" _) => true
        | _ => false)
      fun _ => checkLeaky)
    results := results.push (← timed
      "a session ending while a view is on its way: the view sees a payment asked after the end"
      (fun r => match r.failure with
        | some (.violated "every response is one the spec allows" _) => true
        | _ => false)
      fun _ => check timed' .viaLedger expiryRace [])
  if args.contains "timed-crash" then
    results := results.push (← timed "with timers and a crash anywhere"
      (fun r => r.ok && r.complete)
      fun _ => check timed' .viaLedger abuse [] crashing 1)
  if all || args.contains "faults" then
    results := results.push (← timed "a log-out racing a transfer, with links that reorder"
      (fun r => match r.failure with
        | some (.violated "every response is one the spec allows" _) => true
        | _ => false)
      fun _ => check untimed .viaLedger logOutRace (raceWitnesses .viaLedger) reordering)
    results := results.push (← timed "a log-out racing a transfer, with a crash anywhere"
      (fun r => r.ok && r.complete)
      fun _ => check untimed .viaLedger logOutRace [] crashing 1)
    results := results.push (← timed
      "a log-out racing a transfer, with requests lost and reordered and a crash anywhere"
      (fun r => r.ok && r.complete)
      fun _ => check untimed .viaLedger logOutRace (raceWitnesses .viaLedger) lossyIn 1)
    results := results.push (← timed "transfers between two users, with links to the ledger that lose"
      (fun r => r.ok && r.complete)
      fun _ => check untimed .viaLedger transfers [] lossyToLedger)
  if all || args.contains "bridge" then
    for (name, ok) in Bridge.tests do
      IO.println s!"== {name}: {if ok then "as expected" else "NOT AS EXPECTED"}"
      results := results.push ok
  if all || args.contains "transfers" then
    results := results.push (← timed "transfers between two users" (fun r => r.ok && r.complete)
      fun _ => check untimed .viaLedger transfers transfersWitnesses)
    results := results.push (← timed "transfers between two users, with a crash anywhere"
      (fun r => r.ok && r.complete)
      fun _ => check untimed .viaLedger transfers [] crashing 1)
  return if results.all id then 0 else 1

end Ledger.Check

def main (args : List String) : IO UInt32 := Ledger.Check.main args
