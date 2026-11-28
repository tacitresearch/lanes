import Ledger.Book

/-!
# The spec

What the ledger is to its users, as if requests were handled one at a time: each name has at
most one user, a user logs in with a credential and gets a session, and with a live session asks
the book (`Ledger.Book`). `User.decide` is what one request does to one user's record, and the
spec is that, then `Book.serve`, in one atomic step.

The credential is a parameter: the system is checked with two credentials, a right one and a
wrong one, and deployed with password digests (`Lanes.Auth.Digest`), which the bridge derives
so that no password enters the system.

Time passes in it as deadlines (`Deadline`): a locked account's lock lifting, a live session
ending. Which are armed is read from the users' records, and each passes in the system as the
ledger serves a user's notice of it (`Ledger.delivered`). How long a lock or a session lasts is the system's
configuration, not the spec's. The safety properties are stated below and checked of every
state in `Check.lean`.
-/

namespace Ledger

open Lanes

lanes_data structure Profile (C : Type) where
  credential : C
  attempts : Auth.Attempts := {}
  sessions : Auth.Sessions := {}
  deriving DecidableEq, Repr, Hashable, Codable

/-- What a request asks of the user it names. -/
lanes_data inductive Ask (C : Type) where
  | signUp (credential : C)
  /-- `at_s` is when the request arrived, in seconds: the session's cookie is signed then. -/
  | logIn (credential : C) (at_s : Nat)
  | act (session : Sid) (op : Op)
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Request (N C : Type) where
  | signUp (req : ReqId) (name : N) (credential : C)
  | logIn (req : ReqId) (name : N) (credential : C) (at_s : Nat)
  /-- `name` and `session` are what the request's session cookie carried, verified by the
  bridge; nothing in the request's body names a user. -/
  | act (req : ReqId) (name : N) (session : Sid) (op : Op)
  deriving DecidableEq, Repr, Hashable, Codable

namespace Request

variable {N C : Type}

def req : Request N C → ReqId
  | .signUp req .. | .logIn req .. | .act req .. => req

def name : Request N C → N
  | .signUp _ name _ | .logIn _ name .. | .act _ name .. => name

def ask : Request N C → Ask C
  | .signUp _ _ c => .signUp c
  | .logIn _ _ c at_s => .logIn c at_s
  | .act _ _ session op => .act session op

end Request

/-- A user's decision: answer the request, or have the book serve it. -/
inductive Verdict (N : Type) where
  | reply (r : Reply N)
  | serve (op : Op)
  deriving DecidableEq, Repr

/-- The timers a decision starts and stops. -/
structure Timers where
  locked : Bool := false
  opened : Option Sid := none
  closed : List Sid := []

namespace User

variable {N C : Type} [DecidableEq C]

def logIn (config : Config N) (self : N) (req : ReqId) (p : Profile C) (c : C) (at_s : Nat) :
    Profile C × Reply N × Timers :=
  if p.attempts.locked then (p, .locked, {})
  else if c = p.credential then
    let (sessions, closed) := p.sessions.start config.maxSessions req
    ({ p with attempts := p.attempts.succeed, sessions }, .loggedIn self req at_s,
      { opened := some req, closed })
  else
    let attempts := p.attempts.fail config.maxFailures
    ({ p with attempts }, .refused, { locked := attempts.locked })

def act (p : Profile C) (session : Sid) : Op → Profile C × Verdict N × Timers
  | .logOut => ({ p with sessions := p.sessions.close session }, .reply .loggedOut,
      { closed := [session] })
  | op => (p, .serve op, {})

def decide (config : Config N) (self : N) (req : ReqId) :
    Option (Profile C) → Ask C → Option (Profile C) × Verdict N × Timers
  | none, .signUp c => (some { credential := c }, .reply .signedUp, {})
  | some p, .signUp _ => (some p, .reply .nameTaken, {})
  | none, .logIn .. => (none, .reply .refused, {})
  | some p, .logIn c at_s =>
    let (p, r, timers) := logIn config self req p c at_s
    (some p, .reply r, timers)
  | none, .act .. => (none, .reply .noSession, {})
  | some p, .act session op =>
    if p.sessions.live session then
      let (p, v, timers) := act p session op
      (some p, v, timers)
    else (some p, .reply .noSession, {})

def unlock : Option (Profile C) → Option (Profile C)
  | some p => some { p with attempts := Auth.Attempts.unlock }
  | none => none

def expire (session : Sid) : Option (Profile C) → Option (Profile C)
  | some p => some { p with sessions := p.sessions.close session }
  | none => none

end User

/-- A deadline of the spec: a lock lifting, a session ending. -/
inductive Deadline (N : Type) where
  | unlock (name : N)
  | expire (name : N) (session : Sid)
  deriving DecidableEq, Repr

structure SpecState (N C : Type) where
  users : N → Option (Profile C)
  book : Book N

instance {N C : Type} [Enum N] [DecidableEq C] [DecidableEq N] : BEq (SpecState N C) where
  beq a b := a.users == b.users && a.book == b.book

instance {N C : Type} [Enum N] [Hashable C] [Hashable N] : Hashable (SpecState N C) where
  hash s := mixHash (hash s.users) (hash s.book)

namespace SpecState

variable {N C : Type} [DecidableEq N] [DecidableEq C]

def init : SpecState N C := { users := fun _ => none, book := {} }

/-- One request, atomically: the user it names decides, and the book serves what the user lets
through. `Ledger.spec` is this as a `Service`. -/
def step (config : Config N) (st : SpecState N C) (r : Request N C) :
    SpecState N C × List (Response N) :=
  let (u, verdict, _) := User.decide config r.name r.req (st.users r.name) r.ask
  let users := update st.users r.name u
  match verdict with
  | .reply reply => ({ st with users }, [⟨r.req, reply⟩])
  | .serve op =>
    let (book, reply) := st.book.serve config r.name r.req op
    ({ users, book }, [⟨r.req, reply⟩])

/-- A lock is armed while the account is locked, a session's end while the session is live. -/
def armed (st : SpecState N C) : Deadline N → Bool
  | .unlock n => (st.users n).any (·.attempts.locked)
  | .expire n session => (st.users n).any (·.sessions.live session)

def fire (st : SpecState N C) : Deadline N → SpecState N C × List (Response N)
  | .unlock n => ({ st with users := update st.users n (User.unlock (st.users n)) }, [])
  | .expire n session =>
    ({ st with users := update st.users n (User.expire session (st.users n)) }, [])

end SpecState

def spec (N C : Type) [DecidableEq N] [DecidableEq C] (config : Config N) :
    Service (Request N C) (Response N) (SpecState N C) (Deadline N) where
  init := .init
  step := SpecState.step config
  armed := SpecState.armed
  fire := SpecState.fire

/-! ## Safety properties

Stated of the book, so they hold of the spec's state and of the ledger actor's. Each is checked
of every reachable state in `Check.lean` and proved for every run in `Ledger.Proofs`. -/

namespace Book

variable {N : Type} [DecidableEq N]

/-- Money is conserved: in each currency the balances sum to zero. -/
def conserved (b : Book N) (c : Currency) : Bool :=
  (b.accounts.map fun a => if a.currency = c then a.balance else 0).sum == 0

/-- No account below zero, unless it is allowed to be. -/
def noOverdraft (b : Book N) : Bool :=
  b.accounts.all fun a => a.allowsNegative || 0 ≤ a.balance

def transferSum (b : Book N) (t : ReqId) : Int :=
  ((b.entries.filter (·.transfer == t)).map (·.amount)).sum

/-- The entries of every transfer sum to zero. -/
def paired (b : Book N) : Bool :=
  b.entries.all fun e => b.transferSum e.transfer == 0

def accountSum (b : Book N) (k : AccountId) : Int :=
  ((b.entries.filter (·.account == k)).map (·.amount)).sum

/-- Every entry is of an account there is, and every balance is the sum of its account's
entries. -/
def cached (b : Book N) : Bool :=
  b.entries.all (·.account < b.accounts.length)
    && (List.range b.accounts.length).all fun k =>
      b.accounts[k]?.all fun a => a.balance == b.accountSum k

end Book

/-- A reply to `viewer` shows only `viewer`'s records: their own accounts, and the entries of
their own accounts. The audit, which only the administrator gets, is the exception. -/
def Reply.onlyOf {N : Type} [DecidableEq N] (b : Book N) (viewer : N) : Reply N → Bool
  | .accounts list => list.all fun (k, a) => a.owner == viewer && b.owns viewer k
  | .entries list => list.all fun e => b.owns viewer e.account
  | _ => true

end Ledger
