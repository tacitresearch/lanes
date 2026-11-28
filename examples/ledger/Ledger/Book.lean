import Lanes

/-!
# The book

The ledger's records and what one operation does to them, as pure functions: accounts, and the
entries of every transfer, two to a transfer, summing to zero. The spec (`Ledger.Spec`) and the
ledger actor (`Ledger.System`) both run these functions, so what the checker compares is how the
system is put together, and what holds of the records is proved once, here and in
`Ledger.Proofs`.

A balance is kept in its account so that a transfer does not sum the entries; that it is the sum
of the account's entries is an invariant (`Book.Cached`, rule 1.1).
-/

namespace Ledger

open Lanes

abbrev ReqId := Nat
abbrev AccountId := Nat
/-- A session is named by the id of the log-in request that opened it, which is never reused. -/
abbrev Sid := Nat

lanes_data inductive Currency where
  | eur | usd
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data structure Account (N : Type) where
  owner : N
  currency : Currency
  /-- Only the administrator's accounts may go below zero: they are where money comes from. -/
  allowsNegative : Bool
  balance : Int
  deriving DecidableEq, Repr, Hashable, Codable

/-- One leg of a transfer: what it did to `account`, and the account on the other side. -/
lanes_data structure Entry where
  transfer : ReqId
  account : AccountId
  counterparty : AccountId
  amount : Int
  deriving DecidableEq, Repr, Hashable, Codable

/-- An account's id is its place in `accounts`. Entries are newest first. -/
lanes_data structure Book (N : Type) where
  accounts : List (Account N) := []
  entries : List Entry := []
  deriving DecidableEq, Repr, Hashable, Codable

/-- Why a transfer was refused. -/
lanes_data inductive Problem where
  | notYours
  | noSuchAccount
  | sameAccount
  | currencies
  | nothing
  | insufficient
  deriving DecidableEq, Repr, Hashable, Codable

/-- What a user who is logged in may ask. -/
lanes_data inductive Op where
  | logOut
  | openAccount (currency : Currency) (allowsNegative : Bool)
  | transfer (src dst : AccountId) (amount : Nat)
  | accounts
  | entries
  | audit
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Reply (N : Type) where
  | signedUp
  | nameTaken
  /-- A session opened at `at_s`, when its cookie is signed. -/
  | loggedIn (name : N) (session : Sid) (at_s : Nat)
  /-- Wrong name or wrong password: which one is not said. -/
  | refused
  | locked
  | loggedOut
  | noSession
  | opened (account : AccountId)
  | tooManyAccounts
  | forbidden
  | transferred
  | invalid (problem : Problem)
  | accounts (list : List (AccountId × Account N))
  | entries (list : List Entry)
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data structure Response (N : Type) where
  req : ReqId
  reply : Reply N
  deriving DecidableEq, Repr, Hashable, Codable

/-- The settings both the spec and the system are built with. Every bound is here (rule 2.6). -/
structure Config (N : Type) where
  admin : N
  maxAccounts : Nat := 4
  maxSessions : Nat := 4
  maxFailures : Nat := 5
  /-- How long an account stays locked after `maxFailures` failed log-ins. With `none` it stays
  locked. -/
  lockout_ms : Option Nat := some 300000
  /-- How long a session lasts. With `none` it lasts until log-out or until it is the oldest of
  more than `maxSessions`. -/
  session_ms : Option Nat := some 86400000

namespace Book

variable {N : Type} [DecidableEq N]

def owns (b : Book N) (owner : N) (k : AccountId) : Bool :=
  b.accounts[k]?.any (·.owner == owner)

def accountsOf (b : Book N) (owner : N) : List (AccountId × Account N) :=
  b.accounts.zipIdx.filterMap fun (a, k) => if a.owner = owner then some (k, a) else none

def entriesOf (b : Book N) (owner : N) : List Entry :=
  b.entries.filter fun e => b.owns owner e.account

def openAccount (b : Book N) (owner : N) (currency : Currency) (allowsNegative : Bool) :
    Book N × AccountId :=
  ({ b with accounts := b.accounts ++ [⟨owner, currency, allowsNegative, 0⟩] }, b.accounts.length)

def debit (a : Account N) (amount : Nat) : Account N :=
  { a with balance := a.balance - amount }

def credit (a : Account N) (amount : Nat) : Account N :=
  { a with balance := a.balance + amount }

/-- The two accounts of a transfer, or why it is refused, in the order a user would want to
hear it. -/
def check (owner : N) (src dst : AccountId) (amount : Nat) :
    Option (Account N) → Option (Account N) → Except Problem (Account N × Account N)
  | none, _ => .error .notYours
  | some s, d =>
    if s.owner ≠ owner then .error .notYours
    else match d with
      | none => .error .noSuchAccount
      | some d =>
        if src = dst then .error .sameAccount
        else if s.currency ≠ d.currency then .error .currencies
        else if amount = 0 then .error .nothing
        else if !s.allowsNegative && s.balance < amount then .error .insufficient
        else .ok (s, d)

def transfer (b : Book N) (owner : N) (id : ReqId) (src dst : AccountId) (amount : Nat) :
    Book N × Reply N :=
  match check owner src dst amount b.accounts[src]? b.accounts[dst]? with
  | .error problem => (b, .invalid problem)
  | .ok (s, d) =>
    ({ accounts := (b.accounts.set src (debit s amount)).set dst (credit d amount)
       entries := ⟨id, dst, src, amount⟩ :: ⟨id, src, dst, -(amount : Int)⟩ :: b.entries },
      .transferred)

/-- What the ledger does for a user it has been told is logged in. -/
def serve (config : Config N) (b : Book N) (owner : N) (req : ReqId) : Op → Book N × Reply N
  | .logOut => (b, .loggedOut)
  | .openAccount currency allowsNegative =>
    if allowsNegative && owner ≠ config.admin then (b, .forbidden)
    else if (b.accountsOf owner).length ≥ config.maxAccounts then (b, .tooManyAccounts)
    else
      let (b, k) := b.openAccount owner currency allowsNegative
      (b, .opened k)
  | .transfer src dst amount => b.transfer owner req src dst amount
  | .accounts => (b, .accounts (b.accountsOf owner))
  | .entries => (b, .entries (b.entriesOf owner))
  | .audit => (b, if owner = config.admin then .entries b.entries else .forbidden)

end Book

end Ledger
