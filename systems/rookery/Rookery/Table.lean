import Lanes

/-!
A table of records by name, as a list of pairs: the first pair with a name is that name's
record. The board keeps its accounts in one, at most `Config.maxAccounts` of them, so a lookup
is a walk of a bounded list and a proof is an induction on it.
-/

namespace Rookery

variable {N α : Type} [DecidableEq N]

def lookup (n : N) : List (N × α) → Option α
  | [] => none
  | (m, a) :: rest => if m = n then some a else lookup n rest

def modify (n : N) (f : α → α) (table : List (N × α)) : List (N × α) :=
  table.map fun (m, a) => (m, if m = n then f a else a)

end Rookery
