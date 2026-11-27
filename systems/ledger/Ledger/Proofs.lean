import Ledger.Proofs.Book
import Ledger.Proofs.Actors
import Ledger.Proofs.Refines
import Ledger.Proofs.Timed
import Ledger.Proofs.Axioms

/-!
# What is proved

For every configuration, every run and every environment model (loss, duplication, reordering,
crashes):

- the book conserves money in each currency, no account that may not go below zero does, the
  entries of every transfer sum to zero, and every balance is the sum of its account's entries
  (`book_invariant`). All of these are the properties the checker checks, as they are written
  there; each is a property of the ledger actor alone, because the book is one actor;
- a request reaches the ledger as user `n` only from the actor of user `n`
  (`serve_from_owner`), and the ledger's answer to user `n` shows only `n`'s accounts and the
  entries of `n`'s accounts, unless it is the administrator's audit (`serve_onlyOf`);
- no user has more than `maxSessions` sessions or more than `maxFailures` failed log-ins
  counted, and one with that many is locked (`user_bounded`).

All of it is about the ledger actor, the user actors and pure functions, with no theorem about
the whole system but the lifting lemmas of Lanes: that is what one actor for the book buys.

Without timers the system implements its spec (`implements`), for every configuration and
every environment in which each user's link to the ledger is ordered and does not duplicate
and no request reaches a user twice. With timers it implements its spec with its deadlines, a
lock lifting and a session ending as the ledger serves the user's notice of them
(`implements_timed`), where the links to the ledger also lose nothing and the ledger does not
crash.
-/
