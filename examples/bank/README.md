# bank

Accounts as actors that send each other credits: the source account debits itself and sends a
`credit` message, and the destination applies it. No state is shared, so money moves only as a
message in flight.

```bash
cd examples/bank
mkdir -p .lake && ln -s ../../../.lake/packages .lake/packages   # share the fetched dependencies
lake build      # the bank and its proofs
lake test       # the model checks, and the lost credit found
```

**The balances last only until the process restarts.** Every account is an actor, and an actor's
state is a cache of its process: a restart opens every account again at its opening balance.
This is not how to keep money. An application whose data must outlive the process keeps it in
PostgreSQL, one transaction per request: `examples/todo-db`, `examples/payments` and
`examples/rookery` do.

The bank stays in memory on purpose, because what it teaches is the actor model itself, which a
database example does not show: an invariant of each actor, proved once and lifted to every
system (`Bank.balance_nonneg`); an invariant of the whole system that counts the messages in
flight (`Bank.money_conserved`, and `Bank.money_conserved_restarts` across restarts, where every
account starts again together); and the checker finding the credit a lossy link drops. Within one
process, actors that send each other messages are the right tool for state that is a cache, a
session in progress or a coordination; the bank is the smallest example of that tool.

## The claims

| Claim | Where |
| --- | --- |
| No balance is ever negative | `Bank.balance_nonneg`, gated in `Bank/Proofs/Axioms.lean` |
| Money is conserved, counting credits in flight, for any number of accounts, in an environment that loses, duplicates and crashes nothing; also when the process restarts | `Bank.money_conserved`, `Bank.money_conserved_restarts` |
| Over links that lose messages, the checker finds the dropped credit | `Check.lean`, run by `lake test` |
