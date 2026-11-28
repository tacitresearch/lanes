### Bank

Where: `examples/bank/Bank.lean`.

Checked:

- A lost-credit bug found under lossy links.
- Conservation on 2 accounts.
- Runs on the runtime and over HTTP.

Proved:

- Balance never negative (all environments).
- Money conserved for any number of accounts in a faultless environment.
