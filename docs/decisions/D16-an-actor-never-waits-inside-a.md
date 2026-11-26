# D16. An actor never waits inside a step

A send whose receiver's mailbox is full goes to the sender's outbox, and a separate task delivers
the outbox in order. Inputs from outside are where back-pressure applies: `Runtime.input` waits
and `Runtime.tryInput` refuses, which the HTTP adapter turns into `503`.

Why: waiting inside a step deadlocks as soon as an actor sends to its own full mailbox, or two
actors fill each other's. The semantics has no bound on messages in flight, so losing or
refusing a send between actors would break conformance; refusing at the boundary does not.
The cost is that the outbox is unbounded, which is stated in `TRUSTED.md`.
