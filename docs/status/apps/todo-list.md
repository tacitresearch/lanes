### To-do list

Where: `examples/todo-db/TodoDb.lean`.

Stores to-dos in PostgreSQL through the client's store adapter.

Checked:

- Checked against the store model at read committed and serializable with lost `COMMIT` answers and failures: appending and retrying a lost commit stores a to-do twice, which the checker finds, and the keyed insert never does.

Proved:

- The fixed actor inserts only the to-do being stored, under its user's key, after reading the key free, and no output of any run appends, replaces or deletes (`examples/todo-db/TodoDb/Proofs.lean`).

Known limits:

- That no to-do is stored twice is checked, for one and two to-dos, not proved: the proof covers the actor, and the rest rests on the table's primary key, a premise of the store model.
- The actor's state is volatile: a crash forgets the to-dos waiting.
