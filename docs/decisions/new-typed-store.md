# D?. The typed store: pure transactions over typed tables, at SERIALIZABLE

Status: Accepted

`docs/decisions/D110-volatile-actors.md` puts durable state in outside services with models,
PostgreSQL first, and says a request handler is pure and does one transaction at SERIALIZABLE,
retried automatically. This decision is that API (issue #242): the query subset and its meaning
in Lean, the type of a transaction and of a handler, the model, the theorems, and the driver.

## The query subset, with its meaning in Lean

A table (`Lanes/Db/Basic.lean`) has typed columns: 64-bit integers, bytes, text and booleans,
each nullable or not, a NULL being `Value.null`. Its primary key is its first `key` columns, and
it declares secondary indexes, unique or not. Key and index columns are never NULL
(`Table.valid`), so that NULL's place in an order and its three-valued equality never matter.

The operations (`Lanes/Db/Query.lean`):

- a row by primary key (`get`);
- a scan on the primary key or an index, with equality on its first columns, a range on the next,
  ascending or descending, with a limit (`scan`); a lookup by an index is a scan with equality on
  all its columns (`Txn.lookup`);
- an insert, update, upsert or delete of one row by primary key.

Each means a pure function of a database (`Op.apply`): a database is the rows of each table,
sorted by key, one per key. Out are SQL arithmetic, `LIKE`, floats, JSON, joins and ids the
engine assigns: that logic is written in Lean, where it is proved, and an id is chosen by the
transaction (`examples/todo-db` takes one more than the largest).

**Orders.** Integers by value, booleans `false` first, bytes byte by byte, and text byte by
byte: the driver creates text columns `COLLATE "C"`, so PostgreSQL's order is the one Lean's
`compare` on strings already is (by UTF-8 bytes). A scan orders by the index's columns and then
by the primary key, which makes the order total. PostgreSQL's text cannot hold `NUL`, so a text
value that does is not admitted.

**Writes never fail.** An insert whose key, or a unique value, is taken does nothing and answers
`false`; an update of a missing key, or onto a unique value another row has, likewise; an
upsert inserts or replaces unless a unique value is taken. So a transaction never fails for a
reason it could have read first, and the meaning has no error but an operation the schema does
not admit (a value of the wrong type, a limit past `Scan.limit_max`), which aborts the
transaction before anything is sent. The SQL checks unique indexes in the statement itself
(`ON CONFLICT DO NOTHING`, `NOT EXISTS`), in its snapshot.

## A transaction is a free monad; a handler is `Q → Txn A`

`Txn` (`Lanes/Db/Txn.lean`) is a free monad over the operations: `pure`, `abort`, and an
operation with its continuation. A handler is `Handler Q A := Q → Txn A`.

The alternative was a two-phase plan: the reads as data, then the writes as a function of what
they read. It cannot express a read that depends on an earlier read (look a row up by an index,
then read the row its value names), which the issue asks for, without growing into a free monad
by stages. The free monad has the shape of the code people write (`do` notation, `match` on what
a read gave), and its meaning is one recursion (`Txn.run`), so a proof takes a transaction apart
step by step (`Txn.run_bind`, `Txn.run_op_ok_inv`). Its cost: a transaction is a closure, not
data, so it cannot be sent as a message or compared. That is why a system's call carries the
request (`Q`, data) and the handler is a parameter of the adapter and of the model, not a value
in the message.

The type gives the two promises D110 asks for. A `Txn` is a value: running it has no effect
until the driver interprets it, and nothing in it can do IO. And a handler returns one `Txn`:
the driver brackets the whole of it in one `BEGIN … COMMIT`, so there is no way to write two
transactions in one request, or to do something between them.

`TableOf α` puts a Lean type on a table: rows encoded and decoded, with the law
`ofRow (toRow a) = some a`. A row that does not decode aborts the transaction (rule 3.1). #244
derives these for `lanes_data` types.

## The model

`Lanes/Db/Model.lean` is an `Outside`, so the checker explores an application against it and a
recorded run is checked with `Outside.allows` (`Db.State.run`). A system sends a call (an id and
a request); the reply is `committed a`, `failed`, or `unknown`. The model keeps every world the
answers so far allow, as the key-value store model does (`Lanes/Outside/Store/Basic.lean`):

- a call takes effect at one moment between its request and its reply, as one run of its
  handler's transaction on the database of that moment;
- a call answered failed never took effect (every attempt conflicted, the connection was lost
  before `COMMIT`, the handler aborted, or the server refused);
- a call answered unknown (a lost `COMMIT`) may have taken effect, or takes effect at any later
  moment, or never.

Taking effect inside the call's interval is an order that follows real time. The key-value
model also lets a transaction be ordered before one that committed while it ran, which a call
here covers: the two calls overlap. What it adds is that a transaction begun after another's
commit was answered comes after it, which PostgreSQL's snapshot gives, as long as the second
reads what the first wrote. It is tested on the recorded runs, three calls at once.

Serialization failures do not appear in the model: the driver retries them inside the call. The
theorem below says why that is invisible.

The key-value store model and `Lanes/Lib/Postgres/Table.lean` stay, for their tests and the
recorded runs of the protocol; nothing new is built on them.

## The theorems

`Lanes/Db/Sound.lean`, gated in `Tests/Axioms/Db.lean`:

- **`Db.invariant`.** For an invariant `I` of the database that the start satisfies and every
  transaction of the handler keeps (`Preserves h I`), every database the model allows after
  every run satisfies `I`, also once any call still outstanding or lost takes effect. Lost
  `COMMIT`s, failures and retries cannot break it: each world's database is the start with some
  transactions applied one after another.
- **`Retry.loop_committed`.** A call that committed after attempts that conflicted or lost their
  connection answers what one run of its transaction answers on the state it committed against,
  and leaves that run's state. It is about the driver's loop (`Retry.loop`, built on the
  `Retry.next` the IO follows), over what the server did with each attempt (`Served`).
- **`Txn.interp_apply`.** A transaction answered operation by operation with their meanings is
  `Txn.run`: the interpreter the driver is, run against a server that answers as serializable
  promises.

To prove `Preserves` for an application, the library gives what an operation leaves of its table
(`Op.rows_apply`, `Op.insert_rows`, `Op.update_rows`, `Op.delete_rows`), that a read changes
nothing (`Txn.Reads`), and that a lookup that found nothing means no row has those values
(`Scan.run_eq_nil`, `Scan.matches_lookup`). `examples/todo-db` proves that a user's to-dos are
unique by title, with no unique index saying so (`TodoDb.preserves`, `TodoDb.unique_always`).

## The driver

`Lanes/Lib/Postgres/Sql.lean`, pure: the SQL text and parameters of each operation, `CREATE
TABLE` and `CREATE INDEX` from the schema, the reading of a reply against the operation's table,
and what a reply means for an attempt (`classify`, `committed`). Values travel as text; each
reads back from the text it is sent as (`Postgres.Sql.decode_param`).

`Lanes/Lib/Postgres/IO/Db.lean`, trusted: each attempt on a connection of the pool, `BEGIN
ISOLATION LEVEL SERIALIZABLE`, one statement per operation, `COMMIT`, and `ROLLBACK` on an
attempt that ended otherwise. It tries again, up to `attempts_max` attempts, after:

- `40001` (serialization failure) and `40P01` (deadlock), the two the issue names;
- `23505` (unique violation): a write checks its unique indexes in its snapshot, so a violation
  means a transaction it could not see took the value first. PostgreSQL 16 does not always
  report that as `40001`; the oracle met it with three calls at once. Trying a pure transaction
  again is safe in every case; these are the cases where a new attempt can change the outcome;
- a connection lost, or not had, before `COMMIT` was sent.

A connection lost after `COMMIT` was sent is `unknown` and never retried: it may have committed.

## The oracle

`Tests/Oracle/Service/Db.lean`, a service oracle (D80) run by `oracles/postgres/run.sh` with the
key-value store's, nightly in `.github/workflows/services.yml`, and skipped where no PostgreSQL
is named by `LANES_POSTGRES`. Over two tables that use every column type, nullable columns, a
composite key, and a unique and a non-unique index, it runs generated transactions through the
driver: one call at a time, each answer compared with `Txn.run` on the database the earlier calls
left, a last call reading every row; and three calls at once, on the same few keys, checked
against the model. The runs are kept in `oracles/postgres/db.jsonl`, which `lake test` checks
against the model again.

## Not in this decision

Migrations checked against the typed schema (a test that the database after the SQL migrations
has exactly the declared tables and columns) and a SQLite driver behind the same API are later
work.
