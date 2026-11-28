# PostgreSQL

Status: **checked**.

- **Client**: the frontend/backend protocol 3.0 in Lean (`docs/decisions/D68-postgres-protocol-in-lean.md`).
  Pure: the messages (`Message.lean`, `Bytes.lean`), the connection (`Conn.lean`), SCRAM
  (`Scram.lean`), libpq's settings (`Settings.lean`), the pool's policy (`Pool.lean`), the
  key-value store's SQL (`Table.lean`) and the typed store's (`Sql.lean`). IO, which only
  performs: `IO/Client.lean`, `IO/Pool.lean` and the typed store's driver `IO/Db.lean`.
- **Model**: two shapes of the core. The key-value store, `Lanes/Outside/Store/Basic.lean`, for
  `Postgres.Store.handler`; and the typed store, `Lanes/Db/Model.lean`, for
  `Postgres.Typed.handler`.
- **Oracle**: PostgreSQL itself. `oracles/postgres/run.sh` starts a PostgreSQL 16 of its own,
  runs the store's and the typed store's calls against it, checks the runs against the models
  and records them (`oracles/postgres/store.jsonl`, `oracles/postgres/db.jsonl`), which
  `lake test` checks again; CI runs it nightly. The messages and the connection are also tested
  against sessions recorded from PostgreSQL 16 and psql 16 (`Tests/Postgres.lean`).
