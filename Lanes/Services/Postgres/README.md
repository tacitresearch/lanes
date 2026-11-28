# PostgreSQL

Status: **checked: model plus oracle**.

- **Client**: the frontend/backend protocol 3.0 in Lean (`docs/decisions/D68-postgres-protocol-in-lean.md`).
  Pure: the messages (`Message.lean`, `Bytes.lean`), the connection (`Conn.lean`), SCRAM
  (`Scram.lean`), libpq's connection strings, URIs and service file (`ConnInfo.lean`), libpq's
  settings, which source wins and what the client refuses (`Settings.lean`), the pool's policy (`Pool.lean`), the
  key-value store's SQL (`Table.lean`) and the typed store's (`Sql.lean`). IO, which only
  performs: `IO/Client.lean`, `IO/Pool.lean`, the typed store's driver `IO/Db.lean` (with
  `prepare`, which an application runs at its start: the migrations not yet run, once each, then
  its declared tables compared with the database's), the worker of a jobs table `IO/Worker.lean`,
  and `IO/Serve.lean`, which serves a system whose calls the driver runs.
- **Model**: two shapes of the core. The key-value store, `Lanes/Outside/Store/Basic.lean`, for
  `Postgres.Store.handler`; and the typed store, `Lanes/Db/Model.lean`, for
  `Postgres.Typed.handler`.
- **Oracle**: PostgreSQL itself. `oracles/postgres/run.sh` starts a PostgreSQL 16 of its own,
  runs the store's and the typed store's calls against it, checks the runs against the models
  and records them (`oracles/postgres/store.jsonl`, `oracles/postgres/db.jsonl`), which
  `lake test` checks again; CI runs it nightly. The messages and the connection are also tested
  against sessions recorded from PostgreSQL 16 and psql 16 (`Tests/Postgres.lean`). The
  connection strings and service files are compared with libpq 18 on generated ones
  (`oracles/libpq`, `Tests/Oracle/Libpq.lean`).

## Connecting

`Client.fromEnv conninfo` takes each option from the connection string (`keyword=value` pairs or
a `postgresql://` URI), else from the service it or `PGSERVICE` names, else from libpq's
variable, else from a deploy's (`LANES_DB_*`), else libpq's default (`Settings.read`). It takes
`host` (several, tried in order, with `target_session_attrs`), `port`, `dbname`, `user`,
`password`, `passfile`, `sslmode`, `sslrootcert`, `sslnegotiation`, `channel_binding`,
`application_name`, `fallback_application_name`, `connect_timeout` and `options`. Where it
differs from libpq, it is stricter:

- No TLS only to this machine; elsewhere `verify-full` unless asked. `require` checks the chain,
  as libpq's `verify-ca`; `allow` and `prefer`, which give TLS up, are refused.
- The authorities are `sslrootcert`, else `~/.postgresql/root.crt`, else the deploy's bundle
  (`/etc/lanes/db-ca.pem`, RDS's), else the system's. `sslrootcert=system` asks for
  `verify-full`, as libpq 16 does.
- A password file others may read, or that is not a plain file, is an error, where libpq warns
  and skips it. Its mode comes from `stat`.
- An option libpq knows that the client does not support (Unix sockets, client certificates,
  `hostaddr`, GSSAPI, `load_balance_hosts`, `require_auth`, replication) is refused by name;
  TCP keepalives, `gssencmode` short of `require`, `sslsni=1` and `client_encoding=UTF8` are
  taken and change nothing.
- `connect_timeout` of `0` or less is the client's own deadline, never none (rule 3.4).
