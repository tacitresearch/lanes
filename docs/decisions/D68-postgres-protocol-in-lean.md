# D68. PostgreSQL is spoken in Lean, and a transactional store is a model

Status: Partly superseded by D111-typed-store.md (the store model: typed tables, keys and scans replace the key-value model for new code)

Applications keep their state as actor state with a journal, and that stays the default. Some
must share a database with other programs, or want SQL and its indexes. This decision is how a
Lanes system talks to PostgreSQL, and what a theorem about such a system may assume of it.

## The protocol in Lean, not libpq

The frontend/backend protocol, version 3.0, is a byte format and a state machine over one TCP
connection: messages framed by a type byte and a length, a start-up with authentication, then
queries answered in order, each ended by `ReadyForQuery` and the state of the transaction. That
is the shape of HTTP/1.1, which Lanes already reads and writes in Lean and proves
(`docs/decisions/D49-the-server-reads-requests-by-a-strict-profile.md`,
`docs/decisions/D57-the-server-runs-its-own-connections.md`). Rule 2.7 (D46) says to write in
Lean what decides and bind only what touches physics. libpq decides a great deal: how replies
are matched to queries, what a lost connection means for a transaction in flight, when a
password is sent and to whom. Binding it would put some 40,000 lines of C in the trusted count,
make each of those decisions the C's, and hide them from the checker. What touches physics here
is the socket, which `Std.Net` already gives, and timing, which matters only for comparing the
server's SCRAM signature, which libsodium's comparison does (`Bytes.same`).

So the protocol is pure Lean in `Lanes/Lib/Postgres/`: messages as data with encoders and
decoders proved to be inverses, and one connection as a pure function `Postgres.Conn.step`, as
`Http.Conn.step` is for a connection of the HTTP server. A trusted IO file opens the socket,
feeds the bytes to `step` and performs what it answers (rule 3.9).

## Where it goes

`Lanes/Lib/Postgres/`, beside the other formats of the standard library, and not under
`integrations/` as `docs/decisions/D61-models-of-external-systems.md` places vendors. The wire
protocol is not one vendor's: CockroachDB, YugabyteDB, Neon, Aurora, AlloyDB, Materialize and
others speak it, as many servers speak HTTP. What is a vendor's is the claim that a given server
behaves like the store model at an isolation level, and that claim is a premise, not code. The
model of the class is in `Lanes/Outside/Store/`, where D61 puts models of external systems. The
owner may still prefer the client in an `integrations/postgres` (removed) package; nothing in `Lanes/`
imports it but its tests.

## In scope now

- **Start-up and authentication**: the start-up message with `user`, `database` and
  `client_encoding=UTF8`; trust; cleartext passwords, only when the configuration allows them;
  MD5; SCRAM-SHA-256 (RFC 5802, RFC 7677) without channel binding. SCRAM needs SHA-256 and
  HMAC-SHA-256, which libsodium gives (`Lanes/Lib/Crypto/Sodium.lean`), and PBKDF2-HMAC-SHA-256,
  which libsodium does not have: it is written in Lean over the bound HMAC
  (`Lanes.Lib.Crypto.Pbkdf2`), and MD5 in Lean (`Lanes.Lib.Crypto.Md5`), both tested against
  their RFCs' vectors. D46 removed a PBKDF2 used to digest passwords; this one is not for
  digesting, and passwords stay Argon2id. The connection accepts the server's `AuthenticationOk`
  after SCRAM only once the server has proved it knows the password (its signature, compared by
  `Bytes.same`), so a server cannot skip the exchange. The SCRAM nonce is random bytes the IO
  file draws and passes in, so the state machine stays a function.
- **Plain TCP** to an IPv4 address, as the HTTP client does.
- **The extended query protocol** with parameters, text format in both directions: `Parse`,
  `Bind`, `Describe`, `Execute`, `Sync`, with unnamed statements and portals; and the simple
  query protocol for `BEGIN`, `COMMIT` and `ROLLBACK`. Queries may be pipelined up to a bound;
  each is ended by its own `Sync`, so an error ends only its own query.
- **Errors**: `ErrorResponse` with its fields, as a reply to its query; `NoticeResponse` is
  read and dropped.
- **Transactions**: `BEGIN` with an isolation level, `COMMIT`, `ROLLBACK`. The state of the
  transaction is the one each `ReadyForQuery` reports, and a `COMMIT` is reported committed only
  when the server answered `COMMIT` from inside a transaction that had not failed and is then
  idle; a `COMMIT` in a failed transaction, which PostgreSQL answers with the tag `ROLLBACK`, is
  reported rolled back. A connection that ends or breaks answers every query in flight with
  `unknown`: for a `COMMIT`, the transaction may or may not have committed.
- **Bounds** (rule 2.6), each a field of the configuration: the length of a message, the rows of
  a result (beyond it the reply is an error, and the connection reads on to the end of the
  query), the columns, the fields of an error, the queries in flight, the SCRAM iteration count.

## Out of scope

TLS (`SSLRequest`, and with it channel binding); `COPY`; `LISTEN`/`NOTIFY` and asynchronous
notifications (a `NotificationResponse` breaks the connection); binary formats; named prepared
statements and portals kept across queries; `Execute` with a row limit; cancellation; the
`replication` protocol; `GSSAPI`, `SSPI` and certificates; SASLprep of the password, which is
used as its UTF-8 bytes (PostgreSQL does the same with a password SASLprep refuses); and a pool
of connections.

## The store as a model

What a theorem about an application may assume of the database is `Lanes/Outside/Store/`: an
`Outside` for a transactional key-value store, with the isolation level a parameter
(`Store.Isolation.readCommitted` and `.serializable`). Requests name a transaction and carry one
operation: begin, read a key, read all, write, insert (refused if the key is there, as a unique
constraint refuses), append (the store chooses a fresh key, as a `serial` column does), delete,
commit, rollback. The model keeps every database the answers so far are consistent with, as a
checker of linearizability does, so it can answer the fault that matters: **a `COMMIT` whose
reply is lost leaves its outcome unknown**, and the model keeps both outcomes, and the commit's
effect may still appear later, until something the application reads tells them apart. Any
statement may also fail, as a deadlock, a serialization failure or an administrator may make it.

At read committed each statement sees the latest committed state and a commit applies the
transaction's writes on top of the latest state. At serializable the committed transactions are
equivalent to running them one at a time, in an order in which a transaction comes after every
one that committed before it began. Each model allows more than PostgreSQL does (it is a sound
over-approximation, so that a server that behaves like PostgreSQL behaves like the model), and the
tests record runs against a real server and check them with `Outside.allows`.

The store is not built from the combinators of
`docs/decisions/D65-models-of-external-services.md` (`Rpc.Server`, `Idempotent.server`), which
give each request an effect slot of its own. A transaction's effect is not its own: what it may
read and whether it may commit depend on the others committed around it, which is what an
isolation level says, so the model keeps whole databases rather than slots. A store whose
requests carry idempotency keys could still be wrapped by `Idempotent.server`; whether the store
should be rebuilt on `Rpc.Server` is left open.

## The trust boundary

Trusted: the IO file (`Lanes/Lib/Postgres/IO/Client.lean`), that it hands `step` the bytes
received, in order, and sends what `step` asks, and draws the nonce from libsodium; `Std.Net`;
and, as a premise of every theorem about an application that uses a database, that the server
behaves like the store model at the isolation level the application chose. That premise is not
proved and cannot be: it is tested on recorded runs, not on every server or every concurrency.
Not trusted, because proved or tested: the encoders and decoders, the connection's decisions,
SCRAM's computation, and the model.

*Amendment: the server proves itself, or the connection closes.* "So a server cannot skip the
exchange" above was false: the connection checked the server's signature once SCRAM had begun,
but took an `AuthenticationOk` as the server's first answer, which is `trust`, and answered a
request for MD5 by default. An impostor at the address, or on the plain TCP path, could open a
connection that has a password without knowing it, or have a digest of the password sent, to
guess against offline. `Conn.Config.requireScram`, on by default, now makes a connection that
has a password close on an `AuthenticationOk` before SCRAM's last message and on a request for a
cleartext password or an MD5 digest; it reaches `authed` only from `saslDone`, which only a
`SASLFinal` whose signature `Scram.verify` accepts reaches (`Conn.onMessage_requireScram`, with
`Conn.onMessage_saslFinal`). `allowMd5` is off by default. A server with no SCRAM, or a user whose
password is stored as MD5, needs `requireScram := false` and `allowMd5` or `allowCleartext`, as
`Tests/PostgresLive.lean` gives its MD5 and cleartext users. Without a password, `trust` opens as
before. Channel binding (`SCRAM-SHA-256-PLUS`) needs TLS and is still not done, so SCRAM proves
the server knows the password, not that it is the server meant.
