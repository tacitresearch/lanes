# Examples

Applications built on Lanes, each a Lake package of its own that depends on the framework in
this repository by path, as an application of yours would depend on it by git. They are written
to be read: copy one to start. The tests do not import them, but some of their systems are
copied into `Tests/Fixtures/` and must stay the same as the copies (`Tests/Copies.lean`): those
of `examples/bank`, `examples/kv-cache` and `examples/watchdog`. `examples/counter` is what
`lanes new` writes (`Tests/New.lean`). The large ones are also here to find out what the
framework is missing: anything one of them has to work around is a defect of Lanes, and is fixed
there. Actor state lives as long as the process, as in Go, Tokio or Erlang: every start is a
boot. State that must outlive the process, or that several instances must agree on, lives in
PostgreSQL, one pure transaction per request, as `counter`, `todo-db`, `payments`, `reminders`
and `rookery` keep theirs. `bank`, `bank-web`, `kv-cache` and `watchdog` keep their state in
actors on purpose, to show what actors are for; it lasts until a restart. An example whose tests
need PostgreSQL skips them without `LANES_POSTGRES` (`scripts/with-postgres lake test` runs them
beside a PostgreSQL made for the run).

## In what order to read them

`docs/TUTORIAL.md` comes first: it changes the counter, checks it and proves it.

1. `counter`: exactly what `lake exe lanes new counter` writes. A stateless app with a store: a
   typed table, a migration, one pure transaction per request, a front that keeps nothing, an
   invariant proved per transaction and model-checked beside the store's model, and a web page
   with htmx. At the start it runs its migrations and refuses to start on tables other than the
   declared ones. `lake test` fails if it and the template differ.
2. `bank`: accounts as actors that send each other credits. An invariant of every actor
   (`balance_nonneg`), one of the whole system (`money_conserved`), and the checker finding the
   credit a lossy link drops. Its balances last until a restart, on purpose (its README).
3. `bank-web`: the bank behind a server-rendered page: typed routes, a bridge from requests to
   inputs and templates.
4. `kv-cache`: a key-value store with front ends, checked against a five-line spec with no
   refinement mapping. A read cache breaks it, and the checker and the proof both show the stale
   read; behind the `Once` memo it takes each request once under every fault.
5. `watchdog`: what fairness says about a keep-alive: a fair run in which the dog never barks.
6. `payments`: a shop whose orders are rows, each placed under the customer's idempotency key
   with its charge in an outbox, charged by the worker through a model of a payment service
   whose answers may be late, lost or `unknown` and whose webhooks come late and out of order.
   An order is charged at most once in every run, restarts included (proved), and an order
   paid has a payment that succeeded (checked).
7. `todo-db`: a to-do list kept in PostgreSQL through the typed store: one pure transaction per
   request, at `SERIALIZABLE`. A user's to-dos are unique by title, proved per transaction and so
   in every database the store model allows; adding without looking first, and retrying a lost
   answer, stores a title twice, and the checker finds it. `lake exe todoLive` runs it on a real
   server.
8. `sign-in`: a site whose members sign in with Google or GitHub. The
   sign-in is Lanes' and runs before the system, which gets only the identity it verified and
   gives the member a session.
9. `upload`: uploads of any size, handed to the system in pieces and answered with their size
   and checksum: a request that streams, through the gate a piece at a time.
10. `reminders`: reminders over HTTP, each a job of a jobs table in PostgreSQL
    (`Lanes.Db.Jobs`), posted by the worker to a notification service at its time, under the
    job's id as the idempotency key, and again with a backoff until it is taken, refused, out of
    attempts or cancelled.
11. `chat`: a chat room over WebSockets: each member a socket, each line through the gate as a
    request, each line for a member an output to its socket (`Lanes.Web.Http.WebSocketSession`).
12. `rookery`: the serious system below.

| Feature | Where to see it |
| --- | --- |
| A stateless app with a store: a table, a migration, transactions, a check of the schema at start | `counter`, `rookery` |
| A spec as a `Service`, implemented by actors | `kv-cache` |
| `lanes_data`, with JSON (`ToJson, FromJson`) and a table (`table`) | `counter`, `rookery`, `todo-db` |
| Per-actor invariants (`actor_invariant`, `System.invariant_of_actor`) | `bank`, `upload` |
| Refinement to a spec (`System.Implements`, `System.Refines`) | `kv-cache`, `upload` |
| Invariants per transaction, in every database the store allows (`Db.invariant`, `Txn.All.others`) | `counter`, `todo-db`, `rookery` |
| A request takes effect once on an actor's own state (`Once.actor`, `Service.once`) | `kv-cache` |
| Fairness and liveness | `watchdog` |
| Work due later, an outbox, retried with a backoff, under an idempotency key (`Lanes.Db.Jobs`, `Lanes.Db.Worker`) | `reminders`, `payments` |
| Acting once across restarts: a key stored in the transaction (`Lanes.Db.Keys`) | `payments`, `rookery` |
| A model of an external service: timeouts with unknown outcome, idempotency keys, webhooks (`Lanes/Outside/`) | `payments` |
| A database: typed tables, pure transactions, an invariant per transaction, PostgreSQL | `todo-db` |
| Model checks, a bug found, random runs | `bank`, `kv-cache`, `todo-db` |
| HTTP, routes, htmx, templates | `counter`, `bank-web`, `rookery` |
| Sessions and failed log-ins as rows, passwords checked against a stored hash, cookies, tokens | `rookery` |
| Sign-in with Google or GitHub (OAuth 2.0, OpenID Connect) | `sign-in` |
| A JSON API and rate limits | `rookery` |
| Request bodies in pieces, responses in parts, Server-Sent Events | `upload`, `rookery` |
| WebSockets: a request that switches protocols, messages in, pushes out | `chat` |

## The serious systems

| System | What it is | State |
| --- | --- | --- |
| `rookery` | A small social network for bots and their owners: sign-up, sessions, API tokens, posts, follows, timelines, deletes, rate limits, as a web application with a JSON API | The flagship. Stateless: its data is in PostgreSQL, each request one pure transaction. Proved per transaction, and so of every database the store's model allows: a request changes only the rows of the account it is made as, the windows and failed log-ins stay within their bounds, a response names the account asked as, a change retried with its `seq` writes nothing. Checked beside the store's model, with lost answers and restarts; tested over HTTP on PostgreSQL through SIGKILL and a restart. Its README says what moved from proved to checked, and its friction log |

## Building one

```bash
cd examples/rookery
mkdir -p .lake && ln -s ../../../.lake/packages .lake/packages   # share the fetched dependencies
lake build
lake test                               # the model checks and the bridge's tests
../../scripts/with-postgres lake test   # and a person and a bot over HTTP on PostgreSQL
```

and in each small one, `lake build` and `lake test` (`bank-web` needs `bank` beside it, which it
requires by path;
`upload`'s test drives its front end with no socket, and `lake exe upload 8080` serves it:
`curl -T file http://127.0.0.1:8080/upload`).

Each example's test program prints through `Lanes.Testing.report`: a line for each result, with
its kind (check or test), and the counts. It exits 1 when a result failed and 2 when a model
check passed but hit a bound, and `lake test -- --json` prints the results as JSON.

## Testing a front end

`Http.Loopback` drives an application's front end with no socket: a request is written as a
client writes it, read by the connection the server runs (`Http.Conn`), prepared and handed to
the system behind the gate on a kernel of its own, and the bytes written back read by the
client's reader. It is pure, so a test is a value; the system's state carries over from one
exchange to the next, and time passes only when nothing else can happen, so a request the system
never answers gets the gate's `504`.

```lean
let lb := Http.Loopback.start (bank Acct 100) bridge
let (lb, moved) := lb.post ["transfer"] [("src", "0"), ("dst", "1"), ("amount", "30")]
let (_, balance) := lb.get ["accounts", "1"]
```

`bank-web`'s `Check.lean` does this. A live test of a process uses `Http.Client.fetch port
request`, one request on a connection of its own, as `rookery/Rookery/Live.lean` does.

