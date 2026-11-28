# Deploying an application

A Lanes application is a stateless process: one binary, no disk of its own, its data in
PostgreSQL. It is deployed as any stateless container is: several instances behind a load
balancer, replaced, scaled or restarted at any moment. This page is what is particular to Lanes.
What `lanes new` writes (`examples/counter`) follows it; so does `examples/rookery`.

## The rule for several instances

An actor's state is a cache of its process. A restart puts every actor back at its initial
state, and another instance has actors of its own (`docs/decisions/D110-volatile-actors.md`).
So anything that must outlive the process, or that the instances must agree on, lives in the
database: a count, a session, a failed log-in, an idempotency key, a job, an effect still to
perform. Each request does what it does to it in one pure transaction, which the store runs at
`SERIALIZABLE` (`docs/decisions/D111-typed-store.md`), so requests served by different instances
at once still take effect in some serial order. What an actor may keep is what is safe to lose
and to differ between instances: a cache, a connection, a request in progress.

## The image

The binary links only the C library: build it with Lake in one stage, and copy it, with the
migrations, into a small one.

```dockerfile
FROM debian:bookworm AS build
RUN apt-get update && apt-get install -y curl git clang && \
    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
ENV PATH=/root/.elan/bin:$PATH
WORKDIR /app
COPY . .
RUN lake build

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y ca-certificates && rm -rf /var/lib/apt/lists/*
COPY --from=build /app/.lake/build/bin/myapp /usr/local/bin/myapp
COPY --from=build /app/migrations /app/migrations
WORKDIR /app
ENV LANES_HOST=0.0.0.0
EXPOSE 8080
ENTRYPOINT ["myapp", "8080"]
```

`ca-certificates` is for TLS to the database and other services (`Tls.Trust.system`).

## Configuration, from the environment

What `lanes new` writes reads its variables once, at the start, with `setup` in `Main.lean`, a
reader of the environment (`Lanes/Outside/Environment.lean`). A variable that is not valid, or
required and unset, stops the start, and every such variable is listed at once; a secret's
value is never shown. `Environment.describe setup` lists the variables, each with its text and its default.

- **The database**: `DATABASE_URL`, a `postgresql://` URI or libpq's `keyword=value` pairs,
  which what `lanes new` writes passes to `Postgres.Client.fromEnv`; for what it leaves out,
  libpq's variables (`PGHOST`, `PGPORT`, `PGUSER`, `PGPASSWORD`, `PGDATABASE`, `PGSSLMODE`, …),
  then a deploy's (`LANES_DB_HOST`, `LANES_DB_PORT`, `LANES_DB_USER`, `LANES_DB_NAME`,
  `LANES_DB_PASSWORD_FILE`, `LANES_DB_CA`), as `Lanes/Services/Postgres/README.md` says. Give the
  password as a file the platform mounts from its secret store (`LANES_DB_PASSWORD_FILE`), not in
  the URL or a variable a process listing shows. TLS is verified to the host's name unless the
  host is this machine.
- **Where to listen and how to stop**: `LANES_HOST` (`0.0.0.0` in a container), `LANES_IDLE_MS`,
  and `LANES_DRAIN_MS`, how long SIGTERM waits for the requests in flight.
- **Secrets of the application** (a key that signs cookies, a pepper), the same for every
  instance: from the secret store, as a file. A key made by one instance at its start would be
  another instance's stranger.

## Migrations, at the start

Migrations are plain SQL files in `migrations/`, applied in the order of their names. At its
start every instance runs `Postgres.Typed.prepare`, which:

1. runs the migrations that the table `lanes_migrations` does not record, in one transaction
   under an advisory lock, and records them: instances started at once run each migration once,
   and a migration that fails leaves nothing of the run;
2. compares the tables the application declares (`lanes_data … table …`) with the database's
   catalog: columns, types, nullability, text's collation and primary keys.

On any difference the instance refuses to start and says what differs. So a deploy whose
migrations and code disagree fails at its first instance, before it serves a request on tables
its transactions were not written for. Give each application a database of its own:
`lanes_migrations` names migrations by file, for every application that shares it.

A change to a table is a new migration and the same change to its declaration, deployed
together. A change the running instances cannot work with (a column renamed, dropped, made `NOT
NULL`) needs two deploys: one that adds and copies, and one, once no old instance runs, that
removes.

## Health

The server answers `ServerConfig.ops`'s paths: `/readyz` for the load balancer, which answers
`503` from SIGTERM on so that the balancer stops sending requests while those in flight finish,
`/healthz` for the platform's liveness check, and `/metrics` to this machine only. The access
log goes to stderr.
