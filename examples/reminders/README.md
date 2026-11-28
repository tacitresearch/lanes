# reminders

A reminder is a text and a time. At its time it is posted to a notification service, and posted
again with a backoff until the service takes it (`2xx`), refuses it for good (`4xx`), its
attempts run out, or it is cancelled. It is the smallest application of a jobs table
(`Lanes/Db/Jobs.lean`): each reminder is a job of the table `reminders` in PostgreSQL, and the
worker beside the application (`Lanes/Db/Worker.lean`) delivers it. Everything is in the
table, so a restart loses no reminder and delivers none again that was taken.

```bash
cd examples/reminders
mkdir -p .lake && ln -s ../../../.lake/packages .lake/packages   # share the fetched dependencies
lake build            # the application, the proofs and the tests
lake test             # the model check; with LANES_POSTGRES=host:port, the application on it too
NOTIFY_URL=http://127.0.0.1:9090 NOTIFY_PATH=/notify lake exe reminders 8080
```

## How it works

- `Reminders/App.lean`: the table, and one transaction per request: `remind` (a `text` and
  `in` seconds) counts the reminders waiting and adds one, due at the time the request arrived
  plus `in`; `cancel` stops one that waits; `list` shows the latest. The front holds nothing:
  it sends each request to the store under the request's own number and answers with what the
  store answered.
- `Reminders/Serve.lean` runs the front's calls on PostgreSQL through the typed store's driver,
  and starts the worker, whose attempts are `POST`s of the text with `reminder-` and the job's
  id in `Idempotency-Key`, the same on every attempt, cut off at the attempt's deadline. It
  decides nothing.
- The time a request arrived is written into it by the server (`Web.stamp`); the worker takes
  the time from the wall clock.

## The claims

| Claim | Where |
| --- | --- |
| Every transaction of the reminders keeps the table: it adds or cancels reminders, and never changes what one says | `Reminders.keeps` |
| A reminder is delivered only once every database the store may hold has it, with its text: a request whose transaction did not commit delivers nothing | `Reminders.delivered_committed` |
| At a service that honours idempotency keys, no reminder takes effect twice | `Reminders.delivered_once` |
| A claim takes every reminder due, no more than its limit; the attempts of a reminder are bounded; only the current attempt's answer counts | the jobs table's: `Queue.claim_takes`, `Queue.claim_length`, `Queue.claim_attempts`, `Queue.finish_stale` |

Checked (`Reminders/Check.lean`, run by `lake test`), beside the store's model and a service
that answers `200`, `503` or `unknown`, or never: a reminder is delivered only once every
database the store may hold has it, none takes effect twice, a reminder sent was taken, no more
than `maxReminders` wait; a retry that succeeds, and a cancel followed by a second reminder, are
each reached. Lost answers and crashes of the worker are checked of the worker itself
(`Tests/Worker.lean`). Over HTTP on PostgreSQL (`Test.lean`, when `LANES_POSTGRES` is set): a
service that refuses the first two deliveries takes the third, under one key; a reminder that
waits is cancelled; after a restart on the same database the reminders are as they were and
none is delivered again.

## Limits

- A request carries no form token: anyone who can reach the server can schedule and cancel.
- That no more than `maxReminders` wait is checked, not proved.
- Reminders that are over stay in the table; nothing sweeps them.
