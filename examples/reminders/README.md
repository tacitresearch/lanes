# reminders

A reminder is a text and a time. At its time it is posted to a notification service, and posted
again with a backoff until the service takes it (`2xx`), its attempts run out, or it is
cancelled. It is the smallest application of the scheduler, `Lanes.Schedule`
(`Lanes/Behaviours/Schedule/Basic.lean`): the reminders hold the list; the scheduler beside them
holds the jobs, runs each at its time, retries it, gives up on it, and keeps them across a
restart, since its state is the journal's.

```bash
cd examples/reminders
mkdir -p .lake && ln -s ../../../.lake/packages .lake/packages   # share the fetched dependencies
lake build            # the application, the proofs and the tests
lake test             # the model check, then the application over HTTP through a restart
NOTIFY_URL=http://127.0.0.1:9090 NOTIFY_PATH=/notify lake exe reminders 8080 reminders.journal
```

## How it works

- `Reminders/App.lean`: one actor that holds the reminders, joined with the scheduler
  (`Schedule.attach`). `POST /remind` (a `text` and `in` seconds) schedules a job under the
  reminder's id, a call of the service with the text, due at the time the request arrived plus
  `in`; `POST /cancel/<id>` cancels it. The scheduler tells the reminders how each job ended:
  sent, given up on (the dead letter, which is logged) or cancelled.
- A periodic job sweeps the reminders that are over out of the list every `sweep_ms`, which keeps
  it within `maxReminders`. The reminders schedule the sweep at every start; the scheduler
  holds it under one id, so the second scheduling and every later one is answered `already`.
- `Reminders/Serve.lean` performs the scheduler's calls with the HTTP client, the reminder's id
  in `Idempotency-Key` on every attempt, cut off at the attempt's deadline, and hands the answer,
  or `unknown`, back as an input. It decides nothing.
- The time a request arrived is written into it before it is journalled (`Web.stamp`), so a
  replay sees the same time; the scheduler learns the time from it and from its own timers.

## The claims

| Claim | Where |
| --- | --- |
| The reminders stay within `maxReminders`, in every run and environment | `Reminders.bounded` |
| The scheduler holds at most `maxReminders + 1` jobs, no id twice | `Reminders.jobs_bounded` |
| In a fair run in which the scheduler does not crash, every reminder's delivery ends | `Reminders.delivery_ends` |
| If the reminders do not crash either and the link to them loses nothing, every reminder's delivery is answered to them: sent, given up on or cancelled | `Reminders.delivery_answered` |
| No attempt before its time, none while another of its reminder is out, no more than its attempts | the scheduler's: `Schedule.dispatch_due`, `Schedule.attempt_ends`, `Schedule.calls_le_scheduled` |

Checked (`Reminders/Check.lean`, run by `lake test`): two reminders' worth of requests, a
service that answers `200`, `503` or `unknown`, late or never, every timer firing at any moment;
a reminder the list calls sent was taken by the service, none is delivered more often than its
attempts allow, the sweep is one job; a retry that succeeds, a reminder given up on, one
cancelled while its delivery is out and the sweep emptying the list are each reached (22,709
states). Over HTTP (`Test.lean`): a service that refuses the first two deliveries takes the third,
under one key; a restart on the journal keeps what was sent and what waits; a reminder that
waits is cancelled.

## Limits

- The sweep is scheduled at time 0, and its run time moves on from the time the scheduler knew
  when it last ran; after a start it runs at once.
- A request carries no form token: anyone who can reach the server can schedule and cancel.
- The texts are journalled: do not remind yourself of a password.
