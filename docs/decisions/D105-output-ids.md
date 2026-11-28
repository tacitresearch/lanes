# D105. Output ids: where they come from, where the journal's id is kept, and a start with no effects

Status: Superseded by new-volatile-actors.md

`Lanes/Durable/OutputId.lean`, `Lanes/Runtime/Batch.lean`, `Lanes/Runtime/IO/Shell.lean`,
`Lanes/Durable/IO/Journal.lean`. This carries out clause 2 of D96 (an output is handed over at
least once, each time with the same id) and its first settled detail (the id names its journal).

## The id

An output's id is the journal's id and the output's origin (`Journal.OutputId`). The origin is
the place in the shard's history of the entry that produced it, counting from 1, and the
output's place among that entry's outputs; boot's outputs are at 0. Every entry counts: the
`handed` marks the shell notes after a hand-over and the marks of saves too, since those are what
the journal's files count (`Disk.Found.index`). A turn writes the entry that produces its outputs
last, so a batch knows each output's origin when it produces it, with no work beyond a count
(`Journal.turn_placed`, `Journal.turnAll_placed`, `Batch.run_ids`).

What is proved: an output's origin depends only on the history before it (`Journal.ids_append`);
a batch hands each output over with the origin its history gives it (`Batch.run_ids`), however
its waves are spread (`Batch.run_ids_spread`); a restart hands over again only outputs of the
history, each with the origin it had (`Journal.recoverIds_suffix`), exactly those after the last
mark (`Journal.recoverIds_handed`), and from a snapshot the same (`Journal.resumeIds_eq_recoverIds`).
Trusted: that the shell counts the history as the files do (`TRUSTED.md`, the runtime shell).

## The journal's id

Random, 16 bytes, made when the journal is begun and kept in a file beside it, `.id`, written and
synced before anything else. A journal begun afresh takes a new one, so ids never repeat across
two journals or two lives of one path. D97 plans a manifest in format 2 of the files; the id moves
into it then. A file of its own now changes no format: every journal already written opens as it
did, and takes an id at its first start.

## A start with no effects

`Journal.Store.restored` (and `ServerConfig.restored`): the files are a copy restored from
elsewhere, production into staging. The outputs they owe are marked handed over and not handed
over, and the journal takes a new id, so nothing the copy hands over later has the id of one of
production's. It is an option of one start, not of the store: each start with it drops what the
shard owes. Jobs in flight in the copy are attempted again when their deadlines pass, by the
copy's workers, under new ids; nothing in the runtime can tell those from new work.

## Drivers

- HTTP calls: `Http.Client.handlerKeyed` puts the id in `Idempotency-Key`, the header Stripe
  reads, unless the call carries a key of its own. An application's own key comes first because
  it survives the application's retries, which are new outputs with new ids (rule 1.5).
- S3 takes no key. `S3.Op.put` with `ifAbsent` is a conditional write (`If-None-Match: *`): a put
  handed over again is refused with `412` and writes nothing. It fits a put that creates; a put
  that overwrites has no condition to state without the object's ETag.
- SES takes no key. `Aws.Ses.handlerOnce` keeps one itself: for each journal, the origin of the
  last output it sent, in a file written before each send. Outputs come in the order of their
  origins, and again in that order after a restart, so one at or before the last sent is a repeat,
  answered `unknown` and not sent (`Aws.Ses.Sent.admitted_nodup`). The state is one line a journal.
