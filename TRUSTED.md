# Trusted code

Everything Lanes asks you to trust rather than proves, listed in one place (rule 5.5). A property
of an application is only as strong as this list. Keep it short, and add an entry in the same
change that adds trusted code.

## Trusted by every Lean program

The Lean kernel, compiler and runtime, `Std.Async`, `Std.Sync`, `Std.Http`, libuv, the C
toolchain, the operating system and the hardware.

## Trusted in Lanes

| What | Where | Why it is trusted | How it is checked |
| --- | --- | --- | --- |
| The runtime shell | `Lanes/Actors/Runtime.lean`, 289 lines | It takes everything that has arrived in its inbox, reads the clock, and performs, in order, the acts `Batch.run` returns for those commands: append entries to the journal, record events, hand outputs to the adapter and mark them handed over, save the kernel, answer peeks; then it answers the idle waiters the batch says are answered. Who is refused, who waits for room and who is woken is `Mailbox`, pure and proved (below); the shell keeps one in a reference and resolves the promises it is handed. What a batch does is not the shell's: it is `Batch.run`, proved. The kernel after it is the one its journal entries and saves describe (`Batch.run_kernel`); an output is handed over only after the entries that produce it are appended, a save falls only where every output produced has been handed over, and a peek is answered with the state of the kernel the journal so far describes (`Batch.run_sound`), after every command before it and before any after it (`Batch.run_peek`); an idle waiter is answered exactly when the kernel is quiet, as it asked, at the end of a batch (`Batch.run_resolved`); a save is due exactly when the entries written since the last reach `max 1 snapshotEvery`, and the count starts again (`Batch.flush_save`). Each turn is `Journal.turn` (`Journal.turns_kernel`). Trusted: that the shell performs the acts unchanged, all of them and in order, and hands each output on as given; that it tells the batch whether the journal can save; that it hands over at start the outputs `Journal.resume` says were not marked as handed over; and its ending: that `stop`, or a journal that cannot be written, ends the shard and leaves no caller waiting. | `Tests/Runtime.lean`: one input's several outputs and the boot outputs compared exactly; recorded events replayed through `SysState.run`; timers, back-pressure, stopping an idle and a busy shard. `Tests/Scale.lean`: a message costs the same at 1,000 and 100,000 actors. `Tests/Durable.lean`, on a journal held in memory: every input is in the journal before an output it caused is handed over; outputs not marked as handed over are handed over after a restart and marked ones are not; when a write fails the shard ends, reports the error and releases every caller, also those whose commands it had not yet taken. Each of these fails on the mutant that breaks it. |
| The transport between processes | `Lanes/Env/Peers.lean`, 189 lines | It listens, connects, sends, receives and closes, as the courier tells it, and tells the courier what happened. It reads every connection, also those it made, so that a peer that has left is noticed; it does not send a parcel larger than the receiver would take, and says so once; there is no timeout on a connection being made or on a write. It decides nothing: when to connect, what waits and what is dropped, one write at a time on a connection, what a stream of bytes is as parcels and what `stop` ends are `Peers.Courier.step`, a pure function. What the link promises is no more than `Link.network`: a parcel may be lost, arrive twice, or arrive out of order across connections, and nothing arrives that was not sent. Trusted: that an event is reported when the thing happened, that an action is done as asked, and the last of those promises. Trusted too: that processes run this way, process `k` running `sys.shard (hosts · == k)` and `home i` the address of process `hosts i`, implement `System.shards sys hosts` with its links between shards at most `Link.network`; the model is proved to behave as `sys` for any number of shards (`System.ShardsReachable.unsharded`), for a `home` that does not change and is never `none`. There is no authentication. | `Tests/Courier.lean`: the courier run by the model checker against a network that fails at any moment (connections not made, writes that fail, a peer that leaves, bytes in pieces, `stop` anywhere): one write at a time, nothing written twice, a bounded queue, nothing open after `stop`; three mutants of the courier fail it. `Tests/Peers.lean`: the bank on three shards joined by TCP, every credit arriving; a shard stopped and another started on the same port found again; a shard with peers on a journal, stopped and started. And the transport alone, one end sending and another keeping what arrives: three hundred parcels in the order sent; parcels that arrive in one piece handed on in order; the socket of a peer that left closed; a parcel over the limit not sent and those around it sent; a peer that leaves a connection nothing is being sent on noticed, so that the next parcel reaches whoever listens there now; a peer that was not there tried again and found. `systems/raft-kv`'s `raftProcs` uses it through the death of two leaders. Not tested: an accept that fails, a socket that cannot be made, an address that is not IPv4, that the first parcel over the limit is reported, a write that fails on a connection whose reader has not noticed, and loss on a real network. |
| The journal's files | `Lanes/Env/Journal.lean`, 137 lines | It takes a lock beside the journal before it reads anything, reads the journal and the snapshot, and does the writes it is given, one by one: an append to the journal, flushed and synced, or a file written beside its target, synced, renamed over it, and its directory synced; the directory is synced too when the journal is opened, which may have made it. What the files mean, which are refused, a journal that is not there among them when the store may not begin one, and what is written at a start, for a turn and for a save, in what order, are not its decisions: they are `Journal.Disk.start`, which goes on only with what `Disk.read` found (`Disk.read_of_start`), `Disk.mend`, `appendWrites` and `saveWrites`, pure functions over a model of the two files (`Lanes/Actors/Disk.lean`), proved to leave files that load as the kernel the shard had wherever the process dies (below). Trusted is that the model is the file system: bytes appended and flushed stay when the process dies, and once synced when the power goes; an append that did not finish leaves some of its first bytes and nothing else; and a rename replaces a file at once, and once its directory is synced for good. Since each write is synced before the next begins, a loss of power leaves what a death at the same moment would. `fsync` is the operating system's (`native/lanes.c`, below); on Linux it waits for the disk, on macOS it does not empty the drive's own cache. Also trusted: that it counts the entries it writes, which gives a save the index of its mark; that it checks that entries and records fit a frame before it writes them; and that it hands the shell what `Disk.start` found. | `Tests/Durable.lean`: restart from the journal; a journal cut at eight places; a second opener refused while the first holds the journal; another system's journal (refused with the name it was written under), one written with another codec and one with a flipped bit each refused and left byte for byte as they were; a store that may not begin a journal refused a path with none, where it makes none, and an empty file; a child process killed with SIGKILL while working, after which every request it had answered is in the journal and the state is the one the journal describes; a shard restarted from a snapshot and a cut journal; each state a save can leave the files in, built by hand; the model of the two files run on the compiled code, with a turn's append and a save's mark cut at every byte and the save stopped between any two of its writes, from each state an earlier save can leave (this is the test that fails when the snapshot and the journal are replaced in the other order); a cut journal without its snapshot refused; a process killed four times while saving every forty entries, after which its state, which is its own history, has every acknowledged input once and in order; a journal whose last entry was not wholly written, cut back to the entries before it with exactly the bytes cut off in `.cut`; and two saves with entries of every kind between them, after which the second mark has the index of all that was written before it; `fsync` on a file, on a directory, and on a path that is not there, which is an error. That the journal calls `fsync` no test can see: only a loss of power would show it, so removing a call is a mutant no test kills. Syncing costs about 0.2 ms a batch on the disk it was measured on, one sync per batch, so a burst of inputs shares one. |
| The HTTP adapter's IO | `Lanes/Env/Http.lean`, 228 lines | It reads requests from sockets, prepares each as its bridge says (`Bridge.prepare`, pure), gives each the id `Http.Waiting` hands out, hands them to a system with the gate in it and writes the gate's one response for each. Which id a request gets, who waits on it, who is answered and who is left at the end are `Http.Waiting`, pure and proved: ids are handed out in order from the start, never twice and none below it, and a refused request's id goes to the next (`Http.Waiting.exec_handed`, `exec_handed_nodup`); a waiter waits on the id handed out to it until it is answered (`exec_waiting`); an answer goes to the waiter of its id and no other, and no id is answered twice (`exec_answered`); after a drain nobody waits (`exec_drain`). Trusted: that the server applies `prepare` to every request it reads, on the request's own task, before the request has an id or enters the shard, so that what `prepare` removes (a password, a cookie) is never journalled and the system and its theorems see only prepared requests; that it keeps the table in one mutex, holds it from `wait` until the shard has taken or refused the input and releases the id of a refused one, and resolves exactly the waiters the table hands it; and that the start, the length of the shard's history, is above every id handed out before, which holds because every request the shard admits leaves an entry of its own, so ids stay fresh after a restart and after the journal is cut. There is one loop (`serveOn`) for both such systems: `served sys` (`serve`, `serveWith`), which is `fronted sys` with requests its only inputs and responses its only outputs, and `fronted sys` (`serveFronted`), where an output that is no response is handed to the caller's handler and `Server.tryInput` takes an input that is no request; a request cannot be handed in that way. `serve` names its journal by the application's `system` and the gate's configuration, which its step function reads (`ServerConfig.journalName`), so a journal of another gate, or of the gate before `docs/decisions/D43-one-gate.md`, is refused. It answers `HEAD` as `GET` without the body, `405` for other methods and, when the inbox is full, `503` itself. When the shard ends on an error it answers the requests in flight `503` and shuts down, and `wait` throws. | `Tests/Web.lean`, over a socket: fifty requests at once, the recorded run checked against `Http.servedOutside`, `HEAD`, `405`, `413`, links with awkward text decoded by the real server, stopping with a request in flight, the bank restarted on a journal that was cut, with no request id used twice, a port already taken (the journal is left free and the process can exit), a journal written as the server before `docs/decisions/D43-one-gate.md` wrote it, refused with the names of both systems and left as it was, a bridge's `prepare` taking a header out (the system answers the prepared request and the journal holds no trace of the header), and a journal that stops taking writes (every request is answered and the server ends with the error). `Tests/Fronted.lean`: `serveFronted` under `serveShard`, the recorded run of each front checked against `Http.frontedOutside`, and `serveFronted` on a journal that is cut, restarted, with no request id used twice. The `503` for a full inbox is not tested. |
| A process with a front and peers | `Lanes/Env/Node.lean`, 47 lines | `Http.serveShard` starts `Peers` and `serveFronted` on `fronted (sys.shard hosts)` and ties them: a parcel that arrives is handed to the server as an input that is no request, and of the shard's outputs a parcel is sent to its peer and anything else that is no response goes to the caller. That each goes where it should is trusted. A parcel that finds the inbox full is dropped. Request ids are each process's own, so a response has to be put out by an actor of the process that took the request: one put out elsewhere reaches that process's gate, which may be waiting on the same id for another client. | `Tests/Fronted.lean`: the bank on two shards joined by TCP, each behind its own front; a transfer posted to one front between accounts on different shards is answered and the credit shows through the other front, both ways; each credit is seen entering the other shard as a parcel. The test fails when parcels are not sent. It also shows the limit: a balance asked through the front of the shard that does not host the account is answered `504`. One process alone: an output that is neither a response nor a parcel comes to the caller; a process whose HTTP port is taken does not start and leaves its port for parcels free; on a journal, stopped and started, it is in the state it was in. |
| The clock adapter's handler | `Lanes/Env/Clock.lean`, 77 lines | It reads the wall clock and hands the time back as an input, never a time earlier than one it gave, nor, started on a journal, earlier than the last one in it. | `Tests/Clock.lean` checks a recorded run against `Clock.outside`, the model the checker explores, with a clock started on a journal whose last time is in the future. |
| The HTTP client adapter's handler | `Lanes/Env/HttpClient.lean`, 96 lines | It opens a socket, sends a request and reads until the answer is whole or cannot be one, or until the deadline, whichever comes first; then it closes the socket, whoever won, and hands the answer back as an input. What to send, when the answer is whole, the size limit and what the bytes mean are not its decisions: they are pure code, the next row. That a call given up on leaves no socket and no task behind rests on `close` failing the read still pending, which is `Std`'s. | `Tests/HttpClient.lean`: real calls to a real server, a closed port and a bad address, and the recorded run checked against `Client.outside`. Against servers written in the test: one that never answers is given up on at the deadline, and twenty such calls leave no more files open than before; one that sends a whole response and keeps the connection is answered at once; one that sends more than the limit is refused. A connection that never opens is not tested. |
| The jobs pool | `Lanes/Env/Jobs.lean`, 71 lines | For each attempt the jobs actor dispatches, it starts a task, performs the attempt there (a pure function, or a call through the HTTP client with the job's key in a header) and hands the result back as an input; an attempt that throws gives no result. What to attempt, when to try again, how long to wait, how many at once and what an answer is are the jobs actor's, `Jobs.step`, proved (`Lanes/Behaviours/JobsSound.lean`, `Lanes/Semantics/JobsLive.lean`); the header is put on by a pure function (`Jobs.withHeader`). Trusted: that every attempt dispatched is performed on a task of its own and its result, if any, handed back with the key and the attempt it was dispatched with; that the shard does not wait for it. A result that finds the inbox full is dropped, which the model allows: the attempt's deadline brings the next. | `Tests/Jobs.lean`: calls to a local service that answers `503` twice and then `200`, which sees the same key on all three attempts; a closed port, failed after the last attempt; a service that never answers, timed out at the last deadline; a pure worker on a dedicated task; each recorded run checked against `Jobs.pool`. The mutants of the handler (`scripts/mutants.py jobs`) fail these. |
| The HTTP wire format | `Lanes/Http/Wire.lean`, 439 lines | Pure code: the bytes of a request (`Request.wire`), what the bytes received so far amount to (`Response.read`), and the bytes a server sends for a response, framed by its length, in chunks, by the end of the connection or after interim responses (`Response.wire`, `wireChunked`, `wireToEnd`, `wireAfter`), which say what the reader must understand. What the reader makes of those bytes and of every start of them, its limit and its ending are proved (below). Tested, not proved: what it makes of the forms a server may send that those writers do not write, and that it refuses what cannot be one response. The forms: a reason phrase, `HTTP/1.0`, no blank after a colon or tabs around a value, a length with leading zeros or given twice alike, a coding spelt `CHUNKED`, a chunk size in capitals, with leading zeros, blanks or an extension, a trailer, a 204 or 304 that gives a length, and a body in chunks or to the end after interim responses. The refusals: two lengths that differ, a length beside a coding, a coding other than `chunked` alone, a folded header, a blank before a colon, a control character in a head, a chunk without its CRLF, more than sixteen hex digits or 256 bytes of extension. Of the request writer this is proved, for every request and host: of the headers that frame a message only its own are written, so one `Content-Length`, one `Host`, one `Connection` and no `Transfer-Encoding` (`Request.fields_framing`); every name written is a token (`Request.fields_token`); no line of the head has a control character other than tab, so none has a CR or an LF, and the target has no blank (`Request.head_plain`, `Request.target_visible`). These are theorems about the lines; that the bytes are those lines, each ended by CRLF, is the definition of `Request.wire` and is tested. | `Tests/HttpClient.lean`: requests with hostile names, values, hosts and bodies, each read back leniently and found framed once; each response the reader must refuse; the forms above; 264 generated responses, each written in each of the five ways and cut at every byte, read back as written at the last byte and not before, on the compiled code; the size limit; 20,000 one-byte chunks in under 200 ms. |
| The C | `native/lanes.c`, 69 lines, declared in `Lanes/Data/Sodium.lean`, 59 lines, and `Lanes/Env/Journal.lean` | What Lean cannot express or check, bound as other languages bind it: `fsync`, and from libsodium (the system's, linked statically) SHA-256, HMAC-SHA-256, the comparison of two byte strings (`sodium_memcmp`), secure random bytes and Argon2id. Lean's compiler promises nothing about time, so a hash or a comparison written in Lean may take a time that depends on a secret; libsodium's are written not to. A bound function with a Lean reference (`Sha256.reference`, `Hmac.reference`, `Bytes.sameReference`, pure Lean with nothing trusted in it) has that reference as its body, so every theorem about it (`Sha256.size_hash`, `Bytes.same_iff`, …) is about the reference and holds of the binary only as far as the C computes the same. Trusted: libsodium, that the C computes what its reference does, that it reads its arguments without taking them over and returns a fresh array, and that `sodium_memcmp`, SHA-256 and HMAC-SHA-256 take a time that depends on the lengths of their inputs only. Argon2id has no reference: that it is Argon2id is libsodium's; that a salt is 16 bytes and the cost within libsodium's limits is in the types (`Argon2id`), and the process ends, as on any allocation Lean cannot make, when its memory cannot be had. | `Tests/Crypto.lean`: the NIST and RFC 4231 vectors on both libsodium and the reference; then the two compared on 2,301 messages, every length to 300 and random lengths to 1,000, 531 keys, every length to 130 and random to 200, and 5,000 pairs of strings that are equal, one byte apart, of other lengths or a prefix (a comparison of the first byte only fails it); Argon2id deterministic, 32 bytes, and changed by the password, the salt and each part of the cost; random bytes as many as asked and different each time. `Tests/Auth.lean`: tokens and digests on the bound functions. |
| The template macro | `Lanes/Html/Syntax.lean`, 113 lines | It turns template syntax into `Html` values. What it produces is type-checked, but that it produces the element the template shows is not proved. | `Tests/Html.lean` compares rendered templates with the expected text. |

`lanes lint` fails when one of these files does not have the line count given here (rule
`trusted-size`), so trusted code cannot grow without this file changing. The counts are written
by `lake exe lanes lint --fix`, never by hand.

What the HTTP reader makes of a response is not in this table either, for the responses a
server writes as `Response.wire`, `wireChunked`, `wireToEnd` and `wireAfter` do: any final
status of three digits, headers whose names are tokens and whose values have no control
character but tab and no blank at either end, any body of fewer than 10^18 bytes (none for a
204 or a 304, which are neither chunked nor ended by the connection), and chunks of any sizes
but none. Proved in
`Lanes/Http/WireSound.lean`: such a response is read back as written, its names in lowercase,
as soon as its last byte is there, whatever follows it and whether or not the connection has
ended (`Response.read_wire`, `read_wireChunked`, `read_wireAfter`); every strict start of one
waits while the connection is open and is refused once it has ended (`read_wire_extract`,
`read_wireChunked_extract`, `read_wireAfter_extract`); a body framed by the end of the
connection is read once it ends, and waited for until then (`read_wireToEnd`,
`read_wireToEnd_open`). For any bytes at all: the reader asks for more only while the
connection is open and at most `limit` bytes have arrived, so the adapter's loop ends and holds
at most the limit and one read (`read_more`, `read_ended`); a response it gives ends within
`limit` bytes, and so does its body (`read_some`); and an answer given while the connection is
open stays the answer whatever arrives after it (`read_append`).

What the inbox and the courier decide is not in this table either. Both are pure, and what
they promise is proved for every capacity and limit and every sequence of operations or events,
of every state reached from an empty one. Of the inbox (`Lanes/Actors/MailboxSound.lean`): a
`take` returns exactly what was taken in since the last `take`, in the order it went in
(`Mailbox.batch_since_take`); an offer is refused for want of room exactly when the inbox
holds `capacity`, so it never holds more
(`Mailbox.Reachable.offer_full_iff`, `Mailbox.Reachable.bounded`); once `rest` has put the shard
to sleep, the next thing taken in or a `close` hands it back to be woken
(`Mailbox.woken_after_rest`), it never sleeps on something to take or on a closed inbox
(`Mailbox.rest_eq_false`, `Mailbox.Reachable.asleep_empty`), and with room for one no sender
waits for room while it sleeps (`Mailbox.Reachable.not_asleep_waiting`); every sender that
waited for room is handed back by the next `take` or `close`, as often as it waited
(`Mailbox.wake_since_take`, `Mailbox.close_since_take`); and after `close` nothing is taken in
and nobody sleeps or waits (`Mailbox.after_close`). Of the courier
(`Lanes/Actors/CourierSound.lean`), about the list of what it was told and what it answered from
its start: between two writes on a connection the handler said the first was written, and it
never writes on a connection whose write is under way (`Peers.Courier.written_between`,
`Peers.Courier.Reachable.write_not_busy`); it writes only on a connection it dialed and has not
closed since (`Peers.Courier.write_dialed`); what it writes to a process is what it was told
to send there, in order, each parcel at most once (`Peers.Courier.written_sublist_sent`); the queue for a process never holds more than
`limits.queue` (`Peers.Courier.Reachable.queue_le`); `stop` closes every connection it dialed or
adopted, and after `stop` it only closes and refuses (`Peers.Courier.stop_closes`,
`Peers.Courier.after_stop`); the first dial to a process after a connection to it broke answers a
`send` told `retry_ms` or more after the break, in the courier's clock
(`Peers.Courier.rest_after_break`); and what it delivers from a connection is what its `read`
makes of the bytes told of on that connection, in order, until it closes the connection, and
nothing after (`Peers.Courier.delivered_read`). Stating these showed two promises the courier
broke, now kept and tested: with `queue := 0` the parcel that made it dial waited in the queue,
and bytes reported on a connection it had dialed were answered with `close` while it went on
writing there. Left to the model check, because they are about the handler and the network as
well: that what is reported written was started once, and that nothing is lost unless a
connection failed, a queue was full or the courier stopped.

What a journal file means is not in this table either. Proved in `Lanes/Actors/Journal.lean`
and `Lanes/Data/Frame.lean`: a file reads back as the entries written (`Journal.open?_file`); a
file cut at any byte opens, is never refused, and gives exactly the entries wholly written
before the cut (`Journal.open?_cut`); recovery rebuilds exactly the kernel those entries lead to
(`Journal.recover_kernel`); what is handed over again is exactly what was produced after the
last mark (`Journal.recover_handed`); a kernel restored from its image is the same system state
with the same timers (`Kernel.abs_image_kernel`, `Kernel.WellFormed.image`); a snapshot file
reads back as the kernel saved (`Journal.saved?_saved`); and starting from a snapshot gives
exactly what replaying the whole history gives (`Journal.resume_eq_recover`). Proved in
`Lanes/Actors/Disk.lean`, over a model of the two files in which an append may stop at any byte
and a rename is atomic: if the process dies at any byte of a turn's append, the files load as
the kernel that the entries wholly written lead to (`Journal.Disk.Holds.append_crash`); if it
dies anywhere in a save, they load as the kernel the shard had or, once the mark is wholly
written, the one the saved image restores (`Journal.Disk.Holds.save_crash`,
`Journal.Disk.Torn.load`); and a start mends what a death left into the files of a running
shard (`Journal.Disk.Torn.mend`), so this holds over any number of starts, saves and deaths.
A file that is not a cut journal of this system is
refused, not repaired: a frame that is all there and does not check, an intact entry the codec
cannot read, a header that names another system. Two things are not excluded. A checksum makes
it unlikely, not impossible, that a damaged entry is taken for a good one. And damage to the
length field of the last frames can look like a write that did not finish; what is cut off
then is kept in the `.cut` file, not deleted.

The runtime's decisions are not in this table: routing, start, stop, which mail a stopped
actor loses, which timer is due, how long to sleep, how much to do before looking at the inbox
again, and when the shard is idle. They are in `Lanes/Actors/Kernel.lean` and proved in
`Lanes/Actors/KernelSound.lean` and `Lanes/Actors/KernelTimers.lean`. Nor are the HTTP adapter's (which requests are waiting, when
one times out, when too many are pending): they are `Gate.step` in `Lanes/Http/Gate.lean`,
the one function behind the gate of `fronted sys` and of `served sys`, which `serve` runs, proved
in `Lanes/Http/FrontSound.lean` to answer each arrival at most once and in
`Lanes/Semantics/FrontLive.lean` to answer each request it admits, and model-checked in
`Tests/Gate.lean` and `Tests/Fronted.lean`.

## Assumptions the runtime makes

- **The shell passes things on unchanged.** `Kernel.exec_reachable` proves that any sequence
  of kernel operations, in any order, with any inputs, any clock readings, batches of work of
  any size and timers fired early, late, twice or never armed, leaves the kernel in a state the
  semantics can reach, and that the events it reported are a run reaching it.
  `Kernel.exec_outputs` proves the outputs it hands the shell are exactly the outputs of that
  run. The operations are the calls the shell makes (`Kernel.Op`: `input`, `advance`, `batch`),
  so the theorems are about the shell's loop as it is written, and `Kernel.exec_append` says a
  list of operations run in two parts is the same run. So no property of reachable states
  depends on the inbox, the clock or the scheduler. What is assumed is that the shell gives
  outputs to the adapter as the kernel gave them, and that an input it reports is the one that
  arrived.
- **Progress.** That a queued input is eventually handled and a pending timer eventually fires
  is not proved as a statement about time. It rests on the inbox delivering, the clock advancing
  and the shell calling the kernel again when its sleep ends, which are assumed. The kernel's
  part is proved. `Kernel.exec_wellFormed`: after any sequence of kernel operations the agenda
  holds exactly the pending timers. From that (`Kernel.WellFormed`): while a pending timer is due
  the kernel does not tell the shell to sleep (`wait_of_due`); whenever it says there is work, a
  step does some (`step_events_ne_nil`); it says to sleep until exactly the earliest pending
  deadline (`wait_for_ms`), and without limit only when no message is queued and no timer is
  pending (`wait_forever`); and it reports idle exactly then (`quiet_iff`). A timer that is due
  and a message that is queued take turns, so neither starves the other. The oldest queued
  message is delivered, or its receiver started, by the next step or the one after
  (`step_of_queued`); the exception is that the timer which went first stopped the receiver,
  whose mail the semantics drops. While a pending timer is due, a timer due no later is fired
  by the next step or the one after (`step_of_due`, `runBatch_of_due`); the exception is that
  the message which went first cancelled that timer, armed it again or stopped its actor. So a
  due timer may wait for one message, and the oldest message for one timer. No bound is proved
  for a message that is not the oldest, or from the start of a receiver to its delivery.
  Liveness theorems are stated of fair runs of the semantics (`System.Run.Fair`); that the
  runtime's runs are fair is this assumption, not a theorem. Fairness asks of a timer what the
  kernel does: one that stays pending and is not armed again fires, and one that is armed
  again starts its delay again, so a liveness theorem does not assume that a timer fires
  while its actor keeps arming it.
- **What the gate guarantees, and under what.** These are theorems about `served sys`, the
  system `serve` and `serveWith` run: `fronted sys`, the gate joined in front of `sys`, with
  requests its only inputs and responses its only outputs. *At most once* is proved. In every
  run of `served sys`, for every system, bridge and configuration, no request id is output more
  often than it was input (`Http.served_answered_le_arrived`). The environment may crash and
  restart every actor, the gate included, and may lose, reorder and duplicate messages on every
  link but one: the link from the outside world to the gate must not duplicate. `Kernel.env`
  meets that, so the theorem holds of the events the kernel reports
  (`Http.kernel_served_answered_le_arrived`). "No id is answered twice" follows when the ids that
  arrive are distinct (`Http.served_answered_nodup`). They are taken from `Http.Waiting`, which
  hands out each id once (`Http.Waiting.exec_handed_nodup`); that the server takes them from it
  as it should, and that they stay fresh across a restart, is trusted (`Lanes/Env/Http.lean`).
  A waiting request keeps its deadline armed (`Http.served_deadlines_armed`). *At least once* is
  proved of fair runs, for a request the gate has admitted: in any environment that does not
  crash the gate, an answer to a waiting request is handed over, when its deadline fires if not
  before (`Http.served_pending_leaves`, `Http.served_pending_answered`). What is assumed is that
  the runtime's runs are fair, which is the progress assumption above, and that the gate does
  not crash, which holds on one shard. That an arrival reaches the gate is not proved.
  `Tests/Gate.lean` checks exactly once on two requests of `served sys` and shows each
  precondition is needed: a reused id is answered twice, a duplicating link from outside answers
  one arrival twice, and a gate that crashes leaves a request unanswered. Each theorem is that
  of `fronted sys` (`Http.fronted_answered_le_arrived`, `Http.kernel_fronted_answered_le_arrived`,
  `Http.fronted_deadlines_armed`, `Http.fronted_pending_leaves`, `Http.fronted_pending_answered`)
  carried through the hidden inputs and outputs, so the same holds of `serveFronted` and
  `serveShard`, with the same assumptions.
- **Durability.** Without a journal, the kernel keeps actor state in memory and it is lost with
  the process. With one, the shard returns in the state the journal describes: it survives the
  death of the process and, since every write is synced before an output it allows is handed over, loss of power. Outputs handed over
  shortly before the death may be handed over again. An output counts as handed over when its
  handler was called: a handler that throws is not called again for it. A journal is a list of
  requests and means what the step functions that answered them make of it: replayed through
  changed step functions it gives another state, silently, unless the application changes the
  `system` name it opens the journal under, which makes the old file refused. `serve` adds the
  gate's configuration to that name (`ServerConfig.journalName`).
- **Environment model.** One shard stays within `Kernel.env`: reliable ordered links, no
  crashes other than an actor stopping itself. Properties proved under a stronger model than
  that do not apply to a running system.
- **Unbounded queue.** The kernel's message queue has no bound of its own. The inbox is
  bounded, which limits inputs waiting to enter, parcels from other shards among them (one
  that finds it full is dropped, as `Link.network` allows), but one input may cause any number
  of messages between actors, and those are not limited. The transport's queue to another
  process is bounded by the number of parcels, not by their size, and its queue of events is
  not bounded.
- **Cryptography.** Trusted: libsodium (the row of the C above), checked against the Lean
  references by the differential test. The references in `Lanes/Data/Sha256.lean` and
  `Lanes/Data/Hmac.lean` are pure code with nothing trusted in them, but that they compute what
  their names say is tested, not proved: SHA-256 against the NIST examples and HMAC-SHA-256
  against RFC 4231 (`Tests/Crypto.lean`). Proved: a digest and a tag are 32 bytes, hex reads back
  (`Bytes.unhex?_hex`), and `Bytes.same a b` holds exactly when `a = b` (`Bytes.same_iff`).
  Assumed: that HMAC-SHA-256 is a pseudorandom function, so that nobody without the key can make
  a tag; that is what makes a session cookie or a form token of `Lanes.Auth` unforgeable; and
  that Argon2id makes a password digest slow to guess from, at the cost the application gives
  it.

## Not trusted

Actor `step` functions, `SysState.step`, the kernel (`Kernel.run1_sound`), the model checker's
exploration of a state (`SysState.mem_successors_iff`), its search (`Check.search_sound`), what a
complete PASS of `Check.system` means (`Check.system_sound_of_respects`: for actor states whose
`==` is equality, a driver state whose `==` is an equivalence, with a matching hash, that the
driver respects, and properties that do not tell merged worlds apart; `Check.system_sound` is
the case where `==` on the driver's state is equality), what a complete PASS of a refinement
check means (`Check.refines_sound`, `Check.refines_traces`: under a monitored driver the
inputs and outputs of every run of the instance are a trace of the spec, for a spec state
whose `==` is equality),
the refinement theory and every theorem in `Lanes/` and `Examples/`: these are checked by Lean. No `sorry`, `axiom`, `unsafe` or `@[implemented_by]`
appears in them, and `@[extern]` only in the two files of the C's row.
