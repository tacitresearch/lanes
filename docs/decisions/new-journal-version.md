# D?. A served journal is versioned by the application's name; the gate's settings are read from it

Status: Accepted

A review found that `Http.serve` refused its own journal when a gate setting changed:
`ServerConfig.journalName` adds the gate's `requestTimeout_ms` and `maxPending` to the
application's `system`, and a journal under another name is refused. Raising a timeout took the
site down at its next start. The question was why the gate is in the name, and whether it has
to be.

## The gate's settings change what a replay gives

They do, when the gate was full. The evidence:

- A journal holds the inputs and the clock's readings, not what the step functions answered
  (D24). A timer is due at a reading plus the delay its step function gave (D36).
- The gate is an actor of the system the journal replays (`served sys`, D43). It arms
  `after requestTimeout_ms (expire id)` for each request it admits (`gateActor`,
  `Lanes/Web/Http/Front.lean`), and a request leaves its waiting list when it is answered or
  expires.
- `Gate.step` answers an arrival `503` when `maxPending` requests are waiting, and only an
  admitted arrival is passed to the system (`Lanes/Web/Http/Gate.lean`).

So, replayed behind another gate, a request that found the gate full may find room: under a
larger `maxPending`, or a shorter timeout that leaves fewer waiting. The system then applies a
request its client was told was refused. The other way, a request the system took may be
refused, though its client has its answer. In both cases the replay gives another state. When
the gate never filled, the replay is the same. The name has to say which gate wrote the
journal; D36 found the same for raft-kv's timeouts.

## What is done

- **`ServerConfig.system` is the stated version of the application's step functions.** A
  journal under another `system` is refused, as before. The message now says that `system`
  names the step functions a journal is replayed through, and that the way on is to run the
  version that wrote it or to move the journal and its snapshot aside. `serve` still takes no
  upgrade of the application's own types (D66, "Not done").
- **The gate's settings stay in the name, and a journal of another gate is read.** The name's
  text is unchanged (`Http.journalName`), so every journal written so far reads as before.
  Before it opens its journal, `serve` reads the name in its header. When it is the same
  application behind another gate (`Http.formerGate`, from `Http.gateOf`), `serve` opens the
  journal with one `Journal.Upgrade` (`Http.regateUpgrade`). Its old system is
  `served sys bridge old`, so D66's start replays the journal behind the gate that wrote it and
  gets the kernel the old process had. Then it carries that kernel to the new gate as it is
  (`Http.regate`), saves it under the new name and begins the journal at that mark. Every
  theorem of D66 covers it: wherever the process dies, the next start gives the same kernel
  (`Upgrade.begin_crash`). No file format and no theorem changed.
- An upgrade saves a snapshot, so it needs `serve`'s `saving`. Without it the start is refused,
  with a message that names both gates and says to give `saving` or set the gate back.
- `regate` claims nothing of the states after (`inv` is `True`). As after any migration (D66),
  the gate's theorems about runs from boot are not claimed for the run that follows. The
  waiting list may be longer than a lowered `maxPending` until it drains; the gate refuses new
  arrivals meanwhile.

`Tests/Web.lean` writes the bank's journal behind one gate, starts it behind another, and finds
the balances carried across and the journal renamed; without `saving` the start is refused with
that message.

## Alternatives

- *Take the gate's settings out of the name*, as the review suggested. Rejected: a replay behind
  another gate can apply a request that was refused, as above.
- *Journal the gate's decisions*, so that a replay does not read its settings. Rejected for
  now: it changes the journal's format and the gate's system, and with them the gate's
  theorems.
- *Snapshot at drain*, so that a deploy replays nothing. Rejected, as D66 rejected it: there is
  no clean shutdown (rule 3.3), and a start after a crash still replays a tail.
- *A version number beside the name* (`Journal.Store.version`). Not needed here: `system` is
  already the application's version, and the gate's part is read from the name.

## Not done

- An inductive invariant for the gate across `regate`, such as a waiting list without repeats
  within the larger of the two bounds, so that the gate's theorems carry over.
- `serve` with upgrades of the application's own types (D66).
- `serveFronted` and `serveShard` callers open their own stores; raft-kv still names its journal
  with its gate and refuses a journal of another gate.
