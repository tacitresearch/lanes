# D?. The gate before the shard

Status: Accepted

`Lanes/Web/Http/Admit.lean`, `Lanes/Web/Http/AdmitSound.lean`, `Lanes/Web/IO/Server.lean`,
`Lanes/Web/Http/Loopback.lean`, `Lanes/Web/Http/JournalName.lean`. This carries out clause 2 of
the default runtime in `docs/decisions/D96-runtime-contract.md`: the gate is off the hot path,
with a theorem that the answers are those of the gate in the system. Issue #106, its fourth item.

## What changed

The gate was an actor of the system `serve` runs (`served sys`, D43). Every request went through
it twice, on arrival and on its answer, so it was one serial point for the whole application: a
wave of steps in parallel (D64) always had the gate in it, and a runtime of objects would have had
one object for every request.

The gate's decisions were already a pure function, `Gate.step`, that does not know where it
sits. The server now makes them itself, before the shard:

- **On arrival**, under the lock of its table of waiting requests (`Http.Waiting`), it takes an
  id, decodes the request and lets the gate decide (`Gate.admit`, which is `Gate.step` on an
  arrival with `decode` done first). A refusal (`503` at `maxPending`, or `decode`'s answer) is
  written at once and nothing reaches the shard. An admitted request is handed to the shard
  under the same lock, so that the inbox's `503` leaves the gate's state as it was.
- **On an output**, on the shard's thread, `encode` reads it and the gate decides under the lock
  (`Gate.receive`). An answer to a request that is no longer waiting is dropped.
- **On a deadline**, the server's ticker, which already looks at every connection each
  `tick_ms`, hands the gate each request whose deadline has passed; the gate answers `504`.

The shard runs `admitted sys` (or `admittedFronted sys` for `serveFronted`): `sys` itself, with
no actor that every request goes through. `Loopback` does the same, without a socket.

## What is proved

`Lanes/Web/Http/AdmitSound.lean`:

- **The front with the shard is the gate in the system.** `Http.Front.World` is the server as a
  transition system: the front's waiting list, its armed deadlines and its answers not yet
  written, beside a state of `admitted sys` under the kernel's environment. Every run of it from
  its start is a run of `served sys` from its start, under `Http.Front.servedEnv`, with the same
  requests arriving and the same answers handed over in the same order
  (`Http.Front.World.refines`). The relation (`Http.Front.Rel`) says the gate's waiting list and
  deadlines are the front's, the application's actors have the same states, timers and messages
  in flight, and the answers on their way to the gate are the shard's outputs the front has not
  yet taken. `servedEnv` is the kernel's environment, but for one link kind: the gate takes the
  system's answers in any order, as the front takes the shard's outputs.
- **The gate's three theorems.** No request is answered more often than it arrived: of the server
  through the refinement (`Http.Front.World.answered_le_arrived`, from
  `Http.served_answered_le_arrived`), and of the front alone over any messages
  (`Http.Front.run_answered_le`). The waiting list stays within `maxPending` and free of repeats
  (`Http.Front.run_bounded`, from `Gate.step_bounded`). Every waiting request is answered, if every
  deadline that stays armed is eventually handed to the gate (`Http.Front.pending_answered`); the
  ticker is trusted to do that. And a refusal leaves the waiting list as it was
  (`Gate.admit_refused`), which D97 asked for.

Trusted (`TRUSTED.md`, the server's row): that the server does what `Gate.step` decides, as
`Front.World` models it, and that the shard's `decode` of an admitted request gives what the
gate's did, which holds because both call the same pure function.

The proof is a simulation over the semantics' own states, not over CSLib's `LTS`: what it needs
of the semantics is `SysState.step` in closed form (`Lanes/Core/Step.lean`) and the list lemmas of
`Lanes/Proof/List/Erase.lean`, and its conclusion is a run of `served sys`, to which every
theorem about `served sys` applies.

## The journal

The journal is the shard's inputs: the requests the gate admitted, as `(id, request)`, in the
order it admitted them. Its entries are those of before; it no longer holds the requests the gate
refused. A replay reads none of the gate's settings: they leave the journal's name, and
`Http.regateUpgrade` is gone. A journal is named `Http.admittedName` of the application's
`system`, not the application's name alone, so that a journal of the server from before D43,
which was named so, is still refused; a journal written while the gate was an actor
(`Http.journalName`) is refused, saying why, and left as it was. It cannot be carried across: a
`Migration` maps every output, and the old system's outputs are responses, which the new one's
are not.

D97 (3.4) planned an entry `expire id`, so that a replay would rebuild a waiting list the shard
holds. Here the waiting list is the front's and the shard never holds it: an expiry changes
nothing the shard does, so nothing about it is journalled. After a restart the front starts empty;
the requests that were waiting had their connections in the process that died.

## What remains for D97's decoded inputs

The journal has no codec for `σ.In` yet, so the admitted request goes to the shard as the
prepared `Request` and the shard decodes it again (`admitInput`); one that no longer decodes, at
a replay through a newer `decode`, goes to `sink`, an actor that does nothing. When D97 3.4
lands:

- the entry becomes `(id, x)` with `x : σ.In` written by the application's codec, the server
  hands the shard the `x` the gate decoded, and `admitInput` and `sink` go: the shard's system is
  `sys` with inputs `σ.In`;
- `Front.World.act`'s `forward` carries `x`, and `Front.World.refines` keeps its statement with
  `admitted_accept` replaced by `sys.accept x`;
- the journal's name loses its suffix once the manifest names the format.

## Measured

`benchLanes` (`bench/LanesHello.lean`), before (main) and after, alternating on the same CPUs:
the server on two, the load generator on two, three runs of 10 s at each number of connections.
The machine is a 4-core container shared with other work, so these show a direction only.

Connections on Lean's task threads (`ioThreads := 0`, as `benchLanes` runs them):

| conns | | req/s (median, low–high) | p50 µs | p99 µs | CPU µs/req |
| ---: | --- | ---: | ---: | ---: | ---: |
| 1 | before | 6,043 (5,959–6,049) | 154 | 533 | 142 |
| 1 | after | 6,328 (5,912–7,415) | 145 | 339 | 127 |
| 16 | before | 19,437 (19,351–20,601) | 741 | 3,258 | 70 |
| 16 | after | 18,671 (18,120–19,697) | 754 | 2,644 | 72 |
| 64 | before | 22,813 (21,337–26,555) | 2,726 | 6,346 | 64 |
| 64 | after | 19,552 (19,168–19,618) | 3,167 | 7,937 | 69 |

On two threads of the server's own (`io=2`):

| conns | | req/s (median, low–high) | p50 µs | p99 µs | CPU µs/req |
| ---: | --- | ---: | ---: | ---: | ---: |
| 1 | before | 6,007 (5,612–6,859) | 140 | 362 | 134 |
| 1 | after | 5,915 (5,758–5,923) | 159 | 317 | 150 |
| 16 | before | 20,263 (19,376–20,332) | 698 | 2,360 | 72 |
| 16 | after | 19,511 (12,867–19,725) | 763 | 1,933 | 77 |
| 64 | before | 23,167 (20,610–23,720) | 2,449 | 6,738 | 62 |
| 64 | after | 20,241 (11,090–23,005) | 2,960 | 7,615 | 55 |

At one connection the two are the same within the spread. At 16 and 64 the medians are lower
after, by 4% and by 11–13%, with ranges that overlap; four more runs of 5 s at 64 connections
gave 90,280 and 100,757 requests before and 87,983 and 110,139 after. The load average of the
machine was 2 to 6 during the runs. The warm machine (`bench/README.md`) is where this is to be
measured again.

On one shard the serial point is not what limits a request: the shard's thread runs one step a
request instead of three, and the server's lock is taken as often as before, now with the gate's
decisions inside it. What this buys is that steps of different requests no longer share an actor,
which waves (D64) and a runtime of objects need; the benchmark of mixed step costs that decides
on waves as the default (D96) measures that.
