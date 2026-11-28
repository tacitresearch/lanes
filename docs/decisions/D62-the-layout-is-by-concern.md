# D62. The layout is by concern, and `import Lanes` is the API

Status: Accepted

Before 0.1.0, when module paths become what users copy, the repository was laid out as it grew:
`Lanes/Actors/` (removed) held 39 files and 16,000 lines of five concerns (the actor model, its proof
toolkit, the runtime, durability and the transport), the standard library sat in `Lanes/Data/`
and `Lanes/Http/` (removed) beside framework internals, a behaviour's parts were in four directories, and
IO files were in `Lanes/Env/` (removed), apart from what they serve. This decision is the layout that
replaces it. It moves files and rewrites imports only: no definition, statement or proof
changed, except one HTTP grammar (below).

## The directories

Each directory under `Lanes/` is one concern, and what performs IO is in an `IO/` directory of
its area, which `TRUSTED.md` names file by file:

- `Lanes/Core/`: the model and its meaning. `Actor`, `System`, `World` (the one step function),
  `Step` and `Run` (each event and run in closed form), joins, `Service`, `Inspect`, and the two
  schedulers. The schedulers are here, not in the runtime, because they are the semantics run by
  a seeded or a fair choice: the checker, `Outside` and the proofs of fairness use them, and
  none of them uses the kernel.
- `Lanes/Proof/`: the toolkit a proof of an application uses, and the lemmas it rests on:
  lifting per-actor invariants (`Lift`), `Monotone`, ghosts and `Past`, `SysState.Equiv`,
  deeds, loss (`Lossy`, `Loses`), what survives a join (`JoinSound`, `MapIOSound`, which is
  about `System.filterMapIO` of `Lanes/Core/Join.lean`), and the lemmas about lists, strings and
  byte arrays that were in `Lanes/Data/`. `Lossy` and `Loses` are proof rules about environment
  models and counting, not transport, so they are here and not in `Lanes/Net/`.
- `Lanes/Runtime/`: the kernel and its proofs, `Release`, batches, the inbox and its proofs
  (the shell's, not the network's), shards; the shell (`IO/Shell.lean`, which was
  `Lanes/Actors/Runtime.lean` (removed)) and the parker in `IO/`.
- `Lanes/Durable/`: the journal, snapshots, the model of the two files, the framing of a file
  (`Frame`, used only by them); the journal's files in `IO/`. `Codec` and `lanes_data` stay in
  `Lanes/Data/`: every system's messages are declared with them, and the transport and the
  HTTP layer use them as much as the journal does.
- `Lanes/Net/`: the courier and its proofs; the transport and a process with an HTTP front in
  `IO/`.
- `Lanes/Outside/`: what the outside may do (`Outside`), the home of models of external systems
  (`docs/decisions/` has the decision on them); the clock, an outside with its handler, in
  `IO/`.
- `Lanes/Web/`: `Http/` (requests and responses, their grammar, the gate, routes, cookies, the
  wire format, the server's connections), `Html/`, `Auth/`; the server and the client in `IO/`.
- `Lanes/Behaviours/`: by feature. `Server.lean`; `Jobs/` (the actor, its proofs, the pool in
  `IO/`); `Once/` (the memo and its checker monitor).
- `Lanes/Lib/`: the standard library, kept apart from the framework: `Encoding/` (Base64, JSON,
  digits), `Net/` (IP addresses, URLs), `Time/` (civil dates, formats), `Crypto/` (SHA-256, HMAC,
  `Sodium`), `Mime/` (media types), `RateLimit`. Namespaces did not follow paths before and do
  not now (`Lanes.Json`, `Lanes.Url`), so no public name changed.
- `Lanes/Data/`: what every layer uses: `Enum`, codecs and `lanes_data`, the queue, quorums.
- `Lanes/Check/`, `Lanes/Semantics/`: as they were. A part of a behaviour that needs CSLib or
  Mathlib stays in `Lanes/Semantics/` (rule 1.6), named for what it is about: the liveness of
  jobs is `Lanes/Semantics/Jobs.lean` and of the gate `Lanes/Semantics/Front.lean`. Putting them
  in the feature's directory under a name ending in `Proofs` would pass `lanes lint`, but it
  would put both layers in one directory and give two meanings to `Proofs`.

The import graph between modules has no cycle, as Lean requires. Between directories there is
one loop, and it is the system's: the journal (`Lanes/Durable/Journal.lean`) is stated over the
kernel's runs (`Lanes/Runtime/KernelSound.lean`), and the batch and the shell, in
`Lanes/Runtime/`, write the journal. So `Lanes/Durable/` sits between the kernel and the shell.
`Lanes/Lib/Net/Url.lean` imports `Lanes/Web/Http/Basic.lean` for percent-encoding, a stdlib
module depending on the web layer, which moving those functions would undo; that is a move of
definitions, left for its own change.

## `import Lanes` and `import Lanes.Proofs`

`import Lanes` is the API: the modules an application's code runs and its proofs use, with the
proof toolkit. The framework's soundness theorems, the 24 `…Sound` modules and the kernel's
timers, are `Lanes.Proofs` (`Lanes/Proofs.lean`), which `Lanes.Semantics` imports, so a proof
that imports the proof layer has them as before. A test or a proof that cites one and imports
only `Lanes` imports `Lanes.Proofs` too; four tests needed it. `lanes lint` treats
`Lanes.Proofs` as a proof module, so executable code cannot import it, which it never needs.

What `import Lanes` brings is 98 modules and 29.8 MB of `.olean` instead of 116 and 42.2 MB.
Some soundness modules stay in it because API modules import them (the journal is stated with
`Lanes/Runtime/KernelSound.lean`). The time to import it did not change measurably: about 0.8 s,
as `import Std` alone takes, since Lean maps `.olean` files and reads what it uses.

## One HTTP grammar

Tokens, `OWS` and the characters of a field value were defined in the wire format and again
in media types, which had its own quoted string. They are now one module,
`Lanes/Web/Http/Grammar.lean`, used by the wire format, cookies and media types; the one proof
that read media types' copy of `tchar` goes through `MediaType.tokenChar_eq`. Cookies keep
their own trimming of a `Cookie` header (`trimBlank`, by `Char.isWhitespace`), which removes
more than `OWS` does: replacing it would change what is read, so it is not a copy.
