# D?. The environment, signals and randomness, as platform models

Status: Accepted

`docs/decisions/D110-volatile-actors.md` puts the platform models in the core: the clock,
randomness, environment variables and configuration, the file system, network and DNS, signals
and shutdown, standard input and output. Issue #245 lists those still missing; the clock and the
file system (`docs/decisions/D117-file-system-model.md`) are done. This decision takes the rest,
each weighed by rule 1.8, in the order of what they give.

## The environment and configuration

Rule 2.5 says a program reads its configuration once, at start, into one `Config`. Lanes gave no
help to do so: each `main` read `IO.getEnv` by hand, parsed each number itself, and stopped at
the first bad value, so a deploy with three mistakes took three restarts to find them. A
password read that way is printed by any `Repr` of the `Config` that holds it.

**The model** (`Lanes/Outside/Environment.lean`) is `Vars`: any list of variables and values. A
variable set to the empty text counts as unset, as most programs read it, and as `S3.credentialsOf?`
and the AWS chain already did. The model allows everything, so it has no oracle; what is in it is
the reader.

**The reader** is `Environment.Reader α`, data that says which variable it asks for and what it
does with each answer (a free monad: `pure`, `ask`, `problem`). An application writes it with
`do`:

```lean
def config : Environment.Reader Config := do
  let host ← get "LANES_HOST" "127.0.0.1" (doc := "The address to listen on.")
  let port ← need "PORT"
  let password ← secret "DB_PASSWORD"
  let workers ← get "WORKERS" 4
  check (0 < workers && workers ≤ 64) "WORKERS" "must be from 1 to 64"
  return { host, port, password, workers }
```

`get` has a default, `need` must be set, `opt` may be unset, `secret` and `secret?` read a
`Secret`, and `check` refuses a combination. Values are parsed by the class `Value` (text, whole
numbers, integers, ports, booleans, lists separated by commas, and `Value.oneOf` for a choice of
names). A variable the reader cannot read is recorded as a problem and replaced by a stand-in (its
default, or `Inhabited`'s), and the reader goes on, so `read` and `Environment.load` give every
problem at once. That is the reason for a stand-in over stopping: `do` needs a value to go on
with, and an applicative reader, which needs none, cannot be written with `do`. The price is that
a variable read only because of an earlier one's value may be asked, or not, because of the
stand-in; the run fails either way, and the real problem is listed first.

Proved (`Lanes/Outside/Environment.lean`, gate `Tests/Axioms/Outside.lean`):

- `Reader.run_bind`: a reader's problems are those of its first part and then of the rest,
  whatever the first part found. Nothing found is dropped.
- `Reader.run_congr`: two environments that agree on the variables a run asks give the same run.
  A reader reads nothing else, so the configurations an application can have are the values of
  the variables `describe` lists, and a test or the checker runs it under each by giving `Vars`.
- `secret_problems`, `field_secret_problems`: a secret's problem is `unset` or `hidden`; neither
  its value nor what its parser said of it is kept. A `Secret` prints as `<secret>`
  (`Secret.toString_eq`), so a `Config` that holds one may derive `Repr` and be logged; `reveal`
  is the one way to the text.

`describe` lists every variable a reader asks when none is set, with its text, its default and
whether it is required or secret, for a deploy's documentation or a `--help`.

**The binding** (`Lanes/Outside/IO/Environment.lean`) runs the same interpreter as the model,
`Reader.runM`, in `IO` with `IO.getEnv`. Lean cannot list the environment, which is why the
reader is data that names each variable as it asks for it. `load` throws one error, a problem a
line.

**One `Secret`.** SigV4 and OAuth each had a `Secret` of their own, one with `reveal`, one with
`value`. They are now `Lanes.Secret` (`Lanes/Data/Secret.lean`, the lowest package, so that the
environment's model can use it), with `reveal` (rule 1.7).

**What it does not replace.** `Postgres.Settings.read` follows libpq: a connection string, then
a service file, then libpq's variables, then the deploy's, with a password file whose mode is
checked. That precedence over files is libpq's and is tested against it; the reader models
variables only, and rewriting it would change nothing a user sees. `Aws.Credentials.origin` and
`S3.credentialsFromEnv` already read the variables they name once into a lookup and decide
purely (`Imds.chain`, `S3.credentialsOf?`). Each could become a `Reader` later for `describe`
and the error list; that is a migration, not a design change. The `main`s of the template and the
examples, which read `LANES_HOST`, `LANES_IDLE_MS` and `LANES_DRAIN_MS` by hand, are the ones to
move first, with the template.

Reach against total cost (rule 1.8). Reach: every deployed program reads its environment; the
reader gives typed values, every problem at once, secrets that cannot be printed by accident,
documentation of the variables for free, and configurations a test can enumerate. Cost: a pure
module with its proofs and a binding of a few lines, trusted and listed; a newcomer learns `get`, `need`, `secret` and `load`. Non-users pay nothing: the core
does not call it.

## Signals and shutdown

What the process may be told: SIGTERM or SIGINT, by a supervisor or a shell, at any time. When it
may die: at any time, by SIGKILL, a loss of power or the watchdog (D121), which the semantics
already covers as a restart (`EnvModel.mayRestart`, D110). So the model of signals has one job:
the stop that a caught signal starts must lose nothing it took.

Most of it existed: `Server.stopOnSignal` (D69's amendment, D70's) drains and stops, through
`Std.Async`'s signal waiters, which are Lean's runtime over libuv and need no C of Lanes, and
`Tests/Ops.lean` sends a child process a real SIGTERM. What was missing:

- **The decision was made in IO** (rule 3.9): when to stop draining. It is now `Http.Shutdown.step`
  (`Lanes/Web/Http/Shutdown.lean`), pure, with its phases (`serving`, `draining deadline_ms`,
  `stopping`) and events (a signal, a look at the requests in flight). Proved: the server stops
  only when nothing is in flight or the deadline has passed (`Shutdown.step_stop`), so a request
  whose answer comes before the deadline is answered by the system; it stops at the first look
  at or past the deadline (`Shutdown.step_deadline`), `drain_ms` after the signal
  (`Shutdown.step_signal`); and once (`Shutdown.step_stopping`). With the gate's theorems
  (`Http.served_pending_answered`), every request the server admitted is answered: by the
  system, `504` at its own deadline, or `503` at the stop, which `Server.stop` writes to every
  waiter (trusted, as the server is). `Server.stopOnSignal` now performs what `step` says.
- **A process without a server** could not stop on a signal. `Runtime.stopOnSignal`
  (`Lanes/Runtime/IO/Signal.lean`) waits for SIGTERM, SIGINT or the runtime's end, and stops it:
  `Runtime.stop` takes no more inputs and returns once every input it took has been taken by its
  actor (D116). Both use `awaitStopSignal`, which lets the waiters go after the first signal, so
  a second ends the process at once, as an operator who presses Ctrl-C twice expects.

The listener stays open while the server drains, and closes at `stop`. A load balancer may send
a request in the moments before it reads readiness's `503`, and a closed port would refuse it;
the deadline bounds the drain however many arrive.

Reach against total cost: every server and worker is stopped by its supervisor, and losing the
requests in flight on each deploy is the common failure. Cost: a small pure machine and
short theorems; a little trusted IO, most of it the code that was in `Server.stopOnSignal`; no new concept for a user, who still ends `main` in
`stopOnSignal`.

## Randomness

No model of its own is needed, and none is added. D121 tells each step a `seed`, and every
theorem about a step quantifies over its context (`actor_invariant`, `Monotone.step`), so the
model of the seed is already the weakest one: any `UInt64`. A proof holds for every seed the
runtime could give; the checker explores the seeds a scenario's moments list
(`Scenario.moments`). The runtime draws them from a SplitMix64 generator per worker, seeded from
`IO.getRandomBytes` (`Lanes/Runtime/IO/Shell.lean`); that generator stays private, since nothing
may depend on which seed comes.

For pure code that needs more than 64 bits of choice, Lean's own generator is enough:
`mkStdGen ctx.seed.toNat` and `randNat`, as the checker's random runs use it. A key, a token or
a nonce is never made from the seed: it is 64 bits, recorded in the trace when `Config.record`
is on, and SplitMix64 is not a cryptographic generator. Such a value comes from
`IO.getRandomBytes` (`Crypto.randomBytes`, `Lanes/Lib/Crypto/Native.lean`), in an adapter or at
start, and enters the system as an input or in its `Config`.

## Network and DNS, standard input and output: assessed, left for later

**Network and DNS.** A model would say what a connection may do: resolution that fails or
answers several addresses, a connect refused or timed out, a reset, a write accepted in part, a
peer that half-closes. It would let the proofs of `Http.Conn.step` and of PostgreSQL's
`Conn.step` speak of the socket under them, and the checker explore those faults in the client
loops. Today those loops are trusted IO (`Lanes/Web/IO/Client.lean`,
`Lanes/Services/Postgres/IO/Client.lean`); what a caller sees is already modelled one level up,
as a call whose answer may be unknown (`Rpc`), and the connections' pure parts are told a broken
socket as an event (`Conn.Event.broken`). Cost: a model of byte streams with faults, a binding
of `Std.Net`'s errors to it, and an oracle that injects faults into a real kernel's sockets (a
proxy such as toxiproxy in CI). The gain is in code that stays trusted either way until the
loops themselves are written as pure machines over the model. Later, with that rewrite.

**Standard input and output.** A model would be a stream of bytes in that may end, and one out
whose writes may fail (a closed pipe). It would serve command-line programs and filters. Lean's
`IO.FS.Stream` already lets a test hand a program a buffer for each (`IO.FS.Stream.ofBuffer`),
and a program's logic over lines is pure without help. A model adds little over that; it is left
until a command-line program's proof needs it.
