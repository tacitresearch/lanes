# Tutorial

Fifteen minutes from `lanes new` to a change that is model-checked and proved. You need some
programming, not much Lean. Install what the quick start in `README.md` lists first: elan and
a C compiler.

The code of each step is kept in `Tests/Tutorial/`: `lake build` compiles it, and `lake test`
fails if this page quotes anything but that code and what the checker prints for it.

## 1. Make an app and run it

```bash
git clone https://github.com/tacitresearch/lanes
cd lanes
lake exe lanes new tut --dir ../tut
cd ../tut
lake exe cache get   # prebuilt Mathlib, once: 500 MB to fetch, 7.5 GB on disk
lake test            # the first time builds Lanes and the app (minutes), then checks and proves
lake exe tut         # serves http://127.0.0.1:8080; Ctrl-C stops it
```

`lake test` prints `PASS (complete): every reachable state explored`, and ends with `2 passed, 0
bounded, 0 failed`: the model check and the proofs. Open the page and press "Add one", or ask
from another terminal:

```bash
curl -X POST http://127.0.0.1:8080/increment
```

```html
<div id="counter"><p>Count: 1</p><button hx-post="/increment" hx-target="#counter" hx-swap="outerHTML">Add one</button></div>
```

The app is four files. `Tut/Counter.lean` is the logic, `Main.lean` the web page and the
server, `Check.lean` the model checks, and `Tut/Proofs.lean` the theorems. Nothing imports the
theorems but `lake build`, so a broken proof stops neither the checks nor the server.

**A step is pure.** The counter's logic is `service` in `Tut/Counter.lean`: given the count and
a request, it returns the new count and the responses. It cannot read a clock, a file or a
socket. The server around it does that, so the same function runs in the server, in the checker
and in the proofs.

## 2. Change the counter: take one away

Add a request to `Tut/Counter.lean`:

```lean
lanes_data inductive Request where
  | increment (req : ReqId)
  | decrement (req : ReqId)
  | read (req : ReqId)
  deriving DecidableEq, Repr, Hashable
```

and what it does, in `service`, after the `increment` case. It is refused at zero, as an
increment is refused at the limit:

```lean
    | .decrement req =>
      if 0 < count then (count - 1, [⟨req, count - 1, true⟩])
      else (count, [⟨req, count, false⟩])
```

The count is a `Nat`, and on a `Nat` `0 - 1` is `0`: without the `if`, a decrement at zero
would answer that it was applied, and Lean would not complain. Step 3 shows what does.

In `Main.lean`, add a route to `namespace Routes`, a line after the increment's in `bridge`
(which turns an HTTP request into a `Request`), and a button. Replace `CounterView` with one
whose message says which bound refused the request:

```lean
def decrement : Http.Route Unit := .post (.seg "decrement")
```

```lean
      Routes.increment.handle fun () _ => .ok (.increment id),
      Routes.decrement.handle fun () _ => .ok (.decrement id)
```

```lean
def refusal (response : Response) : String :=
  if response.value == 0 then "The counter is at zero." else "The counter is at its limit."

def CounterView (response : Response) : Html :=
  <div id="counter">
    <p>{s!"Count: {response.value}"}</p>
    {if response.applied then Html.empty else <p class="error">{refusal response}</p>}
    <button {Hx.request Routes.increment ()} {Hx.target "#counter"} {Hx.swap .outerHTML}>
      "Add one"
    </button>
    <button {Hx.request Routes.decrement ()} {Hx.target "#counter"} {Hx.swap .outerHTML}>
      "Take one"
    </button>
  </div>
```

Without the case in `service`, `lake build` stops with `Missing cases: (Request.decrement _)`.
Without the line in the bridge it builds, and the button gets `not found`. Run `lake build`,
then `lake exe tut`, and take one away from zero:

```bash
curl -X POST http://127.0.0.1:8080/decrement
```

```html
<div id="counter"><p>Count: 0</p><p class="error">The counter is at zero.</p><button hx-post="/increment" hx-target="#counter" hx-swap="outerHTML">Add one</button><button hx-post="/decrement" hx-target="#counter" hx-swap="outerHTML">Take one</button></div>
```

The code of this step is `Tests/Tutorial/Counter.lean` and `Tests/Tutorial/Main.lean`.

## 3. Check a property, and break it

**The checker explores every order and fault.** `Check.lean` runs the counter with a limit of 2
on four requests. It sends them in every order and follows every state the system can reach:
each request waiting, taken or answered, and, once you allow it, the actor crashing and
starting again. Each property is tested in every one of those states. An `always` must hold in
all of them. A `sometimes` must hold in at least one, so a check that never reaches the
interesting states fails instead of passing.

In `Check.lean`, send a decrement in place of the read:

```lean
def requests : List Request :=
  [.increment 1, .increment 2, .increment 3, .decrement 4]
```

Then replace the scenario and the properties, from `{ driver` to the closing `]`. This lets
the actor crash once, says that a request is refused only at a bound, and gives each refusal
its own witness, since a refused decrement now meets the old `!·.applied` too:

```lean
    { driver := (service { limit := 2 }).monitored (Driver.anyOrder requests)
      env := { mayCrash := fun _ => true }
      maxCrashes := 1 }
    [ Check.refines "every response is allowed by the spec",
      .always "the counter never exceeds its limit" fun w => w.state.state () ≤ 2,
      .sometimes "the counter reaches its limit" fun w => w.state.state () == 2,
      .sometimes "an increment is refused" fun w =>
        w.state.outbox.any fun r => !r.applied && r.value == 2,
      .always "a request is refused only at zero or at the limit" fun w =>
        w.state.outbox.all fun r => r.applied || r.value == 0 || r.value == 2,
      .sometimes "a decrement is refused" fun w =>
        w.state.outbox.any fun r => !r.applied && r.value == 0 ]
```

Each property is a function of a state of the search, `w`. `w.state.state ()` is the count
held by the one actor, whose name is `()`, and `w.state.outbox` the responses not yet sent.
`lake test` prints the checker's report, then a line for the check and one for the proofs,
`ok (check) …` and `ok (proof) the proofs`, and `2 passed, 0 bounded, 0 failed`. The report:

```text
PASS (complete): every reachable state explored
reached "the counter reaches its limit" in 5 steps
reached "an increment is refused" in 7 steps
reached "a decrement is refused" in 3 steps
states: 5696, transitions: 14066, depth: 15
coverage: output 7387, input 2339, deliver 1860, crash 1315, start 1165, drop 0 (never fired), duplicate 0 (never fired), timeout 0 (never fired)
```

Now seed a bug. In `service`, write `1 <` for `0 <`, so that a decrement at one is refused:

```lean
      if 1 < count then (count - 1, [⟨req, count - 1, true⟩])
```

`lake test` fails. The report gives the shortest run that breaks the property, and a line
after it, `FAIL (check) the counter, with a limit of 2 and four requests`, says what failed:

```text
FAIL: "a request is refused only at zero or at the limit" is violated after 5 steps
  1. input increment 1
  2. start ()
  3. deliver outside → (): increment 1
  4. input decrement 4
  5. deliver outside → (): decrement 4
  state reached:
  () [up] 1
  pending output: { req := 1, value := 1, applied := true }
  pending output: { req := 4, value := 1, applied := false }
reached "the counter reaches its limit" in 5 steps
reached "a decrement is refused" in 3 steps
states: 167, transitions: 223, depth: 5
coverage: input 134, start 40, crash 23, deliver 19, output 7, drop 0 (never fired), duplicate 0 (never fired), timeout 0 (never fired)
```

Read it as a story. A client sends `increment 1`. The actor starts (every start, the first
too, goes through its recovery) and takes it: the count is 1.
Then `decrement 4` arrives and is refused at 1. The state reached shows the count and the two
answers not yet sent. Put `0 <` back and the check passes again. `lake test` exits with 1 on a
`FAIL`, so CI stops on it, and with 2 on `PASS (bounded)`: a search that hit a bound covered
only part of the instance, which is not a pass. `lake test -- --json` prints the same results as
one JSON object, each with its kind (`check` or `proof`), for a program to read.

The checks catch the bug of step 2 as well: with no `if` at all, no decrement is ever refused,
and `lake test` prints `FAIL: never reached: "a decrement is refused"`. Faults find bugs too:
with `env := { link := fun _ _ => .network }`, a link that loses and repeats messages, the
checker finds an increment delivered twice and counted twice. That is why `implements` in
`Tut/Proofs.lean` assumes an environment that does not repeat messages (`env.Faultless`).

The code of this step is `Tests/Tutorial/Check.lean`, where `buggy` is the bug.
`Tests/Tutorial.lean` checks that the two outputs above are what the checker prints.

## 4. Prove it for every run

**A proof covers every run.** The check covered a limit of 2, four requests and one crash. The
first two theorems of `Tut/Proofs.lean` cover every limit, every sequence of requests and every
fault:

```lean
/-- The counter never exceeds its limit. -/
theorem counter_le_limit (config : Config) :
    (Server.actor (service config)).Invariant fun count => count ≤ config.limit := by
  actor_invariant [Server.actor, service]

/-- In every reachable state of the system, under any environment model. -/
theorem system_le_limit (config : Config) (env : EnvModel sig) :
    (system config).Invariant env fun c => c.state () ≤ config.limit :=
  System.invariant_of_actor (system config) () (counter_le_limit config) env
```

`actor_invariant` proves the first by induction: the property holds at the start, every message
keeps it, and recovery keeps it. It splits on the message, unfolds the definitions in brackets,
and closes each case with `grind`, which splits the `if`s and does the arithmetic. You did not
touch it in step 2: `lake test` proved it again with the `decrement` case. The second theorem
lifts what one actor keeps to the whole system, in every environment.

A case `actor_invariant` cannot close is left as a goal. Write `≤` for `<` in the increment.
`lake test` runs the checks, which find the counter past its limit, then builds the proofs,
which fail with `FAIL (proof) the proofs`, and prints Lean's message (after a long `trace:` line
with the command it ran):

```
error: Tut/Proofs.lean:17:2: unsolved goals
case refine_2.increment
config : Config
s✝ : Nat
h✝ : s✝ ≤ config.limit
req✝ : ReqId
⊢ (if s✝ ≤ config.limit then (s✝ + 1, [{ req := req✝, value := s✝ + 1, applied := true }])
      else (s✝, [{ req := req✝, value := s✝, applied := false }])).fst ≤
    config.limit
```

Read the goal: the count `s✝` is at most the limit (`h✝`), and after an increment it must
still be. At `s✝ = config.limit` it is not. A `✝` marks a name Lean made up.

**The axiom gate.** A theorem proves what it states only if nothing under it was assumed.
`#print axioms` lists the axioms a theorem rests on, through every lemma it uses. Lean's three
standard ones are expected. A `sorry` anywhere below shows as `sorryAx`, and an `axiom`
someone declared shows by its name. `#guard_msgs` turns any other list into a build error. Add
a gate for each headline theorem at the end of `Tut/Proofs.lean`:

```lean
/-- info: 'Tut.system_le_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tut.system_le_limit

/-- info: 'Tut.implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tut.implements
```

Now put `sorry` in place of `actor_invariant [Server.actor, service]`. The proof of
`counter_le_limit` is only a warning, but the gate of `system_le_limit`, which rests on it,
fails:

```
warning: Tut/Proofs.lean:15:8: declaration uses `sorry`
info: Tut/Proofs.lean:36:15: 'Tut.system_le_limit' depends on axioms: [propext, sorryAx, Classical.choice]
error: Tut/Proofs.lean:36:0: ❌️ Docstring on `#guard_msgs` does not match generated message:

- info: 'Tut.system_le_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
+ info: 'Tut.system_le_limit' depends on axioms: [propext, sorryAx, Classical.choice]
```

`lake test` fails on the `sorry` even without a gate: it builds the proofs with warnings as
errors (`Testing.build`), and a `sorry` is a warning. The checks still run first, since
`Check.lean` does not import the proofs. `lake exe lanes lint` reports the `sorry` too
(`no-sorry`). Lanes keeps its own gates in `Tests/Axioms/`.

The code of this step is `Tests/Tutorial/Proofs.lean`: the theorems and the gate.

## 5. Where next

`docs/TUTORIAL-WEB.md` is the sequel: a web app with sign-in, uploads to S3, a test of the
whole site, and how to run it.

Then read the examples in the order `examples/README.md` gives:

1. `examples/counter`: what `lanes new` wrote, which you now know.
2. `examples/bank`: actors that send each other messages, an invariant of the whole system,
   and the checker finding the credit a lossy link drops.
3. `examples/bank-web`: the bank behind a web page.
4. `examples/kv-cache`: a store checked against a five-line spec, and a cache that breaks it.
5. `examples/watchdog`: what fairness says.
6. `examples/todo-db`: state that outlives the process, in PostgreSQL.
7. `examples/rookery`: the serious system.

The rules your app's `AGENTS.md` points to are in `AGENTS.md`, sections Design, Code and Proofs.
