# Tutorial

Fifteen minutes from `lanes new` to a change that is model-checked and proved. You need some
programming, not much Lean. Install what the quick start in `README.md` lists first: elan, a C
compiler, libsodium and pkg-config.

The code of each step is kept, compiled and run by `lake test`, in `Tests/Tutorial/`, so this
page cannot drift from what Lanes does.

## 1. Make an app and run it

```bash
git clone https://github.com/tacitresearch/lanes
cd lanes
lake exe lanes new tut --dir ../tut
cd ../tut
lake exe cache get   # prebuilt Mathlib, once: 500 MB to fetch
lake test            # the first time builds Lanes and the app (minutes), then runs the checks
lake exe tut         # serves http://127.0.0.1:8080; Ctrl-C stops it
```

`lake test` ends with `PASS: every reachable state explored`. Open the page and press "Add
one", or ask from another terminal:

```bash
curl -X POST http://127.0.0.1:8080/increment
```

```html
<div id="counter"><p>Count: 1</p><button hx-post="/increment" hx-target="#counter" hx-swap="outerHTML">Add one</button></div>
```

The app is four files. `Tut/Counter.lean` is the logic, `Main.lean` the web page and the
server, `Check.lean` the model checks, and `Tut/Proofs.lean` the proofs that need Mathlib.

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
  deriving DecidableEq, Repr, Hashable, Codable
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

In `Main.lean`, a route, a line in the bridge that turns the route into the request, a button,
and a message that says which limit refused it:

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

`lake test` prints:

```text
PASS: every reachable state explored
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

`lake test` fails, and prints the shortest run that breaks the property:

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

Read it as a story. A client sends `increment 1`. The actor, `()` because there is one, starts
(every actor starts through its recovery, even the first time) and takes it: the count is 1.
Then `decrement 4` arrives and is refused at 1. The state reached shows the count and the two
answers not yet sent. Put `0 <` back and the check passes again. `lake test` exits with 1 on a
`FAIL`, so CI stops on it.

The checks catch the bug of step 2 as well: with no `if` at all, no decrement is ever refused,
and `lake test` prints `FAIL: never reached: "a decrement is refused"`. Faults find bugs too:
with `env := { link := fun _ _ => .network }`, a link that loses and repeats messages, the
checker finds an increment delivered twice and counted twice. That is why `implements` in
`Tut/Proofs.lean` assumes an environment that does not repeat messages (`env.Faultless`).

The code of this step is `Tests/Tutorial/Check.lean`, where `buggy` is the bug.
`Tests/Tutorial.lean` checks that the two outputs above are what the checker prints.
