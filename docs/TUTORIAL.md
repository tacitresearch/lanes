# Tutorial

Fifteen minutes from `lanes new` to a change that is model-checked and proved. You need some
programming, not much Lean. Install what the quick start in `README.md` lists first: elan and
a C compiler; and, to run the app, PostgreSQL.

The code of each step is kept in `Tests/Tutorial/`: `lake build` compiles it, and `lake test`
fails if this page quotes anything but that code and what the checker prints for it.

## 1. Make an app and run it

```bash
git clone https://github.com/tacitresearch/lanes
cd lanes
lake exe lanes new tut --dir ../tut
cd ../tut
lake test            # the first time builds Lanes and the app (minutes), then checks and proves
```

`lake test` prints `PASS (complete): every reachable state explored` for the model check, `ok
(proof) the proofs`, and a test it skips: the app on PostgreSQL, which runs when
`LANES_POSTGRES=host:port` names one (`../lanes/scripts/with-postgres lake test` makes one for
the run). Then run it on a PostgreSQL of yours, named as libpq's variables name it:

```bash
PGHOST=localhost PGUSER=postgres PGDATABASE=postgres lake exe tut   # serves http://127.0.0.1:8080
```

At its start it runs the migration in `migrations/`, which makes the table `counts`, and checks
that the table is the one the code declares; with any difference it refuses to start and says
what differs. Open the page and press "Add one", or ask from another terminal:

```bash
curl -X POST http://127.0.0.1:8080/increment
```

```html
<div id="counter"><p>Count: 1</p><button hx-post="/increment" hx-target="#counter" hx-swap="outerHTML">Add one</button></div>
```

Stop it with Ctrl-C and start it again: the count is still 1. The process keeps nothing; the
count is a row of `counts`. Several instances behind a load balancer would share it.

The app is a few files. `Tut/Counter.lean` is the logic: the table, the transactions, and the
front. `Tut/Web.lean` is the page and the server, `Main.lean` reads the environment and starts
it, `Check.lean` is the model check and `Tut/Proofs.lean` the theorems. Nothing imports the
theorems but `lake build`, so a broken proof stops neither the checks nor the server.

**A request is one pure transaction.** `handler` in `Tut/Counter.lean` says what each request
does to the database, as a value of `Txn`: read the count, write the next one, answer. It cannot
read a clock, a file or a socket, and it is all a request does. The store runs it at
`SERIALIZABLE` and runs it again if another request conflicted with it, which is safe because
running it repeats nothing outside the transaction. The front, an actor that keeps nothing,
only hands each request to the store and the answer back. The same `handler` runs on
PostgreSQL, in the checker beside a model of the store, and in the proofs.

## 2. Change the counter: take one away

Add a request to `Tut/Counter.lean`:

```lean
inductive Request where
  | increment
  | decrement
  | read
  deriving DecidableEq, Repr, Hashable
```

and its transaction, in `handler`, after the `increment` case. It is refused at zero, as an
increment is refused at the limit:

```lean
  | .decrement => do
    let c ← current
    if 0 < c.value.toInt.toNat then
      let c := { c with value := Int64.ofNat (c.value.toInt.toNat - 1) }
      let _ ← counts.upsert c
      return ⟨c.value, true⟩
    else return ⟨c.value, false⟩
```

On a `Nat`, `0 - 1` is `0`: without the `if`, a decrement at zero would answer that it was
applied, and Lean would not complain. Step 3 shows what does. The table does not change, so
there is no migration to write.

In `Tut/Web.lean`, add a route to `namespace Routes`, a line after the increment's in `bridge`
(which turns an HTTP request into an input), and a button. Replace `CounterView` with one whose
message says which bound refused the request:

```lean
def decrement : Http.Route Unit := .post (.seg "decrement")
```

```lean
      Routes.increment.handle fun () _ => .ok (.request id .increment),
      Routes.decrement.handle fun () _ => .ok (.request id .decrement)
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

Without the case in `handler`, `lake build` stops with `Missing cases`. Without the line in the
bridge it builds, and the button gets `not found`. The proofs stop building too, which step 4
mends.

The code of this step is `Tests/Tutorial/Counter.lean` and `Tests/Tutorial/Web.lean`.

## 3. Check a property, and break it

**The checker explores every order and fault.** `Check.lean` runs the front beside the store's
model (`Lanes/Db/Model.lean`), on a limit of 2. It sends the requests in every order and follows
every state the system can reach: each request waiting, sent to the store or answered; the
store answering with what one run of the transaction gives, failing a call, or losing its
answer, and a lost `COMMIT` taking effect at once, later or never; the process restarting once.
The model keeps every database consistent with what the front has seen, and each property is
tested in every one of those states. An `always` must hold in all of them. A `sometimes` must
hold in at least one, so a check that never reaches the interesting states fails instead of
passing.

In `Check.lean`, send a decrement in place of the third increment:

```lean
def requests : List (Nat × Request) := [(1, .increment), (2, .increment), (3, .decrement)]
```

Then replace the properties, from `[ .always` to the closing `]`. They say that a request is
refused only at a bound, and give the decrement's refusal its own witness:

```lean
    [ .always "the count never passes its limit, in any database the store may hold" fun w =>
        w.driver.2.worlds.all fun world => (countsOf world.db).all (·.value.toInt ≤ config.limit),
      .sometimes "the count reaches its limit" fun w =>
        w.driver.2.worlds.any fun world => (countsOf world.db).any (·.value.toInt == config.limit),
      .always "a request is refused only at zero or at the limit" fun w =>
        w.driver.1.answered.all fun (_, r) => r.applied || r.value == 0 || r.value == 2,
      .sometimes "a decrement is refused" fun w =>
        w.driver.1.answered.any fun (_, r) => !r.applied && r.value == 0 ]
```

Each property is a function of a state of the search, `w`. `w.driver.2.worlds` are the
databases the store may hold, and `w.driver.1.answered` what the front has answered. `lake test`
prints the checker's report, then a line for the check and one for the proofs. The report:

```text
PASS (complete): every reachable state explored
reached "the count reaches its limit" in 8 steps
reached "a decrement is refused" in 7 steps
states: 18685, transitions: 56738, depth: 20
coverage: input 26079, output 11003, deliver 9958, restart 6982, start 2716, crash 0 (never fired), drop 0 (never fired), duplicate 0 (never fired), timeout 0 (never fired)
```

Now seed a bug. In `handler`, write `1 <` for `0 <` in the decrement, so that a decrement at one
is refused:

```lean
    if 1 < c.value.toInt.toNat then
```

`lake test` fails. The report gives the shortest run that breaks the property, and a line after
it, `FAIL (check) …`, says what failed:

```text
FAIL: "a request is refused only at zero or at the limit" is violated after 10 steps
  1. input request 1 (increment)
  2. start ()
  3. deliver outside → (): request 1 (increment)
  4. output call { id := 1, request := increment }
  5. input request 3 (decrement)
  6. deliver outside → (): request 3 (decrement)
  7. output call { id := 3, request := decrement }
  8. input store { id := 3, result := committed { value := 1, applied := false } }
  9. deliver outside → (): store { id := 3, result := committed { value := 1, applied := false } }
  10. output answered 3 { value := 1, applied := false }
  state reached:
  () [up] ()
reached "the count reaches its limit" in 8 steps
reached "a decrement is refused" in 7 steps
states: 2285, transitions: 3993, depth: 10
coverage: input 2001, deliver 789, restart 488, output 445, start 270, crash 0 (never fired), drop 0 (never fired), duplicate 0 (never fired), timeout 0 (never fired)
```

Read it as a story. A browser sends `increment` as request 1; the front starts and sends it to
the store as a call. Then the decrement, request 3, is sent too. The store takes the increment
first (the count is 1), then the decrement, which is refused at 1: its answer comes back and the
front hands it out. The front's own state is `()`: it keeps nothing. Put `0 <` back and the
check passes again. `lake test` exits with 1 on a `FAIL`, so CI stops on it, and with 2 on
`PASS (bounded)`: a search that hit a bound covered only part of the instance, which is not a
pass. `lake test -- --json` prints the same results as one JSON object, each with its kind
(`check`, `proof` or `test`), for a program to read.

The checks catch the bug of step 2 as well: with no `if` at all, no decrement is ever refused,
and `lake test` prints `FAIL: never reached: "a decrement is refused"`.

The code of this step is `Tests/Tutorial/Check.lean`, where `buggy` is the bug.
`Tests/Tutorial.lean` checks that the two outputs above are what the checker prints.

## 4. Prove it for every run

**A proof covers every run.** The check covered a limit of 2, three requests and one restart.
`Tut/Proofs.lean` covers every limit, every request and every database. Its invariant is that
every count is between zero and the limit (`Within`), and it is proved per transaction:
`preserves` says that each transaction, run on a database that satisfies it, leaves one that
does. Then `within_always` says it holds in every database the store's model allows, after any
run of the front, with lost `COMMIT`s, failures, retries and restarts:

```lean
theorem within_always (hlimit : config.limit < 2 ^ 63) (cfg : Db.Config)
    {events : List (Event sig)} {s : Db.State Request Response}
    (hrun : (Db.outside cfg (handler config) (Db.empty schema) port).after events = some s) :
    ∀ w ∈ s.worlds, ∀ w' ∈ w.expand (handler config) w.fuel, Within config w'.db :=
  Db.invariant cfg port within_empty (preserves hlimit) hrun
```

Per transaction is enough because the store runs transactions at `SERIALIZABLE`: the database
is always what some order of them, one after another, would leave, and what each keeps, a
sequence of them keeps.

After step 2, `lake test` runs the checks, then fails to build the proofs, with `FAIL (proof)
the proofs` and Lean's message (after a long `trace:` line with the command it ran):

```
error: Tut/Proofs.lean:62:2: Alternative `decrement` has not been provided
```

`preserves` takes the request apart, one case per kind, and the decrement has none. Add it,
before the `read` case. It reads the count, which is within the limit (`current_within`), and
writes one less, which is too (`ofNat_within`); refused, it writes nothing:

```lean
  | decrement =>
    obtain ⟨c, db₁, h₁, h₂⟩ := Txn.run_bind_ok_inv (t := current) h
    obtain ⟨rfl, hc⟩ := current_within hw h₁
    split at h₂
    · obtain ⟨b, db₂, h₃, h₄⟩ := Txn.run_bind_ok_inv h₂
      simp only [Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h₄
      rw [← h₄.2]
      exact upsert_within hw (ofNat_within hlimit _ (by have := hc.2; omega)) h₃
    · simp only [Txn.pure_eq, Txn.run_pure, Except.ok.injEq, Prod.mk.injEq] at h₂
      rw [← h₂.2]
      exact hw
```

`Txn.run_bind_ok_inv` splits a run of `do let c ← current; …` into the run of `current` and the
rest; `split` takes the `if` apart; `omega` does the arithmetic: the count was at most the limit
(`hc.2`), so one less is too. Write `c.value.toInt.toNat + 1` for `- 1` in the decrement and the
proof fails there: one more than the count need not be within the limit.

**The axiom gate.** A theorem proves what it states only if nothing under it was assumed.
`#print axioms` lists the axioms a theorem rests on, through every lemma it uses. Lean's three
standard ones are expected. A `sorry` anywhere below shows as `sorryAx`, and an `axiom`
someone declared shows by its name. `#guard_msgs` turns any other list into a build error. Add
a gate for each headline theorem at the end of `Tut/Proofs.lean`:

```lean
/-- info: 'Tut.preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tut.preserves

/-- info: 'Tut.within_always' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tut.within_always
```

Now put `sorry` in place of the decrement's case. The `sorry` is only a warning, but the gate of
`within_always`, which rests on it, fails:

```
error: Tut/Proofs.lean:101:0: ❌️ Docstring on `#guard_msgs` does not match generated message:

- info: 'Tut.within_always' depends on axioms: [propext, Classical.choice, Quot.sound]
+ info: 'Tut.within_always' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`lake test` fails on the `sorry` even without a gate: it builds the proofs with warnings as
errors (`Testing.build`), and a `sorry` is a warning. The checks still run first, since
`Check.lean` does not import the proofs. `lake exe lanes lint` reports the `sorry` too
(`no-sorry`). Lanes keeps its own gates in `Tests/Axioms/`.

The code of this step is `Tests/Tutorial/Proofs.lean`: the theorems and the gate.

## 5. Where next

`docs/TUTORIAL-WEB.md` is the sequel: a web app with sign-in, uploads to S3, a test of the
whole site, and how to run it. `docs/DEPLOY.md` says how to run an app as a container, several
at once.

Then read the examples in the order `examples/README.md` gives:

1. `examples/counter`: what `lanes new` wrote, which you now know.
2. `examples/bank`: actors that send each other messages, an invariant of the whole system,
   and the checker finding the credit a lossy link drops; their state lasts until a restart.
3. `examples/bank-web`: the bank behind a web page.
4. `examples/kv-cache`: a store checked against a five-line spec, and a cache that breaks it.
5. `examples/watchdog`: what fairness says.
6. `examples/todo-db`: an invariant per transaction that no constraint states.
7. `examples/rookery`: the serious system.

The rules your app's `AGENTS.md` points to are in `AGENTS.md`, sections Design, Code and Proofs.
