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
