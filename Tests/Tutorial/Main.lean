/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Tutorial.Counter

/-!
The edge of the application: HTTP in, HTML out. Everything here is an action; the logic it calls
is in `Tut.Counter`.
-/

open Lanes Tut
open scoped Lanes.Html

/-! Links, htmx attributes and request matching all come from these routes. -/
namespace Routes

def home : Http.Route Unit := .get .root
def count : Http.Route Unit := .get (.seg "count")
def increment : Http.Route Unit := .post (.seg "increment")
def decrement : Http.Route Unit := .post (.seg "decrement")

end Routes

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

def Page : Html :=
  <html lang="en">
    <head>
      <meta charset="utf-8"/>
      <title>"tut"</title>
      <script src="https://unpkg.com/htmx.org@2.0.4"></script>
    </head>
    <body>
      <h1>"tut"</h1>
      <div id="counter" {Hx.request Routes.count ()} {Hx.trigger [.load]} {Hx.swap .outerHTML}>
      </div>
    </body>
  </html>

/-- Requests are parsed here, once (rule 2.2). What a request holds that must not enter the
system, a password or a session cookie, is taken out by a `prepare` field, which the server runs
before the request enters it. -/
def bridge : Http.Bridge sig where
  decode id request :=
    (Http.dispatch [
      Routes.home.handle fun () _ => .error (.html Page.document),
      Routes.count.handle fun () _ => .ok (.read id),
      Routes.increment.handle fun () _ => .ok (.increment id),
      Routes.decrement.handle fun () _ => .ok (.decrement id)
    ] request).getD (.error (.text "not found\n" 404))
  encode response := some (response.req, .html (CounterView response).render)

/-- `tut [port]`. The counter lives as long as the process: a restart starts it at zero. -/
def main (args : List String) : IO Unit := do
  let port := (args.head? >>= String.toNat?).getD 8080
  let config : Http.ServerConfig := { port := port.toUInt16 }
  let server ← (Http.serve (system {}) bridge config).block
  IO.println s!"tut listening on http://127.0.0.1:{server.port.getD 0}"
  (← IO.getStdout).flush
  Lanes.block server.wait
