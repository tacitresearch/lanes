import Lanes
import Lanes.Services.Postgres
import Counter.Counter

/-!
The edge of the application: HTTP in, HTML out, and the store on PostgreSQL. Everything here is
an action or a view; the logic it calls is in `Counter.Counter`.
-/

namespace Counter.Web

open Lanes Std.Async
open scoped Lanes.Html

/-! Links, htmx attributes and request matching all come from these routes. -/
namespace Routes

def home : Http.Route Unit := .get .root
def count : Http.Route Unit := .get (.seg "count")
def increment : Http.Route Unit := .post (.seg "increment")

end Routes

def CounterView (response : Response) : Html :=
  <div id="counter">
    <p>{s!"Count: {response.value}"}</p>
    {if response.applied then Html.empty else <p class="error">"The counter is at its limit."</p>}
    <button {Hx.request Routes.increment ()} {Hx.target "#counter"} {Hx.swap .outerHTML}>
      "Add one"
    </button>
  </div>

def Page : Html :=
  <html lang="en">
    <head>
      <meta charset="utf-8"/>
      <title>"counter"</title>
      <script src="https://unpkg.com/htmx.org@2.0.4"></script>
    </head>
    <body>
      <h1>"counter"</h1>
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
      Routes.count.handle fun () _ => .ok (.request id .read),
      Routes.increment.handle fun () _ => .ok (.request id .increment)
    ] request).getD (.error (.text "not found\n" 404))
  encode
    | .answered id r => some (id, .html (CounterView r).render)
    | .failed id => some (id, .text "The count is not available; try again.\n" 503)
    | .call _ => none

/-- Run the migrations not yet run, check that the tables are the ones `schema` declares, and
serve. With a difference it serves nothing and gives the problems: the transactions were written
for the declared tables, and must not run on others. -/
def start (postgres : Postgres.Client.Config) (migrations : List (String × String))
    (server : Http.ServerConfig) (config : Config := {}) :
    Async (Except (List String) (Http.Server (Http.admittedFronted system bridge))) := do
  let problems ← Postgres.Typed.prepare postgres schema migrations
  unless problems.isEmpty do return .error problems
  let store : Postgres.Typed.Store Request Response :=
    { pool := ← Postgres.Pool.new postgres, handler := handler config }
  return .ok (← Postgres.Typed.serve system bridge port store server)

end Counter.Web
