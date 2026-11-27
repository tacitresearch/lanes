import Lanes
import Counter.Counter

/-!
The edge of the application: HTTP in, HTML out. Everything here is an action; the logic it calls
is in `Counter.Counter`.
-/

open Lanes Counter
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

/-- Requests are parsed here, once (rule 2.2). What a request holds that must not be journalled,
a password or a session cookie, is taken out by a `prepare` field, which the server runs before
the request enters the system. -/
def bridge : Http.Bridge sig where
  decode id request :=
    (Http.dispatch [
      Routes.home.handle fun () _ => .error (.html Page.document),
      Routes.count.handle fun () _ => .ok (.read id),
      Routes.increment.handle fun () _ => .ok (.increment id)
    ] request).getD (.error (.text "not found\n" 404))
  encode response := some (response.req, .html (CounterView response).render)

/-- How the system is written to a snapshot, so that its journal can be cut: an identity, each
actor's state, each actor's messages, and its outputs. -/
def saving : Http.Saving (system {}) where
  actors := { id := Codec.unit, state := fun _ => Codec.nat, msg := fun _ => Request.codec }
  out := Response.codec

/-- `counter [port] [journal]`. With a journal file the counter survives the process: it is
replayed through `step` at start, and cut each time the state is saved. Change the number in
`system` whenever a change to a step function should not be applied to what is already in the
journal. Where to listen and how to stop come from the environment, so that a deployment sets
them without a change here: `LANES_HOST`, the address (`127.0.0.1` unless set; `0.0.0.0` behind a
load balancer), `LANES_IDLE_MS`, how long an idle connection is kept, and `LANES_DRAIN_MS`, how
long SIGTERM or SIGINT waits for the requests in flight. -/
def main (args : List String) : IO Unit := do
  let port := (args.head? >>= String.toNat?).getD 8080
  let journal := args[1]?.map System.FilePath.mk
  let ms (name : String) (default : Nat) : IO Nat := do
    let some text ← IO.getEnv name | return default
    let some n := text.toNat? | throw (IO.userError s!"counter: {name} is not a number: {text}")
    return n
  let host := (← IO.getEnv "LANES_HOST").getD "127.0.0.1"
  let config : Http.ServerConfig :=
    { host, port := port.toUInt16, journal, system := "counter 1"
      idle_ms := ← ms "LANES_IDLE_MS" 10000 }
  let drain_ms ← ms "LANES_DRAIN_MS" 10000
  let server ← (Http.serve (system {}) bridge config {} saving).block
  IO.println s!"counter listening on http://{host}:{server.port.getD 0}"
  (← IO.getStdout).flush
  Lanes.block (server.stopOnSignal drain_ms)
