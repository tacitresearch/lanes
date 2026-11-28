import Lanes
import Lanes.Testing
import Counter.Web

/-!
`lake test`: the model check, the proofs, and, when `LANES_POSTGRES=host:port` names a
PostgreSQL, the application on it.

The model check runs the front beside the store's model (`Lanes/Db/Model.lean`), on a small
instance: a limit of 2 and three increments in any order, the process restarting once. The store
answers each call with what one run of its transaction gives, fails it, or loses its answer; a
lost `COMMIT` may have taken effect, or may take effect at any later moment, or never, and the
model keeps every database consistent with what the front has seen. Every invariant has a
`sometimes` property next to it that shows the interesting states are reached (rule 5.3).

It then builds the proofs, which this file does not import, so that a broken proof does not stop
the checks. It exits 0 when every check explored its whole instance and the proofs build, 1 when
something failed, and 2 when a check passed but hit a bound. `lake test -- --json` prints the
results as JSON instead, each with its kind: check, proof or test.
-/

open Lanes Counter Std.Async

instance : sig.Inspect := {}
instance : system.Inspect := {}

/-- The browser: the requests still to send, and what the front answered. -/
structure Browser where
  toSend : List (Nat × Request)
  answered : List (Nat × Response) := []
  deriving DecidableEq, Hashable

instance : BEq Browser := instBEqOfDecidableEq

def browser (requests : List (Nat × Request)) : Outside sig Browser where
  init := { toSend := requests }
  allow d
    | .request n r => if (n, r) ∈ d.toSend then some { d with toSend := d.toSend.erase (n, r) } else none
    | .store _ => none
  observe d
    | .answered n r => { d with answered := d.answered ++ [(n, r)] }
    | _ => d

def config : Config := { limit := 2 }

abbrev D := Browser × Db.State Request Response

def world (requests : List (Nat × Request)) :=
  (browser requests).both (Db.outside {} (handler config) (Db.Db.empty schema) port)
    fun x => x matches .request ..

def samples (d : D) : List In :=
  d.1.toSend.map (fun (n, r) => .request n r) ++ Db.samples (handler config) port true true d.2

def countsOf (db : Db.Db) : List Count := (db.rows counts.table.name).filterMap counts.ofRow

def requests : List (Nat × Request) := [(1, .increment), (2, .increment), (3, .increment)]

def check :=
  Check.system system
    { env := { mayRestart := true }, driver := (world requests).driver samples, maxRestarts := 1 }
    [ .always "the count never passes its limit, in any database the store may hold" fun w =>
        w.driver.2.worlds.all fun world => (countsOf world.db).all (·.value.toInt ≤ config.limit),
      .sometimes "the count reaches its limit" fun w =>
        w.driver.2.worlds.any fun world => (countsOf world.db).any (·.value.toInt == config.limit),
      .sometimes "an increment is refused" fun w => w.driver.1.answered.any (!·.2.applied) ]
    {}

def fetch (port : UInt16) (method : Http.Method) (path : List String) : Async String := do
  let r ← Http.Client.exchange { host := "127.0.0.1", port, request := { method, path } } {}
  return (r.bind fun r => String.fromUTF8? r.body).getD ""

def shows (page text : String) : Bool := (page.splitOn text).length > 1

/-- The application on PostgreSQL, from tables that hold nothing: it counts, it refuses to start
on a table that differs from the declared one, and a restart keeps the count. -/
def live : IO (List (String × Bool)) := do
  let some spec ← IO.getEnv "LANES_POSTGRES"
    | return [("counter on PostgreSQL: skipped, LANES_POSTGRES is not set", true)]
  let [host, portText] := spec.splitOn ":" | return [("LANES_POSTGRES is host:port", false)]
  let pg : Postgres.Client.Config :=
    { host, port := (portText.toNat?.getD 5432).toUInt16, sslmode := .disable,
      conn := { user := "lanes_trust", database := "lanes_test" } }
  let migrations ← Postgres.Typed.readMigrations "migrations"
  Lanes.block do
    let errors ← Postgres.Typed.reset pg schema (migrations.map (·.1))
    unless errors.isEmpty do return [(s!"counter: the tables are dropped: {errors}", false)]
    let .ok first ← Web.start pg migrations { port := 0 } config
      | return [("counter: the migrations make the declared tables", false)]
    let some port := first.port | return [("counter: the server reports its port", false)]
    for _ in [0:3] do discard <| fetch port .post ["increment"]
    let counted ← fetch port .get ["count"]
    first.stop
    let other := { counts.table with columns := counts.table.columns ++ [{ name := "extra", ty := .int }] }
    let refused ← Postgres.Typed.prepare pg [other] migrations
    let .ok again ← Web.start pg migrations { port := 0 } config
      | return [("counter: it starts again on the same tables", false)]
    let some port := again.port | return [("counter: the server reports its port again", false)]
    let kept ← fetch port .get ["count"]
    again.stop
    return [
      ("counter: on PostgreSQL, three increments with a limit of 2 count to 2", shows counted "Count: 2"),
      ("counter: it refuses to start on a table that differs from the declared one", !refused.isEmpty),
      ("counter: a restart keeps the count", shows kept "Count: 2") ]

def main (args : List String) : IO UInt32 := do
  let report := check
  Testing.report args
    ([.check "the counter beside the store's model, with a limit of 2 and three increments" report
        report.renderSystem,
      ← Testing.build "the proofs" ["Counter.Proofs"]] ++ Testing.Result.tests (← live))
