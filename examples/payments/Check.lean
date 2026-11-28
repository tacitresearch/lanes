import Lanes
import Shop
import Lanes.Testing

/-!
Model checks of the shop, run by `lake test` (Lanes rule 5.1): its worker beside the store's
model, with the shop's transactions running at any moment, and the payment model. One order:
its charge answered with a payment being processed, `unknown` or never; webhooks that it
succeeded or was declined for every payment the service may have made, in any order, each
delivered at most once, and that it succeeded for payments the shop never heard of; a restart.
No order is charged twice, an order paid has a payment that succeeded, and an order is paid.
Retries are checked of the worker itself (`Tests/Worker.lean`); at most once is proved, with
retries and restarts (`Shop.charged_at_most_once`).
-/

open Lanes Lanes.Db Lanes.Db.Jobs Shop

instance : sig.Inspect := {}

def config : Shop.Config :=
  { jobs := { batch_max := 2, attempts_max := 2, lease_ms := 100, backoff_ms := 10 }
    attempt_ms := 50 }

instance : (worker config).Inspect := {}

/-- The clock and the customers: the times still to tick, the orders still to place, and the
attempts the worker made, which the service may answer. -/
structure Driver where
  ticks : List Int64
  toPlace : List Action
  attempts : List (Int64 × Int64) := []
  deriving DecidableEq, Hashable

instance : BEq Driver := instBEqOfDecidableEq

def driver (ticks : List Int64) (toPlace : List Action) : Outside sig Driver where
  init := { ticks, toPlace }
  allow d
    | .tick t => if d.ticks.head? = some t then some { d with ticks := d.ticks.tail } else none
    | .submit a => if a ∈ d.toPlace then some { d with toPlace := d.toPlace.erase a } else none
    | _ => none
  observe d
    | .run id lease _ _ => if (id, lease) ∈ d.attempts then d else { d with attempts := d.attempts ++ [(id, lease)] }
    | _ => d

abbrev Held := Rpc.State (Effects.Model Int64 IntentId Payments.Status Charge)

abbrev D := (Driver × Db.State (Action ⊕ Req) (Reply ⊕ Ans Charge)) × Held

instance : DecidableEq Held := inferInstance

instance : DecidableEq (Driver × Db.State (Action ⊕ Req) (Reply ⊕ Ans Charge)) := inferInstance

instance : BEq D := instBEqOfDecidableEq

def theWorld (ticks : List Int64) (toPlace : List Action) : Outside sig D :=
  world (driver ticks toPlace) {} config (Db.empty schema) 1

def statuses : List Payments.Status := [.succeeded, .requiresPaymentMethod]

def samples (d : D) : List (Worker.In Action Reply Charge Answer) :=
  let model := d.2.server
  let things := model.inner.inner.things
  let fresh := things.length + 7
  d.1.1.ticks.head?.toList.map .tick ++ d.1.1.toPlace.map .submit
    ++ Db.samples (store config) Worker.storePort false false d.1.2
    ++ d.1.1.attempts.flatMap (fun (id, lease) =>
      [.ran id lease .unknown, .ran id lease (.answer (.made fresh .processing))])
    ++ things.flatMap (fun t => statuses.map fun st => .submit (.webhook ⟨t.id, st, t.params⟩))
    ++ model.inner.inner.unseen.map fun (_, p) => .submit (.webhook ⟨fresh, .succeeded, p⟩)

abbrev W := Lanes.World (worker config) D

def ordersOf (db : Db) : List Shop.Order := (db.rows orders.table.name).filterMap orders.ofRow

def chargedOnce (w : W) : Bool := chargesFor w.driver.2 0 ≤ 1

def paidSucceeded (w : W) : Bool :=
  w.driver.1.2.worlds.all fun world => (ordersOf world.db).all fun o =>
    o.status != Status.paid || w.driver.2.server.inner.inner.things.any fun t =>
      t.params.order == o.id && t.state == .succeeded

def check :=
  Check.system (worker config)
    { env := { mayRestart := true }
      driver := (theWorld [0] [.place "k" 0 5]).driver samples
      maxRestarts := 1 }
    [ .always "no order is charged twice" chargedOnce,
      .always "an order paid has a payment that succeeded" paidSucceeded,
      .sometimes "an order is paid" fun w => w.driver.1.2.worlds.any fun world =>
        (ordersOf world.db).any (·.status == Status.paid) ]
    {}

def main (args : List String) : IO UInt32 := do
  let checked := check
  Lanes.Testing.report args [Lanes.Testing.Result.check
    "payments: no order charged twice, and an order paid has a payment that succeeded"
    checked checked.renderSystem]
