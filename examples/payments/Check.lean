import Lanes
import Shop

/-!
Model checks of the shop against the payment model, run by `lake test` (Lanes rule 5.1). One
order, each call answered with any payment in a few statuses, refused, `unknown` or never;
webhooks for every payment the service may have made, each delivered up to twice, in any order,
and for payments the shop never heard of; inputs reordered and handled twice; the shop crashing
and starting again. No order is charged twice, and an order the shop says is paid has a payment
that succeeded. A retry without the key charges the order twice.
-/

open Lanes Shop

instance : sig.Inspect := {}
instance (config : Config) : (shop config).Inspect := {}

/-- Orders still to place, and what the shop told its customers. -/
structure Customers where
  toPlace : List (Nat × Nat)
  paid : List Nat := []
  deriving DecidableEq, Hashable

instance : BEq Customers := instBEqOfDecidableEq

def customers (orders : List (Nat × Nat)) : Outside sig Customers where
  init := { toPlace := orders }
  allow d
    | .order order amount =>
      if (order, amount) ∈ d.toPlace then some { d with toPlace := d.toPlace.erase (order, amount) }
      else none
    | _ => none
  observe d
    | .paid order => if order ∈ d.paid then d else { d with paid := order :: d.paid }
    | _ => d

def orders : List (Nat × Nat) := [(0, 5)]

def world := (customers orders).both (service 2) isOrder

abbrev ShopWorld (config : Config) := World (shop config) (Customers × Held)

def statuses : List Payments.Status := [.processing, .succeeded, .requiresPaymentMethod]

def samples (d : Customers × Held) : List In :=
  let model := d.2.server
  let things := model.inner.inner.things
  let fresh := things.length + 7
  d.1.toPlace.map (fun (o, a) => .order o a)
    ++ d.2.pending.flatMap (fun id =>
      .reply id .unknown :: .reply id (.answer .refused) ::
        ((fresh :: things.map (·.id)).flatMap fun r =>
          statuses.map fun st => .reply id (.answer (.made r st))))
    ++ things.flatMap (fun t => statuses.map fun st => .webhook ⟨t.id, st, t.params⟩)
    ++ model.inner.inner.unseen.flatMap fun (_, p) => statuses.map fun st => .webhook ⟨fresh, st, p⟩

def paidHasSucceeded (w : ShopWorld config) : Bool :=
  (w.state.state ()).orders.all fun o =>
    o.status != .paid || w.driver.2.server.inner.inner.things.any fun t =>
      t.params.order == o.order && t.state == .succeeded

def env : EnvModel sig where
  link _ _ := .unordered
  mayCrash _ := true
  restarts _ := true

/-- Two payments of one order that succeeded: the customer was charged twice. -/
def paidTwice (held : Held) (order : Nat) : Bool :=
  (held.server.inner.inner.things.filter fun t =>
    t.params.order == order && t.state == .succeeded).length ≥ 2

def check (config : Config) (maxCrashes : Nat := 1) :=
  Check.system (shop config) { env, driver := world.driver samples, maxCrashes }
    [ .always "no order is charged twice" fun w => chargedAtMostOnce w.driver.2 (orders.map (·.1)),
      .always "no order has two payments that succeeded" fun w =>
        orders.all fun (o, _) => !paidTwice w.driver.2 o,
      .always "an order the shop calls paid has a payment that succeeded" paidHasSucceeded,
      .sometimes "an order is paid" fun w => !w.driver.1.paid.isEmpty,
      .sometimes "an order is paid after a call with an unknown outcome was retried" fun w =>
        !w.driver.1.paid.isEmpty && (w.state.state ()).calls.length ≥ 2,
      .sometimes "an order is paid whose answer never came" fun w =>
        !w.driver.1.paid.isEmpty && w.driver.2.server.slots.all (·.result.isNone),
      .sometimes "a webhook is delivered twice" fun w =>
        w.driver.2.server.inner.delivered.any (·.2 == 2) ]
    { maxStates := 2000000 }

/-- The checks retry once; the proof is for every `maxAttempts`. -/
def checked : Config := { maxAttempts := 2 }

def bug : Config := { checked with keyedRetries := false }

/-- The bug as the customer sees it: two payments that succeeded. -/
def twice :=
  Check.system (shop bug) { env, driver := world.driver samples, maxCrashes := 0 }
    [ .always "no order has two payments that succeeded" fun w =>
        orders.all fun (o, _) => !paidTwice w.driver.2 o ]

def main : IO UInt32 := do
  let fixed := check checked
  IO.println fixed.renderSystem
  let buggy := check bug
  let found := match buggy.failure with
    | some (.violated "no order is charged twice" t) => some t
    | _ => none
  if let some t := found then
    IO.println s!"a retry without the key: an order charged twice after {t.steps.length} steps"
    IO.println (t.render (fun _ => "") Event.render)
  let paidTwice := match twice.failure with
    | some (.violated _ t) => some t
    | _ => none
  if let some t := paidTwice then
    IO.println s!"a retry without the key: two payments of an order succeed after {t.steps.length} steps"
    IO.println (t.render (fun _ => "") Event.render)
  let tests : List (String × Bool) :=
    [ ("the shop charges each order once, under every fault the model allows",
        fixed.ok && fixed.complete && fixed.witnesses.length == 4),
      ("a retry without the key may charge an order twice", found.isSome),
      ("a retry without the key charges an order twice", paidTwice.isSome) ]
  for (name, ok) in tests do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
  return if tests.all (·.2) then 0 else 1
