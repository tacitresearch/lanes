/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Shop

/-!
# An order is charged at most once

In every run of the shop, under every environment model (lost, reordered and repeated
messages, crashes and restarts), whatever its customers do, and whatever the payment service
does that its model allows (answers late, never or `unknown`, refuses a repeat, reports a
payment only by webhook, late, twice or out of order), the service has made at most one
payment for each order, counting those it may have made without saying so
(`charged_at_most_once`).

The proof is two facts. The shop sends every charge for an order under the order's key
(`emits_keyed`, a fact about its steps alone, lifted to every output of every run by
`System.Emits.outputs`). And a request always sent under one key has its effect at most once in
every run of the model (`Effects.at_most_once`), which holds of every service built with
`Idempotent.server`.
-/

namespace Shop

open Lanes

/-- A charge the shop sends is under the key of its order. -/
def Keyed (out : Out) : Prop :=
  ∀ c, out = .charge c → c.request.key = some c.request.request.order

/-- Every output among the effects is a keyed charge or no charge. -/
def AllKeyed (effs : List Eff) : Prop := ∀ out, Effect.emit out ∈ effs → Keyed out

variable {config : Config}

theorem allKeyed_nil : AllKeyed [] := by simp [AllKeyed]

theorem allKeyed_append {a b : List Eff} (ha : AllKeyed a) (hb : AllKeyed b) :
    AllKeyed (a ++ b) := by
  intro out hout
  rcases List.mem_append.mp hout with h | h
  · exact ha out h
  · exact hb out h

theorem allKeyed_stopWaiting (o : Order) : AllKeyed (stopWaiting o) := by
  intro out hout
  unfold stopWaiting at hout
  split at hout <;> simp at hout

theorem allKeyed_call (h : config.keyedRetries = true) (s : State) (o : Order) (attempt : Nat) :
    AllKeyed (call config s o attempt).2 := by
  intro out hout c hc
  subst hc
  simp only [call, List.mem_cons, Effect.emit.injEq, Out.charge.injEq, reduceCtorEq,
    List.not_mem_nil, or_false] at hout
  subst hout
  simp [Config.key, h]

theorem allKeyed_retry (h : config.keyedRetries = true) (s : State) (o : Order) (attempt : Nat) :
    AllKeyed (retry config s o attempt).2 := by
  unfold retry
  split
  · exact allKeyed_call h _ _ _
  · exact allKeyed_nil

theorem allKeyed_settle (s : State) (o : Order) (st : Payments.Status) :
    AllKeyed (settle s o st).2 := by
  have hpaid : AllKeyed [.emit (.paid o.order)] := by
    intro out hout c hc; subst hc; simp at hout
  have hdeclined : AllKeyed [.emit (.declined o.order)] := by
    intro out hout c hc; subst hc; simp at hout
  unfold settle
  split
  · exact allKeyed_nil
  · exact allKeyed_append (allKeyed_stopWaiting o) hpaid
  · exact allKeyed_nil
  · exact allKeyed_append (allKeyed_stopWaiting o) hdeclined
  · exact allKeyed_stopWaiting o

theorem allKeyed_place (h : config.keyedRetries = true) (s : State) (order amount : Nat) :
    AllKeyed (place config s order amount).2 := by
  unfold place
  split
  · exact allKeyed_nil
  · split
    · intro out hout c hc; subst hc; simp at hout
    · exact allKeyed_call h _ _ _

theorem allKeyed_replied (h : config.keyedRetries = true) (s : State) (id : Nat)
    (reply : Rpc.Reply Answer) : AllKeyed (replied config s id reply).2 := by
  unfold replied
  split
  · exact allKeyed_nil
  · split
    · exact allKeyed_settle _ _ _
    · split
      · intro out hout
        simp only [List.mem_cons, reduceCtorEq, false_or] at hout
        exact allKeyed_retry h _ _ _ out hout
      · exact allKeyed_nil
    · exact allKeyed_nil

theorem allKeyed_expired (h : config.keyedRetries = true) (s : State) (id : Nat) :
    AllKeyed (expired config s id).2 := by
  unfold expired
  split
  · split
    · split
      · exact allKeyed_retry h _ _ _
      · exact allKeyed_nil
    · exact allKeyed_nil
  · exact allKeyed_nil

theorem allKeyed_rearm (s : State) : AllKeyed (rearm config s) := by
  intro out hout
  obtain ⟨o, -, ho⟩ := List.mem_filterMap.mp hout
  split at ho <;> simp at ho

/-- With retries under the key, every charge the shop sends, in any step or start, is under the
key of its order. -/
theorem emits_keyed (h : config.keyedRetries = true) : (shop config).Emits Keyed := by
  refine ⟨fun _ s msg => ?_, fun _ s => allKeyed_rearm s⟩
  cases msg with
  | order order amount => exact allKeyed_place h s order amount
  | reply id reply => exact allKeyed_replied h s id reply
  | webhook e =>
    show AllKeyed (step config s (.webhook e)).2
    simp only [step]
    split
    · exact allKeyed_settle _ _ _
    · exact allKeyed_nil
  | expire id => exact allKeyed_expired h s id

/-- An order is charged at most once: in every run of the shop under every environment model,
beside any customers and the payment service's model, the service has made at most one payment
for each order, seen or not. -/
theorem charged_at_most_once {D : Type} (customers : Outside sig D) (config : Config)
    (hkeyed : config.keyedRetries = true) (maxDeliveries : Nat) (env : EnvModel sig)
    {events : List (Event sig)} {c : SysState (shop config)}
    (hrun : (SysState.init (shop config) env).run env events = some c)
    {d : D × Held} (hd : (customers.both (service maxDeliveries) isOrder).after events = some d)
    (order : Nat) : charges d.2 order ≤ 1 := by
  have houts := (emits_keyed hkeyed).outputs hrun
  refine Effects.at_most_once port Payments.lifecycle maxDeliveries (·.order == order) order
    ?_ (Outside.after_both _ _ _ hd).2
  intro out hout cl hcall horder
  have hout' : Event.output out ∈ events := (List.mem_filter.mp hout).1
  have hk := houts out hout'
  cases out with
  | charge c =>
    simp only [port, Option.some.injEq] at hcall
    subst hcall
    rw [hk _ rfl]
    simpa using horder
  | _ => simp [port] at hcall

end Shop
