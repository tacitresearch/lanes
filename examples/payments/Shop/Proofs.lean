/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Proofs
import Shop

/-!
# An order is charged at most once

In every run of the shop's worker, under every environment model (lost, reordered and repeated
messages, crashes, and restarts of the process), beside any clients, the store's model with the
shop's transactions running at any moment, and whatever the payment service does that its model
allows (answers late, never or `unknown`, refuses a repeat, reports a payment only by webhook,
late, twice or out of order), the service has made at most one payment for each order, counting
those it may have made without saying so (`charged_at_most_once`).

The proof is four facts, none about time:

- every payment the service may have had is under the key of a job of the outbox, with that
  job's charge, in every database the store may hold (`Worker.slots_held`, from
  `Worker.committed_only`);
- every job of the outbox is under its order's key, `charge-<order>`: the shop only adds jobs
  so, and no claim or finish changes a job's key or work (`keyed_always`);
- no two jobs hold one key (`Queue.one_per_key`);
- no two payments are under one job's key (`Idempotent.keys_nodup`).

Before, the shop numbered its calls itself and a restart set the number back, so that an answer
to an earlier call could be taken for another order's. Here an attempt is named by its job and
lease, which the database keeps.
-/

namespace Shop

open Lanes Lanes.Db Lanes.Db.Jobs

/-- The job is under its order's key. -/
def Keyed (j : Job Charge) : Prop := j.key = chargeKey j.work.order

theorem keyed_stable : Queue.Stable Keyed := fun _ _ _ hk hw h => by
  unfold Keyed at *; rw [← hk, ← hw]; exact h

theorem orders_name : orders.table.name ≠ charges.name := by decide

theorem add_adds (order amount : Int64) : (add order amount).All (charges.Adds Keyed) := by
  refine Txn.All.bind (Queue.get_other orders orders_name _ _) fun r => ?_
  cases r with
  | some _ => exact .pure _
  | none =>
    refine Txn.All.bind (Queue.insert_other orders orders_name _ _) fun b => ?_
    cases b
    · exact .pure _
    · exact Txn.All.bind (Txn.All.map _ (Queue.enqueue_adds _ _ _ _ fun _ => rfl)) fun _ => .pure _

theorem webhook_adds (w : Webhook) : (webhook w).All (charges.Adds Keyed) := by
  refine Txn.All.bind (Queue.get_other orders orders_name _ _) fun r => ?_
  cases r with
  | none => exact .pure _
  | some o =>
    simp only
    split
    · exact Txn.All.bind (Txn.All.map _ (Queue.update_other orders orders_name _ _)) fun _ => .pure _
    · exact Txn.All.bind (.pure _) fun _ => .pure _

/-- The shop's transactions only add charges, each under its order's key. -/
theorem shop_adds : ∀ x, (handler x).All (charges.Adds Keyed)
  | .place key order amount =>
    Txn.All.bind (Keys.once_all placed (fun o ho => .inl (by rw [ho]; decide)) key (add_adds order amount))
      fun b => by cases b <;> exact .pure _
  | .webhook w => webhook_adds w
  | .status order => Txn.All.bind (Queue.get_other orders orders_name _ _) fun _ => .pure _

/-- Every job of the outbox is under its order's key, in every database the store may hold. -/
theorem keyed_preserves (config : Config) : Preserves (store config) (charges.Fixed Keyed) := by
  intro x db a db' hP hrun
  cases x with
  | inl x =>
    exact Queue.fixed_of_adds (fun _ h => h) (Txn.All.map _ (shop_adds x)) db a db' hP hrun
  | inr r =>
    obtain ⟨b, hb, -⟩ := Queue.run_map _ _ hrun
    exact Queue.handler_fixed keyed_stable config.jobs r db b db' hP hb

theorem count_le {α : Type} (l : List α) (key : α → Option Int64) (p : α → Bool)
    (hnd : (l.filterMap key).Nodup) (hsame : ∀ a ∈ l, ∀ b ∈ l, p a → p b → key a = key b)
    (hsome : ∀ a ∈ l, p a → (key a).isSome) : (l.filter p).length ≤ 1 := by
  cases h : l.filter p with
  | nil => simp
  | cons a rest =>
    have ha : a ∈ l.filter p := h ▸ List.mem_cons_self
    obtain ⟨hal, hpa⟩ := List.mem_filter.mp ha
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (hsome a hal hpa)
    have heq : l.filter p = (l.filter fun x => key x == some k).filter p := by
      rw [List.filter_filter]
      refine List.filter_congr fun x hx => ?_
      by_cases hpx : p x
      · simp [hpx, hsame x hx a hal hpx hpa, hk]
      · simp [hpx]
    rw [← h, heq]
    exact Nat.le_trans (List.length_filter_le _ _) (Worker.filter_key_le l hnd k)

/-- **An order is charged at most once.** In every run of the worker under every environment
model, process restarts included, beside any clients, the store's model with the shop's
transactions, and the payment service's model, the service has made at most one payment for
each order, seen or not. -/
theorem charged_at_most_once {D : Type} (clients : Outside sig D) (dbcfg : Db.Config) (config : Config)
    (maxDeliveries : Nat) (env : EnvModel sig) {events : List (Event sig)}
    {c : SysState (worker config)} (hrun : (SysState.init (worker config) env).run env events = some c)
    {d : (D × Db.State (Action ⊕ Req) (Reply ⊕ Ans Charge)) ×
      Rpc.State (Effects.Model Int64 IntentId Payments.Status Charge)}
    (hd : (world clients dbcfg config (Db.empty schema) maxDeliveries).after events = some d)
    (order : Int64) : chargesFor d.2 order ≤ 1 := by
  have happ : ∀ x, charges.Keeps (handler x) := fun x => Queue.keeps_of_adds (shop_adds x)
  have hslots := Worker.slots_held (cfg := config.worker) (q := charges) (app := handler) happ
    (Queue.functional_empty _) env hrun hd
  have hstore := (Outside.after_both _ _ _ (Outside.after_both _ _ _ hd).1).2
  have hkeyed := Db.invariant dbcfg Worker.storePort (fun j hj => by simp [Queue.jobs, Queue.rows_empty] at hj)
    (keyed_preserves config) hstore
  have hone := Queue.one_per_key (fun x => Queue.onTable_of_adds (shop_adds x)) config.jobs dbcfg
    Worker.storePort (Queue.keyUnique_empty _) hstore
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ (Db.worlds_ne_nil dbcfg Worker.storePort hstore)
  have hself := expand_self (h := store config) w w.fuel
  -- The job of a payment for `order` is under the key of `order`.
  have hjob : ∀ slot ∈ d.2.server.slots, slot.request.order = order →
      ∃ j ∈ charges.jobs w.db, slot.key = some j.id ∧ j.key = chargeKey order := by
    intro slot hslot hord
    obtain ⟨id, hkey, hh⟩ := hslots slot hslot
    obtain ⟨-, j, hj, hid, hwork⟩ := hh w hw w hself
    refine ⟨j, hj, hid ▸ hkey, ?_⟩
    rw [hkeyed w hw w hself j hj, hwork, hord]
  unfold chargesFor
  refine count_le _ (fun s : Idempotent.Slot Int64 Charge Answer => s.key)
    (fun s : Idempotent.Slot Int64 Charge Answer => s.request.order == order)
    (Idempotent.keys_nodup _ _ _ (Outside.after_both _ _ _ hd).2) ?_ ?_
  · intro a ha b hb hpa hpb
    obtain ⟨ja, hja, hka, hkeya⟩ := hjob a ha (by simpa using hpa)
    obtain ⟨jb, hjb, hkb, hkeyb⟩ := hjob b hb (by simpa using hpb)
    rw [hka, hkb, hone w hw w hself ja hja jb hjb (hkeya.trans hkeyb.symm)]
  · intro a ha hpa
    obtain ⟨_, _, hka, _⟩ := hjob a ha (by simpa using hpa)
    simp [hka]

end Shop
