/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Shop

/-!
# An order the shop calls paid has a payment that succeeded

In every run of the shop, under every environment model, beside any customers and the payment
service's model: every order the shop holds as paid, and every order it has told its customer
is paid, has a payment at the service that succeeded and was made for that order
(`paid_succeeded`). It needs no premise about keys: a retry without the key may charge twice,
but the shop still says paid only of a payment that succeeded.

The shop marks an order paid on two messages: an answer that the payment of a call succeeded,
and a webhook that a payment succeeded. The model allows a webhook only about a payment it holds
in that state, and an answer only about the payment of the call's slot, whose request is the
call's (`Effects.Sound.shows_report`, `Effects.Sound.shows_reply`); a payment that succeeded stays
so (`Payments.succeeded_terminal`). What ties a call to its order is `calls`, the shop's own
record, which the call's id indexes once (`Fresh`): the invariant `Inv` relates it to the routes
of the service's model, and asks of every answer and webhook in flight that it be true already.
-/

namespace Shop

open Lanes

variable {config : Config}

/-- The service holds a payment that succeeded, made for `order`. -/
def Succeeded (held : Held) (order : Nat) : Prop :=
  ∃ p : Charge, p.order = order ∧ Effects.Shows held.server .succeeded p

theorem Succeeded.keeps {held held' : Held}
    (h : Effects.Keeps .succeeded held.server.inner.inner held'.server.inner.inner) {order : Nat}
    (hs : Succeeded held order) : Succeeded held' order := by
  obtain ⟨p, hp, hs⟩ := hs
  exact ⟨p, hp, h.shows hs⟩

/-! ## The shop's steps -/

/-- The message says that the payment of `order` succeeded. -/
def Justified (s : State) (msg : Msg) (order : Nat) : Prop :=
  (∃ w : Webhook, msg = .webhook w ∧ w.state = .succeeded ∧ w.params.order = order) ∨
    ∃ id r, msg = .reply id (.answer (.made r .succeeded)) ∧ s.calls.lookup id = some order

/-- Every call recorded has an id below the next. -/
def Fresh (s : State) : Prop := ∀ p ∈ s.calls, p.1 < s.nextCall

/-- What a step from `s` on `msg` to `r` keeps: calls recorded stay, each charge is of the order
recorded for its call, an order paid was paid or `msg` says so, and so does every `paid` told. -/
structure Good (s : State) (msg : Msg) (r : State × List Eff) : Prop where
  fresh : Fresh r.1
  keeps : ∀ id order, s.calls.lookup id = some order → r.1.calls.lookup id = some order
  charge : ∀ call, Effect.emit (Out.charge call) ∈ r.2 →
    r.1.calls.lookup call.id = some call.request.request.order
  paid : ∀ o ∈ r.1.orders, o.status = .paid →
    (∃ o₀ ∈ s.orders, o₀.order = o.order ∧ o₀.status = .paid) ∨ Justified s msg o.order
  told : ∀ order, Effect.emit (Out.paid order) ∈ r.2 → Justified s msg order
  sends : ∀ to m, Effect.send to m ∉ r.2
  armed : ∀ delay m, Effect.after delay m ∈ r.2 → ∃ id, m = .expire id

/-- An effect that sends nothing, emits no charge and no `paid`, and arms only a deadline. -/
def Quiet (eff : Eff) : Prop :=
  (∀ call, eff ≠ .emit (Out.charge call)) ∧ (∀ order, eff ≠ .emit (Out.paid order)) ∧
    (∀ to m, eff ≠ .send to m) ∧ ∀ delay m, eff = .after delay m → ∃ id, m = .expire id

theorem lookup_cons_of_fresh {s : State} (hs : Fresh s) {id order : Nat} (o : Nat)
    (h : s.calls.lookup id = some order) :
    ((s.nextCall, o) :: s.calls).lookup id = some order := by
  obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.mp h
  have hlt := hs (id, order) (by simp [hl])
  have hne : (id == s.nextCall) = false := by simp; omega
  simp [List.lookup_cons, hne, h]

theorem mem_setStatus {s : State} {order : Nat} {status : Status} {o : Order}
    (h : o ∈ (setStatus s order status).orders) :
    o ∈ s.orders ∨ (o.order = order ∧ o.status = status) := by
  simp only [setStatus, List.mem_map] at h
  obtain ⟨o', ho', rfl⟩ := h
  split
  · next heq => exact .inr ⟨heq, rfl⟩
  · exact .inl ho'

theorem find_order {s : State} {order : Nat} {o : Order} (h : find s order = some o) :
    o ∈ s.orders ∧ o.order = order :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- A step that only changes statuses to one that is not `paid`, with quiet effects. -/
theorem good_of {s s' : State} {msg : Msg} {effs : List Eff} (hs : Fresh s)
    (hcalls : s'.calls = s.calls) (hnext : s'.nextCall = s.nextCall)
    (hpaid : ∀ o ∈ s'.orders, o.status = .paid → ∃ o₀ ∈ s.orders, o₀.order = o.order ∧
      o₀.status = .paid)
    (hquiet : ∀ eff ∈ effs, Quiet eff) : Good s msg (s', effs) where
  fresh := by intro p hp; rw [hnext]; exact hs p (hcalls ▸ hp)
  keeps _ _ h := by simpa [hcalls] using h
  charge call h := absurd rfl ((hquiet _ h).1 call)
  paid o ho hst := .inl (hpaid o ho hst)
  told order h := absurd rfl ((hquiet _ h).2.1 order)
  sends to m h := (hquiet _ h).2.2.1 to m rfl
  armed delay m h := (hquiet _ h).2.2.2 delay m rfl

theorem quiet_stopWaiting (o : Order) : ∀ eff ∈ stopWaiting o, Quiet eff := by
  intro eff h
  unfold stopWaiting at h
  split at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;>
    subst h <;> simp [Quiet]

theorem paid_setStatus {s : State} {order : Nat} {status : Status} (hst : status ≠ .paid) :
    ∀ o ∈ (setStatus s order status).orders, o.status = .paid →
      ∃ o₀ ∈ s.orders, o₀.order = o.order ∧ o₀.status = .paid := by
  intro o ho hpaid
  rcases mem_setStatus ho with ho | ⟨-, rfl⟩
  · exact ⟨o, ho, rfl, hpaid⟩
  · exact absurd hpaid hst

theorem good_call {s s₀ : State} {msg : Msg} (hs : Fresh s) (hcalls : s₀.calls = s.calls)
    (hnext : s₀.nextCall = s.nextCall)
    (hpaid : ∀ o ∈ s₀.orders, o.status = .paid → ∃ o₀ ∈ s.orders, o₀.order = o.order ∧
      o₀.status = .paid) (o : Order) (attempt : Nat) :
    Good s msg (call config s₀ o attempt) where
  fresh := by
    intro p hp
    simp only [call, setStatus, List.mem_cons] at hp ⊢
    rcases hp with rfl | hp
    · omega
    · have := hs p (hcalls ▸ hp); omega
  keeps id order h := by
    simp only [call, setStatus, hcalls, hnext]
    exact lookup_cons_of_fresh hs _ h
  charge c h := by
    simp only [call, List.mem_cons, Effect.emit.injEq, Out.charge.injEq, reduceCtorEq,
      List.not_mem_nil, or_false] at h
    subst h
    simp [call, setStatus]
  paid o' ho' hst := by
    simp only [call] at ho'
    rcases mem_setStatus ho' with ho' | ⟨-, h⟩
    · exact .inl (hpaid o' ho' hst)
    · rw [h] at hst; cases hst
  told order h := by simp [call] at h
  sends to m h := by simp [call] at h
  armed delay m h := by
    simp only [call, List.mem_cons, reduceCtorEq, Effect.after.injEq, List.not_mem_nil,
      or_false, false_or] at h
    exact ⟨_, h.2⟩

theorem good_retry {s : State} {msg : Msg} (hs : Fresh s) (o : Order) (attempt : Nat) :
    Good s msg (retry config s o attempt) := by
  unfold retry
  split
  · exact good_call hs rfl rfl (fun o ho hst => ⟨o, ho, rfl, hst⟩) o _
  · exact good_of hs rfl rfl (paid_setStatus (by simp)) (by simp)

theorem good_settle {s : State} {msg : Msg} (hs : Fresh s) (o : Order) (st : Payments.Status)
    (hj : st = .succeeded → Justified s msg o.order) : Good s msg (settle s o st) := by
  unfold settle
  split
  · exact good_of hs rfl rfl (fun o ho hst => ⟨o, ho, rfl, hst⟩) (by simp)
  · refine ⟨hs, fun _ _ h => h, ?_, ?_, ?_, ?_, ?_⟩
    · intro c h
      simp only [List.mem_append, List.mem_singleton, Effect.emit.injEq, reduceCtorEq,
        or_false] at h
      exact absurd rfl ((quiet_stopWaiting o _ h).1 c)
    · intro o' ho' hst
      rcases mem_setStatus ho' with ho' | ⟨h, -⟩
      · exact .inl ⟨o', ho', rfl, hst⟩
      · exact .inr (h ▸ hj rfl)
    · intro order h
      simp only [List.mem_append, List.mem_singleton, Effect.emit.injEq, Out.paid.injEq] at h
      rcases h with h | rfl
      · exact absurd rfl ((quiet_stopWaiting o _ h).2.1 order)
      · exact hj rfl
    · intro to m h
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h
      exact (quiet_stopWaiting o _ h).2.2.1 to m rfl
    · intro delay m h
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h
      exact (quiet_stopWaiting o _ h).2.2.2 delay m rfl
  · exact good_of hs rfl rfl (fun o ho hst => ⟨o, ho, rfl, hst⟩) (by simp)
  · refine good_of hs rfl rfl (paid_setStatus (by simp)) ?_
    intro eff h
    simp only [List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact quiet_stopWaiting o _ h
    · simp [Quiet]
  · exact good_of hs rfl rfl (paid_setStatus (by simp)) (quiet_stopWaiting o)

theorem good_place {s : State} {msg : Msg} (hs : Fresh s) (order amount : Nat) :
    Good s msg (place config s order amount) := by
  unfold place
  split
  · exact good_of hs rfl rfl (fun o ho hst => ⟨o, ho, rfl, hst⟩) (by simp)
  · split
    · exact good_of hs rfl rfl (fun o ho hst => ⟨o, ho, rfl, hst⟩) (by simp [Quiet])
    · refine good_call (s₀ := { s with orders := ⟨order, amount, .waiting⟩ :: s.orders }) hs rfl rfl
        ?_ ⟨order, amount, .waiting⟩ 1
      intro o ho hst
      simp only [List.mem_cons] at ho
      rcases ho with rfl | ho
      · cases hst
      · exact ⟨o, ho, rfl, hst⟩

theorem Good.cancel {s : State} {msg : Msg} {r : State × List Eff} (h : Good s msg r) (m : Msg) :
    Good s msg (r.1, .cancel m :: r.2) := by
  refine ⟨h.fresh, h.keeps, ?_, h.paid, ?_, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, reduceCtorEq, false_or] at hc
    exact h.charge c hc
  · intro order ho
    simp only [List.mem_cons, reduceCtorEq, false_or] at ho
    exact h.told order ho
  · intro to m' hm
    simp only [List.mem_cons, reduceCtorEq, false_or] at hm
    exact h.sends to m' hm
  · intro delay m' hm
    simp only [List.mem_cons, reduceCtorEq, false_or] at hm
    exact h.armed delay m' hm

theorem good_replied {s : State} (hs : Fresh s) (id : Nat) (reply : Rpc.Reply Answer) :
    Good s (.reply id reply) (replied config s id reply) := by
  unfold replied
  split
  · exact good_of hs rfl rfl (fun o ho hst => ⟨o, ho, rfl, hst⟩) (by simp)
  · next o ho =>
    obtain ⟨order, horder, hfind⟩ := Option.bind_eq_some_iff.mp ho
    split
    · next r st =>
      refine good_settle hs o st fun hst => .inr ⟨id, r, by rw [hst], ?_⟩
      rw [horder, (find_order hfind).2]
    · split
      · exact (good_retry hs o _).cancel _
      · exact good_of hs rfl rfl (fun o ho hst => ⟨o, ho, rfl, hst⟩) (by simp)
    · exact good_of hs rfl rfl (fun o ho hst => ⟨o, ho, rfl, hst⟩) (by simp)

theorem good_expired {s : State} {msg : Msg} (hs : Fresh s) (id : Nat) :
    Good s msg (expired config s id) := by
  unfold expired
  split
  · split
    · split
      · exact good_retry hs _ _
      · exact good_of hs rfl rfl (fun o ho hst => ⟨o, ho, rfl, hst⟩) (by simp)
    · exact good_of hs rfl rfl (fun o ho hst => ⟨o, ho, rfl, hst⟩) (by simp)
  · exact good_of hs rfl rfl (fun o ho hst => ⟨o, ho, rfl, hst⟩) (by simp)

theorem good_step {s : State} (hs : Fresh s) (msg : Msg) : Good s msg (step config s msg) := by
  cases msg with
  | order order amount => exact good_place hs order amount
  | reply id reply => exact good_replied hs id reply
  | webhook e =>
    show Good s (.webhook e) (match find s e.params.order with
      | some o => settle s o e.state
      | none => (s, []))
    split
    · next o ho =>
      exact good_settle hs o e.state fun hst =>
        .inl ⟨e, rfl, hst, (find_order ho).2.symm⟩
    · exact good_of hs rfl rfl (fun o ho hst => ⟨o, ho, rfl, hst⟩) (by simp)
  | expire id => exact good_expired hs id

theorem rearm_after {s : State} {eff : Eff} (h : eff ∈ rearm config s) :
    ∃ delay id, eff = .after delay (.expire id) := by
  obtain ⟨o, -, ho⟩ := List.mem_filterMap.mp h
  split at ho
  · obtain rfl := Option.some.inj ho
    exact ⟨_, _, rfl⟩
  · simp at ho

/-! ## The shop beside the service -/

/-- What holds of the shop beside the service's model: the model is `Sound`; the shop's calls,
deadlines and charges are of its own record; a route to a slot of the same request is of the
order recorded for its call; and every order paid, every `paid` waiting to go out, and every
webhook or answer in flight that says a payment succeeded, is of a payment that did. -/
structure Inv (config : Config) (c : SysState (shop config)) (held : Held) : Prop where
  sound : Effects.Sound .succeeded held.server
  fresh : Fresh (c.state ())
  timers : ∀ m ∈ c.timers (), ∃ id, m = Msg.expire id
  outbox : ∀ call, Out.charge call ∈ c.outbox →
    (c.state ()).calls.lookup call.id = some call.request.request.order
  routes : ∀ id r, held.server.routes.find? (·.call == id) = some r → r.same = true →
    ∃ slot, held.server.slots[r.slot]? = some slot ∧
      (c.state ()).calls.lookup id = some slot.request.order
  orders : ∀ o ∈ (c.state ()).orders, o.status = .paid → Succeeded held o.order
  webhooks : ∀ e ∈ c.net, ∀ w : Webhook, e.msg = Msg.webhook w → w.state = .succeeded →
    Succeeded held w.params.order
  replies : ∀ e ∈ c.net, ∀ id r, e.msg = Msg.reply id (.answer (.made r .succeeded)) →
    ∃ order, (c.state ()).calls.lookup id = some order ∧ Succeeded held order
  told : ∀ order, Out.paid order ∈ c.outbox → Succeeded held order

theorem Inv.below {c c' : SysState (shop config)} {held : Held} (h : Inv config c held)
    (hb : c'.Below c) : Inv config c' held := by
  have hs : c'.state () = c.state () := congrFun hb.state ()
  refine ⟨h.sound, hs ▸ h.fresh, fun m hm => h.timers m (hb.timers () m hm), ?_, ?_, ?_,
    fun e he => h.webhooks e (hb.net e he), ?_, fun order ho => h.told order (hb.outbox _ ho)⟩
  · intro call hc; rw [hs]; exact h.outbox call (hb.outbox _ hc)
  · intro id r hr hsame; rw [hs]; exact h.routes id r hr hsame
  · intro o ho hst; rw [hs] at ho; exact h.orders o ho hst
  · intro e he id r hm; rw [hs]; exact h.replies e (hb.net e he) id r hm

theorem inv_blank (maxDeliveries : Nat) :
    Inv config (SysState.blank (shop config)) (service maxDeliveries).init := by
  refine ⟨Effects.sound_init, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [SysState.blank, Fresh, service, Payments.outside, Effects.outside, Rpc.outside,
      Effects.service, Idempotent.server]

theorem sends_nil {effs : List Eff} (h : ∀ to m, Effect.send to m ∉ effs) :
    Effect.sends (σ := sig) () effs = [] := by
  refine List.eq_nil_iff_forall_not_mem.mpr fun e he => ?_
  exact h _ _ (Effect.mem_sends.mp he).2

/-- What a message from outside says, the service's model allows only when it is true. -/
theorem Inv.input_service {c : SysState (shop config)} {held held' : Held} {maxDeliveries : Nat}
    (h : Inv config c held) {x : In}
    (hallow : (service maxDeliveries).allow held x = some held') :
    Inv config { c with net := c.net ++ [⟨none, ((shop config).accept x).1,
      ((shop config).accept x).2⟩] } held' := by
  obtain ⟨hsound, hkeeps⟩ := h.sound.allow Payments.succeeded_terminal hallow
  obtain ⟨hroutes, hreq⟩ := Effects.allow_requests hallow
  refine ⟨hsound, h.fresh, h.timers, h.outbox, ?_, fun o ho hst => (h.orders o ho hst).keeps hkeeps,
    ?_, ?_, fun order ho => (h.told order ho).keeps hkeeps⟩
  · intro id r hr hsame
    rw [hroutes] at hr
    obtain ⟨slot, hslot, hlookup⟩ := h.routes id r hr hsame
    have := hreq r.slot
    rw [hslot] at this
    obtain ⟨slot', hslot', hreq'⟩ := Option.map_eq_some_iff.mp this
    exact ⟨slot', hslot', hreq' ▸ hlookup⟩
  · intro e he w hw hst
    rcases List.mem_append.mp he with he | he
    · exact (h.webhooks e he w hw hst).keeps hkeeps
    · simp only [List.mem_singleton] at he
      subst he
      cases x with
      | webhook w' =>
        obtain rfl : w = w' := by simpa using hw.symm
        exact ⟨w.params, rfl, h.sound.shows_report Payments.succeeded_terminal
          (port := port) (x := .webhook w) rfl hst hallow⟩
      | _ => simp at hw
  · intro e he id r hm
    rcases List.mem_append.mp he with he | he
    · obtain ⟨order, hl, hs⟩ := h.replies e he id r hm
      exact ⟨order, hl, hs.keeps hkeeps⟩
    · simp only [List.mem_singleton] at he
      subst he
      cases x with
      | reply id' reply =>
        obtain ⟨rfl, rfl⟩ : id = id' ∧ reply = .answer (.made r .succeeded) := by
          simp only [Msg.reply.injEq] at hm
          exact ⟨hm.1.symm, hm.2⟩
        obtain ⟨rt, hrt, hsame, slot, hslot, hshows⟩ := h.sound.shows_reply
          Payments.succeeded_terminal (port := port) (x := .reply id _) rfl hallow
        obtain ⟨slot', hslot', hlookup⟩ := h.routes id rt hrt hsame
        rw [hslot] at hslot'
        obtain rfl := Option.some.inj hslot'
        exact ⟨_, hlookup, slot.request, rfl, hshows⟩
      | _ => simp at hm

theorem Inv.input_order {c : SysState (shop config)} {held : Held} (h : Inv config c held)
    {x : In} (hx : isOrder x = true) :
    Inv config { c with net := c.net ++ [⟨none, ((shop config).accept x).1,
      ((shop config).accept x).2⟩] } held := by
  cases x with
  | order order amount =>
    refine ⟨h.sound, h.fresh, h.timers, h.outbox, h.routes, h.orders, ?_, ?_, h.told⟩
    · intro e he w hw hst
      rcases List.mem_append.mp he with he | he
      · exact h.webhooks e he w hw hst
      · simp only [List.mem_singleton] at he; subst he; simp at hw
    · intro e he id r hm
      rcases List.mem_append.mp he with he | he
      · exact h.replies e he id r hm
      · simp only [List.mem_singleton] at he; subst he; simp at hm
  | _ => simp [isOrder] at hx

/-- A charge handed to the service adds the route of its call, to a slot of the order recorded
for that call. -/
theorem Inv.output {c : SysState (shop config)} {held : Held} {maxDeliveries : Nat}
    (h : Inv config c held) {out : Out} (hout : out ∈ c.outbox) :
    Inv config { c with outbox := c.outbox.erase out } ((service maxDeliveries).observe held out) := by
  show Inv config _ ((Effects.outside port Payments.lifecycle maxDeliveries).observe held out)
  obtain ⟨hsound, hkeeps⟩ := h.sound.observe (port := port) (lifecycle := Payments.lifecycle)
    (maxDeliveries := maxDeliveries) out
  obtain ⟨hslots, hnone, hsome⟩ := Effects.observe_routes (port := port)
    (lifecycle := Payments.lifecycle) (maxDeliveries := maxDeliveries) (d := held) (out := out) rfl
  refine ⟨hsound, h.fresh, h.timers, fun call hc => h.outbox call (List.mem_of_mem_erase hc),
    ?_, fun o ho hst => (h.orders o ho hst).keeps hkeeps, fun e he w hw hst =>
      (h.webhooks e he w hw hst).keeps hkeeps, ?_,
    fun order ho => (h.told order (List.mem_of_mem_erase ho)).keeps hkeeps⟩
  · intro id r hr hsame
    have hold : ∀ r, held.server.routes.find? (·.call == id) = some r → r.same = true →
        ∃ slot, ((Effects.outside port Payments.lifecycle maxDeliveries).observe held
          out).server.slots[r.slot]? = some slot ∧
          (c.state ()).calls.lookup id = some slot.request.order := by
      intro r hr hsame
      obtain ⟨slot, hslot, hl⟩ := h.routes id r hr hsame
      exact ⟨slot, hslots _ _ hslot, hl⟩
    cases hcall : port.called out with
    | none => exact hold r (hnone hcall ▸ hr) hsame
    | some call =>
      obtain ⟨rt, hrts, hrt, hrtsame⟩ := hsome call hcall
      rw [hrts, List.find?_cons] at hr
      split at hr
      · next hid =>
        obtain rfl := Option.some.inj hr
        obtain ⟨slot, hslot, hreq⟩ := Option.map_eq_some_iff.mp (hrtsame hsame)
        refine ⟨slot, hslot, ?_⟩
        have hid : call.id = id := by simpa [hrt] using hid
        cases out with
        | charge c' =>
          obtain rfl : c' = call := by simpa [port] using hcall
          rw [← hid, hreq]
          exact h.outbox _ hout
        | _ => simp [port] at hcall
      · exact hold r hr hsame
  · intro e he id r hm
    obtain ⟨order, hl, hs⟩ := h.replies e he id r hm
    exact ⟨order, hl, hs.keeps hkeeps⟩

theorem Inv.justified {c : SysState (shop config)} {held : Held} (h : Inv config c held)
    {msg : Msg} (hpending : (∃ src, (⟨src, (), msg⟩ : Envelope sig) ∈ c.net) ∨ msg ∈ c.timers ())
    {order : Nat} (hj : Justified (c.state ()) msg order) : Succeeded held order := by
  rcases hpending with ⟨src, he⟩ | hm
  · rcases hj with ⟨w, rfl, hst, rfl⟩ | ⟨id, r, rfl, hl⟩
    · exact h.webhooks _ he w rfl hst
    · obtain ⟨order', hl', hs⟩ := h.replies _ he id r rfl
      rw [hl] at hl'
      exact Option.some.inj hl' ▸ hs
  · obtain ⟨id, rfl⟩ := h.timers _ hm
    rcases hj with ⟨w, hw, -⟩ | ⟨_, _, hr, -⟩
    · cases hw
    · cases hr

/-- A step of the shop on a message in flight or a deadline keeps the invariant. -/
theorem Inv.step {c : SysState (shop config)} {held : Held} (h : Inv config c held) (msg : Msg)
    (hpending : (∃ src, (⟨src, (), msg⟩ : Envelope sig) ∈ c.net) ∨ msg ∈ c.timers ()) :
    Inv config (c.grow () (((shop config).actor ()).step (c.state ()) msg)) held := by
  have hg := good_step (config := config) h.fresh msg
  simp only [SysState.grow, sends_nil hg.sends, List.append_nil]
  refine ⟨h.sound, hg.fresh, ?_, ?_, ?_, ?_, h.webhooks, ?_, ?_⟩
  · intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.timers m hm
    · obtain ⟨delay, hd⟩ := Effect.mem_armed.mp hm
      exact hg.armed delay m hd
  · intro call hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hg.keeps _ _ (h.outbox call hc)
    · exact hg.charge call (Effect.mem_emits.mp hc)
  · intro id r hr hsame
    obtain ⟨slot, hslot, hl⟩ := h.routes id r hr hsame
    exact ⟨slot, hslot, hg.keeps _ _ hl⟩
  · intro o ho hst
    rcases hg.paid o ho hst with ⟨o₀, ho₀, horder, hst₀⟩ | hj
    · exact horder ▸ h.orders o₀ ho₀ hst₀
    · exact h.justified hpending hj
  · intro e he id r hm
    obtain ⟨order, hl, hs⟩ := h.replies e he id r hm
    exact ⟨order, hg.keeps _ _ hl, hs⟩
  · intro order ho
    rcases List.mem_append.mp ho with ho | ho
    · exact h.told order ho
    · exact h.justified hpending (hg.told order (Effect.mem_emits.mp ho))

theorem Inv.recover {c : SysState (shop config)} {held : Held} (h : Inv config c held) :
    Inv config (c.grow () (((shop config).actor ()).recover (c.state ()))) held := by
  have hsends : Effect.sends (σ := sig) () (rearm config (c.state ())) = [] :=
    sends_nil fun to m hm => by obtain ⟨_, _, h⟩ := rearm_after hm; cases h
  have hemits : Effect.emits (rearm config (c.state ())) = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun out ho => by
      obtain ⟨_, _, h⟩ := rearm_after (Effect.mem_emits.mp ho); cases h
  simp only [SysState.grow]
  rw [hsends, hemits, List.append_nil, List.append_nil]
  refine ⟨h.sound, h.fresh, ?_, h.outbox, h.routes, h.orders, h.webhooks, h.replies, h.told⟩
  intro m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact h.timers m hm
  · obtain ⟨delay, hd⟩ := Effect.mem_armed.mp hm
    obtain ⟨_, id, h⟩ := rearm_after hd
    cases h
    exact ⟨id, rfl⟩

/-- The invariant beside any customers and the service's model, under every environment. -/
theorem beside {D : Type} (customers : Outside sig D) (config : Config) (maxDeliveries : Nat)
    (env : EnvModel sig) :
    (customers.both (service maxDeliveries) isOrder).Beside (shop config) env
      fun c d => Inv config c d.2 where
  blank := inv_blank maxDeliveries
  below _ _ _ h hb := h.below hb
  input c d x d' h hallow := by
    simp only [Outside.both] at hallow
    split at hallow
    · next hx =>
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hallow
      exact h.input_order hx
    · obtain ⟨held', hheld, rfl⟩ := Option.map_eq_some_iff.mp hallow
      exact h.input_service hheld
  output _ _ _ h hout := h.output hout
  step _ _ i msg _ h hpending := by
    cases i
    exact h.step msg hpending
  recover _ _ i h := by
    cases i
    exact h.recover

theorem keeps_see {D : Type} {customers : Outside sig D} {maxDeliveries : Nat}
    {c : SysState (shop config)} {d d' : D × Held} (h : Inv config c d.2) {ev : Event sig}
    (hsee : (customers.both (service maxDeliveries) isOrder).see d ev = some d') :
    Effects.Keeps .succeeded d.2.server.inner.inner d'.2.server.inner.inner := by
  cases ev with
  | input x =>
    simp only [Outside.see, Outside.both] at hsee
    split at hsee
    · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hsee
      exact fun t ht _ => ht
    · obtain ⟨held', hheld, rfl⟩ := Option.map_eq_some_iff.mp hsee
      exact (h.sound.allow Payments.succeeded_terminal hheld).2
  | output out =>
    simp only [Outside.see, Outside.both, Option.some.injEq] at hsee
    subst hsee
    exact (h.sound.observe (port := port) (lifecycle := Payments.lifecycle) out).2
  | _ =>
    simp only [Outside.see, Option.some.injEq] at hsee
    subst hsee
    exact fun t ht _ => ht

/-- An order the shop calls paid has a payment that succeeded: in every run of the shop under
every environment model, beside any customers and the payment service's model, every order the
shop holds as paid, and every order it has told its customer is paid, has a payment at the
service that succeeded, made for that order. -/
theorem paid_succeeded {D : Type} (customers : Outside sig D) (config : Config)
    (maxDeliveries : Nat) (env : EnvModel sig) {events : List (Event sig)}
    {c : SysState (shop config)}
    (hrun : (SysState.init (shop config) env).run env events = some c)
    {d : D × Held} (hd : (customers.both (service maxDeliveries) isOrder).after events = some d) :
    (∀ o ∈ (c.state ()).orders, o.status = .paid → Succeeded d.2 o.order) ∧
      ∀ order, Event.output (Out.paid order) ∈ events → Succeeded d.2 order := by
  have hb := beside customers config maxDeliveries env
  refine (customers.both (service maxDeliveries) isOrder).run_induction
    (P := fun events c d => Inv config c d.2 ∧
      ∀ order, Event.output (Out.paid order) ∈ events → Succeeded d.2 order)
    ⟨hb.init, by simp⟩ ?_ hrun hd |>.imp (fun h => h.orders) id
  intro evs c d ev c' d' hc ⟨hinv, hpaid⟩ hstep hsee
  refine ⟨hb.keeps hc hinv hstep hsee, fun order ho => ?_⟩
  have hkeeps := keeps_see hinv hsee
  rcases List.mem_append.mp ho with ho | ho
  · exact (hpaid order ho).keeps hkeeps
  · simp only [List.mem_singleton] at ho
    subst ho
    exact (hinv.told order (SysState.step_output.mp hstep).1).keeps hkeeps

end Shop
