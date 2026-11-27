# D?. Models of external services: calls that may not answer, keys, webhooks, and things with a lifecycle

D61 planned the models of external systems as classes built from combinators on `Outside`. This
is the first of them: the combinators, the class of services that hold things which change on
their own (`Effects`), and two instances, payments and email. It builds part of D61 and changes
none of it, except where it says so below.

## A model of a service, and an `Outside` of it

A service is modelled as an `Rpc.Server` (`Lanes/Outside/Rpc.lean`): a state, told each request
as it is sent, and which answers and events the service may give from it (`answer` and `event`
return `none` for those it may not). `Rpc.outside port server` is that as an `Outside`: each
open call is answered at most once, with an answer the server allows or with `unknown`, or
never; an event is reported when the server allows it. The combinators are functions from a
server to a server, not from an `Outside` to an `Outside` as D61 wrote, because they share one
state: an event about a payment depends on the payment the call made.

**An `unknown` says nothing.** An `Outside` acts only on inputs, so it cannot decide on its own,
between two inputs, that a request took effect. What it does instead is the point of the model:
a request has an effect slot from the moment it is sent, and the slot counts as an effect the
service may have had until an answer or an event shows what it was. A timeout leaves the slot
as it was. Safety is then stated of slots (`Shop.charges` counts them): "charged at most once"
means at most one payment the service has made *or may have made*, which is the only reading
under which a timeout can be honest.

**Idempotency** (`Lanes/Outside/Idempotent.lean`). A request under a key the service has seen
gets no slot of its own: it is routed to the first one's. A repeat with the same request is
answered as the first was, once the first answer is known (`Idempotent.answer_repeat`), or is
refused with no effect (`refusal`: Stripe's `409` while the first is still being handled, `400`
when the parameters differ); a repeat with other parameters can only be refused. A request
without a key always has a slot of its own. Proved: no two slots share a key
(`Idempotent.keys_nodup`), and a request whose parameters are always sent under one key has at
most one slot (`Idempotent.at_most_once`), in every run the model allows.

**Events** (`Lanes/Outside/Events.lean`). `Events.bounded maxDeliveries` delivers an event the
inner model allows at once or later, and again any time after, whatever the service did since,
up to `maxDeliveries` times (`Events.deliveries_le`). The bound is rule 2.6: without it the
checker never ends. A real service delivers at least once and may deliver more often than any
bound; a conformance test of a real run must stay within the bound it is checked with.

**Things with a lifecycle** (`Lanes/Outside/Effects/Basic.lean`). A `Lifecycle` says in which
states a thing may be when its request is answered (`first`), which moves the service may make
on its own (`next`), the phase of each state (created, pending, succeeded, failed, canceled), and
which states are reported by an event. A thing is seen by the answer to its request or by an
event, whichever comes first; an event about a state the thing may have passed through on the
way to the one it is in may still come after it (`Lifecycle.reaches`). The first answer to a
request whose thing an event showed first must name that thing, in a first state that can
reach the one it is in. `Effects.service` is the things behind keys with their events bounded,
and `Effects.at_most_once` the guarantee at this level.

**Where the proof of an application comes from.** `System.Emits.outputs` (`Lanes/Proof/Outputs.lean`)
lifts what every step and start of every actor emits to every output of every run, under every
environment model; `Outside.after_invariant` and `Outside.after_both` carry a property of the
model along the run it allows, beside other outsides. An application proves a fact about its own
steps (the shop sends every charge for an order under the order's key, `Shop.emits_keyed`) and
gets the rest from the model's theorem (`Shop.charged_at_most_once`, `examples/payments`).

## Payments in `Lanes/`, named after a class

D61 keeps vendors' names out of `Lanes/`. `Lanes/Outside/Effects/Payments.lean` is the class of
payment APIs that hold a payment intent, with the states and events Stripe documents for its
PaymentIntent, because they are the best documented; Stripe is named in its documentation and in
this decision, not in its identifiers. An integration for Stripe itself, with its client and
handler and the test of recorded test-mode runs against this model, is still for `integrations/`.
Whether the class should carry Stripe's state names, or be moved out with the integration when
there is one, is for the owner to decide.

## What is assumed of the real services

These are premises of every theorem about a system that uses the models, trusted and not proved
(`TRUSTED.md`, "Models of external services"). The recorded runs in `Tests/Outside.lean` are
written by hand in the shape the documentation gives; none has been recorded from a real
service. Each must be checked against the service's test mode by the integration.

Payments (Stripe's PaymentIntent, as documented, checked by nobody yet):

- A POST under an `Idempotency-Key` it has seen within 24 hours, with the same parameters,
  makes no second PaymentIntent: it is answered with the first response, or with `409` while the
  first is in progress; with other parameters it is answered `400`. **The model has no expiry**:
  a repeat more than 24 hours after the first would be a new payment. A system must stop
  retrying within the window; the shop's `maxAttempts` × `deadline_ms` is far below it, and that
  is not checked by anything.
- A first response is replayed byte for byte. The model is looser: a repeat answers the first
  answer it saw, and if none was seen, any answer that names the same intent in a first state
  that can reach the one it is in.
- A `5xx`, a `429` and a connection that ends without an answer are `unknown`: Stripe says a
  `500` may or may not have been executed. A `429` was not executed; calling it `unknown` allows
  more than Stripe does, which is safe.
- The statuses are `requires_payment_method`, `requires_confirmation`, `requires_action`,
  `processing`, `succeeded` and `canceled`; `requires_capture` (manual capture) is not modelled.
  A payment created and confirmed in one call is answered in any of them but `canceled`; a card
  declined is answered `402` with the intent in `requires_payment_method`, which an adapter reads
  as `made id requiresPaymentMethod`.
- The moves the service may make without the caller (`Payments.Status.next`), since the
  customer's browser confirms and the banks decide: from the `requires_*` states to the later
  ones, back to `requires_payment_method` on a failure, and to `canceled` from any but
  `processing`; `processing` ends in `succeeded` or `requires_payment_method`; `succeeded` and
  `canceled` are final (`Payments.final`).
- Webhooks `payment_intent.requires_action`, `.processing`, `.succeeded`, `.payment_failed`
  (entering `requires_payment_method`) and `.canceled` carry the intent, its status and the
  metadata of the request that made it (the model's `params`), so a system can tell which order
  a payment is for when it never had the answer. `payment_intent.created` and the other events
  are not modelled. They are retried until acknowledged, for up to three days, in no order.
  A webhook for an intent no request of the system made (one made in the Dashboard) is refused by
  the model, so an adapter must drop those by their metadata.

Email (an API that accepts an idempotency key, as Resend's does; Postmark and SES do not, and for
those a resend may send the message twice, which the model does not describe):

- A send is answered at once: accepted or rejected (a suppressed or invalid address).
- After that, webhooks report it sent on, delivered or bounced; an accepted message may still be
  rejected or bounce. A delivered message is final: a bounce after delivery, and complaints, are
  not modelled.

Not modelled at all: retrieving, listing, updating or cancelling a thing by request; refunds and
disputes; amounts and currencies as anything but parameters; time (a deadline is the adapter's,
and the model allows an answer at any moment); the service refusing a first request (a `400` for
bad parameters).

## Consequences

- `Shop.charged_at_most_once` holds under every environment model, for every customer, every
  `maxAttempts` and every bound on deliveries. With retries sent without the key, the checker
  finds an order charged twice in five steps (two slots), and both payments succeeding in seven.
- The checker explores the shop against one order in 1.2 million states, about twenty seconds:
  the model's answers are sampled (three statuses, `unknown`, a refusal, a fresh or a known
  payment id), not enumerated.
- That the shop marks an order paid only when the service says its payment succeeded is
  checked, not proved.
