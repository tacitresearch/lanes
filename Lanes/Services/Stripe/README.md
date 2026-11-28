# Stripe

Status: **checked: model plus oracle**, because `examples/payments` proves a property against the
model (`docs/decisions/new-service-models.md`); the client and the oracle are still owed, so the
model is not yet checked against Stripe.

- **Client**: none yet.
- **Model**: `Payments.lean`, a payment with the statuses and webhooks Stripe documents for a
  PaymentIntent. It is a lifecycle of the core's shape of services that hold things which change
  on their own (`Lanes/Outside/Effects/Basic.lean`), behind idempotency keys
  (`Lanes/Outside/Idempotent.lean`) and with webhooks (`Lanes/Outside/Events.lean`).
  `examples/payments` proves a shop charges each order at most once against it.
- **Oracle**: none. Stripe's test mode needs a key, and stripe-mock keeps no state; the model is
  tested against runs written by hand (`Tests/Outside.lean`).
