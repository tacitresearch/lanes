# D?. A vendor service gets a model only when a proof depends on it

Status: Accepted

This refines the environment section of `docs/decisions/D110-volatile-actors.md` for its third
layer, the vendor services of `Lanes/Services/`. The first two layers are unchanged.

## The rule

- **Layers 1 and 2 stay whole in the core.** The platform models and every generic service
  shape of `Lanes/Outside/` (the cache, the throttling service, the queue, webhooks, idempotency
  keys, lifecycles, the store, the object store) are library pieces that applications use,
  whether or not a service of `Lanes/Services/` uses them. None is removed because no vendor
  service uses it. A shape with no run recorded from a real system says, in its header and in
  ARCHITECTURE's limits, that it is not yet checked against a real service.
- **A vendor service gets its own model and an oracle only when an application's proof depends
  on how that service behaves.** Such a service is *checked*: a client, a model built from a
  shape of the core, and an oracle against the real service or an emulator. Postgres (the
  key-value store and the typed store of D111), S3 (the object store and multipart uploads),
  SES (email) and payments are checked.
- **Any other vendor service is a client only, with tests.** The sign-in presets for Google and
  GitHub are configuration, tested against responses recorded from the vendor or written from
  its documentation; the protocol and its proofs stay in `Lanes/Web/Auth/`. AWS's role
  credentials keep their proved refresh machine. CloudFront is a pure signing function tested
  against botocore. SQS is its calls.
- **A client-only service may still be paired with a shape of layer 2** when an application
  needs it: SQS's calls with the queue shape, checked against moto's SQS
  (`Tests/Aws/SqsMoto.lean`).

Each service's README says which it is: "checked: model plus oracle", or "client only".

## Why

A model and its oracle cost work to write and to keep recorded against the service. They pay
for themselves only where a theorem about an application rests on the service doing no more
than its model allows. Where no proof rests on it, a client with tests says what is needed,
and a model would be a premise nobody uses.

The shapes are different: they are the vocabulary an application states its outside in, and
an application that proves something about a cache or a queue needs the shape whether or not
Lanes ships a vendor's client for it.
