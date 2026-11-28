/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Services.Aws.Ses
public import Lanes.Services.S3.IO.Client

/-!
The SES adapter's IO: credentials read from their source at each send, the wall clock to sign
with, the call `Ses.call` builds made through the HTTP client, and `Ses.interpret`'s reading of
the answer handed back, or `unknown`. Nothing here prints or logs a message, an address or a
secret.
-/

public section

namespace Aws.Ses

open Lanes Lanes.Http Std Std.Async

/-- Sends `m`: the answer, or `none` when there is none by the deadline, which says nothing about
whether it was sent, or when the source has no credentials, and nothing is sent. -/
def exchange (e : Endpoint) (creds : SigV4.Source) (m : Message) (config : Client.Config := {}) :
    Async (Option Answer) := do
  let some creds ← creds.read | return none
  return (← Client.exchange (call e creds (← S3.now) m) config).map interpret

private def sendCall {σ : Signature} {sys : System σ} [Hashable σ.Id] (port : Port σ)
    (e : Endpoint) (creds : SigV4.Source) (config : Client.Config) (rt : Runtime sys)
    (call : Rpc.Call Message) : Async Unit :=
  background do
    let answer ← try exchange e creds call.request { config with timeout_ms := call.deadline_ms }
      catch _ => pure none
    discard <| rt.tryInput (port.reply call.id (match answer with
      | some a => .answer a
      | none => .unknown))

/-- Sends on a task of its own, with the call's deadline, and hands the answer back as an input,
or `unknown`. An answer that finds the inbox full is dropped. -/
def handler {σ : Signature} {sys : System σ} [Hashable σ.Id] (port : Port σ) (e : Endpoint)
    (creds : SigV4.Source) (config : Client.Config := {}) (rt : Runtime sys) (out : σ.Out) :
    Async Unit := do
  if let some call := port.called out then sendCall port e creds config rt call

/-- An attempt of a job of an outbox (`Postgres.Typed.Worker.start`'s `perform`): the message
`render` makes of the job's work, sent once with the attempt's deadline. SES takes no
idempotency key, so the job's id is not sent (`jobPort`). -/
def perform {W : Type} (render : W → Message) (e : Endpoint) (creds : SigV4.Source)
    (config : Client.Config := {}) : Int64 → Nat → W → Async (Option Answer) :=
  fun _ deadline_ms work => exchange e creds (render work) { config with timeout_ms := deadline_ms }

end Aws.Ses
