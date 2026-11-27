/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Aws.Ses

/-!
The SES adapter's IO: credentials read from their source at each send, the wall clock to sign
with, the call `Ses.call` builds made through the HTTP client, and `Ses.interpret`'s reading of
the answer handed back, or `unknown`. Nothing here prints or logs a message, an address or a
secret.
-/

namespace Aws.Ses

open Lanes Lanes.Http Std Std.Async

/-- Sends `m`: the answer, or `none` when there is none by the deadline, which says nothing about
whether it was sent, or when the source has no credentials, and nothing is sent. -/
def exchange (e : Endpoint) (creds : SigV4.Source) (m : Message) (config : Client.Config := {}) :
    Async (Option Answer) := do
  let some creds ← creds.read | return none
  return (← Client.exchange (call e creds (← S3.now) m) config).map interpret

/-- Sends on a task of its own, with the call's deadline, and hands the answer back as an input,
or `unknown`. An answer that finds the inbox full is dropped. -/
def handler {σ : Signature} {sys : System σ} [Hashable σ.Id] (port : Port σ) (e : Endpoint)
    (creds : SigV4.Source) (config : Client.Config := {}) (rt : Runtime sys) (out : σ.Out) :
    Async Unit := do
  if let some call := port.called out then
    background do
      let answer ← try exchange e creds call.request { config with timeout_ms := call.deadline_ms }
        catch _ => pure none
      discard <| rt.tryInput (port.reply call.id (match answer with
        | some a => .answer a
        | none => .unknown))

end Aws.Ses
