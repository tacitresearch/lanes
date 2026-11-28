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

/-- What the adapter has sent (`Sent`), in a file of its own, so that a restart remembers it.
The file is replaced whole, and synced, before each send. -/
structure Once where
  path : System.FilePath
  sent : IO.Ref Sent

/-- The state in the file at `path`, or none sent if there is no file. A file that does not read
is refused, so that nothing is sent twice for want of reading it. -/
def Once.open (path : System.FilePath) : IO Once := do
  let sent ← match ← (IO.FS.readFile path).toBaseIO with
    | .ok text =>
      match Sent.read? text with
      | some sent => pure sent
      | none => throw (IO.userError s!"aws: {path} is not the state of an SES adapter")
    | .error (.noFileOrDirectory ..) => pure []
    | .error e => throw e
  return { path, sent := ← IO.mkRef sent }

/-- Whether to send the output `id`. A new one is written down, and on the disk, before this
answers, so that a send the process may have made is never made again. -/
def Once.admit (once : Once) (id : Journal.OutputId) : IO Bool := do
  let sent ← once.sent.get
  if !sent.admits id then return false
  let sent := sent.record id
  let scratch := once.path.addExtension "tmp"
  IO.FS.writeFile scratch sent.write
  Journal.fsync scratch.toString
  IO.FS.rename scratch once.path
  Journal.fsync ((once.path.parent.getD ".").toString)
  once.sent.set sent
  return true

/-- `handler`, sending each output at most once: an output handed over again, after a restart,
that was sent already, or may have been, is not sent, and is answered `unknown`. The shard
calls its handler one output at a time, so `Once` needs no lock. -/
def handlerOnce {σ : Signature} {sys : System σ} [Hashable σ.Id] (once : Once) (port : Port σ)
    (e : Endpoint) (creds : SigV4.Source) (config : Client.Config := {}) (rt : Runtime sys)
    (id : Journal.OutputId) (out : σ.Out) : Async Unit := do
  if let some call := port.called out then
    if ← once.admit id then sendCall port e creds config rt call
    else discard <| rt.tryInput (port.reply call.id .unknown)

end Aws.Ses
