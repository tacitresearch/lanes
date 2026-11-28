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

/-- The keys the adapter has sent (`Sent`), in a file of its own, so that a restart remembers
them. The file is replaced whole, and synced, before each send (`File.replace`). -/
structure Once where
  path : System.FilePath
  sent : IO.Ref Sent

/-- The keys in the file at `path`, or none if there is no file. -/
def Once.open (path : System.FilePath) : IO Once := do
  let sent ← match ← (IO.FS.readFile path).toBaseIO with
    | .ok text => pure (Sent.read text)
    | .error (.noFileOrDirectory ..) => pure []
    | .error e => throw e
  return { path, sent := ← IO.mkRef sent }

/-- Whether to send the output with `key`. A new key is written down, and on the disk, before
this answers, so that a send the process may have made is never made again. -/
def Once.admit (once : Once) (key : String) : IO Bool := do
  let sent ← once.sent.get
  if !sent.admits key then return false
  let sent := sent.record key
  File.replace once.path sent.write
  once.sent.set sent
  return true

/-- `handler`, sending each output at most once by the key the application gives it (`key`): an
output whose key was sent already, or may have been, also before a restart, is not sent, and is
answered `unknown`; so is one whose key is not `Sent.valid`. An output with no key is sent as
`handler` sends it. The shard calls its handler one output at a time, so `Once` needs no lock. -/
def handlerOnce {σ : Signature} {sys : System σ} [Hashable σ.Id] (once : Once) (port : Port σ)
    (key : σ.Out → Option String) (e : Endpoint) (creds : SigV4.Source)
    (config : Client.Config := {}) (rt : Runtime sys) (out : σ.Out) : Async Unit := do
  if let some call := port.called out then
    match key out with
    | none => sendCall port e creds config rt call
    | some k =>
      if ← once.admit k then sendCall port e creds config rt call
      else discard <| rt.tryInput (port.reply call.id .unknown)

end Aws.Ses
