/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Services.S3.Multipart
public import Std.Time

/-!
The S3 client's IO: credentials from the environment, or read at each call from a source, the
time to sign with, and the call made through the HTTP client. A system calls the store with an
output and is told the answer, or `unknown`, with an input (`S3.handler`); what the answer means
and what is signed are the pure `Lanes.Services.S3.Basic`. Secrets are never formatted or logged
here.
-/

public section

namespace Lanes.SigV4

/-- Credentials as each call reads them: fixed, or kept fresh by something else, such as an
integration that fetches a role's before they expire. `none` when there are none now. -/
structure Source where
  read : IO (Option Credentials)

def Source.fixed (creds : Credentials) : Source := ⟨pure (some creds)⟩

instance : Coe Credentials Source := ⟨Source.fixed⟩

end Lanes.SigV4

namespace Lanes.S3

open Std Std.Async Http

/-- Credentials from `AWS_ACCESS_KEY_ID`, `AWS_SECRET_ACCESS_KEY` and, for a role's,
`AWS_SESSION_TOKEN`: `none` unless the first two are set and not empty. Read once, at start, and
passed on (rule 2.5). -/
def credentialsFromEnv : IO (Option SigV4.Credentials) := do
  let some id := (← IO.getEnv "AWS_ACCESS_KEY_ID").filter (!·.isEmpty) | return none
  let some secret := (← IO.getEnv "AWS_SECRET_ACCESS_KEY").filter (!·.isEmpty) | return none
  let token := (← IO.getEnv "AWS_SESSION_TOKEN").filter (!·.isEmpty)
  return some { accessKeyId := id, secretAccessKey := ⟨secret⟩, sessionToken := token.map (⟨·⟩) }

/-- The wall clock, to the second, as a signature names it. -/
def now : IO Civil.DateTime := do
  let ms := (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.toInt
  return Civil.DateTime.ofUnix (ms / 1000)

/-- Does `op` on `b`: the answer, or `none` when there is none by the deadline, which says
nothing about whether it took effect, or when the source has no credentials, and nothing is
sent. -/
def exchange (b : Bucket) (creds : SigV4.Source) (op : Op) (config : Client.Config := {})
    (payload : Payload := .signed) : Async (Option Answer) := do
  let some creds ← creds.read | return none
  let call := S3.call b creds (← now) op payload
  return (← Client.exchange call config).map (interpret op)

/-- Uploads `body` to `key` in parts, as `flow` decides, and returns where the flow ended:
`done` with the object's ETag, or `failed` with why. -/
def upload (b : Bucket) (creds : SigV4.Source) (flow : Multipart.Flow) (body : ByteArray)
    (config : Client.Config := {}) : Async Multipart.Phase := do
  let mut f := flow
  for _ in [0:flow.bound] do
    let some step := f.next | break
    let answer ← try exchange b creds (f.op body step) config catch _ => pure none
    f := f.answer answer
  return f.phase

/-- Which outputs are calls to the store, and the input that answers one. -/
structure Port (σ : Signature) where
  called : σ.Out → Option (Rpc.Call Op)
  reply : (call : Nat) → Rpc.Reply Answer → σ.In

/-- Makes the call on a task of its own, with the call's deadline, and hands the answer back as
an input, or `unknown`. An answer that finds the inbox full is dropped. -/
def handler {σ : Signature} {sys : System σ} [Hashable σ.Id] (port : Port σ) (b : Bucket)
    (creds : SigV4.Source) (config : Client.Config := {}) (rt : Runtime sys) (out : σ.Out) :
    Async Unit := do
  if let some call := port.called out then
    background do
      let answer ← try exchange b creds call.request { config with timeout_ms := call.deadline_ms }
        catch _ => pure none
      discard <| rt.tryInput (port.reply call.id (match answer with
        | some a => .answer a
        | none => .unknown))

end Lanes.S3
