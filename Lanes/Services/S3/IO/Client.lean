/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Services.S3.Multipart
public import Lanes.Services.S3.Post
public import Std.Time

/-!
The S3 client's IO: credentials from the environment, or read at each call from a source, the
time to sign with, and the call made through the HTTP client. A system calls the store with an
output and is told the answer, or `unknown`, with an input (`S3.handler`); what the answer means
and what is signed are the pure `Lanes.Services.S3.Basic`. Links and forms for a browser are
signed here too, at the time and with the credentials of the moment (`presignNow`,
`Post.formNow`), for no longer than those credentials last (`S3.expiryWithin`). Secrets are
never formatted or logged here.
-/

public section

namespace Lanes.SigV4

/-- Credentials as each call reads them: fixed, or kept fresh by something else, such as a
provider that fetches a role's before they expire (`Aws.Credentials.Provider`). `none` when
there are none now. -/
structure Source where
  /-- The credentials to sign with now, and when they expire, in milliseconds since the epoch,
  if they do. -/
  current : IO (Option (Credentials × Option Nat))

def Source.read (s : Source) : IO (Option Credentials) := return (← s.current).map (·.1)

def Source.fixed (creds : Credentials) : Source := ⟨pure (some (creds, none))⟩

instance : Coe Credentials Source := ⟨Source.fixed⟩

end Lanes.SigV4

namespace Lanes.S3

open Std Std.Async Http

/-- Credentials from `AWS_ACCESS_KEY_ID`, `AWS_SECRET_ACCESS_KEY` and, for a role's,
`AWS_SESSION_TOKEN`: `none` unless the first two are set and not empty. Read once, at start, and
passed on (rule 2.5). -/
def credentialsFromEnv : IO (Option SigV4.Credentials) := do
  let names := ["AWS_ACCESS_KEY_ID", "AWS_SECRET_ACCESS_KEY", "AWS_SESSION_TOKEN"]
  let values ← names.mapM fun n => return (n, ← IO.getEnv n)
  return credentialsOf? fun n => (values.lookup n).join

def nowMs : IO Nat := return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.toInt.toNat

/-- The wall clock, to the second, as a signature names it. -/
def now : IO Civil.DateTime := do
  return Civil.DateTime.ofUnix ((← nowMs) / 1000)

/-- The credentials of the moment and how long what is signed with them may last, from the
time it is signed, with that time: `none` when there are none, or less than a second of them is
left. -/
def signing (creds : SigV4.Source) (expiry : SigV4.Expiry) :
    IO (Option (SigV4.Credentials × SigV4.Expiry × Civil.DateTime)) := do
  let some (c, until_ms) ← creds.current | return none
  let ms ← nowMs
  let some e := expiryWithin expiry ms until_ms | return none
  return some (c, e, Civil.DateTime.ofUnix (ms / 1000))

/-- A presigned link (`S3.presign`), signed now with the source's credentials, for `expiry` or
until they expire, whichever is sooner. -/
def presignNow (b : Bucket) (creds : SigV4.Source) (method : Http.Method) (key : Key)
    (expiry : SigV4.Expiry) (contentType : Option String := none) : IO (Option String) := do
  let some (c, e, t) ← signing creds expiry | return none
  return some (presign b c t method key e contentType)

/-- A form for one upload (`S3.Post.form`), signed now with the source's credentials, its
policy ending at its own expiry or when they expire, whichever is sooner. -/
def Post.formNow (b : Bucket) (creds : SigV4.Source) (p : Post.Policy) : IO (Option Post.Form) := do
  let some (c, e, t) ← signing creds p.expiry | return none
  return some (Post.form b c t { p with expiry := e })

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
