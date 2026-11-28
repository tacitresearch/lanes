/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Services.Aws.Imds
public import Lanes.Services.S3.IO.Client

/-!
The credentials' IO: a task that reads the wall clock, ticks `Refresh.step` with it, makes the
fetch it says through the HTTP client, the calls `Imds.Flow` names in turn, and tells it the
answer with a jitter drawn here; then sleeps until the machine's wake, or a second, whichever
is sooner. What to fetch and when, what an answer means and what may be handed out are pure
(`Aws/Refresh.lean`, `Aws/Imds.lean`). The state is a pure value in a reference, so a reader
(`Provider.source`, read at each call by `S3.exchange`, and by `S3.presignNow` and
`S3.Post.formNow` with the expiry) sees one state or the next. Nothing here prints or logs a
secret: why the last fetch failed is kept, and says no value.

`find` reads the environment once and starts what `Imds.chain` says: keys used as they are, or
a provider of a container's or an instance's role.
-/

public section

namespace Aws.Credentials

open Lanes Lanes.Http Std Std.Async

def nowMs : IO Nat := return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.toInt.toNat

/-- One fetch, the calls of the flow made in turn, all within `deadline_ms`. -/
def fetch (source : Imds.Source) (deadline_ms : Nat) (client : Client.Config) :
    Async (Except String (Refresh.Held SigV4.Credentials)) := do
  let start ← nowMs
  let mut flow := Imds.Flow.start
  for _ in [0:3] do
    let some call := flow.call source | break
    let left := deadline_ms - ((← nowMs) - start)
    if left == 0 then return .error "no answer by the deadline"
    let answer ← try Client.exchange call { client with timeout_ms := left } catch _ => pure none
    flow := flow.next source answer
  return flow.result.getD (.error "the fetch did not end")

structure Provider where
  config : Refresh.Config
  state : IO.Ref (Refresh.State SigV4.Credentials)
  lastError : IO.Ref (Option String)
  stopped : IO.Ref Bool

/-- The credentials to sign with now, as `Refresh.current` says. -/
def Provider.read (p : Provider) : IO (Option SigV4.Credentials) := do
  return Refresh.current p.config (← p.state.get) (← nowMs)

/-- And when they expire (`Refresh.currentHeld`). -/
def Provider.current (p : Provider) : IO (Option (SigV4.Credentials × Option Nat)) := do
  return (Refresh.currentHeld p.config (← p.state.get) (← nowMs)).map fun h =>
    (h.creds, some h.expires_ms)

/-- The provider as the S3 client, or SES's, reads credentials: at each call. -/
def Provider.source (p : Provider) : SigV4.Source := ⟨p.current⟩

/-- Why the last fetch failed, if it did. -/
def Provider.failure (p : Provider) : IO (Option String) := p.lastError.get

def Provider.stop (p : Provider) : IO Unit := p.stopped.set true

/-- Starts fetching from `source` at once, and again before each expiry. -/
def start (source : Imds.Source) (config : Refresh.Config := {}) (client : Client.Config := {}) :
    Async Provider := do
  let p : Provider := { config, state := ← IO.mkRef {}, lastError := ← IO.mkRef none,
                        stopped := ← IO.mkRef false }
  background do
    repeat
      if ← p.stopped.get then break
      let now ← nowMs
      let call ← p.state.modifyGet fun s =>
        let (s', call) := Refresh.step config s (.tick now)
        (call, s')
      if let some call := call then
        let result ← try fetch source call.deadline_ms client
          catch _ => pure (.error "the fetch failed")
        p.lastError.set (match result with | .ok _ => none | .error e => some e)
        let jitter ← IO.rand 0 config.jitter_ms
        let reply : Rpc.Reply _ := match result with
          | .ok held => .answer held
          | .error _ => .unknown
        let now ← nowMs
        p.state.modify fun s => (Refresh.step config s (.reply now call.id reply jitter)).1
      let wake := (← p.state.get).wake
      let now ← nowMs
      Async.sleep (.ofNat (max 1 (min 1000 (wake - now))))
  return p

/-- The variables `Imds.chain` reads. -/
def chainVariables : List String :=
  ["AWS_ACCESS_KEY_ID", "AWS_SECRET_ACCESS_KEY", "AWS_SESSION_TOKEN",
   "AWS_CONTAINER_CREDENTIALS_RELATIVE_URI", "AWS_CONTAINER_CREDENTIALS_FULL_URI",
   "AWS_CONTAINER_AUTHORIZATION_TOKEN", "AWS_EC2_METADATA_DISABLED"]

/-- Where this process's credentials come from (`Imds.chain`), from its environment and the
token file `AWS_CONTAINER_AUTHORIZATION_TOKEN_FILE` names, read once. -/
def origin : IO Imds.Origin := do
  let env ← chainVariables.mapM fun name => return (name, ← IO.getEnv name)
  let tokenFile ← match ← IO.getEnv "AWS_CONTAINER_AUTHORIZATION_TOKEN_FILE" with
    | some path => try some <$> IO.FS.readFile path catch _ => pure none
    | none => pure none
  return Imds.chain (fun name => (env.lookup name).join) tokenFile

/-- What a process signs with, found as `origin` says. -/
inductive Found where
  | keys (creds : SigV4.Credentials)
  | role (provider : Provider)

def Found.source : Found → SigV4.Source
  | .keys creds => .fixed creds
  | .role p => p.source

/-- The process's credentials, as AWS's SDKs find them: keys in the environment, else a
provider started on a container's endpoint or the instance's metadata service, which fetches
them at once and again before they expire. `none` when there are no keys and the metadata
service is turned off. -/
def find (config : Refresh.Config := {}) (client : Client.Config := {}) : Async (Option Found) := do
  match ← origin with
  | .keys creds => return some (.keys creds)
  | .role source => return some (.role (← start source config client))
  | .none => return none

end Aws.Credentials
