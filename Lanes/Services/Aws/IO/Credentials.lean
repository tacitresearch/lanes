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
(`Provider.source`, read at each call by `S3.exchange`) sees one state or the next. Nothing
here prints or logs a secret: why the last fetch failed is kept, and says no value.
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

/-- The provider as the S3 client, or SES's, reads credentials: at each call. -/
def Provider.source (p : Provider) : SigV4.Source := ⟨p.read⟩

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

/-- Where this process's role credentials are: a container's endpoint when its environment
names one, otherwise the instance's metadata service. -/
def detect : IO Imds.Source := do
  let get (name : String) : IO (Option String) := IO.getEnv name
  let env := [("AWS_CONTAINER_CREDENTIALS_RELATIVE_URI", ← get "AWS_CONTAINER_CREDENTIALS_RELATIVE_URI"),
    ("AWS_CONTAINER_CREDENTIALS_FULL_URI", ← get "AWS_CONTAINER_CREDENTIALS_FULL_URI"),
    ("AWS_CONTAINER_AUTHORIZATION_TOKEN", ← get "AWS_CONTAINER_AUTHORIZATION_TOKEN")]
  let tokenFile ← match ← get "AWS_CONTAINER_AUTHORIZATION_TOKEN_FILE" with
    | some path => try some <$> IO.FS.readFile path catch _ => pure none
    | none => pure none
  return (Imds.containerSource? (fun name => (env.lookup name).join) tokenFile).getD (.instance)

end Aws.Credentials
