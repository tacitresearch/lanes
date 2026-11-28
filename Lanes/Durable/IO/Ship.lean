/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Durable.Restore
public import Lanes.Runtime.IO.Park

/-!
The shipper's IO: a thread of its own that asks `Ship.take` what to do, puts what it is told to
put, and tells the shipper how the put ended. The journal's files tell it what they write
(`Shipper.tell`), on the shard's thread, which never waits for the store. What to seal, what to
put next, when to try again and what to drop are `Lanes.Journal.Ship`'s pure decisions; trusted
here is that the clock is monotonic and that a put does what its `Outcome` says.
-/

public section

namespace Lanes.Journal.Ship

variable {σ : Signature}

/-- What shipping needs of an object store; `S3.backup` gives one over S3. -/
structure Remote where
  /-- Put `bytes` at `key` unless something is there already. -/
  put : (key : String) → ByteArray → IO Outcome
  /-- Every key that starts with `keyPrefix`, with when the store last wrote it (RFC 3339), or
  `none` if the listing failed. -/
  list : (keyPrefix : String) → IO (Option (List (String × String)))
  /-- The object at `key`, or `none` if it is not there or cannot be read. -/
  get : (key : String) → IO (Option ByteArray)

/-- Where a journal is shipped: `keyPrefix`, then the journal's id, then the object's name. -/
structure Target where
  remote : Remote
  keyPrefix : String := ""
  config : Config := {}

/-- A running shipper. -/
structure Shipper (σ : Signature) where
  private mk ::
  private target : Target
  private state : IO.Ref (State σ)
  private parker : Parker
  private closing : IO.Ref Bool
  private done : IO.Promise Unit
  private reached : Nat → IO Unit

namespace Shipper

/-- Tell the shipper what the journal did. The thread that puts is woken only when something
was sealed; otherwise it wakes by itself when the oldest waiting entry is due. -/
def tell (s : Shipper σ) (e : Event σ) : BaseIO Unit := do
  let now ← IO.monoMsNow
  let sealed ← s.state.modifyGet fun st =>
    let next := step s.target.config now st e
    (next.sealed != st.sealed, next)
  if sealed then s.parker.unpark

private def loop (s : Shipper σ) (input : Codec σ.In) (system journal : String) : IO Unit := do
  let cfg := s.target.config
  let mut deadline : Option Nat := none
  repeat
    let now ← IO.monoMsNow
    if ← s.closing.get then
      if (← s.state.get).idle then break
      match deadline with
      | some d => if d ≤ now then break
      | none => deadline := some (now + cfg.close_ms)
    match ← s.state.modifyGet fun st => (take cfg now st).swap with
    | .put u =>
      let (name, body) := u.object input system
      let outcome ← match ← (s.target.remote.put (s.target.keyPrefix ++ journal ++ "/" ++ name)
          body).toBaseIO with
        | .ok outcome => pure outcome
        | .error _ => pure .failed
      if outcome == .failed then
        discard (IO.eprintln s!"lanes: shipping {name} of the journal {journal} failed; it is tried again").toBaseIO
      let now ← IO.monoMsNow
      let (before, after) ← s.state.modifyGet fun st =>
        let next := answer cfg now outcome st
        ((st.storedTo, next.storedTo), next)
      if before != after then
        try s.reached after
        catch e => discard (IO.eprintln s!"lanes: shipping the journal {journal}: {e}").toBaseIO
    | .wait ms => s.parker.parkAtMost (min (ms.getD 1000) 1000)
  s.done.resolve ()

/-- Start shipping the journal `journal` of `system`, from `initial` (`Ship.start`). `reached`
is told each time the stored segments reach further (`State.storedTo`). -/
def start (target : Target) (input : Codec σ.In) (system journal : String) (initial : State σ)
    (reached : Nat → IO Unit := fun _ => pure ()) : IO (Shipper σ) := do
  let s : Shipper σ := {
    target, state := ← IO.mkRef initial, parker := ← Parker.new, closing := ← IO.mkRef false
    done := ← IO.Promise.new, reached }
  discard <| IO.asTask (prio := .dedicated) do
    try s.loop input system journal
    catch e =>
      discard (IO.eprintln s!"lanes: shipping the journal {journal} stopped: {e}").toBaseIO
      s.done.resolve ()
  return s

/-- Seal what waits, wait at most `Config.close_ms` for what is pending to be stored, and stop.
What is not stored by then is shipped again from the journal's files at the next start, but for
the entries before the last save. -/
def close (s : Shipper σ) : BaseIO Unit := do
  s.tell .closing
  s.closing.set true
  s.parker.unpark
  discard <| Parker.wait s.done.result?

/-- What the shipper has done: sealed, stored, dropped at the bound, and still pending. -/
structure Counts where
  sealed : Nat
  stored : Nat
  dropped : Nat
  pending : Nat
  deriving Repr, DecidableEq

def counts (s : Shipper σ) : BaseIO Counts := do
  let st ← s.state.get
  return { sealed := st.sealed, stored := st.stored, dropped := st.dropped
           pending := st.pending.length }

end Shipper

end Lanes.Journal.Ship
