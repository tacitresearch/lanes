/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Scheduler

/-!
Clients that wait: a driver that sends each request of a script once the requests it names have
been answered, and lets the rest race. Real-time order is what a refinement check needs to
catch a stale read: a request sent after another was answered must see its effect.
`Driver.anyOrder` has no such order, and `Driver.script` has nothing but.
-/

@[expose] public section

namespace Lanes

/-- What is still to be sent, each with the requests it waits for, and what has been answered. -/
structure Waiting (X : Type) where
  toSend : List (X × List Nat)
  answered : List Nat
  deriving DecidableEq, Hashable, Repr

/-- Requests are named by numbers, and `answers` says which request an output answers. -/
def Driver.after {σ : Signature} (answers : σ.Out → Option Nat)
    (script : List (σ.In × List Nat)) : Driver σ (Waiting σ.In) where
  init := { toSend := script, answered := [] }
  inputs w := (List.range w.toSend.length).filterMap fun k => do
    let (x, after) ← w.toSend[k]?
    if after.all w.answered.contains then some (x, { w with toSend := w.toSend.eraseIdx k })
    else none
  observe w out :=
    match answers out with
    | some req => { w with answered := req :: w.answered }
    | none => w

end Lanes
