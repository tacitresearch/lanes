/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Rpc
public import Lanes.Outside.FileSystem.Basic

/-!
# The file system as an outside

A system reaches the file system through an adapter: an output that calls, with an id and a
deadline (`Rpc.Call`), and an input that answers. `FileSystem.server` is the model of
`Lanes/Outside/FileSystem/Basic.lean` as an `Rpc.Server`, so `Rpc.outside port
(FileSystem.server faults)` is what the file system may answer, for the checker to explore and
for a recorded run to be checked against.

A call takes effect when it is sent, in the order calls are sent: the handler performs them one
at a time. Since an `io` error hides what it did and a power loss may keep several states, the
model keeps every way the file system may be (`World`), each with the answer it owes each open
call; an answer keeps the worlds that owe it. Without faults there is one way at a time
(`FileSystem.server_same`). A power loss is an event the outside reports: every world becomes
every state a crash may leave (`Fs.crashes`). The system's actors are lost with the process; how
the system restarts is its own model's to say.
-/

@[expose] public section

namespace Lanes.FileSystem

/-- Which faults the model allows. -/
structure Faults where
  /-- A call may fail with an `io` error that hides its outcome (`Fs.failures`). -/
  io : Bool := true
  /-- The machine may lose power. -/
  power : Bool := true
  deriving DecidableEq, Repr, Hashable

/-- One way the file system may be, with the answer it owes each call not yet answered. -/
structure World where
  fs : Fs
  owed : List (Nat × Answer)
  deriving DecidableEq, Repr, Hashable

/-- The worlds a call leaves: its answer, and, with `io` faults, an `io` error after each of its
outcomes. -/
def World.receive (faults : Faults) (w : World) (call : Rpc.Call Op) : List World :=
  let (fs, answer) := w.fs.step call.request
  ⟨fs, (call.id, answer) :: w.owed⟩ ::
    if faults.io then
      (w.fs.failures call.request).map fun fs => ⟨fs, (call.id, .failed .io) :: w.owed⟩
    else []

/-- The world if it owes `call` the answer `a`, with the debt paid. -/
def World.pay (w : World) (call : Nat) (a : Answer) : Option World :=
  if w.owed.lookup call = some a then some { w with owed := w.owed.filter (·.1 != call) }
  else none

/-- What a file system that starts as `init` may answer, and may do on a power loss. -/
def server (faults : Faults := {}) (init : Fs := {}) : Rpc.Server (List World) Op Answer Unit where
  init := [⟨init, []⟩]
  receive worlds call := (worlds.flatMap (·.receive faults call)).eraseDups
  answer worlds call a :=
    match worlds.filterMap (·.pay call a) with
    | [] => none
    | kept => some kept.eraseDups
  event worlds _ :=
    if faults.power then some (worlds.flatMap fun w => w.fs.crashes.map (⟨·, w.owed⟩)).eraseDups
    else none

/-- Every answer some world owes, for the checker to propose. -/
def owed (worlds : List World) : List (Nat × Answer) := (worlds.flatMap (·.owed)).eraseDups

/-- Without faults the file system is a function of the calls: in every run the model allows,
every two worlds are the same. -/
theorem server_same {σ : Signature} (port : Rpc.Port σ Op Answer Unit) (init : Fs)
    {events : List (Event σ)} {d : Rpc.State (List World)}
    (h : (Rpc.outside port (server { io := false, power := false } init)).after events = some d) :
    ∀ w ∈ d.server, ∀ w' ∈ d.server, w = w' := by
  refine Rpc.server_invariant port _ (fun _ => True) (fun ws => ∀ w ∈ ws, ∀ w' ∈ ws, w = w')
    (by simp [server]) ?_ ?_ ?_ (fun _ _ _ _ => trivial) h
  · intro ws call hws _ w hw w' hw'
    simp only [server, List.mem_eraseDups, List.mem_flatMap, World.receive] at hw hw'
    obtain ⟨v, hv, hw⟩ := hw
    obtain ⟨v', hv', hw'⟩ := hw'
    obtain rfl := hws v hv v' hv'
    simp_all
  · intro ws call a ws' hws hans w hw w' hw'
    simp only [server] at hans
    split at hans
    · cases hans
    · obtain rfl := Option.some.inj hans
      simp only [List.mem_eraseDups, List.mem_filterMap] at hw hw'
      obtain ⟨v, hv, hw⟩ := hw
      obtain ⟨v', hv', hw'⟩ := hw'
      obtain rfl := hws v hv v' hv'
      rw [hw] at hw'
      exact Option.some.inj hw'
  · intro ws e ws' _ hev
    simp [server] at hev

end Lanes.FileSystem
