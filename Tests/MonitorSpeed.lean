/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The spec monitor's cost (`Lanes/Check/Monitor.lean`) on a shelf of files kept by one actor: a
copy of its service, checked against itself with `Check.refines` and without it, with no crash
and with one. Run by `lake exe lanesCheck`, which prints the times.
-/

namespace Tests.MonitorSpeed

open Lanes

abbrev ReqId := Nat
abbrev FileId := Nat
abbrev Member := String

lanes_data structure Upload where
  id : FileId
  owner : Member
  size : Option Nat
  deriving DecidableEq, Repr, Hashable

lanes_data structure State where
  next : FileId := 0
  uploads : List Upload := []
  deriving DecidableEq, Repr, Hashable

lanes_data inductive Request where
  | list (req : ReqId) (who : Member) (at_s : Nat)
  | begin (req : ReqId) (who : Member) (at_s : Nat)
  | seen (req : ReqId) (who : Member) (file : FileId) (size : Option Nat)
  | delete (req : ReqId) (who : Member) (file : FileId)
  deriving DecidableEq, Repr, Hashable

lanes_data inductive Answer where
  | shelf (viewer : Member) (files : List Upload) (at_s : Nat)
  | form (viewer : Member) (file : FileId) (at_s : Nat)
  | listed (file : FileId)
  | notSeen (file : FileId)
  | deleted (file : FileId)
  | refused (file : FileId)
  | full
  deriving DecidableEq, Repr, Hashable

lanes_data structure Response where
  req : ReqId
  answer : Answer
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature := Server.sig Request Response

def State.holds (s : State) (who : Member) (file : FileId) : Bool :=
  s.uploads.any fun u => u.id == file && u.owner == who

def service (maxFiles : Nat) : Service sig.In sig.Out State where
  init := {}
  step s
    | .list req who at_s => (s, [⟨req, .shelf who (s.uploads.filter (·.size.isSome)) at_s⟩])
    | .begin req who at_s =>
      if s.uploads.length < maxFiles then
        ({ next := s.next + 1, uploads := s.uploads ++ [⟨s.next, who, none⟩] },
          [⟨req, .form who s.next at_s⟩])
      else (s, [⟨req, .full⟩])
    | .seen req who file size =>
      match size with
      | some n =>
        if s.holds who file then
          ({ s with uploads := s.uploads.map fun u =>
              if u.id == file && u.owner == who then { u with size := some n } else u },
            [⟨req, .listed file⟩])
        else (s, [⟨req, .notSeen file⟩])
      | none => (s, [⟨req, .notSeen file⟩])
    | .delete req who file =>
      if s.holds who file then
        ({ s with uploads := s.uploads.filter fun u => !(u.id == file && u.owner == who) },
          [⟨req, .deleted file⟩])
      else (s, [⟨req, .refused file⟩])

instance : sig.Inspect := {}
instance (svc : Service sig.In sig.Out State) : (Server.system svc).Inspect := {}

def requests : List Request :=
  [.begin 1 "alice" 0, .seen 2 "alice" 0 (some 5), .delete 3 "bob" 0, .delete 4 "alice" 0,
    .begin 5 "alice" 0]

def env : EnvModel sig := { mayCrash := fun _ => true }

def monitored (maxCrashes : Nat) :=
  Check.system (Server.system (service 1))
    { driver := (service 1).monitored (Driver.anyOrder requests), env, maxCrashes }
    [Check.refines "every response is allowed by the shelf's spec"]

def plain (maxCrashes : Nat) :=
  Check.system (Server.system (service 1))
    { driver := Driver.anyOrder requests, env, maxCrashes }
    [.always "the shelf holds at most one upload" fun w => (w.state.state ()).uploads.length ≤ 1]

/-- Runs `report` and prints its size and time. -/
def timed (name : String) (report : Unit → Check.Report S L) : IO (Check.Report S L) := do
  let t0 ← IO.monoMsNow
  let r := report ()
  let states := r.states
  IO.eprintln s!"monitor speed: {name}: {states} states, {r.transitions} transitions in \
    {(← IO.monoMsNow) - t0} ms"
  return r

def checks : IO (List (String × Bool)) := do
  let crashes ← (← IO.mkRef 0).get
  let p0 ← timed "the shelf without the monitor" fun _ => plain crashes
  let m0 ← timed "the shelf with the monitor" fun _ => monitored crashes
  let p1 ← timed "the shelf without the monitor, one crash" fun _ => plain (crashes + 1)
  let m1 ← timed "the shelf with the monitor, one crash" fun _ => monitored (crashes + 1)
  return [
    ("monitor speed: the shelf refines its spec", m0.ok && p0.ok),
    ("monitor speed: the shelf refines its spec with one crash",
      m1.ok && p1.ok) ]

end Tests.MonitorSpeed
