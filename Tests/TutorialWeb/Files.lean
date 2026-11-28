/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
# A shelf of files

The spec, the actor and its proofs. Members put files on a shared shelf and take their own off.
This file is logic only: no IO (Lanes rule 2.4).
-/

namespace Shelf

open Lanes

abbrev ReqId := Nat
abbrev FileId := Nat

/-- Who signed in, as the bridge names an identity the sign-in verified. -/
abbrev Member := String

lanes_data structure Upload where
  id : FileId
  owner : Member
  /-- The size the store gave when it was asked; `none` until it held the file. -/
  size : Option Nat
  deriving DecidableEq, Repr, Hashable

lanes_data structure State where
  next : FileId := 0
  uploads : List Upload := []
  deriving DecidableEq, Repr, Hashable

lanes_data inductive Request where
  | list (req : ReqId) (who : Member) (at_s : Nat)
  /-- Begin an upload: the answer is a form to post the file to the store. -/
  | begin (req : ReqId) (who : Member) (at_s : Nat)
  /-- The browser says it posted the file; `size` is what the store answered when asked. -/
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

structure Config where
  /-- Uploads on the shelf at once, begun or seen (rule 2.6). -/
  maxFiles : Nat := 100

abbrev sig : Signature := Server.sig Request Response

/-- Whether `who` has the upload `file` on the shelf, begun or seen. -/
def State.holds (s : State) (who : Member) (file : FileId) : Bool :=
  s.uploads.any fun u => u.id == file && u.owner == who

def service (config : Config) : Service sig.In sig.Out State where
  init := {}
  step s
    | .list req who at_s => (s, [⟨req, .shelf who (s.uploads.filter (·.size.isSome)) at_s⟩])
    | .begin req who at_s =>
      if s.uploads.length < config.maxFiles then
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

abbrev system (config : Config) : System sig :=
  Server.system (service config)

/-- The shelf never holds more than `maxFiles` uploads. -/
theorem shelf_bounded (config : Config) :
    (Server.actor (service config)).Invariant fun s => s.uploads.length ≤ config.maxFiles := by
  actor_invariant [Server.actor, service]

/-- In every reachable state of the system, under any environment model. -/
theorem system_bounded (config : Config) (env : EnvModel sig) :
    (system config).Invariant env fun c => (c.state ()).uploads.length ≤ config.maxFiles :=
  System.invariant_of_actor (system config) () (shelf_bounded config) env

/-- Only its uploader takes a file off the shelf: if a step leaves `owner` without the upload
`file` it had, the step was `owner`'s delete of `file`. -/
theorem only_uploader_deletes (config : Config) (s : State) (r : Request) {owner : Member}
    {file : FileId} (had : s.holds owner file)
    (gone : ((service config).step s r).1.holds owner file = false) :
    ∃ req, r = .delete req owner file := by
  obtain ⟨u, hu, hk⟩ := List.any_eq_true.mp had
  cases r <;> simp only [service] at gone <;> (repeat' split at gone) <;>
    simp_all [State.holds] <;> grind

end Shelf
