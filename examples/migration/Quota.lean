/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Quota.V2

/-!
# A deploy that changes the state type

Version 1 of the quota service (`Quota.V1`) ran and journalled. Version 2 (`Quota.V2`) gives
each user a quota, a field version 1 did not have. The binary of version 2 keeps version 1's
system and reads its files through `upgrade`: it replays them as version 1 did, migrates the
kernel with `migration`, saves it as version 2 and goes on.

The proofs of version 2 are about runs of version 2, and after the migration its run starts
from the migrated kernel. `migration` carries the proof that every state a user of version 1
can reach migrates to one within its quota, so `within_quota` holds of every user, in every
state version 2 reaches after the migration, and at every later start whatever turns, saves
and deaths come between (`within_quota_at_start`).

Had the migration given every user the default quota, a user of version 1 that had used 150
would migrate outside the invariant, and `lands` could not be proved (`Check.lean` shows the
state).
-/

namespace Quota

open Lanes

/-- Users keep their identities, what they used, the messages queued for them and the replies
not yet handed over; a quota is added. -/
def migration : Migration V1.system V2.system where
  id := id
  injective _ _ h := h
  state _ := V2.Usage.migrate
  msg _ := V2.Msg.migrate
  output := V2.Reply.migrate
  inv _ := V2.WithinQuota
  keeps := V2.withinQuota
  lands _ s _ := Nat.le_max_left s.used V2.defaultQuota

/-- How version 2 reads the files of version 1. -/
def upgrade : Journal.Upgrade V2.system where
  old := V1.system
  system := Journal.label "quota" 1
  input := V1.Request.codec
  actors := some V1.actors
  migration

def store (path : System.FilePath) : Journal.Store V2.system :=
  { path, input := V2.Request.codec, system := "quota", version := 2, actors := some V2.actors
    upgrades := [upgrade] }

/-- After the migration, whatever version 2 is asked, every user is within its quota. -/
theorem within_quota (history : List (Journal.Entry V1.sig)) (later : List (Kernel.Op V2.sig))
    (j : V2.User) :
    V2.WithinQuota ((((migration.kernel (Journal.recover V1.system history).1).image.kernel).exec
      later).kernel.cell j).state :=
  migration.inv_exec history later j

/-- At every start after the migration, however many turns and saves came before and wherever
the process died, the files load, and every user is within its quota. -/
theorem within_quota_at_start (history : List (Journal.Entry V1.sig))
    {later : List (Journal.Entry V2.sig)} {disk : Journal.Disk}
    (h : Journal.Disk.Torn V2.system (start := (migration.kernel (Journal.recover V1.system history).1, []))
      V2.Request.codec V2.actors (Journal.label "quota" 2) later disk) :
    ∃ k outputs, disk.load V2.system V2.Request.codec (some V2.actors) (Journal.label "quota" 2)
        = .ok (k, outputs) ∧ ∀ j, V2.WithinQuota (k.cell j).state :=
  Journal.Upgrade.inv_load (u := upgrade) h

/-- The new run starts from the old state, migrated: each user's cell is its old cell with a
quota added. -/
theorem starts_migrated (k : Kernel V1.system) (i : V1.User) :
    (migration.kernel k).cell i = migration.cell i (k.cell i) :=
  migration.cell_kernel (fun _ => rfl) k i

end Quota
