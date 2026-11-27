/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Quota.V1

/-!
Version 2 of the quota service. A user now has a quota: a use that would pass it is refused,
and a grant raises it. The state gains a field, the requests and the messages a constructor,
and the reply becomes a sum. Each type says with `from` how a value of version 1 becomes one of
version 2.

`withinQuota`: no user ever uses more than its quota. It is inductive (it holds at the start and
every step and restart keeps it), which is what carries it across a migration.
-/

namespace Quota.V2

open Lanes

abbrev User := Fin 3

/-- The quota a user starts with. -/
def defaultQuota : Nat := 100

lanes_data inductive Request where
  | use (req : Nat) (user : User) (amount : Nat)
  | grant (req : Nat) (user : User) (amount : Nat)
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Reply where
  | used (req used : Nat)
  | refused (req quota : Nat)
  | granted (req quota : Nat)
  deriving DecidableEq, Repr, Hashable, Codable
  from V1.Reply := fun r => .used r.req r.used

lanes_data inductive Msg where
  | use (req amount : Nat)
  | grant (req amount : Nat)
  deriving DecidableEq, Repr, Hashable, Codable
  from V1.Msg := fun | .use req amount => .use req amount

/-- A user who has used more than the default already keeps what it used as its quota: a quota
below it would be a state no step of version 2 can reach. -/
lanes_data structure Usage where
  used : Nat
  quota : Nat
  deriving DecidableEq, Repr, Hashable, Codable
  from V1.Usage := fun u => { used := u.used, quota := max u.used defaultQuota }

abbrev sig : Signature where
  Id := User
  Msg _ := Msg
  In := Request
  Out := Reply

def user (self : User) : sig.Actor self Usage where
  init := { used := 0, quota := defaultQuota }
  step s
    | .use req amount =>
      if s.used + amount ≤ s.quota then
        ({ s with used := s.used + amount }, [.emit (.used req (s.used + amount))])
      else (s, [.emit (.refused req s.quota)])
    | .grant req amount =>
      ({ s with quota := s.quota + amount }, [.emit (.granted req (s.quota + amount))])
  recover s := (s, [])

abbrev system : System sig where
  State _ := Usage
  actor := user
  accept
    | .use req user amount => ⟨user, .use req amount⟩
    | .grant req user amount => ⟨user, .grant req amount⟩

def actors : Kernel.Image.Codecs system where
  id := Codec.fin
  state _ := Usage.codec
  msg _ := Msg.codec

/-- A user never uses more than its quota. -/
def WithinQuota (s : Usage) : Prop :=
  s.used ≤ s.quota

instance : DecidablePred WithinQuota := fun s => inferInstanceAs (Decidable (s.used ≤ s.quota))

theorem withinQuota (self : User) : (user self).Inductive WithinQuota where
  init := Nat.zero_le _
  step s m h := by
    cases m with
    | use req amount =>
      simp only [user]
      split
      · next hle => exact hle
      · exact h
    | grant req amount => exact Nat.le_add_right_of_le h
  recover _ h := h

end Quota.V2
