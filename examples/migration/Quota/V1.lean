/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Version 1 of the quota service: each of three users is an actor that tallies what it has used.

Version 2 replaced it, and this module stays as it was: version 2 reads version 1's files by
replaying them through these step functions and these codecs, and then migrates the kernel
(`Quota.migration`). Nothing here may change while files of version 1 may exist.
-/

namespace Quota.V1

open Lanes

abbrev User := Fin 3

lanes_data inductive Request where
  | use (req : Nat) (user : User) (amount : Nat)
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data structure Reply where
  req : Nat
  used : Nat
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Msg where
  | use (req amount : Nat)
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data structure Usage where
  used : Nat
  deriving DecidableEq, Repr, Hashable, Codable

abbrev sig : Signature where
  Id := User
  Msg _ := Msg
  In := Request
  Out := Reply

def user (self : User) : sig.Actor self Usage where
  init := { used := 0 }
  step s
    | .use req amount => ({ used := s.used + amount }, [.emit ⟨req, s.used + amount⟩])
  recover s := (s, [])

abbrev system : System sig where
  State _ := Usage
  actor := user
  accept
    | .use req user amount => ⟨user, .use req amount⟩

def actors : Kernel.Image.Codecs system where
  id := Codec.fin
  state _ := Usage.codec
  msg _ := Msg.codec

def store (path : System.FilePath) : Journal.Store system :=
  { path, input := Request.codec, system := "quota", version := 1, actors := some actors }

end Quota.V1
