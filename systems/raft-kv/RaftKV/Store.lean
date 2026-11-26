/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKV.Protocol

/-! The machine this system replicates: a map from keys to values. Reads go through the log
like writes, which is what makes them linearizable without more protocol. -/

namespace RaftKV

inductive Op (K V : Type) where
  | put (key : K) (value : V)
  | get (key : K)
  deriving DecidableEq, Repr, Hashable

inductive Res (V : Type) where
  | ok
  | value (v : Option V)
  deriving DecidableEq, Repr, Hashable

def store (K V : Type) [DecidableEq K] : Machine (Op K V) (Res V) (K → Option V) where
  init _ := none
  apply m
    | .put key value => (fun k => if k = key then some value else m k, .ok)
    | .get key => (m, .value (m key))

end RaftKV
