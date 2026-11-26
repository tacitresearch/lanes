/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LanesCli.Inventory

/-! `lanesInventory`: the inventory, in its own executable because it links `Lean`. -/

def main (args : List String) : IO UInt32 :=
  Lanes.Cli.Inventory.run args
