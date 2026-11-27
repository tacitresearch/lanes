/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LanesCli.Docstrings

/-! `lanesInventory`: the inventory and the docstring coverage, in their own executable because
they link `Lean`. -/

def main (args : List String) : IO UInt32 :=
  match args with
  | "--docstrings" :: rest => Lanes.Cli.Docstrings.run "." rest
  | _ => Lanes.Cli.Inventory.run args
