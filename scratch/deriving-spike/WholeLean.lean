module

import Spike.Class
import Spike.WholeLean

structure Point where
  x : Nat
  y : Nat

instance : Spike.Describe Point := ⟨["x", "y"]⟩

public def main : IO Unit :=
  IO.println (Spike.Describe.fields (α := Point))
