module

import Spike.Class
meta import Spike.Derive

structure Point where
  x : Nat
  y : Nat
  deriving Spike.Describe

public def main : IO Unit :=
  IO.println (Spike.Describe.fields (α := Point))
