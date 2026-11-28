import Lanes.Semantics
import Lanes.Proofs
import Lean

/-! How many modules of each package `import Lanes.Semantics` and `import Lanes.Proofs` load,
and the size of their `.olean` files. Run with `lake env lean experiments/LibraryProofs/Closure.lean`. -/

open Lean

#eval show CoreM Unit from do
  let env ← getEnv
  let sp ← searchPathRef.get
  let mut count : Std.HashMap Name Nat := {}
  let mut bytes : Std.HashMap Name Nat := {}
  for m in env.header.moduleNames do
    let r := m.getRoot
    count := count.insert r (count.getD r 0 + 1)
    if let some path ← (sp.findWithExt "olean" m : IO _) then
      let size := (← path.metadata).byteSize.toNat
      bytes := bytes.insert r (bytes.getD r 0 + size)
  for (r, n) in count.toList do
    IO.println s!"{r}\t{n} modules\t{bytes.getD r 0 / 1000000} MB of .olean"
