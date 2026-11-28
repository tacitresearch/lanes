import Lake
open Lake DSL

/-! Spike for #239: can deriving handlers replace `lanes_data` without linking `Lean` into an
application? `docs/decisions/new-deriving-handlers.md` has the findings. Not built by CI. -/

package spike

require lanes from "../.."

lean_lib Spike where
  globs := #[.submodules `Spike]

/-! Part 1: a toy class, with the toolchain only. -/

/-- Derives `Spike.Describe` with the handler of `Spike.Derive`, which it imports with `meta import`. -/
lean_exe withHandler where
  root := `WithHandler

/-- As `withHandler`, but imports the handler's module with a plain `import` (D15's setup). -/
lean_exe plainImport where
  root := `PlainImport

/-- `byHand`, importing a module that does `public meta import Lean` (D15's measurement). -/
lean_exe wholeLean where
  root := `WholeLean

/-- `byHand` with a plain `import Lean`: what an application must not do. -/
lean_exe importLean where
  root := `ImportLean

/-- The same program with the instance written by hand: the baseline. -/
lean_exe byHand where
  root := `ByHand

/-! Part 2: Lanes' own derivations as deriving handlers (`Spike.Lanes`). -/

/-- Lanes types declared with plain `structure` / `inductive … deriving ToJson, FromJson, Enum`. -/
lean_exe lanesHandler where
  root := `LanesHandler

/-- `lanesHandler` with a plain `import Spike.Prelude`, which does `public meta import Spike.Lanes`:
how `import Lanes` could carry the handlers. -/
lean_exe viaPrelude where
  root := `ViaPrelude

/-- `viaPrelude` in a file without `module`, as an application's `Main.lean` is. -/
lean_exe notModule where
  root := `NotModule

/-- The same types declared with `lanes_data`: the baseline. -/
lean_exe lanesData where
  root := `LanesData
