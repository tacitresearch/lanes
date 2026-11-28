/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Environment

/-!
A reader of the environment (`Lanes/Outside/Environment.lean`) run on the process's: each
variable it asks for is read with `IO.getEnv`, empty as unset, through the same `Reader.runM` as
the model. Read once, at start, and passed on (rule 2.5).
-/

@[expose] public section

namespace Lanes.Environment

variable {α : Type}

/-- The configuration `r` reads from the process's environment, or every problem it found. -/
def load? (r : Reader α) : IO (Except (List Problem) α) := do
  return (← r.runM fun name => return present (← IO.getEnv name)).toExcept

/-- The configuration `r` reads from the process's environment; an error, one problem a line,
names every variable that is unset or not valid, and shows no secret. -/
def load (r : Reader α) (program : String := "lanes") : IO α := do
  match ← load? r with
  | .ok a => return a
  | .error ps =>
    throw (IO.userError (s!"{program}: the environment is not valid:\n" ++
      "\n".intercalate (ps.map fun p => s!"  {p.render}")))

end Lanes.Environment
