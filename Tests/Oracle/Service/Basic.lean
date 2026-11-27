/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Service oracles (`oracles/README.md`): our client runs against a real or reference
implementation of a service, the run is recorded, and the record is checked against our model of
the service with `Outside.allows`. The record is kept in `oracles/<reference>/<model>.jsonl`, one
event a line, so that `lake test` checks it again without the service, and a model made stricter
than the service it describes fails there. A service oracle runs only when the variable that
names its service is set, and says it is skipped otherwise.
-/

namespace Tests.Oracle.Service

open Lanes

structure Oracle where
  name : String
  /-- The folder under `oracles/` of the reference, which holds the record. -/
  reference : String
  /-- The variable that names the service, as `host:port`. -/
  envVar : String
  /-- Runs against the service: the checks, and the record. -/
  live : String → UInt16 → IO (List (String × Bool) × List Json)
  /-- The checks of a record read back. -/
  replay : List Json → List (String × Bool)

def Oracle.path (o : Oracle) (root : System.FilePath := ".") : System.FilePath :=
  root / "oracles" / o.reference / (o.name ++ ".jsonl")

def readLines (path : System.FilePath) : IO (Except String (List Json)) := do
  let text ← IO.FS.readFile path
  return ((text.splitOn "\n").filter (· ≠ "")).mapM Json.parse

def writeLines (path : System.FilePath) (lines : List Json) : IO Unit :=
  IO.FS.writeFile path (String.join (lines.map (Json.compress · ++ "\n")))

/-- The record, checked again: for `lake test`. -/
def Oracle.replayFile (o : Oracle) (root : System.FilePath := ".") : IO (List (String × Bool)) := do
  match ← readLines (o.path root) with
  | .ok lines => return o.replay lines
  | .error e => return [(s!"{o.name}: the record {o.path} reads: {e}", false)]

def endpoint? (envVar : String) : IO (Option (String × UInt16)) := do
  let some spec ← IO.getEnv envVar | return none
  match spec.splitOn ":" with
  | [host, port] => return port.toNat?.map fun p => (host, p.toUInt16)
  | _ => return none

/-- Runs each oracle whose service is named, writes its record with `record`, and prints the
checks; an oracle whose service is not named is skipped, with a message. -/
def main (command : String) (root : System.FilePath) (oracles : List Oracle) (args : List String) :
    IO UInt32 := do
  let record := args.contains "--record"
  let names := args.filter (· != "--record")
  let unknown := names.filter fun n => !oracles.any (·.name == n)
  unless unknown.isEmpty do
    IO.eprintln s!"{command}: no service oracle {", ".intercalate unknown}; there are {", ".intercalate (oracles.map (·.name))}"
    return 2
  let chosen := if names.isEmpty then oracles else oracles.filter (names.contains ·.name)
  let mut failed := 0
  for o in chosen do
    match ← endpoint? o.envVar with
    | none => IO.println s!"{o.name}: skipped, {o.envVar} does not name the service as host:port"
    | some (host, port) =>
      let (checks, lines) ← o.live host port
      for (name, ok) in checks do IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
      failed := failed + checks.countP (!·.2)
      if record && checks.all (·.2) then
        writeLines (o.path root) lines
        IO.println s!"{o.name}: recorded {lines.length} lines in {o.path}"
  return if failed == 0 then 0 else 1

/-! ## JSON, for records -/

def str? (j : Json) (name : String) : Option String :=
  match j.getObjVal? name with
  | .ok (.str s) => some s
  | _ => none

def nat? (j : Json) (name : String) : Option Nat := (j.getObjVal? name >>= Json.getNat?).toOption

def bytes? (j : Json) (name : String) : Option ByteArray := (str? j name).bind Bytes.unhex?

end Tests.Oracle.Service
