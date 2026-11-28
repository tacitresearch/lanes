/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The reader of the environment (`Lanes/Outside/Environment.lean`): every problem at once, no
secret shown, defaults listed, and an application model-checked under each of several
configurations. Live, `Environment.load` reads the process's environment.
-/

namespace Tests.Environment

open Lanes Lanes.Environment

inductive Mode where
  | dev | prod
  deriving DecidableEq, Repr, Inhabited

instance : Value Mode := .oneOf [("dev", .dev), ("prod", .prod)]

structure Config where
  host : String
  port : UInt16
  password : Secret
  limit : Nat
  mode : Mode
  deriving Repr

def config : Reader Config := do
  let host ← get "APP_HOST" "127.0.0.1" (doc := "The address to listen on.")
  let port ← need "APP_PORT"
  let password ← secret "APP_DB_PASSWORD"
  let limit ← get "APP_LIMIT" 3
  check (0 < limit && limit ≤ 10) "APP_LIMIT" "must be from 1 to 10"
  let mode ← get "APP_MODE" Mode.dev
  return { host, port, password, limit, mode }

def names (ps : List Problem) : List String := ps.map (·.name)

def problems (vars : Vars) : List Problem :=
  match read config vars with
  | .ok _ => []
  | .error ps => ps

def valid : Vars := [("APP_PORT", "8080"), ("APP_DB_PASSWORD", "hunter2hunter2")]

/-- A counter that stops at the limit its configuration gives. -/
abbrev countSig : Signature where
  Id := Unit
  Msg _ := Unit
  In := Unit
  Out := Nat

abbrev counter (cfg : Config) : System countSig where
  State _ := Nat
  actor _ :=
    { init := 0
      step := fun n () => if n < cfg.limit then (n + 1, [.emit (n + 1)]) else (n, []) }
  accept x := ⟨(), x⟩

instance : countSig.Inspect := {}
instance (cfg : Config) : (counter cfg).Inspect := {}

/-- The counter under the configuration `vars` gives, model-checked: it never passes its limit
and reaches it. -/
def checkUnder (vars : Vars) : Bool :=
  match read config vars with
  | .error _ => false
  | .ok cfg =>
    (Check.system (counter cfg) { driver := Driver.script (List.replicate 12 ()) }
      [ .always "the count stays within the limit" fun w => w.state.state () ≤ cfg.limit,
        .sometimes "the count reaches the limit" fun w => w.state.state () == cfg.limit ]).ok

def tests : List (String × Bool) :=
  let bad : Vars := [("APP_PORT", "http"), ("APP_DB_PASSWORD", ""), ("APP_LIMIT", "0"),
    ("APP_MODE", "staging")]
  let refused := (field (α := Nat) { name := "TOKEN", secret := true }
    (fun s => .error s!"{s} is not a number")).run [("TOKEN", "tok-123")]
  [ ("environment: a valid environment is read, with the defaults for what is unset",
      match read config valid with
      | .ok c => c.host == "127.0.0.1" && c.port == 8080 && c.password.reveal == "hunter2hunter2"
          && c.limit == 3 && c.mode == .dev
      | .error _ => false),
    ("environment: with nothing set, both required variables are named at once",
      names (problems []) == ["APP_PORT", "APP_DB_PASSWORD"]),
    ("environment: every bad value is named at once, an empty one as unset",
      names (problems bad) == ["APP_PORT", "APP_DB_PASSWORD", "APP_LIMIT", "APP_MODE"]
        && (problems bad)[1]? == some { name := "APP_DB_PASSWORD", why := .unset }),
    ("environment: a problem shows a plain value and why it was refused",
      ((problems bad).map Problem.render).head? == some "APP_PORT=\"http\": not a port"),
    ("environment: a refused secret shows neither its value nor what was said of it",
      refused.problems == [{ name := "TOKEN", why := .hidden }]
        && !((refused.problems.map Problem.render).any (·.contains "tok-123"))),
    ("environment: a configuration holding a secret prints without it",
      match read config valid with
      | .ok c => !(toString (repr c)).contains "hunter2" && (toString (repr c)).contains "<secret>"
      | .error _ => false),
    ("environment: describe lists every variable with its default",
      (describe config).map (fun v => (v.name, v.default, v.required, v.secret)) ==
        [("APP_HOST", some "127.0.0.1", false, false), ("APP_PORT", none, true, false),
         ("APP_DB_PASSWORD", none, true, true), ("APP_LIMIT", some "3", false, false),
         ("APP_MODE", some "dev", false, false)]),
    ("environment: values of each kind are parsed",
      (read (get "L" ([] : List Nat)) [("L", "1, 2,,3")]).toOption == some [1, 2, 3]
        && (read (get "B" false) [("B", "YES")]).toOption == some true
        && read (get "P" (0 : UInt16)) [("P", "65536")] matches .error _),
    ("environment: an application is model-checked under each of several configurations",
      [1, 2, 5].all fun n => checkUnder (("APP_LIMIT", toString n) :: valid)) ]

/-- A name no environment sets. -/
def unset : String := "LANES_TEST_UNSET_9f3c1a"

def live : IO (List (String × Bool)) := do
  let path ← IO.getEnv "PATH"
  let loaded ← load (opt (α := String) "PATH")
  let failed ← try
      discard <| load (do let _ ← need (α := Nat) unset; secret unset) "test"
      pure ""
    catch e => pure (toString e)
  return [
    ("environment: load reads the process's environment", loaded == path),
    ("environment: load fails naming every problem, one a line",
      failed == s!"test: the environment is not valid:\n  {unset} is not set\n  {unset} is not set") ]

end Tests.Environment
