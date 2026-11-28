/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.Secret

/-!
# The environment

What a process is told at start in its environment variables, as a platform model, and a typed
reader that turns them into the application's `Config` once (rule 2.5).

The model is `Vars`: any list of variables and values. A variable set to the empty text counts
as unset, as most programs read it.

A `Reader` says which variables it reads, how each is parsed, and its default. Written with `do`,
it goes on past a variable it cannot read, with a stand-in value, so `read` gives every problem
at once (`run_bind`), not the first. A variable read as a `Secret` never has its value in a
problem (`secret_problems`), and a `Secret` prints as `<secret>`. A reader reads only the
variables it asks for (`run_congr`), so a test, or the checker, runs an application under each
of several configurations by giving each its `Vars`; `describe` lists what it asks for, with each
variable's text and default, for a deploy's documentation or `--help`. `Environment.load`
(`Lanes/Outside/IO/Environment.lean`) runs a reader on the process's environment.

A problem found with a stand-in value in hand may be followed by others that the stand-in
caused, where a later variable is read only because of an earlier one's value.
-/

@[expose] public section

namespace Lanes.Environment

/-- What the environment holds: each variable with its value. The first of a name counts. -/
abbrev Vars := List (String × String)

/-- A variable's value as a reader sees it: none when it is empty. -/
def present (value : Option String) : Option String :=
  value.filter (!·.isEmpty)

/-- The value of `name`, unless it is unset or empty. -/
def Vars.get (vars : Vars) (name : String) : Option String :=
  present (vars.lookup name)

/-- A variable a reader asks for, as `describe` lists it. -/
structure Var where
  name : String
  doc : String := ""
  /-- The value used when it is unset, as text; `none` when there is none. -/
  default : Option String := none
  required : Bool := false
  secret : Bool := false
  deriving DecidableEq, Repr

/-- Why a variable could not be read. A secret's value, and what its parser said of it, are
never kept. -/
inductive Why where
  | unset
  | invalid (value why : String)
  /-- A secret's value was refused. -/
  | hidden
  /-- A check over values already read (`check`). -/
  | refused (why : String)
  deriving DecidableEq, Repr

structure Problem where
  name : String
  why : Why
  deriving DecidableEq, Repr

def Problem.render (p : Problem) : String :=
  match p.why with
  | .unset => s!"{p.name} is not set"
  | .invalid value why => s!"{p.name}={value.quote}: {why}"
  | .hidden => s!"{p.name}: the value is not valid (a secret, not shown)"
  | .refused why => s!"{p.name}: {why}"

/-- A reader of the environment, as data: what it asks, and what it does with each answer. -/
inductive Reader (α : Type) where
  | pure (a : α)
  | ask (v : Var) (k : Option String → Reader α)
  | problem (p : Problem) (next : Reader α)

namespace Reader

variable {α β : Type}

def bind : Reader α → (α → Reader β) → Reader β
  | .pure a, f => f a
  | .ask v k, f => .ask v fun s => (k s).bind f
  | .problem p next, f => .problem p (next.bind f)

instance : Monad Reader where
  pure := .pure
  bind := bind

/-- What a run gave: the value, every problem in the order found, and every variable asked. -/
structure Result (α : Type) where
  value : α
  problems : List Problem
  asked : List Var

/-- Run with the answers `get` gives, in any monad: `Id` for the model, `IO` for the process. -/
def runM {m : Type → Type} [Monad m] (get : String → m (Option String)) :
    Reader α → m (Result α)
  | .pure a => return { value := a, problems := [], asked := [] }
  | .ask v k => do
    let r ← runM get (k (← get v.name))
    return { r with asked := v :: r.asked }
  | .problem p next => do
    let r ← runM get next
    return { r with problems := p :: r.problems }

/-- The value, or every problem if there is one. -/
def Result.toExcept (res : Result α) : Except (List Problem) α :=
  if res.problems.isEmpty then .ok res.value else .error res.problems

def run (vars : Vars) (r : Reader α) : Result α :=
  Id.run (r.runM fun name => vars.get name)

end Reader

/-- The configuration `r` reads from `vars`, or every problem it found. -/
def read {α : Type} (r : Reader α) (vars : Vars) : Except (List Problem) α :=
  (r.run vars).toExcept

/-- The variables `r` asks for when none is set: what a deploy may set. -/
def describe {α : Type} (r : Reader α) : List Var :=
  (r.run []).asked

/-- How a variable's text becomes a value, and a value its text, to show a default. -/
class Value (α : Type) where
  parse : String → Except String α
  text : α → String

instance : Value String := ⟨.ok, id⟩

instance : Value Nat where
  parse s := match s.toNat? with
    | some n => .ok n
    | none => .error "not a whole number"
  text := toString

instance : Value Int where
  parse s := match s.toInt? with
    | some n => .ok n
    | none => .error "not an integer"
  text := toString

/-- A TCP port: `0` asks the system to pick one. -/
instance : Value UInt16 where
  parse s := match s.toNat? with
    | some n => if h : n < 65536 then .ok ⟨⟨n, h⟩⟩ else .error "not a port: above 65535"
    | none => .error "not a port"
  text := toString

instance : Value Bool where
  parse s := match s.toLower with
    | "true" | "1" | "yes" | "on" => .ok true
    | "false" | "0" | "no" | "off" => .ok false
    | _ => .error "not one of true, false, 1, 0, yes, no, on, off"
  text b := toString b

/-- Values separated by commas, each trimmed; empty pieces are dropped. -/
instance {α : Type} [Value α] : Value (List α) where
  parse s := ((s.splitOn ",").map (·.trimAscii.toString)).filter (!·.isEmpty) |>.mapM Value.parse
  text xs := ",".intercalate (xs.map Value.text)

/-- One of the names given, each for its value: for an `inductive` of choices, `instance : Value
Mode := .oneOf [("dev", .dev), ("prod", .prod)]`. -/
@[instance_reducible] def Value.oneOf {α : Type} [BEq α] (choices : List (String × α)) : Value α where
  parse s := match choices.lookup s with
    | some a => .ok a
    | none => .error s!"not one of {", ".intercalate (choices.map (·.1))}"
  text a := ((choices.find? (·.2 == a)).map (·.1)).getD ""

open Reader

/-- Record a problem and go on. -/
def complain (name : String) (why : Why) : Reader Unit :=
  .problem { name, why } (.pure ())

/-- The variable `v` parsed by `parse`, `none` when it is unset or its value is refused (a
problem). A secret's refused value is a `hidden` problem. -/
def field {α : Type} (v : Var) (parse : String → Except String α) : Reader (Option α) :=
  .ask v fun
    | none => .pure none
    | some s => match parse s with
      | .ok a => .pure (some a)
      | .error why => .problem { name := v.name, why := if v.secret then .hidden else .invalid s why }
          (.pure none)

/-- The variable `name` if it is set. -/
def opt {α : Type} [Value α] (name : String) (doc : String := "") : Reader (Option α) :=
  field { name, doc } Value.parse

/-- The variable `name`, or `default` when it is unset. -/
def get {α : Type} [Value α] (name : String) (default : α) (doc : String := "") : Reader α :=
  return (← field { name, doc, default := some (Value.text default) } Value.parse).getD default

/-- The variable `name`, which must be set. -/
def need {α : Type} [Value α] [Inhabited α] (name : String) (doc : String := "") : Reader α :=
  .ask { name, doc, required := true } fun
    | none => .problem { name, why := .unset } (.pure default)
    | some s => match Value.parse s with
      | .ok a => .pure a
      | .error why => .problem { name, why := .invalid s why } (.pure default)

/-- The secret `name` if it is set. -/
def secret? (name : String) (doc : String := "") : Reader (Option Secret) :=
  field { name, doc, secret := true } fun s => .ok ⟨s⟩

/-- The secret `name`, which must be set. -/
def secret (name : String) (doc : String := "") : Reader Secret :=
  .ask { name, doc, required := true, secret := true } fun
    | none => .problem { name, why := .unset } (.pure default)
    | some s => .pure ⟨s⟩

/-- A problem with `name` unless `ok`: a check across values already read. -/
def check (ok : Bool) (name why : String) : Reader Unit :=
  if ok then .pure () else complain name (.refused why)

/-! ## What is proved -/

namespace Reader

variable {α β : Type}

@[simp] theorem run_pure (vars : Vars) (a : α) :
    (Reader.pure a).run vars = { value := a, problems := [], asked := [] } := rfl

@[simp] theorem run_ask (vars : Vars) (v : Var) (k : Option String → Reader α) :
    (Reader.ask v k).run vars =
      let r := (k (vars.get v.name)).run vars
      { r with asked := v :: r.asked } := rfl

@[simp] theorem run_problem (vars : Vars) (p : Problem) (next : Reader α) :
    (Reader.problem p next).run vars =
      let r := next.run vars
      { r with problems := p :: r.problems } := rfl

/-- Problems accumulate: a reader that goes on from `r` gives `r`'s problems and then its own,
whatever `r` found, so `read` lists every problem, not the first. -/
theorem run_bind (vars : Vars) (r : Reader α) (f : α → Reader β) :
    (r.bind f).run vars =
      let a := r.run vars
      let b := (f a.value).run vars
      { value := b.value, problems := a.problems ++ b.problems, asked := a.asked ++ b.asked } := by
  induction r with
  | pure a => rfl
  | ask v k ih => simp [bind, ih]
  | problem p next ih => simp [bind, ih]

/-- A reader reads only the variables it asks for: two environments that agree on those give
the same run. So the configurations an application can have are the values of `describe`'s
variables, and nothing else in the environment changes them. -/
theorem run_congr (r : Reader α) (vars vars' : Vars)
    (h : ∀ v ∈ (r.run vars).asked, vars.get v.name = vars'.get v.name) :
    r.run vars = r.run vars' := by
  induction r with
  | pure a => rfl
  | ask v k ih =>
    simp only [run_ask, List.mem_cons] at h ⊢
    have hv := h v (.inl rfl)
    rw [← hv, ih _ fun w hw => h w (.inr hw)]
  | problem p next ih =>
    simp only [run_problem] at h ⊢
    rw [ih h]

end Reader

/-- A secret's value never reaches a problem: reading one finds it unset or not at all. -/
theorem secret_problems (vars : Vars) (name doc : String) :
    ∀ p ∈ ((secret name doc).run vars).problems, p = { name, why := .unset } := by
  intro p hp
  simp only [secret, Reader.run_ask] at hp
  split at hp <;> simp_all

/-- A refused secret is `hidden`: neither its value nor what was said of it is kept. -/
theorem field_secret_problems {α : Type} (vars : Vars) (v : Var) (parse : String → Except String α)
    (hs : v.secret = true) :
    ∀ p ∈ ((field v parse).run vars).problems, p = { name := v.name, why := .hidden } := by
  intro p hp
  simp only [field, Reader.run_ask] at hp
  split at hp
  · simp at hp
  · split at hp <;> simp_all

theorem read_ok {α : Type} (r : Reader α) (vars : Vars) (a : α) :
    read r vars = .ok a ↔ (r.run vars).problems = [] ∧ (r.run vars).value = a := by
  unfold read Reader.Result.toExcept
  by_cases h : (r.run vars).problems = [] <;> simp [h]

end Lanes.Environment
