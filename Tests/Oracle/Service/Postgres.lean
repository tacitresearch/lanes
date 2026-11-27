/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Service.Basic
import Tests.PostgresLive

/-!
The store's adapter against a real PostgreSQL (`oracles/postgres`), as `Tests/PostgresLive.lean`
runs it: write skew and a `COMMIT` whose reply is lost, at read committed and at serializable,
and runs of two or three transactions interleaved at random, each recorded and checked against
the store model (`Store.State.run`) from the empty table, and kept in
`oracles/postgres/store.jsonl`, one run a line. Two transactions open at once never write one
key, so that no request waits on another's lock: the recorder asks one request at a time.
-/

namespace Tests.Oracle.Service.Postgres

open Lanes Lanes.Postgres Tests.PostgresLive

/-! ## A run, as JSON -/

def opJson : Store.Op Nat String → Json
  | .begin => Json.mkObj [("op", "begin")]
  | .read k => Json.mkObj [("op", "read"), ("key", k)]
  | .scan => Json.mkObj [("op", "scan")]
  | .write k v => Json.mkObj [("op", "write"), ("key", k), ("value", v)]
  | .insert k v => Json.mkObj [("op", "insert"), ("key", k), ("value", v)]
  | .append v => Json.mkObj [("op", "append"), ("value", v)]
  | .delete k => Json.mkObj [("op", "delete"), ("key", k)]
  | .commit => Json.mkObj [("op", "commit")]
  | .rollback => Json.mkObj [("op", "rollback")]

def readOp (j : Json) : Option (Store.Op Nat String) := do
  match ← str? j "op" with
  | "begin" => return .begin
  | "read" => return .read (← nat? j "key")
  | "scan" => return .scan
  | "write" => return .write (← nat? j "key") (← str? j "value")
  | "insert" => return .insert (← nat? j "key") (← str? j "value")
  | "append" => return .append (← str? j "value")
  | "delete" => return .delete (← nat? j "key")
  | "commit" => return .commit
  | "rollback" => return .rollback
  | _ => none

def answerJson : Store.Answer Nat String → Json
  | .ok => Json.mkObj [("answer", "ok")]
  | .value v => Json.mkObj [("answer", "value"), ("value", (v.map Json.str).getD .null)]
  | .rows rows => Json.mkObj [("answer", "rows"),
      ("rows", .arr (rows.map fun (k, v) => Json.arr #[k, v]).toArray)]
  | .key k => Json.mkObj [("answer", "key"), ("key", k)]
  | .committed => Json.mkObj [("answer", "committed")]
  | .failed => Json.mkObj [("answer", "failed")]
  | .unknown => Json.mkObj [("answer", "unknown")]

def readRow (j : Json) : Option (Nat × String) := do
  match (← j.getArr?.toOption).toList with
  | [k, v] => return (← k.getNat?.toOption, ← v.getStr?.toOption)
  | _ => none

def readAnswer (j : Json) : Option (Store.Answer Nat String) := do
  match ← str? j "answer" with
  | "ok" => return .ok
  | "value" => return .value (str? j "value")
  | "rows" => return .rows (← (← (j.getObjVal? "rows" >>= Json.getArr?).toOption).toList.mapM readRow)
  | "key" => return .key (← nat? j "key")
  | "committed" => return .committed
  | "failed" => return .failed
  | "unknown" => return .unknown
  | _ => none

def eventJson : Event → Json
  | .inl r => Json.mkObj [("request", r.id), ("txn", r.txn), ("op", opJson r.op)]
  | .inr r => Json.mkObj [("reply", r.id), ("answer", answerJson r.answer)]

def readEvent (j : Json) : Option Event :=
  match nat? j "request", nat? j "reply" with
  | some id, _ => do return .inl { id, txn := ← nat? j "txn", op := ← readOp (← (j.getObjVal? "op").toOption) }
  | none, some id => do return .inr { id, answer := ← readAnswer (← (j.getObjVal? "answer").toOption) }
  | none, none => none

def isolationName : Store.Isolation → String
  | .readCommitted => "read committed"
  | .serializable => "serializable"

def runJson (name : String) (isolation : Store.Isolation) (events : List Event) : Json :=
  Json.mkObj [("run", name), ("isolation", isolationName isolation),
    ("events", .arr (events.map eventJson).toArray)]

/-- Whether the store model allows the run, from the empty table. -/
def allows (isolation : Store.Isolation) (events : List Event) : Bool :=
  ((({ worlds := [{ db := [], base := [] }] } : Store.State Nat String)).run (model isolation) events).isSome

/-! ## Runs at random -/

/-- A run of `steps` requests by up to three transactions at once, chosen by `seed`; the
transactions still open at the end commit. -/
def randomRun (cfg : Client.Config) (isolation : Store.Isolation) (seed steps : Nat) : IO Recorder := do
  reset cfg
  let r ← Recorder.new cfg isolation
  let gen ← IO.mkRef (mkStdGen seed)
  let below (n : Nat) : IO Nat := gen.modifyGet fun g => let (x, g) := randNat g 0 (n - 1); (x, g)
  let mut open_ : List Nat := []
  -- The keys each open transaction has written, which no other may write until it ends.
  let mut held : List (Nat × Nat) := []
  let mut next := 1
  for step in [0:steps] do
    let roll ← below 10
    if open_.isEmpty || (roll == 0 && open_.length < 3) then
      if (← r.ask next .begin) == .ok then open_ := open_ ++ [next]
      next := next + 1
    else
      let txn := open_[(← below open_.length)]!
      let k := (← below 3) + 1
      let v := s!"v{step}"
      let op : Store.Op Nat String ← match roll with
        | 1 => pure (if (← below 2) == 0 then .commit else .rollback)
        | 2 | 3 => pure (.read k)
        | 4 => pure .scan
        | 5 | 6 => pure (.write k v)
        | 7 => pure (.insert k v)
        | 8 => pure (.delete k)
        | _ => pure .commit
      let writes := match op with | .write .. | .insert .. | .delete _ => true | _ => false
      if writes && held.any fun (key, t) => key == k && t != txn then continue
      if writes then held := (k, txn) :: held
      let answer ← r.ask txn op
      let over := match op, answer with
        | .commit, _ | .rollback, _ => true
        | _, .failed | _, .unknown => true
        | _, _ => false
      if over then
        open_ := open_.filter (· != txn)
        held := held.filter (·.2 != txn)
  for txn in open_ do discard <| r.ask txn .commit
  return r

/-! ## Against PostgreSQL -/

def runs (cfg : Client.Config) : IO (List (String × Store.Isolation × List Event × Bool)) := do
  let mut out := []
  for isolation in [Store.Isolation.readCommitted, .serializable] do
    let (both, skew) ← writeSkewRun cfg isolation
    out := out ++ [(s!"write skew, both committed: {both}", isolation, ← skew.events.get,
      both == (isolation == .readCommitted))]
    let (lost, commit) ← lostCommitRun cfg isolation
    out := out ++ [(s!"a COMMIT whose reply is lost, unknown: {lost}", isolation, ← commit.events.get, lost)]
    for seed in [0:25] do
      let r ← randomRun cfg isolation seed 30
      out := out ++ [(s!"at random, seed {seed}", isolation, ← r.events.get, true)]
  return out

def run (host : String) (tcpPort : UInt16) : IO (List (String × Bool) × List Json) := do
  let cfg := config host tcpPort "lanes_trust" none
  match ← (connect cfg).block with
  | .error _ => return ([(s!"store on postgres: lanes_trust connects to {host}:{tcpPort}", false)], [])
  | .ok s => (s.close).block
  let all ← runs cfg
  let checks := all.map fun (name, isolation, events, expected) =>
    (s!"store on postgres, {isolationName isolation}, {name}: {events.length} events the store model allows",
      expected && allows isolation events)
  for (name, isolation, events, _) in all do
    unless allows isolation events do
      IO.println s!"  not allowed: {(runJson name isolation events).compress}"
  return (checks, all.map fun (name, isolation, events, _) => runJson name isolation events)

def readRun (j : Json) : Option (String × Store.Isolation × List Event) := do
  let isolation ← match ← str? j "isolation" with
    | "read committed" => some Store.Isolation.readCommitted
    | "serializable" => some .serializable
    | _ => none
  let lines ← (j.getObjVal? "events" >>= Json.getArr?).toOption
  return (← str? j "run", isolation, ← lines.toList.mapM readEvent)

def replay (lines : List Json) : List (String × Bool) :=
  let read := lines.filterMap readRun
  [ (s!"store on postgres, recorded: {read.length} runs read", read.length == lines.length && !lines.isEmpty),
    ("store on postgres, recorded: every run is one the store model allows",
      read.all fun (_, isolation, events) => allows isolation events) ]

def oracle : Oracle where
  name := "store"
  reference := "postgres"
  envVar := "LANES_POSTGRES"
  live := run
  replay := replay

end Tests.Oracle.Service.Postgres
