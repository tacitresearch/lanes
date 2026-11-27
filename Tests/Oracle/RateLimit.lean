/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic

/-!
`Lanes.RateLimit` against `golang.org/x/time/rate`. A case is a limiter and a sequence of
requests; the answers are compared request by request. Rates are powers of two between 1/8 and
8 a second and times are multiples of 125 ms, so that Go's float64 token count, and the delays
it computes from it, are exact.
-/

namespace Tests.Oracle.RateLimit

open Lanes Lanes.RateLimit

def config (num den burst : Nat) : Config := { burst, count := num, period_ms := den * 1000 }

def step (c : Config) : Bucket × List Json → String × Nat × Nat → Bucket × List Json
  | (b, out), ("allow", t, n) =>
    let (ok, b) := allow c b t n
    (b, out ++ [.bool ok])
  | (b, out), (_, t, n) =>
    match reserve c b t n with
    | some (d, b) => (b, out ++ [Json.num (d * 1000000 : Nat)])
    | none => (b, out ++ [.null])

def request (line : String) : Option (String × Nat × Nat) :=
  match line.splitOn " " with
  | [kind, t, n] => do return (kind, ← t.toNat?, ← n.toNat?)
  | _ => none

def run (s : String) : Option Json := do
  match s.splitOn "\n" with
  | first :: lines =>
    match first.splitOn " " with
    | [r, burst] =>
      match r.splitOn "/" with
      | [num, den] =>
        let c := config (← num.toNat?) (← den.toNat?) (← burst.toNat?)
        let reqs ← lines.mapM request
        return .arr (reqs.foldl (step c) (full c, [])).2.toArray
      | _ => none
    | _ => none
  | [] => none

def answer (c : Case) : Answer :=
  match c.op, String.fromUTF8? c.input with
  | "run", some s => run s
  | _, _ => none

def runText (rate : String) (burst : Nat) (reqs : List (String × Nat × Nat)) : String :=
  "\n".intercalate (s!"{rate} {burst}" :: reqs.map fun (k, t, n) => s!"{k} {t} {n}")

def tests : List (String × Bool) :=
  [ ("rate: a burst of 2 at 1 a second, then one a second",
      run (runText "1/1" 2 [("allow", 0, 1), ("allow", 0, 1), ("allow", 0, 1), ("allow", 500, 1),
        ("allow", 1000, 1), ("allow", 1000, 1)])
        == some (.arr #[.bool true, .bool true, .bool false, .bool false, .bool true, .bool false])),
    ("rate: a reservation into debt tells how long to wait",
      run (runText "2/1" 1 [("reserve", 0, 1), ("reserve", 0, 1), ("reserve", 0, 2), ("allow", 0, 1)])
        == some (.arr #[Json.num (0 : Nat), Json.num (500000000 : Nat), .null, .bool false])) ]

def rates : List String := ["1/8", "1/4", "1/2", "1/1", "2/1", "4/1", "8/1"]

def case : Gen Case := do
  let rate ← Gen.pick rates
  let burst ← Gen.below 6
  let count ← Gen.below 13
  let start ← Gen.below 40
  let (_, reqs) ← (List.range count).foldlM (init := (start, ([] : List (String × Nat × Nat))))
    fun (t, reqs) _ => do
      let t ← match ← Gen.below 10 with
        | 0 => pure (t - min t (← Gen.below 9))
        | 1 | 2 => pure t
        | _ => pure (t + (← Gen.below 17))
      let kind ← if ← Gen.chance 30 then pure "reserve" else pure "allow"
      let n ← Gen.below (burst + 2)
      return (t, reqs ++ [(kind, t * 125, n)])
  return text (runText rate burst reqs) "run"

def package : Package where
  name := "rate"
  edges := [text (runText "1/1" 2 [("allow", 0, 1), ("allow", 0, 1), ("allow", 0, 1), ("allow", 500, 1),
      ("allow", 1000, 1)]) "run",
    text (runText "2/1" 1 [("reserve", 0, 1), ("reserve", 0, 1), ("reserve", 0, 2), ("allow", 0, 1)]) "run",
    text (runText "1/8" 0 [("allow", 0, 0), ("allow", 0, 1), ("reserve", 0, 0)]) "run"]
  case := case
  answer := answer

end Tests.Oracle.RateLimit
