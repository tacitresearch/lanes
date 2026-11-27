/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic

/-!
`Lanes.Metrics.render` against Prometheus's `expfmt`, which parses what ours writes. A case is
the families, written as JSON, and the page ours renders from them; ours answers with what the
families say a reader should see, Go with what its parser read from the page. A case whose page
is not what ours renders now answers that, so recorded answers fail when the renderer changes.
-/

namespace Tests.Oracle.Metrics

open Lanes Lanes.Metrics

/-! ## Families as JSON, both ways -/

def labelsJson (ls : Labels) : Json := .arr (ls.map fun (k, v) => Json.arr #[k, v]).toArray

def natsJson (ns : List Nat) : Json := .arr (ns.map fun (n : Nat) => Json.num (JsonNumber.fromNat n)).toArray

def familyJson (f : Family) : Json :=
  let (kind, bounds, samples) : String × List Nat × List Json := match f.series with
    | .counter s => ("counter", [], s.map fun (ls, n) => Json.mkObj [("labels", labelsJson ls), ("value", n)])
    | .gauge s => ("gauge", [], s.map fun (ls, v) => Json.mkObj [("labels", labelsJson ls), ("value", v)])
    | .histogram bounds s => ("histogram", bounds, s.map fun (ls, h) =>
        Json.mkObj [("labels", labelsJson ls), ("below", natsJson h.below), ("count", h.count),
          ("sum", h.sum)])
  Json.mkObj [("name", f.name), ("help", f.help), ("scale", f.scale), ("kind", kind),
    ("bounds", natsJson bounds), ("samples", .arr samples.toArray)]

def readLabels (j : Json) : Except String Labels := do
  (← j.getArr?).toList.mapM fun p => do
    match (← p.getArr?).toList with
    | [k, v] => return (← k.getStr?, ← v.getStr?)
    | _ => throw "a label is a pair"

def readNats (j : Json) : Except String (List Nat) := do (← j.getArr?).toList.mapM Json.getNat?

def readFamily (j : Json) : Except String Family := do
  let samples := (← (← j.getObjVal? "samples").getArr?).toList
  let series ← match ← (← j.getObjVal? "kind").getStr? with
    | "counter" => Series.counter <$> samples.mapM fun s => do
        return (← readLabels (← s.getObjVal? "labels"), ← (← s.getObjVal? "value").getNat?)
    | "gauge" => Series.gauge <$> samples.mapM fun s => do
        return (← readLabels (← s.getObjVal? "labels"), ← (← s.getObjVal? "value").getInt?)
    | "histogram" =>
      let bounds ← readNats (← j.getObjVal? "bounds")
      Series.histogram bounds <$> samples.mapM fun s => do
        let below ← readNats (← s.getObjVal? "below")
        let count ← (← s.getObjVal? "count").getNat?
        let sum ← (← s.getObjVal? "sum").getNat?
        return (← readLabels (← s.getObjVal? "labels"), ({ below, count, sum } : Histogram bounds))
    | kind => throw s!"no kind {kind}"
  return { name := ← (← j.getObjVal? "name").getStr?, help := ← (← j.getObjVal? "help").getStr?,
           scale := ← (← j.getObjVal? "scale").getNat?, series }

def pageJson (families : List Family) : Json :=
  Json.mkObj [("families", .arr (families.map familyJson).toArray), ("text", render families)]

def readPage (input : ByteArray) : Except String (List Family × String) := do
  let some s := String.fromUTF8? input | throw "not UTF-8"
  let j ← Json.parse s
  let families ← (← (← j.getObjVal? "families").getArr?).toList.mapM readFamily
  return (families, ← (← j.getObjVal? "text").getStr?)

/-! ## What a reader should see -/

def sortedLabels (ls : Labels) : Json :=
  labelsJson ((ls.map fun (k, v) => (sanitize k, v)).mergeSort fun a b => a.1 ≤ b.1)

def seriesOf (f : Family) : List Json :=
  match f.series with
  | .counter s => s.map fun (ls, n) =>
      Json.mkObj [("labels", sortedLabels ls), ("value", decimal f.scale n)]
  | .gauge s => s.map fun (ls, v) =>
      Json.mkObj [("labels", sortedLabels ls), ("value", decimalInt f.scale v)]
  | .histogram bounds s => s.map fun (ls, h) =>
      let buckets := (bounds.zip h.below).map (fun (b, n) => Json.arr #[decimal f.scale b, toString n])
        ++ [Json.arr #["+Inf", toString h.count]]
      Json.mkObj [("labels", sortedLabels ls), ("buckets", .arr buckets.toArray),
        ("sum", decimal f.scale h.sum), ("count", toString h.count)]

/-- The families a reader sees: by name, a family without series left out, as the format writes
nothing of one. -/
def expected (families : List Family) : Json :=
  let seen := families.filter fun f => !(seriesOf f).isEmpty
  .arr ((seen.mergeSort fun a b => sanitize a.name ≤ sanitize b.name).map fun f =>
    Json.mkObj [("name", sanitize f.name), ("help", f.help), ("type", f.series.kind),
      ("series", .arr (seriesOf f).toArray)]).toArray

def answer (c : Case) : Answer :=
  match readPage c.input with
  | .ok (families, text) =>
    if render families == text then some (expected families)
    else some (.str "the page is not what ours renders now")
  | .error _ => none

/-! ## Cases -/

def familyNames : List String :=
  ["requests", "lanes_http_requests_total", "latency-seconds", "9lives", "", "a.b", "é"]

def helps : List String := ["", "Requests.", "a \\ backslash", "line\nbreak", "é ሴ", "\"quoted\""]

def labelNames : List String := ["method", "path", "code", "a-b", "region", "9", "status"]

/-- Names the format reserves, or that are one once made valid. -/
def clashing : List String := ["le", "__name__", "a_b", "a-b"]

def labelValues : List String := ["GET", "/", "", "a\"b", "back\\slash", "new\nline", "é", "{x=\"1\"}"]

def genLabels : Gen Labels := do
  let names := if ← Gen.chance 5 then labelNames ++ clashing else labelNames
  let ls ← Gen.list (← Gen.below 3) (return (← Gen.pick names, ← Gen.pick labelValues))
  return if ← Gen.chance 90 then ls.eraseDupsBy (·.1 == ·.1) else ls

def genNat : Gen Nat := do
  match ← Gen.below 10 with
  | 0 => return 0
  | 1 => do
    let big ← Gen.chance 20
    let n ← Gen.below 1000
    return if big then n * 10 ^ 18 + 7 else n * 10 ^ 9
  | 2 | 3 => Gen.below 10
  | _ => Gen.below 1000000

def genFamily : Gen Family := do
  let name ← Gen.pick familyNames
  let help ← Gen.pick helps
  let scale ← Gen.pick [0, 0, 1, 3, 6]
  let n ← Gen.below 4
  let series ← match ← Gen.below 3 with
    | 0 => Series.counter <$> Gen.list n (return (← genLabels, ← genNat))
    | 1 => Series.gauge <$> Gen.list n (do
        let v : Int := ← genNat
        return (← genLabels, if ← Gen.chance 30 then -v else v))
    | _ => do
      let bounds ← Gen.list (← Gen.below 4) genNat
      let bounds := if ← Gen.chance 80 then bounds.mergeSort (· ≤ ·) else bounds
      Series.histogram bounds <$> Gen.list n (do
        let vs ← Gen.list (← Gen.below 5) genNat
        return (← genLabels, Histogram.observeAll bounds vs))
  return { name, help, scale, series }

def case : Gen Case := do
  let families ← Gen.list (← Gen.below 4) genFamily
  let families ← if ← Gen.chance 90 then pure (families.eraseDupsBy fun a b => sanitize a.name == sanitize b.name)
    else pure families
  return ⟨"parse", (pageJson families).compress.toUTF8⟩

def edges : List Case :=
  let h : Histogram [5, 10] := Histogram.observeAll [5, 10] [3, 7, 12]
  [ [], [{ name := "up", help := "Up.", series := .gauge [([], 1)] }],
    [{ name := "lanes_requests_total", help := "Requests answered.",
       series := .counter [([("method", "GET"), ("code", "200")], 12), ([("method", "POST")], 0)] }],
    [{ name := "latency_seconds", help := "Latency.", scale := 3,
       series := .histogram [5, 10] [([("path", "/")], h)] }],
    [{ name := "escapes", help := "back\\slash and\nline", series := .gauge [([("v", "a\"b\\c\nd")], -2)] }],
    [{ name := "empty", help := "None yet.", series := .counter [] }] ].map
    fun fs => ⟨"parse", (pageJson fs).compress.toUTF8⟩

/-! ## Where the text ours writes is not one reader reads as given -/

def families? (c : Case) : List Family :=
  match readPage c.input with
  | .ok (fs, _) => fs
  | .error _ => []

def seriesLabels (f : Family) : List Labels :=
  match f.series with
  | .counter s => s.map (·.1)
  | .gauge s => s.map (·.1)
  | .histogram _ s => s.map (·.1)

/-- Two families whose names are one once made valid: the format allows one. -/
def sameName (c : Case) : Bool :=
  let names := ((families? c).map (sanitize ·.name))
  names.eraseDups.length < names.length

/-- A series with two labels whose names are one once made valid, `__name__`, which the format
reserves, or, in a histogram, `le`, which its buckets take. -/
def badLabelNames (c : Case) : Bool :=
  (families? c).any fun f => (seriesLabels f).any fun ls =>
    let names := ls.map (sanitize ·.1)
    names.eraseDups.length < names.length || names.contains "__name__"
      || (f.series.kind == "histogram" && names.contains "le")

/-- Two series of a histogram with one set of labels, which a reader takes for one. -/
def sameSeries (c : Case) : Bool :=
  (families? c).any fun f => f.series.kind == "histogram" &&
    let sets := (seriesLabels f).map fun ls =>
      (ls.map fun (k, v) => (sanitize k, v)).mergeSort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)
    sets.eraseDups.length < sets.length

/-- A number of more than 15 significant digits: Go reads values as float64. -/
def beyondFloat (c : Case) : Bool :=
  let big (n : Nat) := n ≥ 10 ^ 15
  (families? c).any fun f => match f.series with
    | .counter s => s.any (big ·.2)
    | .gauge s => s.any (big ·.2.natAbs)
    | .histogram bounds s => bounds.any big || s.any fun (_, h) => big h.sum || big h.count

def package : Package where
  name := "expfmt"
  edges := edges
  shrinks := false
  recorded := 300
  case := case
  answer := answer
  known c go :=
    if sameName c && go.isNone then some "two families with one name, which ours writes as given"
    else if badLabelNames c && go.isNone then
      some "labels with one name, `__name__`, or `le` in a histogram, which ours writes as given"
    else if sameSeries c then some "two series of a histogram with one set of labels, which ours writes as given"
    else if beyondFloat c then some "a number beyond float64's precision, which Go reads"
    else none

end Tests.Oracle.Metrics
