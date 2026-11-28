/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Waves

/-! `videosWaves [actions]`: how wide the waves of the site's journal are, with an actor and a
scheduler for each member and the reads from the members' states (`Videos.Waves`). -/

open Videos Videos.Waves

def main (args : List String) : IO Unit := do
  let actions := (args.head?.bind String.toNat?).getD 20000
  IO.println "| Views | Batch | Waves per batch | Entries per wave | In waves of 2 or more | In waves of 8 or more |"
  IO.println "| --- | --- | --- | --- | --- | --- |"
  let mut notes := #[]
  for popular in [true, false] do
    let w : Workload := { actions, popular }
    let d := run w
    let es := d.log.toList
    for n in [64, 256] do
      IO.println (Stats.row (if popular then "by popularity" else "uniform") (measure n es))
    notes := notes.push s!"- Views {if popular then "by popularity" else "uniform"}: {w.members} members, {d.ready.size} videos ready at the end, {d.actions} actions of which {d.reads} reads, {es.length} entries; the actor most entries touch: {hottest es}"
  IO.println ""
  for n in notes do IO.println n
