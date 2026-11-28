/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Waves

/-! `videosWaves [entries]`: how wide the waves of the site's journal are, as it runs and split
into an actor per member (`Videos.Waves`). -/

open Videos Videos.Waves

def layouts : List (String × Layout) :=
  [ ("as it runs: the site beside the scheduler", .asRuns),
    ("by member, a catalog, one scheduler", .split {}),
    ("by member, a catalog, a scheduler per member", .split { perMember := true }),
    ("by member, a catalog, one scheduler; reads from state", .split { reads := false }),
    ("by member, a catalog, a scheduler per member; reads from state",
      .split { perMember := true, reads := false }),
    ("by member, a scheduler per member; reads, the feed's among them, from state",
      .split { perMember := true, reads := false, index := false }),
    ("the same, and each member's actor named by its identity",
      .split { perMember := true, reads := false, index := false, directory := false }),
    ("the same, and likes and comments held by who makes them",
      .split { perMember := true, reads := false, index := false, directory := false
               writerHolds := true }) ]

def main (args : List String) : IO Unit := do
  let entries := (args.head?.bind String.toNat?).getD 20000
  for popular in [true, false] do
    let w : Workload := { entries, popular }
    let d := run w
    IO.println s!"\n{if popular then "Views by popularity" else "Views uniform"}: {w.members} members, {d.ready.size} videos ready at the end, {w.entries} entries\n"
    IO.println "| Layout | Batch | Waves per batch | Entries per wave | In waves of 2 or more | In waves of 8 or more |"
    IO.println "| --- | --- | --- | --- | --- | --- |"
    let mut hot := #[]
    for (name, layout) in layouts do
      let kept := d.log.toList.filter fun (x, _) => layout.keeps x
      let es := kept.map fun (_, units) => (units.flatMap (layout.touches d.owners)).eraseDups
      for n in [64, 256] do
        IO.println (Stats.row name (measure n es))
      hot := hot.push s!"- {name}: {es.length} entries; the actor most of them touch, {hottest es}"
    IO.println ""
    for h in hot do IO.println h
