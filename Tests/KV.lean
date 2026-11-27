/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Fixtures.KV

/-!
Refinement checks of the key-value store against its service spec, on one key, two values and
two front ends. The driver sends a read, a write and a second read; the monitor checks every
response against the map spec.

Without caching the store refines the spec with messages lost and reordered and a crash, and
breaks it when any link it uses hands a message over twice: every handling of a message answers
a client or sends on, so a request handed over twice is answered twice. The `kv-cache` example
proves the first for every instance, and that caching breaks it with one front end already.

Behind `Once.actor`, with requests named by front end and number, the store refines `once` of
the map spec with every link duplicating, losing and reordering; without the memo a retry and a
duplicated read take effect twice (the example's `KV.implements_once` proves the first).
-/

namespace Tests.KV

open Lanes Tests.Fixtures.KV

abbrev K := Fin 1
abbrev V := Fin 2
abbrev F := Fin 2

instance : (sig K V F).Inspect := by instance_by_cases
instance (caching : Bool) : (system K V F caching).Inspect := by instance_by_cases
instance : (onceSystem K V F).Inspect := by instance_by_cases

/-- Read through front end 0, write through front end 1, read through front end 0 again. -/
def requests : List (Request K V F) :=
  [⟨1, 0, .get 0⟩, ⟨2, 1, .put 0 1⟩, ⟨3, 0, .get 0⟩]

/-- The same through front end 0 only. -/
def alone : List (Request K V F) :=
  [⟨1, 0, .get 0⟩, ⟨2, 0, .put 0 1⟩, ⟨3, 0, .get 0⟩]

abbrev W (caching : Bool) :=
  World (system K V F caching)
    (List (Request K V F) × Check.Monitor (Request K V F) (Response V) (K → Option V))

def props (caching : Bool) : List (Check.Property (W caching)) :=
  [ Check.refines "every response is allowed by the map spec",
    .sometimes "a read sees the written value" fun w =>
      w.state.outbox.any fun r => r.res == .value (some 1),
    .sometimes "a read sees the empty store" fun w =>
      w.state.outbox.any fun r => r.res == .value none ]

def check (caching : Bool) (env : EnvModel (sig K V F) := {}) (maxCrashes := 0)
    (reqs := requests) :=
  Check.system (system K V F caching)
    { env, driver := (spec K V F).monitored (Driver.anyOrder reqs), maxCrashes } (props caching)

def faulty : EnvModel (sig K V F) where
  link _ _ := { ordered := false, lossy := true }
  mayCrash _ := true
  restarts _ := true

def repeating (dup : Option (Tests.Fixtures.KV.Id F) → Tests.Fixtures.KV.Id F → Bool) :
    EnvModel (sig K V F) where
  link src dst := { duplicating := dup src dst }

def violated (r : Check.Report (W false) (Event (sig K V F))) : Bool :=
  match r.failure with
  | some (.violated "every response is allowed by the map spec" _) => true
  | _ => false

def violated' {sys : System (sig K V F)}
    (r : Check.Report (World sys (List (Request K V F) × Check.Monitor (Request K V F) (Response V) (K → Option V)))
      (Event (sig K V F))) : Bool :=
  match r.failure with
  | some (.violated "every response is allowed by the map spec" _) => true
  | _ => false

def stale (r : Check.Report (W true) (Event (sig K V F))) : Bool :=
  match r.failure with
  | some (.violated "every response is allowed by the map spec" t) =>
    (match t.labels.getLast? with
      | some (.output ⟨3, .value none⟩) => true
      | _ => false)
  | _ => false

/-! ## Requests named by their client -/

/-- Every link loses, reorders and hands messages over twice, and every actor may crash. -/
def chaos : EnvModel (sig K V F) where
  link _ _ := Link.network
  mayCrash _ := true
  restarts _ := true

/-- Write 1, then 0, then read, all through front end 0: if the first write took effect again
after the second, the read would see 1. -/
def overwrite : List (Request K V F) :=
  [⟨1, 0, .put 0 1⟩, ⟨2, 0, .put 0 0⟩, ⟨3, 0, .get 0⟩]

/-- `overwrite` with the first write sent again after the second. -/
def retried : List (Request K V F) :=
  [⟨1, 0, .put 0 1⟩, ⟨2, 0, .put 0 0⟩, ⟨1, 0, .put 0 1⟩, ⟨3, 0, .get 0⟩]

abbrev OW (sys : System (sig K V F)) :=
  World sys (List (Request K V F) × Check.OnceMonitor (Request K V F) (Response V) (K → Option V) (F × ReqId))

def onceProps (sys : System (sig K V F)) : List (Check.Property (OW sys)) :=
  [ Check.refinesOnce "every response is allowed by the map spec, once per request",
    .sometimes "a read sees the written value" fun w =>
      w.state.outbox.any fun r => r.res == .value (some 1),
    .sometimes "an answer is waiting twice" fun w =>
      w.state.outbox.any fun r => w.state.outbox.count r ≥ 2 ]

/-- The client sends its requests in order, one after another's arrival: a duplicate is the
link's, or a retry the list makes. -/
def checkOnce (sys : System (sig K V F)) [sys.Inspect] (env : EnvModel (sig K V F))
    (reqs : List (Request K V F)) (maxCrashes := 0) (depth := 12) :=
  Check.system sys
    { env, driver := (spec K V F).onceMonitored requestKey (Driver.script reqs), maxCrashes }
    (onceProps sys) { maxDepth := some depth }

def violatedOnce {sys : System (sig K V F)} (r : Check.Report (OW sys) (Event (sig K V F))) :
    Bool :=
  match r.failure with
  | some (.violated "every response is allowed by the map spec, once per request" _) => true
  | _ => false

def tests : List (String × Bool) :=
  let plain := check false
  let lost := check false faulty 1
  [ ("kv: without caching the store refines the map spec",
      plain.ok && plain.complete),
    ("kv: the check is not vacuous: reads see both the empty store and the written value",
      plain.witnesses.length == 2),
    ("kv: with messages lost and reordered and a crash, the store still refines the map spec",
      lost.ok && lost.complete && lost.witnesses.length == 2),
    ("kv: a request handed to a front end twice breaks refinement",
      violated (check false (repeating fun src _ => src.isNone))),
    ("kv: a put handed to the store twice breaks refinement: it is acknowledged twice",
      violated (check false (repeating fun src dst => src.isSome && decide (dst = .store)))),
    ("kv: a read's answer handed to a front end twice breaks refinement",
      violated (check false (repeating fun src _ => decide (src = some .store)))),
    ("kv: read caching breaks refinement: a stale read after an acknowledged write",
      stale (check true)),
    ("kv: one front end is enough: it does not forget its cache when it writes",
      stale (check true {} 0 alone)),
    ("kv: the run found is `staleRead`, which the proof replays for every instance",
      match (check true {} 0 alone).failure with
      | some (.violated _ t) =>
        t.labels.map Event.render == (staleRead (0 : K) (1 : V) (0 : F)).map Event.render
      | _ => false),
    ("kv once: with every link duplicating, the store that remembers refines the map spec once per request",
      let r := checkOnce (onceSystem K V F) (repeating fun _ _ => true) requests
      r.ok && r.witnesses.length == 2),
    ("kv once: and with every link losing and reordering too, and a crash",
      let r := checkOnce (onceSystem K V F) chaos overwrite 1 10
      r.ok && r.witnesses.length == 2),
    ("kv once: a client that retries its first write after its second gets one effect of each",
      let r := checkOnce (onceSystem K V F) {} retried 0 20
      !violatedOnce r && r.complete),
    ("kv once: without the memo, that retry takes effect again and the read sees it",
      violatedOnce (checkOnce (system K V F false) {} retried 0 20)),
    ("kv once: without the memo, a request handed to the store twice takes effect twice: a read is answered with two values",
      violatedOnce (checkOnce (system K V F false)
        { link := fun src dst => { ordered := false, duplicating := src.isSome && decide (dst = .store) } }
        overwrite 0 17)),
    ("kv once: with the memo, the map spec without `once` is still broken: an answer is handed over twice",
      violated' (Check.system (onceSystem K V F)
        { env := repeating fun _ _ => true,
          driver := (spec K V F).monitored (Driver.anyOrder requests) }
        [Check.refines "every response is allowed by the map spec"] { maxDepth := some 14 })) ]

end Tests.KV
