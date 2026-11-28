/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.System

/-!
# Does the site's work spread over actors?

Waves (`Lanes.WavePlan`) apply a batch of journal entries in parallel where the entries touch no
actor in common. This measures, for a workload of many members, how wide the waves of the site's
journal are, with the site as it runs: an actor and a scheduler for each member, named by the
identity that signs in, and the reads answered from the members' states and not journalled.

The workload runs through the real system on a kernel: members sign in, make videos that are
checked, transcoded and reported, watch and like the popular ones, comment, read the feed and
the channels, and delete. The store's and the worker's answers come back as entries a few entries
after their call. A read is a browser's action but no entry. The choices are a fixed
generator's, so every run gives the same numbers.

An entry touches every actor that one of its messages, or a timer it leads to, reaches before
the kernel is quiet again: the actor its input goes to, the owner's actor a visit goes to, the
scheduler a job goes to and the member its word comes back to.
-/

namespace Videos.Waves

open Lanes

def workerKey : Hmac.Key := .of "the worker's key".toUTF8

def config : Config := { workerKey }

abbrev K := Kernel (system config)

abbrev Entry := fullSig.In

abbrev Actor := fullSig.Id

/-- A deterministic generator: a 64-bit linear congruential one. -/
structure Gen where
  seed : UInt64

def Gen.next (g : Gen) (n : Nat) : Nat × Gen :=
  let s := g.seed * 6364136223846793005 + 1442695040888963407
  (((s >>> 33).toNat) % max 1 n, ⟨s⟩)

/-- An index below `n`, the low ones far more often: about `1 / (r + 1)`, as views of videos by
their rank are. -/
def Gen.popular (g : Gen) (n : Nat) : Nat × Gen :=
  let (x, g) := g.next 1000000
  let u := x.toFloat / 1000000.0
  let r := (Float.pow (n.toFloat + 1.0) u - 1.0).floor.toUInt64.toNat
  (min r (n - 1), g)

/-- How often a browser does each thing, in parts of `total`: views most, then the feed, likes,
channel pages, comments, sign-ins, uploads and deletes. An upload brings four entries more (the
browser's "uploaded", the store's answer to the check, the worker's to the job, its report), and
a delete one (the store's answer). Views, the feed and channel pages are reads. -/
structure Mix where
  watch : Nat := 500
  feed : Nat := 130
  channel : Nat := 90
  like : Nat := 150
  comment : Nat := 50
  create : Nat := 20
  delete : Nat := 10
  signIn : Nat := 50
  deriving Repr

def Mix.total (m : Mix) : Nat :=
  m.watch + m.feed + m.channel + m.like + m.comment + m.create + m.delete + m.signIn

structure Workload where
  members : Nat := 1000
  mix : Mix := {}
  /-- Videos made, checked, transcoded and reported before the measured actions. -/
  warmVideos : Nat := 400
  /-- The entries measured, with the reads, which would be entries if they were journalled, as
  D107 counts them. -/
  actions : Nat := 20000
  /-- Whether views follow popularity, or are uniform over the ready videos. -/
  popular : Bool := true
  seed : UInt64 := 42
  deriving Repr

def name (s : String) : {s : String // Name.valid s} :=
  if h : Name.valid s = true then ⟨s, h⟩ else ⟨"x", by simp [Name.valid]⟩

/-- Member `m` of the workload, signed in with the provider `google`. -/
def who (m : Nat) : Who := ⟨name "google", name s!"user{m}"⟩

/-- What the driver knows, as a browser and the store would: each member's session, the videos
there are, and the entries due later (the store's and the worker's answers, and the browsers'
"uploaded"). -/
structure Driver where
  k : K
  gen : Gen
  req : Nat := 0
  sessions : Std.HashMap Nat Sid := {}
  ready : Array VideoId := #[]
  later : List (Nat × Entry) := []
  /-- The actors each measured entry touches, in order. -/
  log : Array (List Actor) := #[]
  entry : Nat := 0
  /-- The entries and reads measured, and how many were reads. -/
  actions : Nat := 0
  reads : Nat := 0

def at_s (d : Driver) : Nat := 1000000 + d.entry / 20

def touchedBy : Event fullSig → Option Actor
  | .deliver e => some e.dst
  | .timeout i _ => some i
  | _ => none

/-- Run the kernel until there is no work to do now, and the actors its steps reached. -/
def drain (k : K) : (fuel : Nat) → K × List Actor × List fullSig.Out
  | 0 => (k, [], [])
  | fuel + 1 =>
    if k.wait != .none then (k, [], [])
    else
      match k.step with
      | { kernel, events, outputs } =>
        let (k, more, outs) := drain kernel fuel
        (k, events.filterMap touchedBy ++ more, outputs ++ outs)

def answerFor : Op → Answer
  | .head _ => .found 1000
  | .delete _ => .deleted
  | .transcode _ => .accepted

def report (r : Round) : Command :=
  let rep : Report := .done r
  .report 0 rep (Transcode.signature workerKey rep.round.id rep.status)

/-- The member number a workload's identity has. -/
def numberOf (w : Who) : Nat := ((w.subject.val.drop 4).toString.toNat?).getD 0

/-- What the outputs make the driver do: remember sessions and videos, and answer calls. -/
def Driver.take (d : Driver) (outs : List fullSig.Out) : Driver :=
  outs.foldl (init := d) fun d out =>
    match out with
    | .inr (.reply _ _ (.signedIn m sid _)) => { d with sessions := d.sessions.insert (numberOf m) sid }
    | .inr (.reply _ (some (m, sid)) (.created v _ _)) =>
      { d with later := (d.entry + 5, .inr (.request (.uploaded 0 m sid v) 0)) :: d.later }
    | .inl (.call a) =>
      let answer := answerFor a.key.op
      let reports := match a.key with
        | .transcode r => [(d.entry + 20, .inr (.request (report r) 0))]
        | _ => []
      { d with later := (d.entry + 3, .inl (.reply a.key a.attempt (.answer answer)))
                 :: reports ++ d.later }
    | _ => d

/-- Number the request and stamp it with the time, as the bridge does. -/
def Driver.stamp (d : Driver) : Entry → Driver × Entry
  | .inr (.request c _) =>
    let req := d.req
    let c := match c with
      | .signIn _ w n => .signIn req w n
      | .signOut _ m s => .signOut req m s
      | .create _ m s t a v md => .create req m s t a v md
      | .uploaded _ m s v => .uploaded req m s v
      | .like _ m s v on => .like req m s v on
      | .comment _ m s v b => .comment req m s v b
      | .uncomment _ m s v c => .uncomment req m s v c
      | .delete _ m s v => .delete req m s v
      | .retry _ m s v => .retry req m s v
      | .report _ r sig => .report req r sig
    ({ d with req := req + 1 }, .inr (.request c (at_s d)))
  | x => (d, x)

def isReady (k : K) (v : VideoId) : Bool :=
  (((k.cell (.inr v.owner)).state : Site).find? v).any (·.status.isReady)

/-- The kernel with `entries` accepted, taken out of the driver, which then holds none: a kernel
held twice would copy its table of actors at its next write. -/
def Driver.begin (d : Driver) (entries : List Entry) : K × Driver :=
  let now := at_s d * 1000
  let k := d.k
  let d := { d with k := {} }
  ((k.advance now).acceptAll entries, d)

def Driver.feed (d : Driver) (x : Entry) (measured : Bool) : Driver :=
  let (d, x) := d.stamp x
  let (k, d) := d.begin [x]
  let (k, touched, outs) := drain k 100000
  let d := { d with k, entry := d.entry + 1
                    log := if measured then d.log.push touched.eraseDups else d.log }
  let d := d.take outs
  match x with
  | .inr (.request (.report _ r _) _) =>
    if isReady d.k r.round.video then { d with ready := d.ready.push r.round.video } else d
  | _ => d

def title : Title := ⟨"a video", by decide⟩
def about : About := ⟨"", by decide⟩
def remark : Remark := ⟨"nice", by decide⟩

def Driver.member (d : Driver) (w : Workload) : Nat × Driver :=
  let (m, gen) := d.gen.next w.members
  (m, { d with gen })

def Driver.video (d : Driver) (w : Workload) : Option VideoId × Driver :=
  if d.ready.isEmpty then (none, d)
  else
    let (i, gen) := if w.popular then d.gen.popular d.ready.size else d.gen.next d.ready.size
    (d.ready[i]?, { d with gen })

def visibility (n : Nat) : Visibility :=
  if n < 8 then .public else if n < 9 then .unlisted else .private

/-- The next thing a browser does: a kind drawn by the mix's weights. A read is no entry. -/
def Driver.browse (d : Driver) (w : Workload) : Option Entry × Bool × Driver :=
  let mix := w.mix
  let (roll, gen) := d.gen.next mix.total
  let d := { d with gen }
  let session (m : Nat) := d.sessions.get? m
  let cuts := [mix.watch, mix.feed, mix.channel, mix.like, mix.comment, mix.create, mix.delete]
  let kind := (cuts.foldl (fun (acc, n) c => (acc + c, if acc + c ≤ roll then n + 1 else n))
    (0, 0)).2
  -- A read draws what the journalled read drew (D107), so that the generator's choices are the
  -- same, and makes no entry.
  let viewer (d : Driver) : Driver :=
    let (_, gen) := d.gen.next 2
    let (_, gen) := gen.next w.members
    { d with gen }
  match kind with
  | 0 | 2 => (none, true, ((viewer d).video w).2)
  | 1 => (none, true, viewer d)
  | 3 =>
    let (m, d) := d.member w
    let (v, d) := d.video w
    let (on, gen) := d.gen.next 4
    ((session m).bind fun s => v.map fun v => .inr (.request (.like 0 (who m) s v (on != 0)) 0),
      false, { d with gen })
  | 4 =>
    let (m, d) := d.member w
    let (v, d) := d.video w
    ((session m).bind fun s => v.map fun v => .inr (.request (.comment 0 (who m) s v remark) 0),
      false, d)
  | 5 =>
    let (m, d) := d.member w
    let (vis, gen) := d.gen.next 10
    ((session m).map fun s => .inr (.request (.create 0 (who m) s title about (visibility vis) .mp4) 0),
      false, { d with gen })
  | 6 =>
    let (i, gen) := d.gen.next d.ready.size
    let d := { d with gen }
    let v := d.ready[i]?
    let d := match v with
      | some v => { d with ready := d.ready.filter (· != v) }
      | none => d
    (v.bind fun v => (session (numberOf v.owner)).map fun s =>
      .inr (.request (.delete 0 v.owner s v) 0), false, d)
  | _ =>
    let (m, d) := d.member w
    (some (.inr (.request (.signIn 0 (who m) s!"member {m}") 0)), false, d)

/-- The entries due now, the oldest first. -/
def Driver.due (d : Driver) : List Entry × Driver :=
  let (now, later) := d.later.partition (·.1 ≤ d.entry)
  ((now.reverse.map (·.2)), { d with later })

def Driver.tick (d : Driver) (w : Workload) (measured : Bool) : Driver :=
  let (due, d) := d.due
  let count (d : Driver) (read : Bool) : Driver :=
    if measured then { d with actions := d.actions + 1, reads := d.reads + read.toNat } else d
  match due with
  | x :: rest =>
    let d' := count (d.feed x measured) false
    { d' with later := (rest.map fun x => (d.entry, x)) ++ d'.later }
  | [] =>
    let (x, read, d) := d.browse w
    match x with
    | some x => count (d.feed x measured) false
    | none => if read then count d true else d

/-- Every member signs in, and `warmVideos` videos are made and their pipelines run out. -/
def warm (w : Workload) : Driver := Id.run do
  let (k, _) := Kernel.boot (system config)
  let mut d : Driver := { k, gen := ⟨w.seed⟩ }
  for m in [0:w.members] do
    d := d.feed (.inr (.request (.signIn 0 (who m) s!"member {m}") 0)) false
  for i in [0:w.warmVideos] do
    let m := (i * 7919) % w.members
    match d.sessions.get? m with
    | some s =>
      d := d.feed (.inr (.request (.create 0 (who m) s title about (visibility (i % 10)) .mp4) 0)) false
    | none => pure ()
  for _ in [0:40 * w.warmVideos] do
    if d.later.isEmpty then break
    d := d.tick w false
  return d

/-- `warm`, then `actions` actions of the browsers, each entry fed alone and measured. -/
def run (w : Workload) : Driver := Id.run do
  let mut d := warm w
  while d.actions < w.actions do
    d := d.tick w true
  return d

/-! ## Batches, as a shard takes them

A shard takes what has arrived at once, accepts it, and runs until it is quiet; the answers to
the calls of one batch come in a later one. -/

/-- Up to `n` entries, the oldest due first and then the browsers', each stamped: the inputs of
one batch. Reads are counted and make no entry. -/
def Driver.gather (d : Driver) (w : Workload) (n : Nat) : List Entry × Driver := Id.run do
  let mut d := d
  let mut taken : Array Entry := #[]
  for _ in [0:4 * n + 16] do
    if n ≤ taken.size || w.actions ≤ d.actions then break
    let (due, d') := d.due
    d := d'
    let x? ← match due with
      | x :: rest =>
        d := { d with later := (rest.map fun x => (d.entry, x)) ++ d.later }
        pure (some x)
      | [] =>
        let (x, read, d') := d.browse w
        d := d'
        if read then d := { d with actions := d.actions + 1, reads := d.reads + 1 }
        pure x
    if let some x := x? then
      let (d', x) := d.stamp x
      d := { d' with entry := d'.entry + 1, actions := d'.actions + 1 }
      taken := taken.push x
  return (taken.toList, d)

/-- The driver after a batch of `entries` left the kernel `k` with `outs`. -/
def Driver.settle (d : Driver) (k : K) (entries : List Entry) (outs : List fullSig.Out) : Driver :=
  let d := { d with k }.take outs
  entries.foldl (init := d) fun d x =>
    match x with
    | .inr (.request (.report _ r _) _) =>
      if isReady d.k r.round.video then { d with ready := d.ready.push r.round.video } else d
    | _ => d

/-- A wave of the kernel's, as `Kernel.waves` cuts it: its messages, its receivers, and the most
messages one receiver has in it. -/
structure KernelWave where
  messages : Nat
  actors : Nat
  most : Nat

/-- The kernel's waves for a batch: the messages queued when each begins, until it is quiet. -/
def kernelWaves (k : K) : (fuel : Nat) → List KernelWave
  | 0 => []
  | fuel + 1 =>
    if k.wait != .none then []
    else
      let n := max 1 k.queue.length
      let mail := Kernel.mail (k.queue.toList.take n)
      let wave : KernelWave :=
        { messages := n, actors := mail.size, most := mail.fold (fun m _ ms => max m ms.length) 0 }
      wave :: kernelWaves (k.runBatch n).kernel fuel

/-- The kernel's waves of every batch of `n` entries of the workload, the batches as `gather`
takes them. -/
def batchWaves (w : Workload) (n : Nat) : List (List KernelWave) := Id.run do
  let mut d := warm w
  let mut out := #[]
  for _ in [0:w.actions + 1] do
    if w.actions ≤ d.actions then break
    let (batch, d') := d.gather w n
    let (k, d') := d'.begin batch
    d := d'
    out := out.push (kernelWaves k 100000)
    match k.runBatch 1000000 with
    | { kernel, outputs, .. } => d := d.settle kernel batch outputs
  return out.toList

/-! ## The waves -/

structure Stats where
  batch : Nat
  batches : Nat := 0
  entries : Nat := 0
  waves : Nat := 0
  /-- Entries in waves of at least two, and of at least eight. -/
  wide2 : Nat := 0
  wide8 : Nat := 0
  deriving Repr

def Stats.add (s : Stats) (widths : List Nat) : Stats :=
  { s with batches := s.batches + 1, entries := s.entries + widths.foldl (· + ·) 0
           waves := s.waves + widths.length
           wide2 := s.wide2 + (widths.filter (2 ≤ ·)).foldl (· + ·) 0
           wide8 := s.wide8 + (widths.filter (8 ≤ ·)).foldl (· + ·) 0 }

/-- The waves of each batch of `n` entries, in order, each entry touching `touches`. -/
def measure (n : Nat) (entries : List (List Actor)) : Stats := Id.run do
  let mut s : Stats := { batch := n }
  let mut rest := entries
  while !rest.isEmpty do
    let batch := rest.take n
    rest := rest.drop n
    let waves := WavePlan.split id batch
    s := s.add (waves.map List.length)
  return s

def pct (a b : Nat) : String :=
  if b = 0 then "-" else
    let t := (a * 1000 + b / 2) / b
    s!"{t / 10}.{t % 10}%"

def ratio (a b : Nat) : String :=
  if b = 0 then "-" else
    let t := (a * 100 + b / 2) / b
    s!"{t / 100}.{if t % 100 < 10 then "0" else ""}{t % 100}"

def Stats.row (name : String) (s : Stats) : String :=
  s!"| {name} | {s.batch} | {ratio s.waves s.batches} | {ratio s.entries s.waves} | {pct s.wide2 s.entries} | {pct s.wide8 s.entries} |"

def Actor.name : Actor → String
  | .inl w => s!"the scheduler of {w.subject.val}"
  | .inr w => s!"the actor of {w.subject.val}"

/-- The share of entries touching the actor most entries touch, and what it is. -/
def hottest (entries : List (List Actor)) : String :=
  let counts := entries.foldl (init := (∅ : Std.HashMap Actor Nat)) fun m as =>
    as.eraseDups.foldl (fun m a => m.insert a (m.getD a 0 + 1)) m
  match counts.toList.foldl (fun best (a, n) => match best with
      | some (_, b) => if b < n then some (a, n) else best
      | none => some (a, n)) none with
  | some (a, n) => s!"{a.name}, in {pct n entries.length}"
  | none => "-"

end Videos.Waves
