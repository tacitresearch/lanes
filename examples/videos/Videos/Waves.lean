/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.System

/-!
# Does the site's work spread over actors?

Waves (`Lanes.WavePlan`) apply a batch of journal entries in parallel where the entries touch no
actor in common. This measures, for a workload of many members, how wide the waves of the site's
journal would be: as the site runs (one actor beside the scheduler), and with the site split
into an actor per member.

The workload runs through the real system on a kernel: members sign in, make videos that are
checked, transcoded and reported, watch and like the popular ones, comment, read the feed and
the channels, and delete. The store's and the worker's answers come back as entries a few entries
after their call. The choices are a fixed generator's, so every run gives the same numbers.

An entry touches every actor that one of its messages reaches before the kernel is quiet again.
The split is projected from the run, not built (`Split.touches`): a member's own requests go to
their actor; a request about another member's video goes to the viewer's actor, which checks the
session, and then to the owner's; a job's word goes to the owner of the video its key names; the
feed and sign-in go to a `catalog` that holds the listed cards and who is which member, told of
every change to a listed card. The flags of `Split` take the shared actors away one at a time.
-/

namespace Videos.Waves

open Lanes

/-- An actor an entry may touch: the site and the scheduler as they run, or the split's. -/
inductive Actor where
  | site
  | scheduler (owner : Option Member)
  | member (m : Member)
  | catalog
  deriving DecidableEq, Hashable, Repr

def Key.video : Key → VideoId
  | .check v _ | .expire v | .delete v => v
  | .transcode r => r.video

def schedKey : Schedule.Msg Key Unit Answer → Key
  | .schedule _ spec => spec.key
  | .cancel key | .reply key .. | .due key | .expire key => key

/-- A unit of work of the system: a message, or a timer, for the site or the scheduler, and the
site's state before it and after. -/
inductive Work where
  | site (i : Input) (before after : Site)
  | scheduler (m : Schedule.Msg Key Unit Answer)

/-- How the split being measured is laid out. -/
structure Split where
  /-- A scheduler per member, which holds the jobs of the member's videos. -/
  perMember : Bool := false
  /-- Whether watches, feeds and channel pages are entries. -/
  reads : Bool := true
  /-- Whether the catalog holds the feed's cards, told of every change to one. Without it, and
  without `reads`, the feed is read from the members' states, and the catalog only signs in. -/
  index : Bool := true
  /-- Whether a sign-in goes through the catalog, which says who is which member. Without it,
  a member's actor is named by the identity that signs in. -/
  directory : Bool := true
  /-- Whether a like or a comment is held by the member who makes it, and not by the video's
  owner: a video's count is then read from the members' states. -/
  writerHolds : Bool := false
  deriving Repr

/-- The listed card of video `v`, as the feed shows it. -/
def listedCard (s : Site) (v : VideoId) : Option Card :=
  (s.find? v).bind fun w => if w.listed then some (s.card w) else none

abbrev Owners := Std.HashMap VideoId Member

def ownerOf (owners : Owners) (v : VideoId) : Actor :=
  match owners.get? v with
  | some m => .member m
  | none => .catalog

def viewerOf : Viewer → List Actor
  | some (m, _) => [.member m]
  | none => []

/-- The actors of the split that the site's handling of `i` touches. -/
def splitSite (split : Split) (owners : Owners) (i : Input) (before after : Site) :
    List Actor :=
  let about (v : VideoId) (rest : List Actor) : List Actor :=
    let base := ownerOf owners v :: rest
    if split.index && listedCard before v != listedCard after v then .catalog :: base else base
  let directory := if split.directory then [Actor.catalog] else []
  match i with
  | .request c _ =>
    match c with
    | .signIn _ issuer subject _ =>
      match after.channels.find? fun (_, ch) => ch.issuer == issuer && ch.subject == subject with
      | some (m, _) => .member m :: directory
      | none => directory
    | .signOut _ m _ | .create _ m .. => [.member m]
    | .uploaded _ m _ v | .delete _ m _ v | .retry _ m _ v => about v [.member m]
    | .like _ m _ v _ | .comment _ m _ v _ | .uncomment _ m _ v _ =>
      if split.writerHolds then [.member m] else about v [.member m]
    | .watch _ viewer v => about v (viewerOf viewer)
    | .feed _ viewer _ => .catalog :: viewerOf viewer
    | .channel _ viewer whose => .member whose :: viewerOf viewer
    | .report _ r _ => about r.round.video []
  | .job key _ | .noticed key => about (Key.video key) []

def Split.touches (split : Split) (owners : Owners) : Work → List Actor
  | .site i before after => splitSite split owners i before after
  | .scheduler m =>
    [.scheduler (if split.perMember then (owners.get? (Key.video (schedKey m))) else none)]

/-- The actors the system as it runs touches. -/
def asRuns : Work → List Actor
  | .site .. => [.site]
  | .scheduler _ => [.scheduler none]

def isRead : Input → Bool
  | .request (.watch ..) _ | .request (.feed ..) _ | .request (.channel ..) _ => true
  | _ => false

/-- Whether input `x` is an entry of the split's journal. -/
def Split.keeps (split : Split) : fullSig.In → Bool
  | .inr i => split.reads || !isRead i
  | .inl _ => true

/-- A layout measured: the system as it runs, or a split. -/
inductive Layout where
  | asRuns
  | split (s : Split)

def Layout.keeps : Layout → fullSig.In → Bool
  | .asRuns, _ => true
  | .split s, x => s.keeps x

def Layout.touches (owners : Owners) : Layout → Work → List Actor
  | .asRuns, w => Waves.asRuns w
  | .split s, w => s.touches owners w

/-! ## The run -/

def workerKey : Hmac.Key := .of "the worker's key".toUTF8

def config : Config := { workerKey }

abbrev K := Kernel (system config)

abbrev Entry := fullSig.In

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

/-- How often a browser makes each kind of request, in parts of `total`: views most, then the
feed, likes, channel pages, comments, sign-ins, uploads and deletes. An upload brings four
entries more (the browser's "uploaded", the store's answer to the check, the worker's to the job,
its report), and a delete one (the store's answer). -/
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
  /-- Videos made, checked, transcoded and reported before the measured entries. -/
  warmVideos : Nat := 400
  entries : Nat := 20000
  /-- Whether views follow popularity, or are uniform over the ready videos. -/
  popular : Bool := true
  seed : UInt64 := 42
  deriving Repr

/-- What the driver knows, as a browser and the store would: each member's session, the videos
there are and their owners, and the entries due later (the store's and the worker's answers,
and the browsers' "uploaded"). -/
structure Driver where
  k : K
  gen : Gen
  req : Nat := 0
  sessions : Std.HashMap Member Sid := {}
  owners : Owners := {}
  ready : Array VideoId := #[]
  later : List (Nat × Entry) := []
  /-- Each entry's units of work, the measured ones only, in order. -/
  log : Array (Entry × List Work) := #[]
  entry : Nat := 0

def at_s (d : Driver) : Nat := 1000000 + d.entry / 20

def siteState (k : K) : Site := (k.cell (.inr ())).state

def unitOf (before after : Site) : Envelope fullSig → Option Work
  | ⟨_, .inr (), msg⟩ => some (.site msg before after)
  | ⟨_, .inl (), msg⟩ => some (.scheduler msg)

def timeoutOf (i : fullSig.Id) (msg : fullSig.Msg i) : Option Work :=
  match i, msg with
  | .inl (), msg => some (.scheduler msg)
  | .inr (), _ => none

/-- Run the kernel until there is no work to do now, one unit at a time. -/
def drain (k : K) : (fuel : Nat) → K × List Work × List fullSig.Out
  | 0 => (k, [], [])
  | fuel + 1 =>
    if k.wait != .none then (k, [], [])
    else
      let before := siteState k
      let r := k.step
      let after := siteState r.kernel
      let units := r.events.filterMap fun
        | .deliver e => unitOf before after e
        | .timeout i msg => timeoutOf i msg
        | _ => none
      let (k, more, outs) := drain r.kernel fuel
      (k, units ++ more, r.outputs ++ outs)

def answerFor : Op → Answer
  | .head _ => .found 1000
  | .delete _ => .deleted
  | .transcode _ => .accepted

def report (r : Round) : Command :=
  let rep : Report := .done r
  .report 0 rep (Transcode.signature workerKey rep.round.id rep.status)

/-- What the outputs make the driver do: remember sessions and videos, and answer calls. -/
def Driver.take (d : Driver) (outs : List fullSig.Out) : Driver :=
  outs.foldl (init := d) fun d out =>
    match out with
    | .inr (.reply _ _ (.signedIn m sid _)) => { d with sessions := d.sessions.insert m sid }
    | .inr (.reply _ (some (m, sid)) (.created v _ _)) =>
      { d with owners := d.owners.insert v m
               later := (d.entry + 5, .inr (.request (.uploaded 0 m sid v) 0)) :: d.later }
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
      | .signIn _ i s n => .signIn req i s n
      | .signOut _ m s => .signOut req m s
      | .create _ m s t a v md => .create req m s t a v md
      | .uploaded _ m s v => .uploaded req m s v
      | .watch _ w v => .watch req w v
      | .like _ m s v on => .like req m s v on
      | .comment _ m s v b => .comment req m s v b
      | .uncomment _ m s v c => .uncomment req m s v c
      | .delete _ m s v => .delete req m s v
      | .feed _ w b => .feed req w b
      | .channel _ w m => .channel req w m
      | .retry _ m s v => .retry req m s v
      | .report _ r sig => .report req r sig
    ({ d with req := req + 1 }, .inr (.request c (at_s d)))
  | x => (d, x)

def Driver.feed (d : Driver) (x : Entry) (measured : Bool) : Driver :=
  let (d, x) := d.stamp x
  let k := (d.k.advance (at_s d * 1000)).accept x |>.kernel
  let (k, units, outs) := drain k 100000
  let d := { d with k, entry := d.entry + 1, log := if measured then d.log.push (x, units) else d.log }
  let d := d.take outs
  match x with
  | .inr (.request (.report _ r _) _) =>
    if ((siteState d.k).find? r.round.video).any (·.status.isReady) then
      { d with ready := d.ready.push r.round.video } else d
  | _ => d

def title : Title := ⟨"a video", by decide⟩
def about : About := ⟨"", by decide⟩
def remark : Remark := ⟨"nice", by decide⟩

def Driver.member (d : Driver) (w : Workload) : Nat × Driver :=
  let (m, gen) := d.gen.next w.members
  (m, { d with gen })

def Driver.viewer (d : Driver) (w : Workload) : Viewer × Driver :=
  let (anon, gen) := d.gen.next 2
  let (m, gen) := gen.next w.members
  ((if anon = 0 then none else (d.sessions.get? m).map (m, ·)), { d with gen })

def Driver.video (d : Driver) (w : Workload) : Option VideoId × Driver :=
  if d.ready.isEmpty then (none, d)
  else
    let (i, gen) := if w.popular then d.gen.popular d.ready.size else d.gen.next d.ready.size
    (d.ready[i]?, { d with gen })

def visibility (n : Nat) : Visibility :=
  if n < 8 then .public else if n < 9 then .unlisted else .private

/-- The next entry a browser makes: a kind drawn by the mix's weights. -/
def Driver.browse (d : Driver) (w : Workload) : Option Entry × Driver :=
  let mix := w.mix
  let (roll, gen) := d.gen.next mix.total
  let d := { d with gen }
  let session (m : Member) := d.sessions.get? m
  let cuts := [mix.watch, mix.feed, mix.channel, mix.like, mix.comment, mix.create, mix.delete]
  let kind := (cuts.foldl (fun (acc, n) c => (acc + c, if acc + c ≤ roll then n + 1 else n))
    (0, 0)).2
  match kind with
  | 0 =>
    let (viewer, d) := d.viewer w
    let (v, d) := d.video w
    (v.map fun v => .inr (.request (.watch 0 viewer v) 0), d)
  | 1 =>
    let (viewer, d) := d.viewer w
    (some (.inr (.request (.feed 0 viewer none) 0)), d)
  | 2 =>
    let (viewer, d) := d.viewer w
    let (v, d) := d.video w
    let whose := (v.bind d.owners.get?).getD 0
    (some (.inr (.request (.channel 0 viewer whose) 0)), d)
  | 3 =>
    let (m, d) := d.member w
    let (v, d) := d.video w
    let (on, gen) := d.gen.next 4
    ((session m).bind fun s => v.map fun v => .inr (.request (.like 0 m s v (on != 0)) 0),
      { d with gen })
  | 4 =>
    let (m, d) := d.member w
    let (v, d) := d.video w
    ((session m).bind fun s => v.map fun v => .inr (.request (.comment 0 m s v remark) 0), d)
  | 5 =>
    let (m, d) := d.member w
    let (vis, gen) := d.gen.next 10
    ((session m).map fun s => .inr (.request (.create 0 m s title about (visibility vis) .mp4) 0),
      { d with gen })
  | 6 =>
    let (i, gen) := d.gen.next d.ready.size
    let d := { d with gen }
    let v := d.ready[i]?
    let owner := v.bind d.owners.get?
    let d := match v with
      | some v => { d with ready := d.ready.filter (· != v) }
      | none => d
    (owner.bind fun m => (session m).bind fun s => v.map fun v =>
      .inr (.request (.delete 0 m s v) 0), d)
  | _ =>
    let (m, d) := d.member w
    (some (.inr (.request (.signIn 0 "google" s!"user{m}" s!"member {m}") 0)), d)

/-- The entries due now, the oldest first. -/
def Driver.due (d : Driver) : List Entry × Driver :=
  let (now, later) := d.later.partition (·.1 ≤ d.entry)
  ((now.reverse.map (·.2)), { d with later })

def Driver.tick (d : Driver) (w : Workload) (measured : Bool) : Driver :=
  let (due, d) := d.due
  match due with
  | x :: rest =>
    let d' := d.feed x measured
    { d' with later := (rest.map fun x => (d.entry, x)) ++ d'.later }
  | [] =>
    match d.browse w with
    | (some x, d) => d.feed x measured
    | (none, d) => d

/-- Every member signs in, `warmVideos` videos are made and their pipelines run out, then
`entries` entries are logged. -/
def run (w : Workload) : Driver := Id.run do
  let (k, _) := Kernel.boot (system config)
  let mut d : Driver := { k, gen := ⟨w.seed⟩ }
  for m in [0:w.members] do
    d := d.feed (.inr (.request (.signIn 0 "google" s!"user{m}" s!"member {m}") 0)) false
  for i in [0:w.warmVideos] do
    let m := (i * 7919) % w.members
    match d.sessions.get? m with
    | some s =>
      d := d.feed (.inr (.request (.create 0 m s title about (visibility (i % 10)) .mp4) 0)) false
    | none => pure ()
  for _ in [0:40 * w.warmVideos] do
    if d.later.isEmpty then break
    d := d.tick w false
  let start := d.log.size
  while d.log.size < start + w.entries do
    d := d.tick w true
  return d

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

/-- The share of entries touching the actor most entries touch, and what it is. -/
def hottest (entries : List (List Actor)) : String :=
  let counts := entries.foldl (init := (∅ : Std.HashMap Actor Nat)) fun m as =>
    as.eraseDups.foldl (fun m a => m.insert a (m.getD a 0 + 1)) m
  match counts.toList.foldl (fun best (a, n) => match best with
      | some (_, b) => if b < n then some (a, n) else best
      | none => some (a, n)) none with
  | some (a, n) => s!"{repr a} in {pct n entries.length}"
  | none => "-"

end Videos.Waves
