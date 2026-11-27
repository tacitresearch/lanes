/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.System

/-!
# Model checks

The site and its scheduler beside two members' browsers, which follow a script, and beside the
model of an object store (`Lanes.ObjectStore`, D71), which answers each attempt the scheduler
makes at most once, late, never, refused or `unknown`, and whose writes that were not answered
may take effect at any moment or never. The browser's upload is a write the site grants and
never hears the answer to (the upload form, the model's `granted`): the model may let it land
before the site asks, after, or never. A check is the model's head, and a delete the model's
delete. An answer comes only to an attempt out (as `Schedule.callee` has it): one to an attempt
abandoned, which the scheduler would not take, is not given, but the write it answers may still
land. Every timer of the scheduler may fire at any moment, and the site's actor or the scheduler
may crash and start again anywhere.

What the browsers see is judged as they see it: no private video shown to anyone but its owner;
nothing shown to a request made after its delete was answered; nothing shown that the store did
not first say it holds. The state is judged too: each like counted once, every bound, and, in
runs with no crash, every deleted video's object deleted in the store or reported once its job
is over. A crash in the semantics loses the actor's mail (`SysState.down`), so a scheduling or an
end on its way is lost with it; on one shard an actor crashes only by stopping itself, which
neither does, and the death of the process returns to the journal, mail included (`TRUSTED.md`,
"Environment model"). Every `always` has `sometimes` beside it (rule 5.3).

Three seeded bugs, each found: a video made ready because the browser says so, a check the
store did not answer in time taken as found, and sessions that never end.
-/

namespace Videos.Check

open Lanes

instance : (Schedule.sig Key Unit StoreAnswer).Inspect := {}
instance : sig.Inspect := {}
instance : fullSig.Inspect := .join
instance (config : Config) : (alone config).Inspect := {}
instance (config : Config) : (Schedule.system (K := Key) (P := Unit) (A := StoreAnswer)
  config.scheduler).Inspect := {}
instance (config : Config) : (system config).Inspect := .join

/-- The model's state: what the store may hold, for videos' objects. -/
abbrev Store := Rpc.State (ObjectStore.State VideoId Unit)

/-- The browser's put of video `v`'s object, granted by the link the site handed out, as the
model's call: a call of its own, which the site never sees answered. -/
def uploadCall (v : VideoId) : Nat := 1000 + v

/-- The model's call of an attempt: above every upload's, and one for each key and attempt,
for the small bounds checked (attempts below 8, requests below 64). -/
def callOf (key : Key) (attempt : Nat) : Nat :=
  let code := match key with
    | .check v req => 3 * (v * 64 + req)
    | .expire v => 3 * v + 1
    | .delete v => 3 * v + 2
  2000 + code * 8 + attempt

/-- The key and attempt of a model's call, the inverse of `callOf`. -/
def attemptOf (call : Nat) : Option (Key × Nat) :=
  if call < 2000 then none
  else
    let n := call - 2000
    let code := n / 8
    let x := code / 3
    let key : Key := match code % 3 with
      | 0 => .check (x / 64) (x % 64)
      | 1 => .expire x
      | _ => .delete x
    some (key, n % 8)

def storeAnswer : StoreAnswer → ObjectStore.Answer Unit
  | .found _ => .present
  | .missing => .missing
  | .deleted => .deleted
  | .failed => .refused

def request : StoreOp → ObjectStore.Request VideoId Unit
  | .head v => .head v
  | .delete v => .delete v

def port : Rpc.Port fullSig (ObjectStore.Request VideoId Unit) (ObjectStore.Answer Unit) Empty where
  called
    | .inr (.reply _ _ (.created v _ _)) => some ⟨uploadCall v, 0, .granted v ()⟩
    | .inl (.call a) => some ⟨callOf a.key a.attempt, a.deadline_ms, request a.key.op⟩
    | _ => none
  replied
    | .inl (.reply key attempt .unknown) => some (callOf key attempt, .unknown)
    | .inl (.reply key attempt (.answer a)) => some (callOf key attempt, .answer (storeAnswer a))
    | _ => none

def store : Outside fullSig Store := Rpc.outside port ObjectStore.server

/-- A request, the time it arrives, and the requests whose answers it waits for. -/
abbrev Script := List (Command × Nat × List ReqId)

/-- Requests that all arrive at time 0. -/
def Script.of (l : List (Command × List ReqId)) : Script := l.map fun (c, deps) => (c, 0, deps)

/-- The browsers: what they have still to send, what they were answered, and what they saw go
wrong; and what the store did with the deletes. -/
structure Browsers where
  todo : Script
  answered : List ReqId := []
  /-- Videos whose delete was answered. -/
  deleted : List VideoId := []
  /-- For each request sent, the videos whose delete was answered before it was sent. -/
  sent : List (ReqId × List VideoId) := []
  /-- When each request sent arrived. -/
  times : List (ReqId × Nat) := []
  broken : List String := []
  watched : List (VideoId × Option Member) := []
  /-- Videos whose object the store said it deleted, to some attempt. -/
  gone : List VideoId := []
  /-- Videos whose object the site reported given up. -/
  orphans : List VideoId := []
  /-- The attempts out at the store, and those abandoned before they were handed over, as
  `Schedule.callee` keeps them: an attempt abandoned is cut off, and its answer, which the
  scheduler would not take, is not given. -/
  out : List (Key × Nat) := []
  early : List (Key × Nat) := []
  /-- The most attempts made by one check, one last check and one delete. -/
  checkTries : Nat := 0
  expireTries : Nat := 0
  deleteTries : Nat := 0
  deriving DecidableEq, Hashable, Repr

instance : BEq Browsers := instBEqOfDecidableEq

def Command.req : Command → ReqId
  | .signIn req .. | .signOut req .. | .create req .. | .uploaded req .. | .watch req ..
  | .like req .. | .comment req .. | .uncomment req .. | .delete req .. | .feed req ..
  | .channel req .. => req

def Browsers.ready (b : Browsers) (deps : List ReqId) : Bool := deps.all b.answered.contains

def Browsers.send (b : Browsers) (c : Command) (at_s : Nat) : Option Browsers :=
  match b.todo.find? fun (c', t, deps) => c' == c && t == at_s && b.ready deps with
  | some entry =>
    some { b with todo := b.todo.erase entry, sent := (Command.req c, b.deleted) :: b.sent
                  times := (Command.req c, at_s) :: b.times }
  | none => none

/-- What each claim says of a reply as a browser sees it, with the store as it is then. A
session is named by the request that signed in, so it began when that request arrived. -/
def judge (life : Auth.Lifetime) (b : Browsers) (held : Store) (req : ReqId) (viewer : Viewer)
    (r : Reply) : Browsers :=
  let cards := r.cards
  let liveOk := match viewer, b.times.lookup req with
    | some (_, sid), some t => match b.times.lookup sid with
      | some began => !life.absolute_s.any (began + · ≤ t)
      | none => true
    | _, _ => true
  let before := ((b.sent.lookup req).getD [])
  let privateOk := cards.all fun c => c.visibility != .private || viewer.map (·.1) == some c.owner
  let goneOk := cards.all fun c => !before.contains c.id
  let confirmedOk := cards.all fun c => held.server.held.contains c.id
  let fail := [("a private video is shown to someone else", privateOk),
    ("a deleted video is shown", goneOk),
    ("a video is shown that the store did not say it holds", confirmedOk),
    ("a session past its lifetime is let in", liveOk)].filterMap
      fun (name, ok) => if ok then none else some name
  let b := { b with answered := req :: b.answered, broken := b.broken ++ fail }
  match r with
  | .deleted v => { b with deleted := v :: b.deleted }
  | .watch view _ => { b with watched := (view.card.id, viewer.map (·.1)) :: b.watched }
  | _ => b

/-- The store's answer to an attempt out: what it tells of a delete. -/
def Browsers.answered' (b : Browsers) : SchedIn → Option Browsers
  | .reply key attempt r =>
    if b.out.contains (key, attempt) then
      let b := { b with out := b.out.erase (key, attempt) }
      match key, r with
      | .delete v, .answer .deleted => some (if b.gone.contains v then b else { b with gone := v :: b.gone })
      | _, _ => some b
    else none
  | _ => none

/-- An attempt handed over: out at the store, unless its abandon came first. -/
def Browsers.call (b : Browsers) (a : Schedule.Attempt Key Unit) : Browsers :=
  let b := if b.early.contains (a.key, a.attempt) then { b with early := b.early.erase (a.key, a.attempt) }
    else { b with out := (a.key, a.attempt) :: b.out }
  match a.key with
  | .check .. => { b with checkTries := max b.checkTries a.attempt }
  | .expire _ => { b with expireTries := max b.expireTries a.attempt }
  | .delete _ => { b with deleteTries := max b.deleteTries a.attempt }

def Browsers.observe (b : Browsers) (life : Auth.Lifetime) (held : Store) : SchedOut ⊕ Out → Browsers
  | .inr (.reply req viewer r) => judge life b held req viewer r
  | .inr (.orphan v) => if b.orphans.contains v then b else { b with orphans := v :: b.orphans }
  | .inl (.call a) => b.call a
  | .inl (.abandon key attempt) =>
    if b.out.contains (key, attempt) then { b with out := b.out.erase (key, attempt) }
    else { b with early := (key, attempt) :: b.early }
  | _ => b

def world (life : Auth.Lifetime) (script : Script) : Outside fullSig (Browsers × Store) where
  init := ({ todo := script }, store.init)
  allow d
    | .inr (.request c at_s) => (d.1.send c at_s).map (·, d.2)
    | .inl x => do pure (← d.1.answered' x, ← store.allow d.2 (.inl x))
    | x => (store.allow d.2 x).map (d.1, ·)
  observe d out := (d.1.observe life d.2 out, store.observe d.2 out)

def answers : List (Rpc.Reply StoreAnswer) :=
  [.unknown, .answer (.found 1), .answer .missing, .answer .deleted, .answer .failed]

def samples (d : Browsers × Store) : List (SchedIn ⊕ Input) :=
  (d.1.todo.filterMap fun (c, at_s, deps) =>
      if d.1.ready deps then some (Sum.inr (Input.request c at_s)) else none)
    ++ (d.2.pending.filterMap attemptOf).flatMap fun (key, attempt) =>
      answers.map fun r => Sum.inl (Schedule.Input.reply key attempt r)

abbrev W (config : Config) := World (system config) (Browsers × Store)

def site {config : Config} (w : W config) : Site := w.state.state (.inr ())

def jobs {config : Config} (w : W config) : List (Schedule.Job Key Unit) :=
  (w.state.state (.inl ()) : Schedule.State Key Unit).jobs

/-- The browsers' requests reach the site in the order sent; the actors in `crashing` may crash
anywhere. -/
def env (crashing : fullSig.Id → Bool := fun _ => true) : EnvModel fullSig where
  mayCrash := crashing
  restarts _ := true

/-- Only the site crashes, for the scenarios too large to crash either. -/
def siteCrashes : fullSig.Id → Bool
  | .inr () => true
  | .inl () => false

/-- One attempt for each job: the scenarios with many requests. -/
def config : Config :=
  { maxMembers := 2, maxSessions := 1, maxVideos := 2, maxOwned := 1, maxPending := 1,
    maxComments := 2, maxCommentsEach := 1, maxJobs := 3, pageSize := 1, pending_s := none
    checkRetry := { maxAttempts := 1, deadline_ms := 1, base_ms := 1, cap_ms := 1 }
    deleteRetry := { maxAttempts := 1, deadline_ms := 1, base_ms := 1, cap_ms := 1 } }

/-- Two attempts for each check: a scenario of a retry. -/
def checkTwice : Config :=
  { config with checkRetry := { maxAttempts := 2, deadline_ms := 1, base_ms := 1, cap_ms := 1 } }

/-- Two attempts for each delete: a scenario of a retry. -/
def deleteTwice : Config :=
  { config with deleteRetry := { maxAttempts := 2, deadline_ms := 1, base_ms := 1, cap_ms := 1 } }

def bounded (config : Config) {c : Config} (w : W c) : Bool :=
  let s := site w
  s.channels.length ≤ config.maxMembers && s.videos.length ≤ config.maxVideos
    && (jobs w).length ≤ config.maxJobs
    && s.videos.all (·.comments.length ≤ config.maxComments)
    && s.channels.all (fun (m, _) => (s.videos.filter (·.owner == m)).length ≤ config.maxOwned)
    && s.videos.all (fun v => v.comments.all fun c =>
      (v.comments.filter (·.author == c.author)).length ≤ config.maxCommentsEach)
    && s.channels.all fun (_, ch) => ch.sessions.ids.length ≤ config.maxSessions

/-- The delete of `v`'s object is not over: its job is held, or on its way to the scheduler, or
its end on its way to the site, or the report of it not yet handed over. -/
def deleting {config : Config} (w : W config) (v : VideoId) : Bool :=
  (jobs w).any (·.key == .delete v)
    || w.state.net.any (fun e => match e with
      | ⟨_, .inl (), .schedule _ spec⟩ => spec.key == .delete v
      | ⟨_, .inr (), .job key _⟩ => key == .delete v
      | _ => false)
    || w.state.outbox.contains (Sum.inr (Out.orphan v))

def t : Title := ⟨"t", by decide⟩
def none_ : About := ⟨"", by decide⟩
def hi : Remark := ⟨"hi", by decide⟩

/-- Member 0 signs in with request 1 and session 1, member 1 with request 2 and session 2. -/
def signIns : List (Command × List ReqId) :=
  [(.signIn 1 "id" "a" "a", []), (.signIn 2 "id" "b" "b", [1])]

/-- `0` makes a public video and says it is uploaded; `1` watches it, likes it twice, and `0`
likes it; `0` deletes it, and `1` asks for it again. -/
def life : Script := .of <|
  signIns ++
  [ (.create 3 0 1 t none_ .public .mp4, [2]), (.uploaded 4 0 1 0, [3]),
    (.watch 5 (some (1, 2)) 0, [4]), (.like 6 1 2 0 true, [5]), (.like 7 1 2 0 true, [6]),
    (.like 8 0 1 0 true, [7]), (.delete 9 0 1 0, [8]), (.watch 10 (some (1, 2)) 0, [9]) ]

/-- `0` makes a video and says twice that it is uploaded, the second while the first check may
be out; then asks for it. -/
def twice : Script := .of <|
  signIns.take 1 ++
  [ (.create 3 0 1 t none_ .public .mp4, [1]), (.uploaded 4 0 1 0, [3]),
    (.uploaded 5 0 1 0, [3]), (.watch 6 (some (0, 1)) 0, [4, 5]) ]

/-- `0` makes a private video; `1`, a stranger and `0` ask for it, for `0`'s channel and for
the feed; `1` tries to like it and comment on it. -/
def secret : Script := .of <|
  signIns ++
  [ (.create 3 0 1 t none_ .private .webm, [2]), (.uploaded 4 0 1 0, [3]),
    (.watch 5 (some (1, 2)) 0, [4]), (.watch 6 none 0, [5]), (.watch 7 (some (0, 1)) 0, [6]),
    (.channel 8 (some (1, 2)) 0, [7]), (.channel 9 (some (0, 1)) 0, [8]),
    (.feed 10 (some (1, 2)) none, [9]), (.like 11 1 2 0 true, [10]), (.comment 12 1 2 0 hi, [11]) ]

/-- `0` makes a video and deletes it at once, while a check may be out; then asks for it. -/
def gone : Script := .of <|
  signIns.take 1 ++
  [ (.create 3 0 1 t none_ .unlisted .mp4, [1]), (.uploaded 4 0 1 0, [3]),
    (.delete 5 0 1 0, [3]), (.channel 6 (some (0, 1)) 0, [5]) ]

/-- `0` makes a video and deletes it, and asks for its channel. -/
def purge : Script := .of <|
  signIns.take 1 ++
  [ (.create 3 0 1 t none_ .unlisted .mp4, [1]), (.delete 4 0 1 0, [3]),
    (.channel 5 (some (0, 1)) 0, [4]) ]

/-- `0` makes a video and never says it is uploaded; its last check comes, and `0` asks for it
and for its channel. -/
def lapsed : Script := .of <|
  signIns.take 1 ++
  [ (.create 3 0 1 t none_ .public .mp4, [1]), (.channel 4 (some (0, 1)) 0, [3]),
    (.watch 5 (some (0, 1)) 0, [4]) ]

/-- `0` signs in at 0 and makes a private video; it watches it at 50, inside its session's
lifetime of 100, and at 150, past it, when it also tries to like it and is then let in by the
session of a new sign-in. -/
def expiry : Script :=
  [ (.signIn 1 "id" "a" "a", 0, []), (.create 2 0 1 t none_ .private .mp4, 10, [1]),
    (.uploaded 3 0 1 0, 20, [2]), (.watch 4 (some (0, 1)) 0, 50, [3]),
    (.watch 5 (some (0, 1)) 0, 150, [4]), (.like 6 0 1 0 true, 150, [5]),
    (.signIn 7 "id" "a" "a", 150, [6]), (.watch 8 (some (0, 7)) 0, 160, [7]) ]

def short : Config := { config with lifetime := { absolute_s := some 100 } }

def lapsing : Config := { checkTwice with pending_s := some 1 }

def claims {config : Config} : List (Check.Property (W config)) :=
  [ .always "a private video is shown to its owner only" fun w =>
      !w.driver.1.broken.contains "a private video is shown to someone else",
    .always "a video is not shown to a request made after its delete was answered" fun w =>
      !w.driver.1.broken.contains "a deleted video is shown",
    .always "a video is shown only once the store said it holds its object" fun w =>
      !w.driver.1.broken.contains "a video is shown that the store did not say it holds",
    .always "a session past its lifetime lets no request in" fun w =>
      !w.driver.1.broken.contains "a session past its lifetime is let in",
    .always "each like is a member's, counted once" fun w =>
      (site w).videos.all fun v => v.likes.eraseDups.length == v.likes.length,
    .always "every bound holds" fun w => bounded config w,
    .always "with no crash, a deleted video's object is deleted in the store, or reported, once \
        its job is over"
      fun w => w.crashes != 0 || w.driver.1.deleted.all fun v =>
        deleting w v || w.driver.1.gone.contains v || w.driver.1.orphans.contains v ]

def shown {config : Config} : Check.Property (W config) :=
  .sometimes "a video is shown" fun w => !w.driver.1.watched.isEmpty

def goneWhileHeld {config : Config} : Check.Property (W config) :=
  .sometimes "a video is deleted while its object may still be in the store" fun w =>
    w.driver.1.deleted.any (deleting w)

def deletedAfterRetry {config : Config} : Check.Property (W config) :=
  .sometimes "an object is deleted in the store after its first delete failed" fun w =>
    w.driver.1.gone.contains 0 && w.driver.1.deleteTries == 2

def reported {config : Config} : Check.Property (W config) :=
  .sometimes "an object given up is reported" fun w => w.driver.1.orphans.contains 0

def checkedAgain {config : Config} : Check.Property (W config) :=
  .sometimes "a last check is tried again" fun w => w.driver.1.expireTries == 2

def twoLikes {config : Config} : Check.Property (W config) :=
  .sometimes "a video has two likes" fun w => (site w).videos.any (·.likes.length == 2)

def watchedTwice {config : Config} : Check.Property (W config) :=
  .sometimes "a private video is watched by its owner in two sessions" fun w =>
    (w.driver.1.watched.filter (· == (0, some 0))).length == 2

def ownerWatches {config : Config} : Check.Property (W config) :=
  .sometimes "a private video is watched by its owner" fun w =>
    w.driver.1.watched.contains (0, some 0)

def othersAsk {config : Config} : Check.Property (W config) :=
  .sometimes "a private video is asked for by another member and by a stranger" fun w =>
    w.driver.1.answered.contains 5 && w.driver.1.answered.contains 6

def lapsedReady {config : Config} : Check.Property (W config) :=
  .sometimes "an upload never confirmed is made ready by its last check, and shown" fun w =>
    w.driver.1.watched.contains (0, some 0)

def lapsedOut {config : Config} : Check.Property (W config) :=
  .sometimes "an upload never confirmed is taken out by its last check" fun w =>
    (site w).next == 1 && (site w).videos.isEmpty

/-- The site of `config` checked against `script`; its sessions are judged by `life`, the
site's own unless a seeded bug says otherwise. -/
def check (config : Config) (script : Script) (witnesses : List (Check.Property (W config)))
    (maxCrashes : Nat := 1) (life : Auth.Lifetime := config.lifetime)
    (crashing : fullSig.Id → Bool := fun _ => true) :=
  Check.system (system config)
    { env := env crashing, driver := (world life script).driver samples, maxCrashes }
    (claims ++ witnesses) { maxStates := 3000000 }

def trusting : Config := { config with trustBrowser := true }
def hasty : Config := { config with readyOnTimeout := true }

/-- The first violation's name and length, if the report has one. -/
def found {S L : Type} (r : Check.Report S L) : Option (String × Nat) :=
  match r.failure with
  | some (.violated p t) => some (p, t.steps.length)
  | _ => none

/-- One member cannot fill the site: their videos, and their comments on one video, are bounded
far below the site's; a video's owner takes out anyone's comment on it. -/
def capTests : List (String × Bool) :=
  let cfg : Config := { maxOwned := 2, maxCommentsEach := 2 }
  let video (id owner : Nat) : Video :=
    { id, owner, title := t, about := none_, visibility := .public, media := .mp4, status := .ready 1 }
  let s : Site := { videos := [video 1 0, video 0 0], next := 2 }
  let says (r : Site × List Out) (reply : Reply) := r.2 == [.reply 9 none reply]
  let c (id author : Nat) : Comment := { id, author, body := hi }
  let v := { video 0 0 with comments := [c 0 1, c 1 1] }
  [ ("caps: a member with maxOwned videos is refused another, and another member is not",
      says (s.create cfg 9 none 0 t none_ .public .mp4 0) .tooMany
        && (s.create cfg 9 none 1 t none_ .public .mp4 0).1.videos.length == 3),
    ("caps: a member with maxCommentsEach comments on a video is refused another, another member is not",
      says (s.comment cfg 9 none 1 v hi) (.tooManyComments 0)
        && says (s.comment cfg 9 none 2 v hi) (.commented 0)),
    ("caps: a video's owner takes out another member's comment on it, a third member cannot",
      says (s.uncomment 9 none 0 v 0) (.uncommented 0) && says (s.uncomment 9 none 2 v 0) .notFound
        && says (s.uncomment 9 none 1 v 1) (.uncommented 0)),
    ("calls: the model's call of an attempt names its key and attempt back",
      [Key.check 1 9, .expire 1, .delete 0, .check 0 63].all fun k =>
        (List.range 8).all fun n => attemptOf (callOf k n) == some (k, n)) ]

def run : IO (List (String × Bool)) := do
  let life' := check config life [shown, goneWhileHeld, twoLikes]
  IO.println s!"life: {life'.renderSystem}"
  let secret' := check config secret [ownerWatches, othersAsk]
  IO.println s!"secret: {secret'.renderSystem}"
  let gone' := check config gone [goneWhileHeld]
  IO.println s!"gone: {gone'.renderSystem}"
  let twice' := check config twice [shown]
  IO.println s!"twice: {twice'.renderSystem}"
  let purge' := check deleteTwice purge [goneWhileHeld, deletedAfterRetry, reported]
  IO.println s!"purge: {purge'.renderSystem}"
  let lapsed' := check lapsing lapsed [lapsedReady, lapsedOut, checkedAgain]
  IO.println s!"lapsed: {lapsed'.renderSystem}"
  let expiry' := check short expiry [watchedTwice]
  IO.println s!"expiry: {expiry'.renderSystem}"
  let trusted := found (check trusting life [] 0)
  if let some (p, n) := trusted then
    IO.println s!"seeded, the browser trusted: \"{p}\" after {n} steps"
  let rushed := found (check hasty life [] 0)
  if let some (p, n) := rushed then
    IO.println s!"seeded, a check that timed out taken as found: \"{p}\" after {n} steps"
  let endless := found (check { short with lifetime := {} } expiry [] 0 short.lifetime)
  if let some (p, n) := endless then
    IO.println s!"seeded, sessions that never end: \"{p}\" after {n} steps"
  let unconfirmed := "a video is shown only once the store said it holds its object"
  return [
    ("check: a video's life, with the store's faults and a crash anywhere",
      life'.ok && life'.complete && life'.witnesses.length == 3),
    ("check: a private video, with the store's faults and a crash anywhere",
      secret'.ok && secret'.complete && secret'.witnesses.length == 2),
    ("check: a video deleted while its check may be out, and a crash anywhere",
      gone'.ok && gone'.complete && gone'.witnesses.length == 1),
    ("check: a second check while the first may be out, and a crash anywhere",
      twice'.ok && twice'.complete && twice'.witnesses.length == 1),
    ("check: a delete tried twice, deleted or reported, and a crash anywhere",
      purge'.ok && purge'.complete && purge'.witnesses.length == 3),
    ("check: an upload never confirmed, checked a last time, twice, and a crash anywhere",
      lapsed'.ok && lapsed'.complete && lapsed'.witnesses.length == 3),
    ("check: a session past its lifetime lets nothing in, and a new sign-in does",
      expiry'.ok && expiry'.complete && expiry'.witnesses.length == 1),
    ("check, seeded: trusting the browser shows a video the store never confirmed",
      trusted.any (·.1 == unconfirmed)),
    ("check, seeded: a check that timed out taken as found shows such a video",
      rushed.any (·.1 == unconfirmed)),
    ("check, seeded: sessions that never end let a request in past the lifetime",
      endless.any (·.1 == "a session past its lifetime lets no request in")) ]

end Videos.Check
