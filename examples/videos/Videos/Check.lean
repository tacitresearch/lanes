/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.System

/-!
# Model checks

The site and its scheduler beside two members' browsers, which follow a script, and beside the
model of a transcode worker and the object store it writes to (`Lanes.Transcode`, over
`Lanes.ObjectStore`), which answers each attempt the scheduler makes at most once, late, never,
refused or `unknown`, and whose writes that were not answered may take effect at any moment or
never. The browser's upload is a write the site grants and never hears the answer to (the upload
form, the model's `granted`): the model may let it land before the site asks, after, or never. A
check is the model's head, a delete the model's delete of the upload, and a transcode's attempt
the job of its round, given to the worker. The worker, honest, writes the rendition and the
thumbnail at any moment after it is given a job, and reports the job done (once its source may
be held, its writes landed) or failed, late, again or never; anyone else may post a report with
a signature that is not the worker's. An answer comes only to an attempt out (as
`Schedule.callee` has it): one to an attempt abandoned, which the scheduler would not take, is
not given, but the write it answers may still land. Every timer of the scheduler may fire at any
moment, and the site's actor or the scheduler may crash and start again anywhere.

What the browsers see is judged as they see it: no private video shown to anyone but its owner;
nothing shown to a request made after its delete was answered; nothing shown that the store did
not first say it holds, that the worker did not first report done with its signature, or whose
rendition and thumbnail the store may not hold. The state is judged too: each like counted
once, every bound, and, in runs with no crash, every deleted video's object deleted in the store
or reported once its job is over. A crash in the semantics loses the actor's mail
(`SysState.down`), so a scheduling or an end on its way is lost with it; on one shard an actor
crashes only by stopping itself, which neither does, and the death of the process returns to
the journal, mail included (`TRUSTED.md`, "Environment model"). Every `always` has `sometimes`
beside it (rule 5.3).

The worker's faults multiply every interleaving, so each scenario explores those it is about
(`Worker`): the scenarios about the site and the store have a worker that reports each job done
once (`quiet`), or never answers (`silent`); the pipeline and the forgery explore its faults.

Of runs with no crash, every run that cannot go on, every message delivered, every timer fired
and the worker done reporting, leaves no video transcoding: a confirmed upload ends ready or
failed (`pipeline`, the checker's deadlocks). The site's part of it is proved from the worker's
report (`Videos.report_settles`); that the worker reports is its model's, checked here.

Four seeded bugs, each found: a video made ready because the browser says so, a check the
store did not answer in time taken as found, sessions that never end, and a report taken
whatever its signature.
-/

namespace Videos.Check

open Lanes

instance : (Schedule.sig Key Unit Answer).Inspect := {}
instance : sig.Inspect := {}
instance : fullSig.Inspect := .join
instance (config : Config) : (alone config).Inspect := {}
instance (config : Config) : (Schedule.system (K := Key) (P := Unit) (A := Answer)
  config.scheduler).Inspect := {}
instance (config : Config) : (system config).Inspect := .join

/-- The objects of a video in the store. -/
inductive Object where
  | upload (v : VideoId)
  | rendition (v : VideoId)
  | thumbnail (v : VideoId)
  deriving DecidableEq, Hashable, Repr

abbrev WorkerReport := Transcode.Report Round Object

/-- The model's state: what the worker was given and reported, and what the store may hold. -/
abbrev Store := Rpc.State (Events.State (Transcode.State Round Object Unit) WorkerReport)

/-- The key the site and the worker share in the checks. -/
def workerKey : Hmac.Key := .of "the worker's key".toUTF8

/-- The browser's put of video `v`'s object, granted by the link the site handed out, as the
model's call: a call of its own, which the site never sees answered. -/
def uploadCall (v : VideoId) : Nat := 1000 + v

/-- The model's call of an attempt: above every upload's, and one for each key and attempt,
for the small bounds checked (attempts below 8, requests below 64, rounds below 8). -/
def callOf (key : Key) (attempt : Nat) : Nat :=
  let code := match key with
    | .check v req => 4 * (v * 64 + req)
    | .expire v => 4 * v + 1
    | .delete v => 4 * v + 2
    | .transcode r => 4 * (r.video * 8 + r.n) + 3
  2000 + code * 8 + attempt

/-- The key and attempt of a model's call, the inverse of `callOf`. -/
def attemptOf (call : Nat) : Option (Key × Nat) :=
  if call < 2000 then none
  else
    let n := call - 2000
    let code := n / 8
    let x := code / 4
    let key : Key := match code % 4 with
      | 0 => .check (x / 64) (x % 64)
      | 1 => .expire x
      | 2 => .delete x
      | _ => .transcode ⟨x / 8, x % 8⟩
    some (key, n % 8)

/-- The worker's job of a round, as the site's bridge writes it (`Settings.job`). -/
def jobOf (r : Round) : Transcode.Job Round Object :=
  ⟨r, .upload r.video, [.rendition r.video, .thumbnail r.video]⟩

def answerOf : Answer → Transcode.Answer Unit
  | .found _ => .store .present
  | .missing => .store .missing
  | .deleted => .store .deleted
  | .accepted => .accepted
  | .failed => .store .refused

def request : Op → Transcode.Request Round Object Unit
  | .head v => .store (.head (.upload v))
  | .delete v => .store (.delete (.upload v))
  | .transcode r => .start (jobOf r)

/-- A report as the worker's model reads it. -/
def Report.ofWorker : Report → WorkerReport
  | .done r => .done r (jobOf r).targets
  | .failed r => .failed r

def port : Rpc.Port fullSig (Transcode.Request Round Object Unit) (Transcode.Answer Unit) WorkerReport where
  called
    | .inr (.reply _ _ (.created v _ _)) => some ⟨uploadCall v, 0, .store (.granted (.upload v) ())⟩
    | .inl (.call a) => some ⟨callOf a.key a.attempt, a.deadline_ms, request a.key.op⟩
    | _ => none
  replied
    | .inl (.reply key attempt .unknown) => some (callOf key attempt, .unknown)
    | .inl (.reply (.transcode r) attempt (.answer .failed)) => some (callOf (.transcode r) attempt, .answer .refused)
    | .inl (.reply key attempt (.answer a)) => some (callOf key attempt, .answer (answerOf a))
    | _ => none
  notified
    | .inr (.request (.report _ r signature) _) =>
      if r.signed workerKey signature then some (Report.ofWorker r) else none
    | _ => none

/-- How the worker reports: each report delivered up to `deliveries` times; failures reported
or not; and whether anyone else posts reports. Which answers are explored: every answer the store
may give, or only `found` and `unknown` where the scenario is about the worker; and every answer
to a job, or only `accepted` where it is not (a job not answered still times out). -/
structure Worker where
  deliveries : Nat := 1
  failures : Bool := true
  forging : Bool := false
  everyAnswer : Bool := true
  startFaults : Bool := true
  /-- Whether a report may come after its video's delete was answered. -/
  late : Bool := true
  /-- A worker that never answers and never reports, where the scenario is about the store. -/
  silent : Bool := false
  /-- The first round of each video reported failed and never done, and every later round done
and never failed: the one path to a retry, for its scenario at small bounds. -/
  firstFails : Bool := false

def store (worker : Worker) : Outside fullSig Store :=
  Rpc.outside port (Transcode.service worker.deliveries () true)

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
  /-- The rounds the worker reported done, with its signature. -/
  done : List Round := []
  /-- The reports posted without the worker's signature, each once. -/
  forged : List ReqId := []
  /-- The forged reports the site refused. -/
  refused : List ReqId := []
  /-- What a video not ready was shown waiting for, to its owner. -/
  stages : List Stage := []
  /-- The videos whose upload a waiting request was told is confirmed. -/
  confirmed : List VideoId := []
  deriving DecidableEq, Hashable, Repr

instance : BEq Browsers := instBEqOfDecidableEq

/-- `a` put into `l` in the order of `key`. The browsers read their lists as sets, or count in
them, so keeping each sorted gives a state one form whatever the order things happened in. -/
def ins {α : Type} (key : α → Nat) (a : α) : List α → List α
  | [] => [a]
  | b :: l => if key a ≤ key b then a :: b :: l else b :: ins key a l

def watchKey (w : VideoId × Option Member) : Nat := w.1 * 64 + (w.2.map (· + 1)).getD 0

def attemptKey (a : Key × Nat) : Nat := callOf a.1 a.2

def Command.req : Command → ReqId
  | .signIn req .. | .signOut req .. | .create req .. | .uploaded req .. | .watch req ..
  | .like req .. | .comment req .. | .uncomment req .. | .delete req .. | .feed req ..
  | .channel req .. | .retry req .. | .report req .. => req

def Browsers.ready (b : Browsers) (deps : List ReqId) : Bool := deps.all b.answered.contains

def Browsers.send (b : Browsers) (c : Command) (at_s : Nat) : Option Browsers :=
  match b.todo.find? fun (c', t, deps) => c' == c && t == at_s && b.ready deps with
  | some entry =>
    some { b with todo := b.todo.erase entry, sent := ins (·.1) (Command.req c, b.deleted) b.sent
                  times := ins (·.1) (Command.req c, at_s) b.times }
  | none => none

/-- What each claim says of a reply as a browser sees it, with the store as it is then. A
session is named by the request that signed in, so it began when that request arrived. The
answers to reports show nothing and nobody waits for them, so they are not kept as answered. -/
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
  let store := held.server.inner.store
  let confirmedOk := cards.all fun c => store.held.contains (.upload c.id)
  let transcodedOk := cards.all fun c => b.done.any (·.video == c.id)
  let mayHold (o : Object) := (store.possible o).any Option.isSome
  let playableOk := cards.all fun c => mayHold (.rendition c.id) && mayHold (.thumbnail c.id)
  let fail := [("a private video is shown to someone else", privateOk),
    ("a deleted video is shown", goneOk),
    ("a video is shown that the store did not say it holds", confirmedOk),
    ("a video is shown that the worker did not report done, signed", transcodedOk),
    ("a video is shown whose rendition or thumbnail the store may not hold", playableOk),
    ("a session past its lifetime is let in", liveOk)].filterMap
      fun (name, ok) => if ok then none else some name
  let answered := { b with answered := ins id req b.answered, broken := b.broken ++ fail }
  match r with
  | .deleted v => { answered with deleted := ins id v b.deleted }
  | .watch view _ => { answered with watched := ins watchKey (view.card.id, viewer.map (·.1)) b.watched }
  | .preparing _ _ stage =>
    if b.stages.contains stage then answered else { answered with stages := ins (hash · |>.toNat) stage b.stages }
  | .confirmed v => if b.confirmed.contains v then answered else { answered with confirmed := ins id v b.confirmed }
  | .reported => b
  | .forged => if b.refused.contains req then b else { b with refused := ins id req b.refused }
  | _ => answered

/-- The store's answer to an attempt out: what it tells of a delete. -/
def Browsers.answered' (b : Browsers) : SchedIn → Option Browsers
  | .reply key attempt r =>
    if b.out.contains (key, attempt) then
      let b := { b with out := b.out.erase (key, attempt) }
      match key, r with
      | .delete v, .answer .deleted => some (if b.gone.contains v then b else { b with gone := ins id v b.gone })
      | _, _ => some b
    else none
  | _ => none

/-- An attempt handed over: out at the store, unless its abandon came first. -/
def Browsers.call (b : Browsers) (a : Schedule.Attempt Key Unit) : Browsers :=
  let b := if b.early.contains (a.key, a.attempt) then { b with early := b.early.erase (a.key, a.attempt) }
    else { b with out := ins attemptKey (a.key, a.attempt) b.out }
  match a.key with
  | .check .. => { b with checkTries := max b.checkTries a.attempt }
  | .expire _ => { b with expireTries := max b.expireTries a.attempt }
  | .delete _ => { b with deleteTries := max b.deleteTries a.attempt }
  | .transcode _ => b

def Browsers.observe (b : Browsers) (life : Auth.Lifetime) (held : Store) : SchedOut ⊕ Out → Browsers
  | .inr (.reply req viewer r) => judge life b held req viewer r
  | .inr (.orphan v) => if b.orphans.contains v then b else { b with orphans := ins id v b.orphans }
  | .inl (.call a) => b.call a
  | .inl (.abandon key attempt) =>
    if b.out.contains (key, attempt) then { b with out := b.out.erase (key, attempt) }
    else { b with early := ins attemptKey (key, attempt) b.early }
  | _ => b

/-- A report posted to the site: by the worker, signed; or by anyone else, with a signature
that is not the worker's. -/
def Browsers.reported (b : Browsers) (worker : Worker) (req : ReqId) (r : Report) (signature : String) :
    Option Browsers :=
  if r.signed workerKey signature then
    match r with
    | .done round => some (if b.done.contains round then b else { b with done := ins (fun r => r.video * 8 + r.n) round b.done })
    | .failed _ => some b
  else if worker.forging && !b.forged.contains req then some { b with forged := ins id req b.forged }
  else none

def world (life : Auth.Lifetime) (script : Script) (worker : Worker) :
    Outside fullSig (Browsers × Store) where
  init := ({ todo := script }, (store worker).init)
  allow d
    | x@(.inr (.request (.report req r signature) _)) => do
      let b ← d.1.reported worker req r signature
      if r.signed workerKey signature then pure (b, ← (store worker).allow d.2 x) else pure (b, d.2)
    | .inr (.request c at_s) => (d.1.send c at_s).map (·, d.2)
    | .inl x => do pure (← d.1.answered' x, ← (store worker).allow d.2 (.inl x))
    | x => ((store worker).allow d.2 x).map (d.1, ·)
  observe d out := (d.1.observe life d.2 out, (store worker).observe d.2 out)

def answers : List (Rpc.Reply Answer) :=
  [.unknown, .answer (.found 1), .answer .missing, .answer .deleted, .answer .failed]

def workerAnswers : List (Rpc.Reply Answer) := [.unknown, .answer .accepted, .answer .failed]

/-- The request id of a report: one for each round, kind and signer, for the small bounds
checked (videos below 2, rounds below 4). -/
def reportReq (r : Report) (forged : Bool) : ReqId :=
  100 + 16 * r.round.video + 4 * r.round.n + 2 * (match r with | .done _ => 0 | .failed _ => 1)
    + (if forged then 1 else 0)

def signedReport (r : Report) : SchedIn ⊕ Input :=
  .inr (.request (.report (reportReq r false) r (Transcode.signature workerKey r.round.id r.status)) 0)

def forgedReport (r : Report) : SchedIn ⊕ Input :=
  .inr (.request (.report (reportReq r true) r "forged") 0)

/-- The worker's reports of every job it was given, and, with `forging`, a done report of the
first round of video 0 signed by someone else. -/
def reports (worker : Worker) (d : Browsers × Store) : List (SchedIn ⊕ Input) :=
  let rounds := (d.2.server.inner.jobs.map (·.2.id)).filter fun r =>
    !worker.silent && (worker.late || !d.1.deleted.contains r.video)
  (rounds.flatMap fun r =>
      if worker.firstFails then [signedReport (if r.n == 0 then .failed r else .done r)]
      else signedReport (.done r) :: if worker.failures then [signedReport (.failed r)] else [])
    ++ if worker.forging then [forgedReport (.done ⟨0, 0⟩)] else []

def samples (worker : Worker) (d : Browsers × Store) : List (SchedIn ⊕ Input) :=
  (d.1.todo.filterMap fun (c, at_s, deps) =>
      if d.1.ready deps then some (Sum.inr (Input.request c at_s)) else none)
    ++ ((d.2.pending.filterMap attemptOf).flatMap fun (key, attempt) =>
      (match key with
        | .transcode _ =>
          if worker.silent then [] else if worker.startFaults then workerAnswers else [.answer .accepted]
        | _ => if worker.everyAnswer then answers else [.unknown, .answer (.found 1)]).map fun r =>
        Sum.inl (Schedule.Input.reply key attempt r))
    ++ reports worker d

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
    workerKey
    checkRetry := { maxAttempts := 1, deadline_ms := 1, base_ms := 1, cap_ms := 1 }
    transcodeRetry := { maxAttempts := 1, deadline_ms := 1, base_ms := 1, cap_ms := 1 }
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

/-- `0` makes a public video and says it is uploaded; it asks for it while it may be prepared,
asks for it to be tried again (which does something only if it failed), and a stranger asks for
it. -/
def pipeline : Script := .of <|
  signIns.take 1 ++
  [ (.create 3 0 1 t none_ .public .mp4, [1]), (.uploaded 4 0 1 0, [3]),
    (.watch 5 (some (0, 1)) 0, [4]), (.retry 6 0 1 0, [5]), (.watch 7 none 0, [6]) ]

/-- `0` makes a public video and says it is uploaded; it asks for it, and a stranger asks for
it. -/
def forgery : Script := .of <|
  signIns.take 1 ++
  [ (.create 3 0 1 t none_ .public .mp4, [1]), (.uploaded 4 0 1 0, [3]),
    (.watch 5 (some (0, 1)) 0, [4]), (.watch 6 none 0, [5]) ]

/-! The small bounds' scripts: each a large one's, cut to the requests its witnesses need. -/

/-- `life` up to its likes: `1` watches a public video and likes it twice, and `0` likes it. -/
def likes : Script := life.take 8

/-- `0` makes a public video, watches it once it is shown, deletes it, and asks for it again. -/
def deleteShown : Script := .of <|
  signIns.take 1 ++
  [ (.create 3 0 1 t none_ .public .mp4, [1]), (.uploaded 4 0 1 0, [3]),
    (.watch 5 (some (0, 1)) 0, [4]), (.delete 6 0 1 0, [5]), (.watch 7 (some (0, 1)) 0, [6]) ]

/-- `gone` without asking for the channel after the delete. -/
def goneShort : Script := gone.take 4

/-- `twice` without asking for the video after both checks. -/
def twiceShort : Script := twice.take 4

/-- `lapsed` without asking for the channel: `0` makes a video, never says it is uploaded, and
asks for it. -/
def lapsedShort : Script := .of <|
  signIns.take 1 ++
  [ (.create 3 0 1 t none_ .public .mp4, [1]), (.watch 5 (some (0, 1)) 0, [3]) ]

/-- `pipeline` up to the first time `0` asks for its video, while it may be prepared. -/
def prepared : Script := pipeline.take 4

/-- `0` makes a public video, says it is uploaded, and asks for it to be tried again. -/
def retried : Script := .of <|
  signIns.take 1 ++
  [ (.create 3 0 1 t none_ .public .mp4, [1]), (.uploaded 4 0 1 0, [3]), (.retry 5 0 1 0, [4]) ]

/-- `forgery` without the stranger's request. -/
def forgeryShort : Script := forgery.take 4

/-- A worker that takes each job and reports it done, once, at any moment while its video is
there: for the scenarios about the site and the store, whose interleavings the worker's faults
would multiply past what the checker holds. The worker's faults are the pipeline's. -/
def quiet : Worker := { failures := false, startFaults := false, late := false }

/-- The worker as the pipeline is checked against: a job not answered, refused or `unknown`,
and its report late, failed or never. -/
def faulty : Worker := { everyAnswer := false }

/-- Reports delivered twice, and forged by others, beside the worker's. -/
def forged : Worker := { deliveries := 2, forging := true, failures := false, everyAnswer := false }

def lapsing : Config := { checkTwice with pending_s := some 1 }

def claims {config : Config} : List (Check.Property (W config)) :=
  [ .always "a private video is shown to its owner only" fun w =>
      !w.driver.1.broken.contains "a private video is shown to someone else",
    .always "a video is not shown to a request made after its delete was answered" fun w =>
      !w.driver.1.broken.contains "a deleted video is shown",
    .always "a video is shown only once the store said it holds its object" fun w =>
      !w.driver.1.broken.contains "a video is shown that the store did not say it holds",
    .always "a video is shown only once the worker reported it done, signed" fun w =>
      !w.driver.1.broken.contains "a video is shown that the worker did not report done, signed",
    .always "a video shown has a rendition and a thumbnail the store may hold" fun w =>
      !w.driver.1.broken.contains "a video is shown whose rendition or thumbnail the store may not hold",
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

def confirmedOnce {config : Config} : Check.Property (W config) :=
  .sometimes "a check confirms an upload and its request is told" fun w =>
    !w.driver.1.confirmed.isEmpty

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

def preparing {config : Config} : Check.Property (W config) :=
  .sometimes "a video being prepared is shown so to its owner" fun w =>
    w.driver.1.stages.contains .transcoding

def failedShown {config : Config} : Check.Property (W config) :=
  .sometimes "a video whose transcode failed is shown so to its owner" fun w =>
    w.driver.1.stages.contains .failed

def shownAfterRetry {config : Config} : Check.Property (W config) :=
  .sometimes "a video is shown after its owner tried its transcode again" fun w =>
    w.driver.1.done.contains ⟨0, 1⟩ && w.driver.1.watched.any (·.1 == 0)

def readyAfterRetry {config : Config} : Check.Property (W config) :=
  .sometimes "a video is ready after its owner tried its transcode again" fun w =>
    w.driver.1.done.contains ⟨0, 1⟩ && (site w).videos.any fun v => v.id == 0 && v.status matches .ready ..

def forgedRefused {config : Config} : Check.Property (W config) :=
  .sometimes "a forged report is refused" fun w => !w.driver.1.refused.isEmpty

def deliveredTwice {config : Config} : Check.Property (W config) :=
  .sometimes "a report is delivered twice" fun w => w.driver.2.server.delivered.any (·.2 == 2)

/-- No video is transcoding: each confirmed upload is ready or failed. -/
def settled {config : Config} (w : W config) : Bool :=
  (site w).videos.all fun v => !(v.status matches .transcoding ..)

/-- The site of `config` checked against `script`; its sessions are judged by `life`, the
site's own unless a seeded bug says otherwise. -/
def check (config : Config) (script : Script) (witnesses : List (Check.Property (W config)))
    (maxCrashes : Nat := 1) (life : Auth.Lifetime := config.lifetime)
    (crashing : fullSig.Id → Bool := fun _ => true) (worker : Worker := {}) (live : Bool := false) :=
  Check.system (system config)
    { env := env crashing, driver := (world life script worker).driver (samples worker), maxCrashes }
    (claims ++ witnesses) { maxStates := 3000000, checkDeadlock := live, terminal := settled }

def trusting : Config := { config with trustBrowser := true }
def hasty : Config := { config with readyOnTimeout := true }
def credulous : Config := { config with trustUnsigned := true }

/-- The first violation's name and length, if the report has one. -/
def found {S L : Type} (r : Check.Report S L) : Option (String × Nat) :=
  match r.failure with
  | some (.violated p t) => some (p, t.steps.length)
  | _ => none

/-- One member cannot fill the site: their videos, and their comments on one video, are bounded
far below the site's; a video's owner takes out anyone's comment on it. -/
def capTests : List (String × Bool) :=
  let cfg : Config := { maxOwned := 2, maxCommentsEach := 2, workerKey }
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
      [Key.check 1 9, .expire 1, .delete 0, .check 0 63, .transcode ⟨1, 7⟩, .transcode ⟨0, 0⟩].all fun k =>
        (List.range 8).all fun n => attemptOf (callOf k n) == some (k, n)) ]

/-- A check by its name: the report it prints, and whether it passed. -/
structure Run where
  name : String
  result : Unit → String × Bool

def passes {config : Config} (r : Check.Report (W config) (Event fullSig)) (witnesses : Nat) :
    String × Bool :=
  (r.renderSystem, r.ok && r.complete && r.witnesses.length == witnesses)

/-- A seeded bug, found as a violation of `claim`. -/
def seeded {config : Config} (r : Check.Report (W config) (Event fullSig)) (claim : String) :
    String × Bool :=
  match found r with
  | some (p, n) => (s!"\"{p}\" after {n} steps", p == claim)
  | none => ("not found", false)

def unconfirmed : String := "a video is shown only once the store said it holds its object"

/-- How large a scenario is checked. `lake test` checks each at small bounds, exhaustively and
in seconds; the large bounds run nightly (`.github/workflows/large.yml`, `lake exe videosTest
large`). Each small scenario still reaches every witness it names (`passes`), so it cannot pass
by exploring nothing (rule 5.3). -/
inductive Size where
  | small
  | large
  deriving DecidableEq

/-- The scenarios at small bounds: each a large one's script cut to the requests its witnesses
need, and where it says so with fewer of the store's answers (`unknown` and `found`), or with no
crash. What a small one leaves out, its large one checks. -/
def smallRuns : List Run :=
  [ ⟨"check: a video watched and liked three times, with the store's faults and a crash anywhere",
      fun () => passes (check config likes [shown, twoLikes] (worker := quiet)) 2⟩,
    ⟨"check: a video shown, deleted and asked for again, with no crash",
      fun () => passes (check config deleteShown [shown, goneWhileHeld] 0
        (worker := { quiet with everyAnswer := false })) 2⟩,
    ⟨"check: a private video, with the store's faults and a crash anywhere",
      fun () => passes (check config secret [ownerWatches, othersAsk] (worker := quiet)) 2⟩,
    ⟨"check: a video deleted while its check may be out, the store answering found or unknown, and a crash of the site anywhere",
      fun () => passes (check config goneShort [goneWhileHeld] (crashing := siteCrashes)
        (worker := { silent := true, everyAnswer := false })) 1⟩,
    ⟨"check: a second check while the first may be out, with no crash",
      fun () => passes (check config twiceShort [confirmedOnce] 0 (worker := { silent := true })) 1⟩,
    ⟨"check: a delete tried twice, deleted or reported, and a crash anywhere",
      fun () => passes (check deleteTwice purge [goneWhileHeld, deletedAfterRetry, reported]
        (worker := quiet)) 3⟩,
    ⟨"check: an upload never confirmed, checked a last time, twice, and a crash anywhere",
      fun () => passes (check lapsing lapsedShort [lapsedReady, lapsedOut, checkedAgain]
        (worker := quiet)) 3⟩,
    ⟨"check: a session past its lifetime lets nothing in, and a new sign-in does",
      fun () => passes (check short expiry [watchedTwice] (worker := quiet)) 1⟩,
    ⟨"check: the pipeline, with jobs and reports late, failed or never, and a crash of the site anywhere",
      fun () => passes (check config prepared [shown, preparing, failedShown] (crashing := siteCrashes)
        (worker := { faulty with startFaults := false })) 3⟩,
    ⟨"check: reports delivered twice and forged beside the worker's, and a crash anywhere",
      fun () => passes (check config forgeryShort [shown, forgedRefused, deliveredTwice]
        (worker := forged)) 3⟩,
    ⟨"check: with no crash, every run that cannot go on leaves each confirmed upload ready or failed",
      fun () => passes (check config prepared [shown, failedShown] 0 (worker := faulty)
        (live := true)) 2⟩,
    ⟨"check: with no crash, a transcode that failed is tried again, and every run that cannot go on leaves the upload ready or failed",
      fun () => passes (check config retried [readyAfterRetry] 0
        (worker := { faulty with firstFails := true }) (live := true)) 1⟩ ]

/-- The scenarios at large bounds. -/
def largeRuns : List Run :=
  [ ⟨"check: a video's life, with the store's faults and a crash anywhere",
      fun () => passes (check config life [shown, goneWhileHeld, twoLikes] (worker := quiet)) 3⟩,
    ⟨"check: a private video, with the store's faults and two crashes anywhere",
      fun () => passes (check config secret [ownerWatches, othersAsk] (worker := quiet) (maxCrashes := 2)) 2⟩,
    ⟨"check: a video deleted while its check may be out, and a crash of the site anywhere",
      fun () => passes (check config gone [goneWhileHeld] (crashing := siteCrashes)
        (worker := { silent := true })) 1⟩,
    ⟨"check: a second check while the first may be out, and a crash of the site anywhere",
      fun () => passes (check config twice [confirmedOnce] (crashing := siteCrashes)
        (worker := { silent := true })) 1⟩,
    ⟨"check: a delete tried twice, deleted or reported, and two crashes anywhere",
      fun () => passes (check deleteTwice purge [goneWhileHeld, deletedAfterRetry, reported]
        (worker := quiet) (maxCrashes := 2)) 3⟩,
    ⟨"check: an upload never confirmed, checked a last time, twice, and a crash anywhere",
      fun () => passes (check lapsing lapsed [lapsedReady, lapsedOut, checkedAgain] (worker := quiet)) 3⟩,
    ⟨"check: a session past its lifetime lets nothing in, and a new sign-in does, with two crashes anywhere",
      fun () => passes (check short expiry [watchedTwice] (worker := quiet) (maxCrashes := 2)) 1⟩,
    ⟨"check: the pipeline, with jobs and reports late, failed or never, a retry, and a crash of the site anywhere",
      fun () => passes (check config pipeline [shown, preparing, failedShown, shownAfterRetry]
        (crashing := siteCrashes) (worker := { faulty with startFaults := false })) 4⟩,
    ⟨"check: reports delivered twice and forged beside the worker's, and a crash anywhere",
      fun () => passes (check config forgery [shown, forgedRefused, deliveredTwice]
        (worker := forged)) 3⟩,
    ⟨"check: with no crash, every run that cannot go on leaves each confirmed upload ready or failed",
      fun () => passes (check config pipeline [shown, failedShown, shownAfterRetry] 0
        (worker := faulty) (live := true)) 3⟩ ]

/-- Seeded bugs, each found at the bounds of `lake test`. -/
def seededRuns : List Run :=
  [ ⟨"check, seeded: trusting the browser shows a video the store never confirmed",
      fun () => seeded (check trusting life [] 0 (worker := quiet)) unconfirmed⟩,
    ⟨"check, seeded: a check that timed out taken as found shows such a video",
      fun () => seeded (check hasty life [] 0 (worker := quiet)) unconfirmed⟩,
    ⟨"check, seeded: sessions that never end let a request in past the lifetime",
      fun () => seeded (check { short with lifetime := {} } expiry [] 0 short.lifetime (worker := quiet))
        "a session past its lifetime lets no request in"⟩,
    ⟨"check, seeded: a report taken unsigned shows a video the worker never reported done",
      fun () => seeded (check credulous forgery [] 0 (worker := forged))
        "a video is shown only once the worker reported it done, signed"⟩ ]

def runs : Size → List Run
  | .small => smallRuns ++ seededRuns
  | .large => largeRuns

/-- The checks of `size` whose names contain one of `only`, or all of them. They share nothing,
so up to `jobs` run at once, each on a thread of its own; each report is printed in order. -/
def run (size : Size := .small) (only : List String := []) (jobs : Nat := 4) :
    IO (List (String × Bool)) := do
  let chosen := (runs size).filter fun r => only.isEmpty || only.any (r.name.contains ·)
  let mut results := []
  let n := max jobs 1
  for batch in (List.range ((chosen.length + n - 1) / n)).map fun i => (chosen.drop (i * n)).take n do
    let tasks := batch.map fun r => Task.spawn (prio := .dedicated) fun () => r.result ()
    for (r, task) in batch.zip tasks do
      let (report, ok) ← IO.wait task
      IO.println s!"{r.name}: {report}"
      (← IO.getStdout).flush
      results := results ++ [(r.name, ok)]
  return results

end Videos.Check
