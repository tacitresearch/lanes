/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.System

/-!
# Model checks

The site's two members, `a` and `b`, each with its actor and its scheduler, beside their
browsers, which follow a script, and beside the model of a transcode worker and the object
store it writes to (`Lanes.Transcode`, over `Lanes.ObjectStore`), which answers each attempt a
scheduler makes at most once, late, never, refused or `unknown`, and whose writes that were not
answered may take effect at any moment or never. The browser's upload is a write the site grants
and never hears the answer to (the upload form, the model's `granted`): the model may let it
land before the site asks, after, or never. A check is the model's head, a delete the model's
delete of the upload, and a transcode's attempt the job of its round, given to the worker. The
worker, honest, writes the rendition and the thumbnail at any moment after it is given a job,
and reports the job done (once its source may be held, its writes landed) or failed, late, again
or never; anyone else may post a report with a signature that is not the worker's. An answer
comes only to an attempt out (as `Schedule.callee` has it): one to an attempt abandoned, which
the scheduler would not take, is not given, but the write it answers may still land. Every timer
of a scheduler may fire at any moment, and an actor may crash and start again anywhere.

The system checked is the one that runs, with its actors named by the two members only
(`checked`): the checker enumerates the actors, and a member is any identity. Each of the four
actors runs the system's own actor, and a message to a member the check does not have is not
sent; none is, since the scripts name only `a` and `b`.

The writes are judged as they are answered, and the reads, which change nothing and are
answered from the members' sites, at every state: a read may come at any boundary. No private
video is shown to anyone but its owner; nothing is shown after its delete was answered; nothing
is shown that the store did not first say it holds, that the worker did not first report done
with its signature, or whose rendition and thumbnail the store may not hold; no session past its
lifetime lets a request in. The state is judged too: each like counted once, every bound, and,
in runs with no crash, every deleted video's object deleted in the store or reported once its
job is over. A crash in the semantics loses the actor's mail (`SysState.down`), so a scheduling
or an end on its way is lost with it; on one shard an actor crashes only by stopping itself,
which none does, and the death of the process returns to the journal, mail included
(`TRUSTED.md`, "Environment model"). Every `always` has `sometimes` beside it (rule 5.3).

The worker's faults multiply every interleaving, so each scenario explores those it is about
(`Worker`). Of runs with no crash, every run that cannot go on leaves no video transcoding: a
confirmed upload ends ready or failed (`pipeline`, the checker's deadlocks). The site's part of
it is proved from the worker's report (`Videos.report_settles`).

Four seeded bugs, each found: a video made ready because the browser says so, a check the
store did not answer in time taken as found, sessions that never end, and a report taken
whatever its signature.
-/

namespace Videos.Check

open Lanes

/-! ## The members checked -/

def name (s : String) (h : Name.valid s = true := by simp [Name.valid]) : {s : String // Name.valid s} :=
  ⟨s, h⟩

def a : Who := ⟨name "id", name "a"⟩
def b : Who := ⟨name "id", name "b"⟩

def who : Fin 2 → Who
  | 0 => a
  | 1 => b

def idx (w : Who) : Fin 2 := if w = b then 1 else 0

/-- Video `n` of member `m`. -/
def vid (m : Who) (n : Nat) : VideoId := ⟨m, n⟩

/-- A number for each video the checks make: two members, at most two videos each. -/
def vcode (v : VideoId) : Nat := 2 * (idx v.owner).val + v.n

abbrev Idx := Fin 2 ⊕ Fin 2

def lift : Idx → fullSig.Id := Sum.map who who

/-- An actor of the system, as one of the check's, if the check has it. -/
def lower : (i : fullSig.Id) → Option {j : Idx // lift j = i}
  | .inl w => if h : who (idx w) = w then some ⟨.inl (idx w), by simp [lift, h]⟩ else none
  | .inr w => if h : who (idx w) = w then some ⟨.inr (idx w), by simp [lift, h]⟩ else none

abbrev csig : Signature where
  Id := Idx
  Msg i := fullSig.Msg (lift i)
  In := fullSig.In
  Out := fullSig.Out
  decEqMsg i := fullSig.decEqMsg (lift i)

def conv {i : Idx} : Effect fullSig (lift i) → List (Effect csig i)
  | .send to msg =>
    match lower to with
    | some ⟨j, h⟩ => [.send j (cast (congrArg fullSig.Msg h.symm) msg)]
    | none => []
  | .emit out => [.emit out]
  | .after delay_ms msg => [.after delay_ms msg]
  | .cancel msg => [.cancel msg]
  | .stop => [.stop]

/-- The system with its actors named by the check's two members. They are started when the
system starts, not on their first message as they are where it runs: a start of an empty site or
scheduler does nothing, and starting them together keeps the interleavings of the starts out of
the states explored. -/
abbrev checked (config : Config) : System csig where
  State i := (system config).State (lift i)
  actor i := ((system config).actor (lift i)).mapEff conv
  accept x :=
    match lower ((system config).accept x).1, ((system config).accept x).2 with
    | some ⟨j, h⟩, msg => ⟨j, cast (congrArg fullSig.Msg h.symm) msg⟩
    | none, _ => ⟨.inr 0, Input.noticed (.delete (vid a 9))⟩
  boot := [.inl 0, .inr 0, .inl 1, .inr 1]

instance : csig.Inspect where
  reprMsg
    | .inl _ => inferInstanceAs (Repr (Schedule.Msg Key Unit Answer))
    | .inr _ => inferInstanceAs (Repr Input)
  hashMsg
    | .inl _ => inferInstanceAs (Hashable (Schedule.Msg Key Unit Answer))
    | .inr _ => inferInstanceAs (Hashable Input)

instance (config : Config) : (checked config).Inspect where
  beqState
    | .inl _ => inferInstanceAs (BEq (Schedule.State Key Unit))
    | .inr _ => inferInstanceAs (BEq Site)
  reprState
    | .inl _ => inferInstanceAs (Repr (Schedule.State Key Unit))
    | .inr _ => inferInstanceAs (Repr Site)
  hashState
    | .inl _ => inferInstanceAs (Hashable (Schedule.State Key Unit))
    | .inr _ => inferInstanceAs (Hashable Site)

/-! ## The store and the worker -/

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
def uploadCall (v : VideoId) : Nat := 1000 + vcode v

/-- The model's call of an attempt: above every upload's, and one for each key and attempt,
for the small bounds checked (attempts below 8, requests below 64, rounds below 8, videos
below 4). -/
def callOf (key : Key) (attempt : Nat) : Nat :=
  let code := match key with
    | .check v req => 4 * (vcode v * 64 + req)
    | .expire v => 4 * vcode v + 1
    | .delete v => 4 * vcode v + 2
    | .transcode r => 4 * (vcode r.video * 8 + r.n) + 3
  2000 + code * 8 + attempt

def videoOf (code : Nat) : VideoId := ⟨who (if code / 2 % 2 = 1 then 1 else 0), code % 2⟩

/-- The key and attempt of a model's call, the inverse of `callOf`. -/
def attemptOf (call : Nat) : Option (Key × Nat) :=
  if call < 2000 then none
  else
    let n := call - 2000
    let code := n / 8
    let x := code / 4
    let key : Key := match code % 4 with
      | 0 => .check (videoOf (x / 64)) (x % 64)
      | 1 => .expire (videoOf x)
      | 2 => .delete (videoOf x)
      | _ => .transcode ⟨videoOf (x / 8), x % 8⟩
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

def port : Rpc.Port csig (Transcode.Request Round Object Unit) (Transcode.Answer Unit) WorkerReport where
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

def store (worker : Worker) : Outside csig Store :=
  Rpc.outside port (Transcode.service worker.deliveries () true)

/-! ## The browsers -/

/-- A request, the time it arrives, and the requests whose answers it waits for. -/
abbrev Script := List (Command × Nat × List ReqId)

/-- Requests that all arrive at time 0. -/
def Script.of (l : List (Command × List ReqId)) : Script := l.map fun (c, deps) => (c, 0, deps)

/-- A read a browser may make, by its name in the scenario, at a time, once the requests it
names are answered. -/
structure Ask where
  name : Nat
  read : Read
  at_s : Nat := 0
  deps : List ReqId := []

/-- The browsers: what they have still to send, what they were answered, and what they saw go
wrong; and what the store did with the deletes. -/
structure Browsers where
  todo : Script
  answered : List ReqId := []
  /-- Videos whose delete was answered. -/
  deleted : List VideoId := []
  /-- When each request sent arrived. -/
  times : List (ReqId × Nat) := []
  broken : List String := []
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
  /-- The videos whose upload a waiting request was told is confirmed. -/
  confirmed : List VideoId := []
  deriving DecidableEq, Hashable, Repr

instance : BEq Browsers := instBEqOfDecidableEq

/-- `a` put into `l` in the order of `key`. The browsers read their lists as sets, or count in
them, so keeping each sorted gives a state one form whatever the order things happened in. -/
def ins {α : Type} (key : α → Nat) (a : α) : List α → List α
  | [] => [a]
  | b :: l => if key a ≤ key b then a :: b :: l else b :: ins key a l

def attemptKey (a : Key × Nat) : Nat := callOf a.1 a.2

def Command.req : Command → ReqId
  | .signIn req .. | .signOut req .. | .create req .. | .uploaded req .. | .like req ..
  | .comment req .. | .uncomment req .. | .delete req .. | .retry req .. | .report req .. => req

def Browsers.ready (b : Browsers) (deps : List ReqId) : Bool := deps.all b.answered.contains

def Browsers.send (b : Browsers) (c : Command) (at_s : Nat) : Option Browsers :=
  match b.todo.find? fun (c', t, deps) => c' == c && t == at_s && b.ready deps with
  | some entry =>
    some { b with todo := b.todo.erase entry, times := ins (·.1) (Command.req c, at_s) b.times }
  | none => none

/-- Whether a session named by a request of `viewer` lets a request of `t` in, as the browsers
know: it began when its sign-in arrived. -/
def liveAt (life : Auth.Lifetime) (b : Browsers) (viewer : Viewer) (t : Nat) : Bool :=
  match viewer with
  | some (_, sid) => match b.times.lookup sid with
    | some began => !life.absolute_s.any (began + · ≤ t)
    | none => true
  | none => true

/-- What a write's answer is judged by, as a browser sees it: its session's lifetime. -/
def judge (life : Auth.Lifetime) (b : Browsers) (req : ReqId) (viewer : Viewer) (r : Reply) :
    Browsers :=
  let liveOk := match b.times.lookup req with
    | some t => liveAt life b viewer t
    | none => true
  let answered := { b with answered := ins id req b.answered
                           broken := if liveOk then b.broken else b.broken ++ ["a session past its lifetime is let in"] }
  match r with
  | .deleted v => { answered with deleted := ins vcode v b.deleted }
  | .confirmed v => if b.confirmed.contains v then answered else { answered with confirmed := ins vcode v b.confirmed }
  | .reported => b
  | .forged => if b.refused.contains req then b else { b with refused := ins id req b.refused }
  | _ => answered

/-- The store's answer to an attempt out: what it tells of a delete. -/
def Browsers.answered' (b : Browsers) : SchedIn → Option Browsers
  | .reply key attempt r =>
    if b.out.contains (key, attempt) then
      let b := { b with out := b.out.erase (key, attempt) }
      match key, r with
      | .delete v, .answer .deleted => some (if b.gone.contains v then b else { b with gone := ins vcode v b.gone })
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

def Browsers.observe (b : Browsers) (life : Auth.Lifetime) : SchedOut ⊕ Out → Browsers
  | .inr (.reply req viewer r) => judge life b req viewer r
  | .inr (.orphan v) => if b.orphans.contains v then b else { b with orphans := ins vcode v b.orphans }
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
    | .done round => some (if b.done.contains round then b else { b with done := ins (fun r => vcode r.video * 8 + r.n) round b.done })
    | .failed _ => some b
  else if worker.forging && !b.forged.contains req then some { b with forged := ins id req b.forged }
  else none

def world (life : Auth.Lifetime) (script : Script) (worker : Worker) :
    Outside csig (Browsers × Store) where
  init := ({ todo := script }, (store worker).init)
  allow d
    | x@(.inr (.request (.report req r signature) _)) => do
      let b ← d.1.reported worker req r signature
      if r.signed workerKey signature then pure (b, ← (store worker).allow d.2 x) else pure (b, d.2)
    | .inr (.request c at_s) => (d.1.send c at_s).map (·, d.2)
    | .inl x => do pure (← d.1.answered' x, ← (store worker).allow d.2 (.inl x))
    | x => ((store worker).allow d.2 x).map (d.1, ·)
  observe d out := (d.1.observe life out, (store worker).observe d.2 out)

def answers : List (Rpc.Reply Answer) :=
  [.unknown, .answer (.found 1), .answer .missing, .answer .deleted, .answer .failed]

def workerAnswers : List (Rpc.Reply Answer) := [.unknown, .answer .accepted, .answer .failed]

/-- The request id of a report: one for each round, kind and signer, for the small bounds
checked (videos below 4, rounds below 4). -/
def reportReq (r : Report) (forged : Bool) : ReqId :=
  100 + 16 * vcode r.round.video + 4 * r.round.n + 2 * (match r with | .done _ => 0 | .failed _ => 1)
    + (if forged then 1 else 0)

def signedReport (r : Report) : SchedIn ⊕ Input :=
  .inr (.request (.report (reportReq r false) r (Transcode.signature workerKey r.round.id r.status)) 0)

def forgedReport (r : Report) : SchedIn ⊕ Input :=
  .inr (.request (.report (reportReq r true) r "forged") 0)

/-- The worker's reports of every job it was given, and, with `forging`, a done report of the
first round of `a`'s first video signed by someone else. -/
def reports (worker : Worker) (d : Browsers × Store) : List (SchedIn ⊕ Input) :=
  let rounds := (d.2.server.inner.jobs.map (·.2.id)).filter fun r =>
    !worker.silent && (worker.late || !d.1.deleted.contains r.video)
  (rounds.flatMap fun r =>
      if worker.firstFails then [signedReport (if r.n == 0 then .failed r else .done r)]
      else signedReport (.done r) :: if worker.failures then [signedReport (.failed r)] else [])
    ++ if worker.forging then [forgedReport (.done ⟨vid a 0, 0⟩)] else []

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

abbrev W (config : Config) := World (checked config) (Browsers × Store)

/-- Member `k`'s site. -/
def site {config : Config} (w : W config) (k : Fin 2) : Site := w.state.state (.inr k)

def jobs {config : Config} (w : W config) (k : Fin 2) : List (Schedule.Job Key Unit) :=
  (w.state.state (.inl k) : Schedule.State Key Unit).jobs

/-- The members' sites as a read sees them. -/
def sites {config : Config} (w : W config) : Site := Site.union [(a, site w 0), (b, site w 1)]

/-- What a read gets at this state: its one reply, and who it is for. -/
def readAt {config : Config} (w : W config) (ask : Ask) : Option (Viewer × Reply) :=
  match (sites w).read config ask.read ask.at_s with
  | [.reply _ viewer r] => some (viewer, r)
  | _ => none

/-- The reads a browser may make at this state: those whose requests are answered. -/
def asked {config : Config} (w : W config) (asks : List Ask) : List (Ask × Viewer × Reply) :=
  asks.filterMap fun ask =>
    if w.driver.1.ready ask.deps then (readAt w ask).map (ask, ·) else none

/-- What a read shows, judged as the browser sees it, with the store as it is then: the names of
the claims it breaks. -/
def readBreaks (life : Auth.Lifetime) {config : Config} (w : W config) (ask : Ask) (viewer : Viewer)
    (r : Reply) : List String :=
  let b := w.driver.1
  let cards := r.cards
  let store := w.driver.2.server.inner.store
  let mayHold (o : Object) := (store.possible o).any Option.isSome
  [("a private video is shown to someone else",
      cards.all fun c => c.visibility != .private || viewer.map (·.1) == some c.owner),
    ("a deleted video is shown", cards.all fun c => !b.deleted.contains c.id),
    ("a video is shown that the store did not say it holds",
      cards.all fun c => store.held.contains (.upload c.id)),
    ("a video is shown that the worker did not report done, signed",
      cards.all fun c => b.done.any (·.video == c.id)),
    ("a video is shown whose rendition or thumbnail the store may not hold",
      cards.all fun c => mayHold (.rendition c.id) && mayHold (.thumbnail c.id)),
    ("a session past its lifetime is let in", cards.isEmpty || liveAt life b viewer ask.at_s)].filterMap
    fun (name, ok) => if ok then none else some name

/-- The browsers' requests reach the site in the order sent; the actors in `crashing` may crash
anywhere. -/
def env (crashing : csig.Id → Bool := fun _ => true) : EnvModel csig where
  mayCrash := crashing
  restarts _ := true

/-- Only `a`'s actor crashes, for the scenarios too large for its scheduler to crash too. -/
def siteCrashes : csig.Id → Bool
  | .inr 0 => true
  | _ => false

/-- Only `a`'s actor and scheduler crash: `b` takes part only in reads and visits. -/
def aCrashes : csig.Id → Bool
  | .inr 0 | .inl 0 => true
  | _ => false

/-- One attempt for each job: the scenarios with many requests. -/
def config : Config :=
  { maxSessions := 1, maxVideos := 1, maxOwned := 1, maxPending := 1,
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
  [0, 1].all fun (k : Fin 2) =>
    let s := site w k
    s.channels.length ≤ 1 && s.videos.length ≤ config.maxVideos
      && (jobs w k).length ≤ config.maxJobs
      && s.videos.all (·.comments.length ≤ config.maxComments)
      && s.channels.all (fun (m, _) => (s.videos.filter (·.owner == m)).length ≤ config.maxOwned)
      && s.videos.all (fun v => v.comments.all fun c =>
        (v.comments.filter (·.author == c.author)).length ≤ config.maxCommentsEach)
      && s.channels.all fun (_, ch) => ch.sessions.ids.length ≤ config.maxSessions

/-- The delete of `v`'s object is not over: its job is held, or on its way to a scheduler, or
its end on its way to the owner, or the report of it not yet handed over. -/
def deleting {config : Config} (w : W config) (v : VideoId) : Bool :=
  [0, 1].any (fun (k : Fin 2) => (jobs w k).any (·.key == .delete v))
    || w.state.net.any (fun e => match e with
      | ⟨_, .inl _, .schedule _ spec⟩ => spec.key == .delete v
      | ⟨_, .inr _, .job key _⟩ => key == .delete v
      | _ => false)
    || w.state.outbox.contains (Sum.inr (Out.orphan v))

def t : Title := ⟨"t", by decide⟩
def none_ : About := ⟨"", by decide⟩
def hi : Remark := ⟨"hi", by decide⟩

def v0 : VideoId := vid a 0

/-- `a` signs in with request 1 and session 1, `b` with request 2 and session 2. -/
def signIns : List (Command × List ReqId) :=
  [(.signIn 1 a "a", []), (.signIn 2 b "b", [1])]

/-- `a` makes a public video and says it is uploaded; `b` likes it twice, and `a` likes it; `a`
deletes it. `b` watches it at any time, and again once the delete is answered. -/
def life : Script := .of <|
  signIns ++
  [ (.create 3 a 1 t none_ .public .mp4, [2]), (.uploaded 4 a 1 v0, [3]),
    (.like 6 b 2 v0 true, [4]), (.like 7 b 2 v0 true, [6]),
    (.like 8 a 1 v0 true, [7]), (.delete 9 a 1 v0, [8]) ]

def byB : Viewer := some (b, 2)
def byA : Viewer := some (a, 1)

/-- `a` makes a video and says twice that it is uploaded, the second while the first check may
be out. -/
def twice : Script := .of <|
  signIns.take 1 ++
  [ (.create 3 a 1 t none_ .public .mp4, [1]), (.uploaded 4 a 1 v0, [3]),
    (.uploaded 5 a 1 v0, [3]) ]

/-- `a` makes a private video; `b`, a stranger and `a` ask for it, for `a`'s channel and for
the feed; `b` tries to like it and comment on it. -/
def secret : Script := .of <|
  signIns ++
  [ (.create 3 a 1 t none_ .private .webm, [2]), (.uploaded 4 a 1 v0, [3]),
    (.like 11 b 2 v0 true, [4]), (.comment 12 b 2 v0 hi, [11]) ]

/-- `a` makes a video and deletes it at once, while a check may be out. -/
def gone : Script := .of <|
  signIns.take 1 ++
  [ (.create 3 a 1 t none_ .unlisted .mp4, [1]), (.uploaded 4 a 1 v0, [3]),
    (.delete 5 a 1 v0, [3]) ]

/-- `a` makes a video and deletes it. -/
def purge : Script := .of <|
  signIns.take 1 ++
  [ (.create 3 a 1 t none_ .unlisted .mp4, [1]), (.delete 4 a 1 v0, [3]) ]

/-- `a` makes a video and never says it is uploaded; its last check comes. -/
def lapsed : Script := .of <|
  signIns.take 1 ++ [ (.create 3 a 1 t none_ .public .mp4, [1]) ]

/-- `a` signs in at 0 and makes a private video, and tries to like it at 150, past its session's
lifetime of 100, and is then let in by the session of a new sign-in. -/
def expiry : Script :=
  [ (.signIn 1 a "a", 0, []), (.create 2 a 1 t none_ .private .mp4, 10, [1]),
    (.uploaded 3 a 1 v0, 20, [2]), (.like 6 a 1 v0 true, 150, [3]),
    (.signIn 7 a "a", 150, [6]) ]

def short : Config := { config with lifetime := { absolute_s := some 100 } }

/-- `a` makes a public video and says it is uploaded, and asks for it to be tried again (which
does something only if it failed). -/
def pipeline : Script := .of <|
  signIns.take 1 ++
  [ (.create 3 a 1 t none_ .public .mp4, [1]), (.uploaded 4 a 1 v0, [3]), (.retry 6 a 1 v0, [4]) ]

/-- `a` makes a public video and says it is uploaded. -/
def forgery : Script := .of <|
  signIns.take 1 ++ [ (.create 3 a 1 t none_ .public .mp4, [1]), (.uploaded 4 a 1 v0, [3]) ]

/-! The reads of the scenarios: a watch page, a channel page and the feed, by `a`, `b` or a
stranger, at any state once their requests are answered. -/

def watchBy (viewer : Viewer) (name : Nat) (deps : List ReqId := []) (at_s : Nat := 0) : Ask :=
  { name, read := .watch viewer v0, deps, at_s }

def lifeReads : List Ask := [watchBy byB 5 [4]]

def secretReads : List Ask :=
  [ watchBy byB 5 [4], watchBy none 6 [4], watchBy byA 7 [4],
    { name := 8, read := .channel byB a, deps := [4] }, { name := 9, read := .channel byA a, deps := [4] },
    { name := 10, read := .feed byB none, deps := [4] } ]

def ownerReads : List Ask := [watchBy byA 5 [3]]

def expiryReads : List Ask :=
  [ watchBy byA 4 [3] 50, watchBy byA 5 [3] 150, watchBy (some (a, 7)) 8 [7] 160 ]

/-! The small bounds' scripts: each a large one's, cut to the requests its witnesses need. -/

/-- `life` up to its likes. -/
def likes : Script := life.take 7

/-- `a` makes a public video, deletes it, and watches it. -/
def deleteShown : Script := .of <|
  signIns.take 1 ++
  [ (.create 3 a 1 t none_ .public .mp4, [1]), (.uploaded 4 a 1 v0, [3]), (.delete 6 a 1 v0, [4]) ]

/-- `pipeline` without the retry. -/
def prepared : Script := pipeline.take 3

def retried : Script := pipeline

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

def claims {config : Config} (life : Auth.Lifetime) (asks : List Ask) : List (Check.Property (W config)) :=
  let reads (claim : String) (w : W config) : Bool :=
    (asked w asks).all fun (ask, viewer, r) => !(readBreaks life w ask viewer r).contains claim
  [ .always "a private video is shown to its owner only" (reads "a private video is shown to someone else"),
    .always "a video is not shown once its delete was answered" (reads "a deleted video is shown"),
    .always "a video is shown only once the store said it holds its object"
      (reads "a video is shown that the store did not say it holds"),
    .always "a video is shown only once the worker reported it done, signed"
      (reads "a video is shown that the worker did not report done, signed"),
    .always "a video shown has a rendition and a thumbnail the store may hold"
      (reads "a video is shown whose rendition or thumbnail the store may not hold"),
    .always "a session past its lifetime lets no request in" fun w =>
      reads "a session past its lifetime is let in" w
        && !w.driver.1.broken.contains "a session past its lifetime is let in",
    .always "each like is a member's, counted once" fun w =>
      [0, 1].all fun (k : Fin 2) => (site w k).videos.all fun v => v.likes.eraseDups.length == v.likes.length,
    .always "every bound holds" fun w => bounded config w,
    .always "with no crash, a deleted video's object is deleted in the store, or reported, once \
        its job is over"
      fun w => w.crashes != 0 || w.driver.1.deleted.all fun v =>
        deleting w v || w.driver.1.gone.contains v || w.driver.1.orphans.contains v ]

/-- The reply read `name` of `asks` gets at this state, if it may be made. -/
def got {config : Config} (w : W config) (asks : List Ask) (name : Nat) : Option Reply :=
  ((asked w asks).find? (·.1.name == name)).map (·.2.2)

def showsVideo : Option Reply → Bool
  | some (.watch _ _) => true
  | _ => false

def shown {config : Config} (asks : List Ask) : Check.Property (W config) :=
  .sometimes "a video is shown" fun w => (asked w asks).any fun (_, _, r) => !r.cards.isEmpty

def confirmedOnce {config : Config} : Check.Property (W config) :=
  .sometimes "a check confirms an upload and its request is told" fun w =>
    !w.driver.1.confirmed.isEmpty

def goneWhileHeld {config : Config} : Check.Property (W config) :=
  .sometimes "a video is deleted while its object may still be in the store" fun w =>
    w.driver.1.deleted.any (deleting w)

def deletedAfterRetry {config : Config} : Check.Property (W config) :=
  .sometimes "an object is deleted in the store after its first delete failed" fun w =>
    w.driver.1.gone.contains v0 && w.driver.1.deleteTries == 2

def reported {config : Config} : Check.Property (W config) :=
  .sometimes "an object given up is reported" fun w => w.driver.1.orphans.contains v0

def checkedAgain {config : Config} : Check.Property (W config) :=
  .sometimes "a last check is tried again" fun w => w.driver.1.expireTries == 2

def twoLikes {config : Config} : Check.Property (W config) :=
  .sometimes "a video has two likes" fun w => (site w 0).videos.any (·.likes.length == 2)

def shownThenGone {config : Config} : Check.Property (W config) :=
  .sometimes "a video shown is deleted and then not shown" fun w =>
    w.driver.1.deleted.contains v0 && !showsVideo (got w ownerReads 5)

def watchedFirst {config : Config} : Check.Property (W config) :=
  .sometimes "a private video is watched by its owner inside its session's lifetime" fun w =>
    showsVideo (got w expiryReads 4)

def watchedAgain {config : Config} : Check.Property (W config) :=
  .sometimes "a private video is watched by its owner in a new session, past the first's lifetime" fun w =>
    showsVideo (got w expiryReads 8)

def ownerWatches {config : Config} : Check.Property (W config) :=
  .sometimes "a private video is watched by its owner" fun w => showsVideo (got w secretReads 7)

def othersAsk {config : Config} : Check.Property (W config) :=
  .sometimes "a private video is ready, and asked for by another member and by a stranger" fun w =>
    (site w 0).videos.any (·.status.isReady) && got w secretReads 5 == some .notFound
      && got w secretReads 6 == some .notFound

def lapsedReady {config : Config} : Check.Property (W config) :=
  .sometimes "an upload never confirmed is made ready by its last check, and shown" fun w =>
    showsVideo (got w ownerReads 5)

def lapsedOut {config : Config} : Check.Property (W config) :=
  .sometimes "an upload never confirmed is taken out by its last check" fun w =>
    (site w 0).next == 1 && (site w 0).videos.isEmpty

def preparing {config : Config} : Check.Property (W config) :=
  .sometimes "a video being prepared is shown so to its owner" fun w =>
    got w ownerReads 5 == some (.preparing v0 "t" .transcoding)

def failedShown {config : Config} : Check.Property (W config) :=
  .sometimes "a video whose transcode failed is shown so to its owner" fun w =>
    got w ownerReads 5 == some (.preparing v0 "t" .failed)

def shownAfterRetry {config : Config} : Check.Property (W config) :=
  .sometimes "a video is shown after its owner tried its transcode again" fun w =>
    w.driver.1.done.contains ⟨v0, 1⟩ && showsVideo (got w ownerReads 5)

def readyAfterRetry {config : Config} : Check.Property (W config) :=
  .sometimes "a video is ready after its owner tried its transcode again" fun w =>
    w.driver.1.done.contains ⟨v0, 1⟩ && (site w 0).videos.any fun v => v.id == v0 && v.status matches .ready ..

def forgedRefused {config : Config} : Check.Property (W config) :=
  .sometimes "a forged report is refused" fun w => !w.driver.1.refused.isEmpty

def deliveredTwice {config : Config} : Check.Property (W config) :=
  .sometimes "a report is delivered twice" fun w => w.driver.2.server.delivered.any (·.2 == 2)

/-- No video is transcoding: each confirmed upload is ready or failed. -/
def settled {config : Config} (w : W config) : Bool :=
  [0, 1].all fun (k : Fin 2) => (site w k).videos.all fun v => !(v.status matches .transcoding ..)

/-- The site of `config` checked against `script`, its reads `asks` judged at every state; its
sessions are judged by `life`, the site's own unless a seeded bug says otherwise. -/
def check (config : Config) (script : Script) (asks : List Ask)
    (witnesses : List (Check.Property (W config))) (maxCrashes : Nat := 1)
    (life : Auth.Lifetime := config.lifetime) (crashing : csig.Id → Bool := aCrashes)
    (worker : Worker := {}) (live : Bool := false) :=
  Check.system (checked config)
    { env := env crashing, driver := (world life script worker).driver (samples worker), maxCrashes }
    (claims life asks ++ witnesses) { maxStates := 3000000, checkDeadlock := live, terminal := settled }

def trusting : Config := { config with trustBrowser := true }
def hasty : Config := { config with readyOnTimeout := true }
def credulous : Config := { config with trustUnsigned := true }

/-- The first violation's name and length, if the report has one. -/
def found {S L : Type} (r : Check.Report S L) : Option (String × Nat) :=
  match r.failure with
  | some (.violated p t) => some (p, t.steps.length)
  | _ => none

/-- One member cannot fill another's site: their videos, and their comments on one video, are
bounded; a video's owner takes out anyone's comment on it. -/
def capTests : List (String × Bool) :=
  let cfg : Config := { maxOwned := 2, maxCommentsEach := 2, workerKey }
  let video (n : Nat) (owner : Who) : Video :=
    { id := vid owner n, owner, title := t, about := none_, visibility := .public, media := .mp4,
      status := .ready 1, made_s := 0 }
  let s : Site := { videos := [video 1 a, video 0 a], next := 2 }
  let says (r : Site × List Out) (reply : Reply) := r.2 == [.reply 9 none reply]
  let c (id : Nat) (author : Who) : Comment := { id, author, name := "", body := hi }
  let x := { video 0 a with comments := [c 0 b, c 1 b] }
  let other : Who := ⟨name "id", name "c"⟩
  [ ("caps: a member with maxOwned videos is refused another",
      says (s.create cfg 9 none a t none_ .public .mp4 0) .tooMany
        && ((({ } : Site).create cfg 9 none b t none_ .public .mp4 0).1.videos.length == 1)),
    ("caps: a member with maxCommentsEach comments on a video is refused another, another member is not",
      says (s.comment cfg 9 none b "" x hi) (.tooManyComments v0)
        && says (s.comment cfg 9 none other "" x hi) (.commented v0)),
    ("caps: a video's owner takes out another member's comment on it, a third member cannot",
      says (s.uncomment 9 none a x 0) (.uncommented v0) && says (s.uncomment 9 none other x 0) .notFound
        && says (s.uncomment 9 none b x 1) (.uncommented v0)),
    ("calls: the model's call of an attempt names its key and attempt back",
      [Key.check (vid a 1) 9, .expire (vid b 1), .delete v0, .check v0 63, .transcode ⟨vid b 1, 7⟩,
        .transcode ⟨v0, 0⟩].all fun k =>
        (List.range 8).all fun n => attemptOf (callOf k n) == some (k, n)),
    ("routes: an input goes to the actor of the member it is about, and a visit to the owner's",
      (Input.request (.like 1 b 2 v0 true) 0).member == b && (Input.visit (.like 1 byB b v0 true)).member == a
        && (Input.job (.delete v0) .scheduled).member == a) ]

/-- A check by its name: the report it prints, and whether it passed. -/
structure Run where
  name : String
  result : Unit → String × Bool

def passes {config : Config} (r : Check.Report (W config) (Event csig)) (witnesses : Nat) :
    String × Bool :=
  (r.renderSystem, r.ok && r.witnesses.length == witnesses)

/-- A seeded bug, found as a violation of `claim`. -/
def seeded {config : Config} (r : Check.Report (W config) (Event csig)) (claim : String) :
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
      fun () => passes (check config likes lifeReads [shown lifeReads, twoLikes] (worker := quiet)) 2⟩,
    ⟨"check: a video shown, deleted and asked for again, with no crash",
      fun () => passes (check config deleteShown ownerReads [shown ownerReads, goneWhileHeld, shownThenGone] 0
        (worker := { quiet with everyAnswer := false })) 3⟩,
    ⟨"check: a private video, with the store's faults and a crash anywhere",
      fun () => passes (check config secret secretReads [ownerWatches, othersAsk] (worker := quiet)) 2⟩,
    ⟨"check: a video deleted while its check may be out, the store answering found or unknown, and a crash of the site anywhere",
      fun () => passes (check config gone ownerReads [goneWhileHeld] (crashing := siteCrashes)
        (worker := { silent := true, everyAnswer := false })) 1⟩,
    ⟨"check: a second check while the first may be out, with no crash",
      fun () => passes (check config twice ownerReads [confirmedOnce] 0 (worker := { silent := true })) 1⟩,
    ⟨"check: a delete tried twice, deleted or reported, and a crash anywhere",
      fun () => passes (check deleteTwice purge ownerReads [goneWhileHeld, deletedAfterRetry, reported]
        (worker := quiet)) 3⟩,
    ⟨"check: an upload never confirmed, checked a last time, twice, and a crash anywhere",
      fun () => passes (check lapsing lapsed ownerReads [lapsedReady, lapsedOut, checkedAgain]
        (worker := quiet)) 3⟩,
    ⟨"check: a session past its lifetime lets nothing in, and a new sign-in does",
      fun () => passes (check short expiry expiryReads [watchedFirst, watchedAgain] (worker := quiet)) 2⟩,
    ⟨"check: the pipeline, with jobs and reports late, failed or never, and a crash of the site anywhere",
      fun () => passes (check config prepared ownerReads [shown ownerReads, preparing, failedShown]
        (crashing := siteCrashes) (worker := { faulty with startFaults := false })) 3⟩,
    ⟨"check: reports delivered twice and forged beside the worker's, and a crash anywhere",
      fun () => passes (check config forgery ownerReads [shown ownerReads, forgedRefused, deliveredTwice]
        (worker := forged)) 3⟩,
    ⟨"check: with no crash, every run that cannot go on leaves each confirmed upload ready or failed",
      fun () => passes (check config prepared ownerReads [shown ownerReads, failedShown] 0 (worker := faulty)
        (live := true)) 2⟩,
    ⟨"check: with no crash, a transcode that failed is tried again, and every run that cannot go on leaves the upload ready or failed",
      fun () => passes (check config retried ownerReads [readyAfterRetry] 0
        (worker := { faulty with firstFails := true }) (live := true)) 1⟩ ]

/-- The scenarios at large bounds. -/
def largeRuns : List Run :=
  [ ⟨"check: a video's life, with the store's faults and a crash anywhere",
      fun () => passes (check config life lifeReads [shown lifeReads, goneWhileHeld, twoLikes]
        (worker := quiet) (crashing := fun _ => true)) 3⟩,
    ⟨"check: a private video, with the store's faults and two crashes anywhere",
      fun () => passes (check config secret secretReads [ownerWatches, othersAsk] (worker := quiet)
        (maxCrashes := 2) (crashing := fun _ => true)) 2⟩,
    ⟨"check: a video deleted while its check may be out, and a crash of the site anywhere",
      fun () => passes (check config gone ownerReads [goneWhileHeld] (crashing := siteCrashes)
        (worker := { silent := true })) 1⟩,
    ⟨"check: a second check while the first may be out, and a crash of the site anywhere",
      fun () => passes (check config twice ownerReads [confirmedOnce] (crashing := siteCrashes)
        (worker := { silent := true })) 1⟩,
    ⟨"check: a delete tried twice, deleted or reported, and two crashes anywhere",
      fun () => passes (check deleteTwice purge ownerReads [goneWhileHeld, deletedAfterRetry, reported]
        (worker := quiet) (maxCrashes := 2)) 3⟩,
    ⟨"check: an upload never confirmed, checked a last time, twice, and a crash anywhere",
      fun () => passes (check lapsing lapsed ownerReads [lapsedReady, lapsedOut, checkedAgain] (worker := quiet)) 3⟩,
    ⟨"check: a session past its lifetime lets nothing in, and a new sign-in does, with two crashes anywhere",
      fun () => passes (check short expiry expiryReads [watchedFirst, watchedAgain] (worker := quiet)
        (maxCrashes := 2)) 2⟩,
    ⟨"check: the pipeline, with jobs and reports late, failed or never, a retry, and a crash of the site anywhere",
      fun () => passes (check config pipeline ownerReads [shown ownerReads, preparing, failedShown, shownAfterRetry]
        (crashing := siteCrashes) (worker := { faulty with startFaults := false })) 4⟩,
    ⟨"check: reports delivered twice and forged beside the worker's, and a crash anywhere",
      fun () => passes (check config forgery ownerReads [shown ownerReads, forgedRefused, deliveredTwice]
        (worker := forged) (crashing := fun _ => true)) 3⟩,
    ⟨"check: with no crash, every run that cannot go on leaves each confirmed upload ready or failed",
      fun () => passes (check config pipeline ownerReads [shown ownerReads, failedShown, shownAfterRetry] 0
        (worker := faulty) (live := true)) 3⟩ ]

/-- Seeded bugs, each found at the bounds of `lake test`. -/
def seededRuns : List Run :=
  [ ⟨"check, seeded: trusting the browser shows a video the store never confirmed",
      fun () => seeded (check trusting likes lifeReads [] 0 (worker := quiet)) unconfirmed⟩,
    ⟨"check, seeded: a check that timed out taken as found shows such a video",
      fun () => seeded (check hasty likes lifeReads [] 0 (worker := quiet)) unconfirmed⟩,
    ⟨"check, seeded: sessions that never end let a request in past the lifetime",
      fun () => seeded (check { short with lifetime := {} } expiry expiryReads [] 0 short.lifetime (worker := quiet))
        "a session past its lifetime lets no request in"⟩,
    ⟨"check, seeded: a report taken unsigned shows a video the worker never reported done",
      fun () => seeded (check credulous forgery ownerReads [] 0 (worker := forged))
        "a video is shown only once the worker reported it done, signed"⟩ ]

def runs : Size → List Run
  | .small => smallRuns ++ seededRuns
  | .large => largeRuns

/-- The checks of `size` whose names contain one of `only`, or all of them. They share nothing,
so up to `jobs` run at once, each on a thread of its own; each report is printed in order. -/
def run (size : Size := .small) (only : List String := []) (jobs : Nat := 4)
    (quiet : Bool := false) : IO (List (String × Bool)) := do
  let chosen := (runs size).filter fun r => only.isEmpty || only.any (r.name.contains ·)
  let mut results := []
  let n := max jobs 1
  for batch in (List.range ((chosen.length + n - 1) / n)).map fun i => (chosen.drop (i * n)).take n do
    let tasks := batch.map fun r => Task.spawn (prio := .dedicated) fun () => r.result ()
    for (r, task) in batch.zip tasks do
      let (report, ok) ← IO.wait task
      unless quiet do
        IO.println s!"{r.name}: {report}"
        (← IO.getStdout).flush
      results := results ++ [(r.name, ok)]
  return results

end Videos.Check
