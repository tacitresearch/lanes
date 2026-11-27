/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.System

/-!
# Model checks

The site beside two members' browsers, which follow a script, and beside the model of an object
store (`Lanes.ObjectStore`, D71), which answers each call at most once, late, never, refused or
`unknown`, and whose writes that were not answered may take effect at any moment or never. The
browser's upload is a write the site grants and never hears the answer to (the presigned link,
the model's `granted`): the model may let it land before the site asks, after, or never. The
site's `HEAD` is the model's head, and its delete the model's delete. The site's actor may crash
and start again anywhere.

What the browsers see is judged as they see it: no private video shown to anyone but its owner;
nothing shown to a request made after its delete was answered; nothing shown that the store did
not first say it holds. The state is judged too: each like counted once, every bound. Every
`always` has `sometimes` beside it (rule 5.3).

Three seeded bugs, each found: a video made ready because the browser says so, a check the
store did not answer in time taken as found, and sessions that never end.
-/

namespace Videos.Check

open Lanes

instance : sig.Inspect := {}
instance (config : Config) : (system config).Inspect := {}

/-- The model's state: what the store may hold, for videos' objects. -/
abbrev Store := Rpc.State (ObjectStore.State VideoId Unit)

/-- The browser's put of video `v`'s object, granted by the link the site handed out, as the
model's call: a call of its own, which the site never sees answered. -/
def uploadCall (v : VideoId) : Nat := 1000 + v

def storeAnswer : StoreAnswer → ObjectStore.Answer Unit
  | .found _ => .present
  | .missing => .missing
  | .deleted => .deleted
  | .failed => .refused

def port : Rpc.Port sig (ObjectStore.Request VideoId Unit) (ObjectStore.Answer Unit) Empty where
  called
    | .reply _ _ (.created v _ _) => some ⟨uploadCall v, 0, .granted v ()⟩
    | .store ⟨id, deadline, .head v⟩ => some ⟨id, deadline, .head v⟩
    | .store ⟨id, deadline, .delete v⟩ => some ⟨id, deadline, .delete v⟩
    | _ => none
  replied
    | .store call .unknown => some (call, .unknown)
    | .store call (.answer a) => some (call, .answer (storeAnswer a))
    | .request .. => none

def store : Outside sig Store := Rpc.outside port ObjectStore.server

/-- A request, the time it arrives, and the requests whose answers it waits for. -/
abbrev Script := List (Command × Nat × List ReqId)

/-- Requests that all arrive at time 0. -/
def Script.of (l : List (Command × List ReqId)) : Script := l.map fun (c, deps) => (c, 0, deps)

/-- The browsers: what they have still to send, what they were answered, and what they saw go
wrong. -/
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

def world (life : Auth.Lifetime) (script : Script) : Outside sig (Browsers × Store) where
  init := ({ todo := script }, store.init)
  allow d
    | .request c at_s => (d.1.send c at_s).map (·, d.2)
    | x => (store.allow d.2 x).map (d.1, ·)
  observe d out :=
    let b := match out with
      | .reply req viewer r => judge life d.1 d.2 req viewer r
      | _ => d.1
    (b, store.observe d.2 out)

def answers : List (Rpc.Reply StoreAnswer) :=
  [.unknown, .answer (.found 1), .answer .missing, .answer .deleted, .answer .failed]

def samples (d : Browsers × Store) : List Input :=
  (d.1.todo.filterMap fun (c, at_s, deps) => if d.1.ready deps then some (.request c at_s) else none)
    ++ (d.2.pending.filter (· < 1000)).flatMap fun id => answers.map (.store id)

abbrev W (config : Config) := World (system config) (Browsers × Store)

def site {config : Config} (w : W config) : Site := w.state.state ()

/-- The browsers' requests reach the site in the order sent; the actor may crash anywhere. -/
def env : EnvModel sig where
  mayCrash _ := true
  restarts _ := true

def config : Config :=
  { maxMembers := 2, maxSessions := 1, maxVideos := 2, maxOwned := 1, maxPending := 1,
    maxComments := 2, maxCommentsEach := 1, maxDeleting := 1, maxAttempts := 2, pageSize := 1 }

def bounded (config : Config) (s : Site) : Bool :=
  s.channels.length ≤ config.maxMembers && s.videos.length ≤ config.maxVideos
    && s.deleting.length ≤ config.maxDeleting
    && s.videos.all (·.comments.length ≤ config.maxComments)
    && s.channels.all (fun (m, _) => (s.videos.filter (·.owner == m)).length ≤ config.maxOwned)
    && s.videos.all (fun v => v.comments.all fun c =>
      (v.comments.filter (·.author == c.author)).length ≤ config.maxCommentsEach)
    && s.channels.all fun (_, ch) => ch.sessions.ids.length ≤ config.maxSessions

def t : Title := ⟨"t", by decide⟩
def none_ : About := ⟨"", by decide⟩
def hi : Remark := ⟨"hi", by decide⟩

/-- Member 0 signs in with request 1 and session 1, member 1 with request 2 and session 2. -/
def signIns : List (Command × List ReqId) :=
  [(.signIn 1 "id" "a" "a", []), (.signIn 2 "id" "b" "b", [1])]

/-- `0` makes a public video and says it is uploaded, twice if need be; `1` watches it, likes it
twice, and `0` likes it; `0` deletes it, and `1` asks for it again, and for the feed. -/
def life : Script := .of <|
  signIns ++
  [ (.create 3 0 1 t none_ .public .mp4, [2]), (.uploaded 4 0 1 0, [3]), (.uploaded 5 0 1 0, [4]),
    (.watch 6 (some (1, 2)) 0, [5]), (.like 7 1 2 0 true, [6]), (.like 8 1 2 0 true, [7]),
    (.like 9 0 1 0 true, [8]), (.delete 10 0 1 0, [9]), (.watch 11 (some (1, 2)) 0, [9]),
    (.watch 12 (some (1, 2)) 0, [10]), (.feed 13 (some (1, 2)) none, [12]) ]

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

/-- `0` signs in at 0 and makes a private video; it watches it at 50, inside its session's
lifetime of 100, and at 150, past it, when it also tries to like it and is then let in by the
session of a new sign-in. -/
def expiry : Script :=
  [ (.signIn 1 "id" "a" "a", 0, []), (.create 2 0 1 t none_ .private .mp4, 10, [1]),
    (.uploaded 3 0 1 0, 20, [2]), (.watch 4 (some (0, 1)) 0, 50, [3]),
    (.watch 5 (some (0, 1)) 0, 150, [4]), (.like 6 0 1 0 true, 150, [5]),
    (.signIn 7 "id" "a" "a", 150, [6]), (.watch 8 (some (0, 7)) 0, 160, [7]) ]

def short : Config := { config with lifetime := { absolute_s := some 100 } }

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
    .always "every bound holds" fun w => bounded config (site w) ]

def shown {config : Config} : Check.Property (W config) :=
  .sometimes "a video is shown" fun w => !w.driver.1.watched.isEmpty

def goneWhileHeld {config : Config} : Check.Property (W config) :=
  .sometimes "a video is deleted while its object may still be in the store" fun w =>
    !w.driver.1.deleted.isEmpty && !(site w).deleting.isEmpty

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

/-- The site of `config` checked against `script`; its sessions are judged by `life`, the
site's own unless a seeded bug says otherwise. -/
def check (config : Config) (script : Script) (witnesses : List (Check.Property (W config)))
    (maxCrashes : Nat := 1) (life : Auth.Lifetime := config.lifetime) :=
  Check.system (system config) { env, driver := (world life script).driver samples, maxCrashes }
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
        && says (s.uncomment 9 none 1 v 1) (.uncommented 0)) ]

def run : IO (List (String × Bool)) := do
  let life' := check config life [shown, goneWhileHeld, twoLikes]
  IO.println s!"life: {life'.renderSystem}"
  let secret' := check config secret [ownerWatches, othersAsk]
  IO.println s!"secret: {secret'.renderSystem}"
  let gone' := check config gone [goneWhileHeld]
  IO.println s!"gone: {gone'.renderSystem}"
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
    ("check: a session past its lifetime lets nothing in, and a new sign-in does",
      expiry'.ok && expiry'.complete && expiry'.witnesses.length == 1),
    ("check, seeded: trusting the browser shows a video the store never confirmed",
      trusted.any (·.1 == unconfirmed)),
    ("check, seeded: a check that timed out taken as found shows such a video",
      rushed.any (·.1 == unconfirmed)),
    ("check, seeded: sessions that never end let a request in past the lifetime",
      endless.any (·.1 == "a session past its lifetime lets no request in")) ]

end Videos.Check
