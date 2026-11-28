/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
# The spec

A video site, as if inputs were handled one at a time. Members sign in with another service
(Google, GitHub) and each has a channel. A member makes a video record, which starts `pending`,
and gets a form to post the video to the store (S3) from the browser: the bytes never pass
through the site. The browser then says it is done, the site has the store asked whether the
object is there (a `HEAD`); a `found` answer confirms the upload, and the video is
`transcoding`: a worker outside the site (`Lanes.Transcode`) is given a job to write a playable
rendition and a thumbnail beside the upload. Only the worker's report that the job is done,
signed with the key the site shares with it, makes the video `ready`; a report that it failed,
or a job the worker could not be given, makes it `failed`, which its owner may try again. Ready
videos are watched (the rendition, with the thumbnail as its poster), liked once per member,
commented on and listed in a feed; a video is public (in the feed and its channel), unlisted (by
its link) or private (its owner only). Deleting a video takes its record out at once and then
deletes its objects in the store.

The site calls the store and the worker through the scheduler beside it (`Lanes.Schedule`,
D79), which holds each call as a job, retries it with a backoff and keeps it across a restart.
There are four kinds (`Key`): the check a member asked for; the last check of an upload never
confirmed, a day after its record was made, which confirms it if the store has it and takes the
record out if not; the start of a transcode, a round of a video's, which gives the worker its
job; and the delete of a deleted video's objects, retried until the store takes it and reported
(`Out.orphan`) if it never does. The worker's reports come as requests (webhooks), each with its
signature.

The whole state is one value, `Site`, and one input is one call of `Site.handle`: a request, or
the scheduler's word on a job. A start of the actor is one call of `Site.recover`. The system
runs these functions in one actor (`Videos.System`), so what is proved of them (`Videos.Proofs`)
is proved of the code that runs.

Every bound is in `Config` (rule 2.6), with what happens at it: a sign-in past `maxMembers` is
`full`, a video past `maxVideos`, past its member's `maxOwned` or past
`maxPending` uploads not yet confirmed is `tooMany`, a comment past `maxComments` or past its
member's `maxCommentsEach` on the video is `tooManyComments`, a job past `maxJobs` is refused by
the scheduler: a check is then `unconfirmed`, a transcode `failed`, a delete given up and
reported. The bounds of one member are far below those of the site, so that one member cannot
fill the site's.
-/

namespace Videos

open Lanes

abbrev ReqId := Nat
abbrev Member := Nat
/-- A session is named by the id of the sign-in request that opened it, which is never reused. -/
abbrev Sid := Nat
abbrev VideoId := Nat
abbrev CommentId := Nat

def Title.valid (s : String) : Bool := 0 < s.length && s.length ≤ 100
def About.valid (s : String) : Bool := s.length ≤ 2000
def Remark.valid (s : String) : Bool := 0 < s.length && s.length ≤ 500

abbrev Title := {s : String // Title.valid s}
abbrev About := {s : String // About.valid s}
abbrev Remark := {s : String // Remark.valid s}

lanes_data inductive Visibility where
  /-- In the feed and on the channel. -/
  | public
  /-- Watched by whoever has its link; listed nowhere but on its owner's own channel page. -/
  | unlisted
  /-- Its owner's alone. -/
  | private
  deriving DecidableEq, Repr, Hashable, Codable

/-- What an upload may be. The upload form's policy names it, so the browser must send it. -/
lanes_data inductive Media where
  | mp4
  | webm
  | quicktime
  deriving DecidableEq, Repr, Hashable, Codable

def Media.mime : Media → String
  | .mp4 => "video/mp4"
  | .webm => "video/webm"
  | .quicktime => "video/quicktime"

lanes_data inductive Status where
  /-- Waiting for the browser's upload, or for the member to say it is done. -/
  | pending
  /-- The store is asked, by the check job of `waiter`, whether the object is there; `waiter`
  is told. -/
  | checking (waiter : ReqId)
  /-- The store said the upload is there, of `size` bytes, and round `round` of its transcode
  is the worker's. -/
  | transcoding (size round : Nat)
  /-- The worker said, signed, that the rendition and the thumbnail are written. -/
  | ready (size : Nat)
  /-- Round `round` of its transcode failed: the worker said so, or could not be given it. -/
  | failed (size round : Nat)
  deriving DecidableEq, Repr, Hashable, Codable

def Status.isReady : Status → Bool
  | .ready _ => true
  | _ => false

/-- Waiting for the upload: not yet confirmed by the store. -/
def Status.awaiting : Status → Bool
  | .pending | .checking _ => true
  | _ => false

/-- What a video not ready is waiting for, as its owner is shown it. -/
lanes_data inductive Stage where
  | upload
  | transcoding
  | failed
  deriving DecidableEq, Repr, Hashable, Codable

def Status.stage? : Status → Option Stage
  | .pending | .checking _ => some .upload
  | .transcoding .. => some .transcoding
  | .failed .. => some .failed
  | .ready _ => none

lanes_data structure Comment where
  id : CommentId
  author : Member
  body : {s : String // Remark.valid s}
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data structure Video where
  id : VideoId
  owner : Member
  title : {s : String // Title.valid s}
  about : {s : String // About.valid s}
  visibility : Visibility
  media : Media
  status : Status
  /-- The members who like it. -/
  likes : List Member := []
  /-- Oldest first. -/
  comments : List Comment := []
  deriving DecidableEq, Repr, Hashable, Codable

/-- A member: who signed in, by the other service's issuer and subject, which do not change; the
name shown; the sessions open. -/
lanes_data structure Channel where
  issuer : String
  subject : String
  name : String
  sessions : Auth.Sessions := {}
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data structure Site where
  channels : List (Member × Channel) := []
  /-- Newest first. -/
  videos : List Video := []
  /-- The id the next video gets: none is used twice. -/
  next : VideoId := 0
  nextComment : CommentId := 0
  deriving DecidableEq, Repr, Hashable, Codable

/-! ## Inputs and outputs -/

/-- Round `n` of the transcode of `video`: the worker's job, by `Round.id`. A new round is a new
job, so a report of an old one is told apart. -/
lanes_data structure Round where
  video : VideoId
  n : Nat
  deriving DecidableEq, Repr, Hashable, Codable

/-- The job's id on the wire. -/
def Round.id (r : Round) : String := s!"{r.video}.{r.n}"

/-- What the worker reports of a round. The keys it wrote are the site's own, so the site does not
read them. -/
lanes_data inductive Report where
  | done (round : Round)
  | failed (round : Round)
  deriving DecidableEq, Repr, Hashable, Codable

def Report.round : Report → Round
  | .done r | .failed r => r

def Report.status : Report → String
  | .done _ => "done"
  | .failed _ => "failed"

/-- Whether `signature` is the worker's for this report, under the key the site shares with it
(`Transcode.verify`). -/
def Report.signed (key : Hmac.Key) (r : Report) (signature : String) : Bool :=
  Transcode.verify key r.round.id r.status signature

/-- What the site asks the store or the worker. Video `v`'s upload is at the key `videos/<v>`,
its rendition and its thumbnail beside it. -/
lanes_data inductive Op where
  | head (video : VideoId)
  /-- The upload, the rendition and the thumbnail. -/
  | delete (video : VideoId)
  /-- Give the worker the job of round `round`. -/
  | transcode (round : Round)
  deriving DecidableEq, Repr, Hashable, Codable

/-- The store's or the worker's answer, as the site reads it. -/
lanes_data inductive Answer where
  | found (size : Nat)
  | missing
  | deleted
  /-- The worker took the job. -/
  | accepted
  /-- Anything else: an error, which may have come after the operation took effect. -/
  | failed
  deriving DecidableEq, Repr, Hashable, Codable

/-- A job of the scheduler, by what it is for. The key says what the job asks the store
(`Key.op`), so no job can ask about another video than its key names. -/
lanes_data inductive Key where
  /-- The check that request `req` asked for. -/
  | check (video : VideoId) (req : ReqId)
  /-- The last check of an upload never confirmed. -/
  | expire (video : VideoId)
  /-- The start of round `round` of a video's transcode. -/
  | transcode (round : Round)
  /-- The delete of a deleted video's objects. -/
  | delete (video : VideoId)
  deriving DecidableEq, Repr, Hashable, Codable

def Key.op : Key → Op
  | .check v _ | .expire v => .head v
  | .transcode r => .transcode r
  | .delete v => .delete v

/-- What the scheduler says of a job: scheduled, refused, or how it ended. -/
abbrev Outcome := Schedule.Outcome Unit Answer

/-- A job given up: refused by the scheduler, or out of attempts or time. -/
def Outcome.givenUp : Outcome → Bool
  | .failed .. | .refused _ => true
  | _ => false

/-- A viewer: the member and the session a request's cookie names, when it names one. -/
abbrev Viewer := Option (Member × Sid)

/-- `member` and `session` are never read from a request's body: the bridge takes them from a
session cookie it has verified. -/
lanes_data inductive Command where
  /-- The sign-in verified this identity (`Lanes.OAuth`). -/
  | signIn (req : ReqId) (issuer subject name : String)
  | signOut (req : ReqId) (member : Member) (session : Sid)
  /-- The upload form is signed for the time the request arrived. -/
  | create (req : ReqId) (member : Member) (session : Sid) (title : {s : String // Title.valid s})
    (about : {s : String // About.valid s}) (visibility : Visibility) (media : Media)
  /-- The browser says the upload is done. -/
  | uploaded (req : ReqId) (member : Member) (session : Sid) (video : VideoId)
  | watch (req : ReqId) (viewer : Option (Member × Sid)) (video : VideoId)
  /-- `on` to like, off to take the like back. -/
  | like (req : ReqId) (member : Member) (session : Sid) (video : VideoId) (on : Bool)
  | comment (req : ReqId) (member : Member) (session : Sid) (video : VideoId)
    (body : {s : String // Remark.valid s})
  | uncomment (req : ReqId) (member : Member) (session : Sid) (video : VideoId)
    (comment : CommentId)
  | delete (req : ReqId) (member : Member) (session : Sid) (video : VideoId)
  /-- The newest public videos older than `before`, if given. -/
  | feed (req : ReqId) (viewer : Option (Member × Sid)) (before : Option VideoId)
  | channel (req : ReqId) (viewer : Option (Member × Sid)) (whose : Member)
  /-- The owner asks for a failed transcode to be tried again. -/
  | retry (req : ReqId) (member : Member) (session : Sid) (video : VideoId)
  /-- The worker's report, posted to the site, with the signature it came with. -/
  | report (req : ReqId) (r : Report) (signature : String)
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Input where
  /-- A request, and when it arrived, in seconds since the epoch: the server's clock, which
  `arrive` writes (`Web.stamp`), so it is in the journal and the same on replay. A session is
  judged at that time, links are signed for it, and the scheduler learns it. -/
  | request (c : Command) (at_s : Nat)
  /-- The scheduler's word on the job of `key`. -/
  | job (key : Key) (outcome : Schedule.Outcome Unit Answer)
  /-- A notice of the scheduler. The site schedules only calls, so none comes. -/
  | noticed (key : Key)
  deriving DecidableEq, Repr, Hashable, Codable

/-- When an input arrived: a request's time; the scheduler's word carries none. -/
def Input.at_s : Input → Nat
  | .request _ at_s => at_s
  | _ => 0

/-- A video as a list shows it. -/
lanes_data structure Card where
  id : VideoId
  owner : Member
  ownerName : String
  title : String
  visibility : Visibility
  likes : Nat
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data structure Remarked where
  id : CommentId
  author : Member
  authorName : String
  body : String
  deriving DecidableEq, Repr, Hashable, Codable

/-- A video as its page shows it. -/
lanes_data structure View where
  card : Card
  about : String
  media : Media
  /-- Whether the viewer likes it. -/
  liked : Bool
  comments : List Remarked
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Reply where
  /-- A session opened at `at_s`: the bridge signs its cookie then. -/
  | signedIn (member : Member) (session : Sid) (at_s : Nat)
  | full
  | signedOut
  | noSession
  /-- The record is made: the bridge signs the form for the upload at `at_s`. -/
  | created (video : VideoId) (media : Media) (at_s : Nat)
  | tooMany
  /-- The store has the upload: its transcode is begun. -/
  | confirmed (video : VideoId)
  /-- The store has no such object: the video stays pending. -/
  | notUploaded (video : VideoId)
  /-- The store did not say, or another check took this one's place: try again. -/
  | unconfirmed (video : VideoId)
  /-- The bridge signs the link to watch it at `at_s`. -/
  | watch (view : View) (at_s : Nat)
  /-- No such video, or none this viewer may see: which one is not said. -/
  | notFound
  /-- To its owner, a video not ready, and what it waits for. -/
  | preparing (video : VideoId) (title : String) (stage : Stage)
  | retrying (video : VideoId)
  /-- A report taken; one of a round no longer under way is taken and changes nothing. -/
  | reported
  /-- A report whose signature is not the worker's. -/
  | forged
  | liked (video : VideoId) (likes : Nat) (on : Bool)
  | commented (video : VideoId)
  | tooManyComments (video : VideoId)
  | uncommented (video : VideoId)
  | deleted (video : VideoId)
  | feed (cards : List Card) (next : Option VideoId)
  /-- A member's videos; `pending`, the titles of those not ready and what each waits for, only
  to their owner. -/
  | channel (whose : Member) (name : String) (cards : List Card)
    (pending : List (VideoId × String × Stage))
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Out where
  /-- The answer to request `req`, for the session that made it, if it is live. -/
  | reply (req : ReqId) (viewer : Option (Member × Sid)) (r : Reply)
  /-- A job for the scheduler, at `now_ms`, the time of the request that asks for it. -/
  | schedule (now_ms : Nat) (spec : Schedule.Spec Key Unit)
  | cancel (key : Key)
  /-- The object of a deleted video that the store did not say it deleted, given up on. -/
  | orphan (video : VideoId)
  deriving DecidableEq, Repr, Hashable, Codable

/-- The settings the spec and the system are built with. Every bound is here (rule 2.6). -/
structure Config where
  maxMembers : Nat := 10000
  maxSessions : Nat := 4
  /-- How long a session lets requests in after its sign-in. The site does not record each use
  (`Auth.Sessions.touch`), so an idle limit would count from the sign-in too. -/
  lifetime : Auth.Lifetime := { absolute_s := some (30 * 86400) }
  maxVideos : Nat := 10000
  /-- Videos of one member, ready or not. -/
  maxOwned : Nat := 100
  /-- Videos of one member not yet ready. -/
  maxPending : Nat := 4
  maxComments : Nat := 200
  /-- Comments of one member on one video. -/
  maxCommentsEach : Nat := 10
  /-- The key the site shares with the worker, which signs its reports. -/
  workerKey : Hmac.Key
  /-- The jobs the scheduler holds: checks, last checks, transcodes and deletes. -/
  maxJobs : Nat := 30000
  /-- How a check is retried. A member waits for it, so it is short. -/
  checkRetry : Schedule.Retry :=
    { maxAttempts := 2, deadline_ms := 5000, base_ms := 500, cap_ms := 500, jitter_ms := 250 }
  /-- How the start of a transcode is retried: for about five minutes. -/
  transcodeRetry : Schedule.Retry :=
    { maxAttempts := 6, deadline_ms := 10000, base_ms := 1000, cap_ms := 120000, jitter_ms := 1000 }
  /-- How a delete is retried: for about ten minutes. -/
  deleteRetry : Schedule.Retry :=
    { maxAttempts := 10, deadline_ms := 10000, base_ms := 1000, cap_ms := 300000, jitter_ms := 1000 }
  /-- How long after its record is made an upload not confirmed is checked a last time, and taken
  out if the store does not have it. Far past the upload form's fifteen minutes, so no upload
  begun with it is still under way. `none`: never. -/
  pending_s : Option Nat := some 86400
  pageSize : Nat := 12
  /-- A seeded bug: a video is ready when the browser says it is uploaded, without asking. -/
  trustBrowser : Bool := false
  /-- A seeded bug: a check the store did not answer in time is taken as found. -/
  readyOnTimeout : Bool := false
  /-- A seeded bug: a report is taken whatever its signature. -/
  trustUnsigned : Bool := false

/-- The scheduler beside the site. An error is worth another attempt; any other answer is the
store's word. Two jobs that failed together wait different times (`Schedule.hashJitter`). -/
def Config.scheduler (config : Config) : Schedule.Config Key Unit Answer where
  maxJobs := config.maxJobs
  maxPayload := 0
  maxAttempts := max (max config.checkRetry.maxAttempts config.transcodeRetry.maxAttempts)
    config.deleteRetry.maxAttempts
  ok a := a != .failed
  jitter := Schedule.hashJitter

namespace Site

def channel? (s : Site) (m : Member) : Option Channel := s.channels.lookup m

def name (s : Site) (m : Member) : String := ((s.channel? m).map (·.name)).getD ""

def live (s : Site) (m : Member) (session : Sid) : Bool :=
  ((s.channel? m).map (·.sessions.live session)).getD false

/-- Whether `m`'s `session` lets in a request that arrived at `at_s`: open, and not over then. -/
def accepts (s : Site) (life : Auth.Lifetime) (at_s : Nat) (m : Member) (session : Sid) : Bool :=
  ((s.channel? m).map (·.sessions.accepts life session at_s)).getD false

/-- The member and session a request of `at_s` names, if that session lets it in. -/
def viewer (s : Site) (life : Auth.Lifetime) (at_s : Nat) : Viewer → Viewer
  | some (m, session) => if s.accepts life at_s m session then some (m, session) else none
  | none => none

def find? (s : Site) (v : VideoId) : Option Video := s.videos.find? (·.id == v)

def setVideo (s : Site) (v : Video) : Site :=
  { s with videos := s.videos.map fun w => if w.id == v.id then v else w }

def card (s : Site) (v : Video) : Card :=
  { id := v.id, owner := v.owner, ownerName := s.name v.owner, title := v.title.val
    visibility := v.visibility, likes := v.likes.length }

def view (s : Site) (v : Video) (viewer : Option Member) : View :=
  { card := s.card v, about := v.about.val, media := v.media
    liked := viewer.any (v.likes.contains ·)
    comments := v.comments.map fun c =>
      { id := c.id, author := c.author, authorName := s.name c.author, body := c.body.val } }

end Site

/-- Whether `who` may see the video: it is ready, and not private or theirs. -/
def Video.visibleTo (v : Video) (who : Option Member) : Bool :=
  v.status.isReady && (v.visibility != .private || who == some v.owner)

def Video.listed (v : Video) : Bool :=
  v.status.isReady && v.visibility == .public

def Video.waiting (v : Video) : Bool := !v.status.isReady

/-- What a report makes of a status: the round under way, or a failed one, done is ready; the
round under way failed is failed. Any other report changes nothing. -/
def Report.next (r : Report) : Status → Option Status
  | .transcoding size n => if n = r.round.n then
      some (match r with | .done _ => .ready size | .failed _ => .failed size n) else none
  | .failed size n => if n = r.round.n then
      (match r with | .done _ => some (.ready size) | .failed _ => none) else none
  | _ => none

/-- What a report of `r` does to a video: the one its round names moves on, if it may. -/
def Report.move (r : Report) (w : Video) : Video :=
  if w.id = r.round.video then
    match r.next w.status with
    | some status => { w with status }
    | none => w
  else w

/-- The one output of a request. -/
def answer (req : ReqId) (viewer : Viewer) (r : Reply) : List Out := [.reply req viewer r]

namespace Site

variable (config : Config)

/-- A sign-in at `at_s`: the member's sessions over by then are swept, and one is opened. -/
def signIn (s : Site) (req : ReqId) (issuer subject name : String) (at_s : Nat) : Site × List Out :=
  let start (m : Member) (ch : Channel) : Site × List Out :=
    let (sessions, _) := ch.sessions.start config.maxSessions req at_s config.lifetime
    ({ s with channels := (m, { ch with name, sessions }) :: s.channels.filter (·.1 != m) },
      answer req (some (m, req)) (.signedIn m req at_s))
  match s.channels.find? fun (_, ch) => ch.issuer == issuer && ch.subject == subject with
  | some (m, ch) => start m ch
  | none =>
    if config.maxMembers ≤ s.channels.length then (s, answer req none .full)
    else start s.channels.length { issuer, subject, name }

/-- `f`, for a session of `m` that lets in a request of `at_s`. -/
def withSession (s : Site) (life : Auth.Lifetime) (at_s : Nat) (req : ReqId) (m : Member)
    (session : Sid) (f : Viewer → Site × List Out) : Site × List Out :=
  if s.accepts life at_s m session then f (some (m, session)) else (s, answer req none .noSession)

/-- `f`, for a video of `m`'s. -/
def owned (s : Site) (req : ReqId) (viewer : Viewer) (m : Member) (v : VideoId)
    (f : Video → Site × List Out) : Site × List Out :=
  match s.find? v with
  | some video => if video.owner = m then f video else (s, answer req viewer .notFound)
  | none => (s, answer req viewer .notFound)

/-- `f`, for a video `m` may see. -/
def seen (s : Site) (req : ReqId) (viewer : Viewer) (m : Member) (v : VideoId)
    (f : Video → Site × List Out) : Site × List Out :=
  match s.find? v with
  | some video => if video.visibleTo (some m) then f video else (s, answer req viewer .notFound)
  | none => (s, answer req viewer .notFound)

/-- A job of `key`, due at `at_ms`, asked for at `at_s`. -/
def schedule (key : Key) (retry : Schedule.Retry) (at_s at_ms : Nat) : Out :=
  .schedule (at_s * 1000) ⟨key, (), .call retry, at_ms⟩

/-- The last check of a video made at `at_s`, if there is one. -/
def expiry (v : VideoId) (at_s : Nat) : List Out :=
  match config.pending_s with
  | some p => [schedule (.expire v) config.checkRetry at_s ((at_s + p) * 1000)]
  | none => []

/-- The last check of `v` is not needed: it is ready, or deleted. -/
def unexpire (v : VideoId) : List Out :=
  if config.pending_s.isSome then [.cancel (.expire v)] else []

def create (s : Site) (req : ReqId) (viewer : Viewer) (m : Member) (title : Title) (about : About)
    (visibility : Visibility) (media : Media) (at_s : Nat) : Site × List Out :=
  if config.maxVideos ≤ s.videos.length
      || config.maxOwned ≤ (s.videos.filter (·.owner == m)).length
      || config.maxPending ≤ (s.videos.filter fun v => v.owner == m && v.waiting).length then
    (s, answer req viewer .tooMany)
  else
    let video : Video := { id := s.next, owner := m, title, about, visibility, media, status := .pending }
    ({ s with videos := video :: s.videos, next := s.next + 1 },
      answer req viewer (.created s.next media at_s) ++ expiry config s.next at_s)

/-- The start of round `round` of a transcode, due at once. -/
def start (round : Round) : Out := schedule (.transcode round) config.transcodeRetry 0 0

/-- The request that waits for a check of `video`, if one does, told `r`. -/
def waiterOf (video : Video) (viewer : Viewer) (r : Reply) : List Out :=
  match video.status with
  | .checking waiter => answer waiter viewer r
  | _ => []

/-- Have the store asked whether the object of `video` is there, and tell `req`. A check
already waited for is answered `unconfirmed`: the newer takes its place. -/
def check (s : Site) (req : ReqId) (viewer : Viewer) (video : Video) (at_s : Nat) :
    Site × List Out :=
  let superseded := waiterOf video viewer (.unconfirmed video.id)
  if config.trustBrowser then
    (s.setVideo { video with status := .transcoding 0 0 },
      superseded ++ answer req viewer (.confirmed video.id) ++ [start config ⟨video.id, 0⟩])
  else
    (s.setVideo { video with status := .checking req },
      superseded ++ [schedule (.check video.id req) config.checkRetry at_s (at_s * 1000)])

def uploaded (s : Site) (req : ReqId) (viewer : Viewer) (at_s : Nat) (video : Video) :
    Site × List Out :=
  if video.status.awaiting then check config s req viewer video at_s
  else (s, answer req viewer (.confirmed video.id))

/-- A failed transcode is tried again, as a new round. -/
def retry (s : Site) (req : ReqId) (viewer : Viewer) (video : Video) : Site × List Out :=
  match video.status with
  | .failed size n =>
    (s.setVideo { video with status := .transcoding size (n + 1) },
      answer req viewer (.retrying video.id) ++ [start config ⟨video.id, n + 1⟩])
  | _ => (s, answer req viewer (.retrying video.id))

/-- The start of the round under way, if one is: a delete cancels it. -/
def unstart (video : Video) : List Out :=
  match video.status with
  | .transcoding _ n => [.cancel (.transcode ⟨video.id, n⟩)]
  | _ => []

/-- What a report of `r` does to the site: the video its round names moves on, if it may. -/
def settle (s : Site) (r : Report) : Site := { s with videos := s.videos.map r.move }

/-- The worker's report, taken only with the worker's signature. -/
def report (s : Site) (req : ReqId) (r : Report) (signature : String) : Site × List Out :=
  if config.trustUnsigned || r.signed config.workerKey signature then
    (s.settle r, answer req none .reported)
  else (s, answer req none .forged)

def like (s : Site) (req : ReqId) (viewer : Viewer) (m : Member) (video : Video) (on : Bool) :
    Site × List Out :=
  let likes := if on then (if video.likes.contains m then video.likes else m :: video.likes)
    else video.likes.erase m
  (s.setVideo { video with likes }, answer req viewer (.liked video.id likes.length on))

def comment (s : Site) (req : ReqId) (viewer : Viewer) (m : Member) (video : Video) (body : Remark) :
    Site × List Out :=
  if config.maxComments ≤ video.comments.length
      || config.maxCommentsEach ≤ (video.comments.filter (·.author == m)).length then
    (s, answer req viewer (.tooManyComments video.id))
  else
    let c : Comment := { id := s.nextComment, author := m, body }
    ({ s.setVideo { video with comments := video.comments ++ [c] } with
        nextComment := s.nextComment + 1 },
      answer req viewer (.commented video.id))

/-- Only the comment's author, or the video's owner, takes it out. -/
def uncomment (s : Site) (req : ReqId) (viewer : Viewer) (m : Member) (video : Video)
    (c : CommentId) : Site × List Out :=
  if video.comments.any fun x => x.id == c && (x.author == m || video.owner == m) then
    (s.setVideo { video with comments := video.comments.filter (·.id != c) },
      answer req viewer (.uncommented video.id))
  else (s, answer req viewer .notFound)

/-- The record goes at once; the object is deleted in the store after, by a job. -/
def delete (s : Site) (req : ReqId) (viewer : Viewer) (at_s : Nat) (video : Video) :
    Site × List Out :=
  ({ s with videos := s.videos.filter (·.id != video.id) },
    waiterOf video viewer (.unconfirmed video.id) ++ answer req viewer (.deleted video.id)
      ++ [schedule (.delete video.id) config.deleteRetry at_s (at_s * 1000)]
      ++ unexpire config video.id ++ unstart video)

def watch (s : Site) (req : ReqId) (viewer : Viewer) (v : VideoId) (at_s : Nat) : Site × List Out :=
  let who := viewer.map (·.1)
  match s.find? v with
  | some video =>
    if video.visibleTo who then (s, answer req viewer (.watch (s.view video who) at_s))
    else if who = some video.owner then
      match video.status.stage? with
      | some stage => (s, answer req viewer (.preparing video.id video.title.val stage))
      | none => (s, answer req viewer .notFound)
    else (s, answer req viewer .notFound)
  | none => (s, answer req viewer .notFound)

def feed (s : Site) (req : ReqId) (viewer : Viewer) (before : Option VideoId) : Site × List Out :=
  let all := s.videos.filter fun v => v.listed && before.all (v.id < ·)
  let page := all.take config.pageSize
  let next := if config.pageSize < all.length then page.getLast?.map (·.id) else none
  (s, answer req viewer (.feed (page.map s.card) next))

/-- A member's own page shows all of their ready videos and the titles of the others; anyone
else's, the public ones. -/
def channel (s : Site) (req : ReqId) (viewer : Viewer) (whose : Member) : Site × List Out :=
  let own := viewer.map (·.1) == some whose
  let theirs := s.videos.filter (·.owner == whose)
  let shown := theirs.filter fun v => if own then v.status.isReady else v.listed
  let waiting := if own then
      theirs.filterMap fun v => v.status.stage?.map fun stage => (v.id, v.title.val, stage)
    else []
  match s.channel? whose with
  | some ch => (s, answer req viewer (.channel whose ch.name (shown.map s.card) waiting))
  | none => (s, answer req viewer .notFound)

def request (s : Site) (c : Command) (at_s : Nat) : Site × List Out :=
  let life := config.lifetime
  match c with
  | .signIn req issuer subject name => s.signIn config req issuer subject name at_s
  | .signOut req m session => s.withSession life at_s req m session fun _ =>
    ({ s with channels := s.channels.map fun (n, ch) =>
        (n, if n = m then { ch with sessions := ch.sessions.close session } else ch) },
      answer req none .signedOut)
  | .create req m session title about visibility media =>
    s.withSession life at_s req m session fun viewer =>
      s.create config req viewer m title about visibility media at_s
  | .uploaded req m session v => s.withSession life at_s req m session fun viewer =>
    s.owned req viewer m v (s.uploaded config req viewer at_s)
  | .watch req viewer v => s.watch req (s.viewer life at_s viewer) v at_s
  | .like req m session v on => s.withSession life at_s req m session fun viewer =>
    s.seen req viewer m v fun video => s.like req viewer m video on
  | .comment req m session v body => s.withSession life at_s req m session fun viewer =>
    s.seen req viewer m v fun video => s.comment config req viewer m video body
  | .uncomment req m session v c => s.withSession life at_s req m session fun viewer =>
    s.seen req viewer m v fun video => s.uncomment req viewer m video c
  | .delete req m session v => s.withSession life at_s req m session fun viewer =>
    s.owned req viewer m v (s.delete config req viewer at_s)
  | .feed req viewer before => s.feed config req (s.viewer life at_s viewer) before
  | .channel req viewer whose => s.channel req (s.viewer life at_s viewer) whose
  | .retry req m session v => s.withSession life at_s req m session fun viewer =>
    s.owned req viewer m v (s.retry config req viewer)
  | .report req r signature => s.report config req r signature

/-- The store has the upload of `video`, of `size` bytes: its first round of transcoding begins,
and whoever waits is told. -/
def found (s : Site) (video : Video) (size : Nat) : Site × List Out :=
  (s.setVideo { video with status := .transcoding size 0 },
    waiterOf video none (.confirmed video.id) ++ unexpire config video.id ++ [start config ⟨video.id, 0⟩])

/-- The check of `req` did not confirm `video`: if `req` still waits, the video is pending
again and `req` is told `r`. -/
def unconfirmed (s : Site) (video : Video) (req : ReqId) (r : Reply) : Site × List Out :=
  if video.status = .checking req then (s.setVideo { video with status := .pending }, answer req none r)
  else (s, [])

/-- How the check of `req` ended, for a video awaiting its upload. -/
def checked (s : Site) (video : Video) (req : ReqId) : Outcome → Site × List Out
  | .succeeded (.found size) => s.found config video size
  | .succeeded _ => s.unconfirmed video req (.notUploaded video.id)
  | .failed _ _ none =>
    if config.readyOnTimeout then s.found config video 0
    else s.unconfirmed video req (.unconfirmed video.id)
  | .failed .. | .refused _ | .cancelled => s.unconfirmed video req (.unconfirmed video.id)
  | .scheduled | .already => (s, [])

/-- How the last check of a video awaiting its upload ended: found, it is confirmed; not there,
its record is taken out; not known, it stays as it is. -/
def expired (s : Site) (video : Video) : Outcome → Site × List Out
  | .succeeded (.found size) => s.found config video size
  | .succeeded _ =>
    ({ s with videos := s.videos.filter (·.id != video.id) }, waiterOf video none (.notUploaded video.id))
  | _ => (s, [])

/-- `f`, for a video that awaits its upload. -/
def awaiting (s : Site) (v : VideoId) (f : Video → Site × List Out) : Site × List Out :=
  match s.find? v with
  | some video => if video.status.awaiting then f video else (s, [])
  | none => (s, [])

/-- The scheduler's word on a job. A transcode the worker could not be given failed; a delete
given up is reported. -/
def job (s : Site) : Key → Outcome → Site × List Out
  | .check v req, o => s.awaiting v fun video => s.checked config video req o
  | .expire v, o => s.awaiting v fun video => s.expired config video o
  | .transcode r, o => (if o.givenUp then s.settle (.failed r) else s, [])
  | .delete v, o => (s, if o.givenUp then [.orphan v] else [])

def handle (s : Site) : Input → Site × List Out
  | .request c at_s => s.request config c at_s
  | .job key o => s.job config key o
  | .noticed _ => (s, [])

/-- A start: the requests that waited for a check are gone with the connections, so each is
told to try again and its video is pending. The jobs are the scheduler's, which keeps them, and a
round under way is the worker's, whose report may still come. -/
def recover (s : Site) : Site × List Out :=
  let waiters := s.videos.filterMap fun v => match v.status with
    | .checking waiter => some (Out.reply waiter none (.unconfirmed v.id))
    | _ => none
  let videos := s.videos.map fun v => match v.status with
    | .checking .. => { v with status := .pending }
    | _ => v
  ({ s with videos }, waiters)

end Site

/-! ## What a reply shows -/

def Reply.cards : Reply → List Card
  | .watch view _ => [view.card]
  | .feed cards _ => cards
  | .channel _ _ cards _ => cards
  | _ => []

/-- The cards of an output, and the member it is for. -/
def Out.cards : Out → List Card
  | .reply _ _ r => r.cards
  | _ => []

def Out.viewer : Out → Option Member
  | .reply _ viewer _ => viewer.map (·.1)
  | _ => none

/-- An output shows a private video only to its owner. -/
def Out.private_ok (o : Out) : Prop :=
  ∀ c ∈ o.cards, c.visibility = .private → o.viewer = some c.owner

end Videos
