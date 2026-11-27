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
through the site. The browser then says it is done, the site asks the store whether the object
is there (a `HEAD`), and only a `found` answer makes the video `ready`. Ready videos are watched,
liked once per member, commented on and listed in a feed; a video is public (in the feed and its
channel), unlisted (by its link) or private (its owner only). Deleting a video takes its record
out at once and then deletes the object in the store, again until the store says so or the
attempts run out.

The whole state is one value, `Site`, and one input is one call of `Site.handle`: a request,
or the store's answer to a call (`Rpc.Reply`, which may be `unknown`). A start of the actor is
one call of `Site.recover`. The system runs these functions in one actor (`Videos.System`), so
what is proved of them (`Videos.Proofs`) is proved of the code that runs.

Every bound is in `Config` (rule 2.6), with what happens at it: a sign-in past `maxMembers` is
`full`, a video past `maxVideos` or past `maxPending` uploads not yet confirmed is `tooMany`, a
comment past `maxComments` is `tooManyComments`, a delete past `maxDeleting` gives up the oldest
delete in the store, which is reported (`Out.orphan`).
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
  /-- The store is asked, under `call`, whether the object is there; `waiter` is told. -/
  | checking (call : Nat) (waiter : ReqId)
  /-- The store said the object is there, of `size` bytes. -/
  | ready (size : Nat)
  deriving DecidableEq, Repr, Hashable, Codable

def Status.isReady : Status → Bool
  | .ready _ => true
  | _ => false

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

/-- An object in the store whose video was deleted, and the delete sent for it. -/
lanes_data structure Deleting where
  video : VideoId
  call : Nat
  attempts : Nat
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data structure Site where
  channels : List (Member × Channel) := []
  /-- Newest first. -/
  videos : List Video := []
  /-- The id the next video gets: none is used twice. -/
  next : VideoId := 0
  nextComment : CommentId := 0
  nextCall : Nat := 0
  /-- Newest first. -/
  deleting : List Deleting := []
  deriving DecidableEq, Repr, Hashable, Codable

/-! ## Inputs and outputs -/

/-- What the site asks the store. The object of video `v` is at the key `videos/<v>`. -/
lanes_data inductive StoreOp where
  | head (video : VideoId)
  | delete (video : VideoId)
  deriving DecidableEq, Repr, Hashable, Codable

/-- The store's answer, as the site reads it. -/
lanes_data inductive StoreAnswer where
  | found (size : Nat)
  | missing
  | deleted
  /-- Anything else: an error, which may have come after the operation took effect. -/
  | failed
  deriving DecidableEq, Repr, Hashable, Codable

/-- A viewer: the member and the session a request's cookie names, when it names one. -/
abbrev Viewer := Option (Member × Sid)

/-- `member` and `session` are never read from a request's body: the bridge takes them from a
session cookie it has verified. -/
lanes_data inductive Command where
  /-- The sign-in verified this identity (`Lanes.OAuth`). -/
  | signIn (req : ReqId) (issuer subject name : String)
  | signOut (req : ReqId) (member : Member) (session : Sid)
  /-- `at_s` is when the request arrived, in seconds since the epoch: the upload form is
  signed for it. -/
  | create (req : ReqId) (member : Member) (session : Sid) (title : {s : String // Title.valid s})
    (about : {s : String // About.valid s}) (visibility : Visibility) (media : Media) (at_s : Nat)
  /-- The browser says the upload is done. -/
  | uploaded (req : ReqId) (member : Member) (session : Sid) (video : VideoId)
  | watch (req : ReqId) (viewer : Option (Member × Sid)) (video : VideoId) (at_s : Nat)
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
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Input where
  | request (c : Command)
  /-- The store's answer to `call`, or `unknown` at its deadline. -/
  | store (call : Nat) (reply : Rpc.Reply StoreAnswer)
  deriving DecidableEq, Repr, Hashable, Codable

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
  | signedIn (member : Member) (session : Sid)
  | full
  | signedOut
  | noSession
  /-- The record is made: the bridge signs the form for the upload at `at_s`. -/
  | created (video : VideoId) (media : Media) (at_s : Nat)
  | tooMany
  | confirmed (video : VideoId)
  /-- The store has no such object: the video stays pending. -/
  | notUploaded (video : VideoId)
  /-- The store did not say, or another check took this one's place: try again. -/
  | unconfirmed (video : VideoId)
  /-- The bridge signs the link to watch it at `at_s`. -/
  | watch (view : View) (at_s : Nat)
  /-- No such video, or none this viewer may see: which one is not said. -/
  | notFound
  | liked (video : VideoId) (likes : Nat) (on : Bool)
  | commented (video : VideoId)
  | tooManyComments (video : VideoId)
  | uncommented (video : VideoId)
  | deleted (video : VideoId)
  | feed (cards : List Card) (next : Option VideoId)
  /-- A member's videos; `pending`, the titles of those not ready, only to their owner. -/
  | channel (whose : Member) (name : String) (cards : List Card) (pending : List (VideoId × String))
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Out where
  /-- The answer to request `req`, for the session that made it, if it is live. -/
  | reply (req : ReqId) (viewer : Option (Member × Sid)) (r : Reply)
  | store (call : Rpc.Call StoreOp)
  /-- The object of a deleted video that the store did not say it deleted, given up on. -/
  | orphan (video : VideoId)
  deriving DecidableEq, Repr, Hashable, Codable

/-- The settings the spec and the system are built with. Every bound is here (rule 2.6). -/
structure Config where
  maxMembers : Nat := 10000
  maxSessions : Nat := 4
  maxVideos : Nat := 10000
  /-- Videos of one member not yet ready. -/
  maxPending : Nat := 4
  maxComments : Nat := 200
  maxDeleting : Nat := 1000
  /-- Deletes sent for one object before it is given up. -/
  maxAttempts : Nat := 3
  pageSize : Nat := 12
  /-- How long the store is waited for. -/
  store_ms : Nat := 10000
  /-- A seeded bug: a video is ready when the browser says it is uploaded, without asking. -/
  trustBrowser : Bool := false
  /-- A seeded bug: a check the store did not answer in time is taken as found. -/
  readyOnTimeout : Bool := false

namespace Site

def channel? (s : Site) (m : Member) : Option Channel := s.channels.lookup m

def name (s : Site) (m : Member) : String := ((s.channel? m).map (·.name)).getD ""

def live (s : Site) (m : Member) (session : Sid) : Bool :=
  ((s.channel? m).map (·.sessions.live session)).getD false

/-- The member and session a request names, if that session is live. -/
def viewer (s : Site) : Viewer → Viewer
  | some (m, session) => if s.live m session then some (m, session) else none
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

/-- The one output of a request. -/
def answer (req : ReqId) (viewer : Viewer) (r : Reply) : List Out := [.reply req viewer r]

namespace Site

variable (config : Config)

def signIn (s : Site) (req : ReqId) (issuer subject name : String) : Site × List Out :=
  let start (m : Member) (ch : Channel) : Site × List Out :=
    let (sessions, _) := ch.sessions.start config.maxSessions req
    ({ s with channels := (m, { ch with name, sessions }) :: s.channels.filter (·.1 != m) },
      answer req (some (m, req)) (.signedIn m req))
  match s.channels.find? fun (_, ch) => ch.issuer == issuer && ch.subject == subject with
  | some (m, ch) => start m ch
  | none =>
    if config.maxMembers ≤ s.channels.length then (s, answer req none .full)
    else start s.channels.length { issuer, subject, name }

/-- `f`, for a live session of `m`. -/
def withSession (s : Site) (req : ReqId) (m : Member) (session : Sid)
    (f : Viewer → Site × List Out) : Site × List Out :=
  if s.live m session then f (some (m, session)) else (s, answer req none .noSession)

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

def create (s : Site) (req : ReqId) (viewer : Viewer) (m : Member) (title : Title) (about : About)
    (visibility : Visibility) (media : Media) (at_s : Nat) : Site × List Out :=
  if config.maxVideos ≤ s.videos.length
      || config.maxPending ≤ (s.videos.filter fun v => v.owner == m && v.waiting).length then
    (s, answer req viewer .tooMany)
  else
    let video : Video := { id := s.next, owner := m, title, about, visibility, media, status := .pending }
    ({ s with videos := video :: s.videos, next := s.next + 1 },
      answer req viewer (.created s.next media at_s))

/-- Ask the store whether the object of `video` is there, and tell `req`. A check already out
is answered `unconfirmed`: the newer takes its place. -/
def check (s : Site) (req : ReqId) (viewer : Viewer) (video : Video) : Site × List Out :=
  let superseded := match video.status with
    | .checking _ waiter => answer waiter viewer (.unconfirmed video.id)
    | _ => []
  if config.trustBrowser then
    (s.setVideo { video with status := .ready 0 }, superseded ++ answer req viewer (.confirmed video.id))
  else
    ({ s.setVideo { video with status := .checking s.nextCall req } with nextCall := s.nextCall + 1 },
      superseded ++ [.store ⟨s.nextCall, config.store_ms, .head video.id⟩])

def uploaded (s : Site) (req : ReqId) (viewer : Viewer) (video : Video) : Site × List Out :=
  match video.status with
  | .ready _ => (s, answer req viewer (.confirmed video.id))
  | _ => check config s req viewer video

def like (s : Site) (req : ReqId) (viewer : Viewer) (m : Member) (video : Video) (on : Bool) :
    Site × List Out :=
  let likes := if on then (if video.likes.contains m then video.likes else m :: video.likes)
    else video.likes.erase m
  (s.setVideo { video with likes }, answer req viewer (.liked video.id likes.length on))

def comment (s : Site) (req : ReqId) (viewer : Viewer) (m : Member) (video : Video) (body : Remark) :
    Site × List Out :=
  if config.maxComments ≤ video.comments.length then
    (s, answer req viewer (.tooManyComments video.id))
  else
    let c : Comment := { id := s.nextComment, author := m, body }
    ({ s.setVideo { video with comments := video.comments ++ [c] } with
        nextComment := s.nextComment + 1 },
      answer req viewer (.commented video.id))

/-- Only the comment's author takes it out. -/
def uncomment (s : Site) (req : ReqId) (viewer : Viewer) (m : Member) (video : Video)
    (c : CommentId) : Site × List Out :=
  if video.comments.any fun x => x.id == c && x.author == m then
    (s.setVideo { video with comments := video.comments.filter (·.id != c) },
      answer req viewer (.uncommented video.id))
  else (s, answer req viewer .notFound)

/-- The deletes in the store with `d` added, newest first, and the oldest given up on when there
are more than `maxDeleting`. -/
def pushDeleting (s : Site) (d : Deleting) : List Deleting × List Out :=
  let all := d :: s.deleting
  (all.take config.maxDeleting, (all.drop config.maxDeleting).map (.orphan ·.video))

/-- The record goes at once; the object is deleted in the store after. -/
def delete (s : Site) (req : ReqId) (viewer : Viewer) (video : Video) : Site × List Out :=
  let waiter := match video.status with
    | .checking _ waiter => answer waiter viewer (.unconfirmed video.id)
    | _ => []
  let d : Deleting := { video := video.id, call := s.nextCall, attempts := 1 }
  let (deleting, given) := s.pushDeleting config d
  ({ s with videos := s.videos.filter (·.id != video.id), nextCall := s.nextCall + 1, deleting },
    waiter ++ answer req viewer (.deleted video.id)
      ++ [.store ⟨s.nextCall, config.store_ms, .delete video.id⟩] ++ given)

def watch (s : Site) (req : ReqId) (viewer : Viewer) (v : VideoId) (at_s : Nat) : Site × List Out :=
  let who := viewer.map (·.1)
  match s.find? v with
  | some video =>
    if video.visibleTo who then (s, answer req viewer (.watch (s.view video who) at_s))
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
  let waiting := if own then (theirs.filter (·.waiting)).map fun v => (v.id, v.title.val) else []
  match s.channel? whose with
  | some ch => (s, answer req viewer (.channel whose ch.name (shown.map s.card) waiting))
  | none => (s, answer req viewer .notFound)

def request (s : Site) : Command → Site × List Out
  | .signIn req issuer subject name => s.signIn config req issuer subject name
  | .signOut req m session => s.withSession req m session fun _ =>
    ({ s with channels := s.channels.map fun (n, ch) =>
        (n, if n = m then { ch with sessions := ch.sessions.close session } else ch) },
      answer req none .signedOut)
  | .create req m session title about visibility media at_s =>
    s.withSession req m session fun viewer =>
      s.create config req viewer m title about visibility media at_s
  | .uploaded req m session v => s.withSession req m session fun viewer =>
    s.owned req viewer m v (s.uploaded config req viewer)
  | .watch req viewer v at_s => s.watch req (s.viewer viewer) v at_s
  | .like req m session v on => s.withSession req m session fun viewer =>
    s.seen req viewer m v fun video => s.like req viewer m video on
  | .comment req m session v body => s.withSession req m session fun viewer =>
    s.seen req viewer m v fun video => s.comment config req viewer m video body
  | .uncomment req m session v c => s.withSession req m session fun viewer =>
    s.seen req viewer m v fun video => s.uncomment req viewer m video c
  | .delete req m session v => s.withSession req m session fun viewer =>
    s.owned req viewer m v (s.delete config req viewer)
  | .feed req viewer before => s.feed config req (s.viewer viewer) before
  | .channel req viewer whose => s.channel req (s.viewer viewer) whose

/-- The store's answer to a check of `video`, which `waiter` waits for. -/
def checked (s : Site) (video : Video) (waiter : ReqId) (reply : Rpc.Reply StoreAnswer) :
    Site × List Out :=
  let tell (r : Reply) := answer waiter none r
  match reply with
  | .answer (.found size) => (s.setVideo { video with status := .ready size }, tell (.confirmed video.id))
  | .answer .missing => (s.setVideo { video with status := .pending }, tell (.notUploaded video.id))
  | .unknown =>
    if config.readyOnTimeout then
      (s.setVideo { video with status := .ready 0 }, tell (.confirmed video.id))
    else (s.setVideo { video with status := .pending }, tell (.unconfirmed video.id))
  | .answer _ => (s.setVideo { video with status := .pending }, tell (.unconfirmed video.id))

/-- The store's answer to a delete: done, or sent again under a new call, or given up on. -/
def deleteAnswered (s : Site) (d : Deleting) (reply : Rpc.Reply StoreAnswer) : Site × List Out :=
  let rest := s.deleting.filter (·.call != d.call)
  match reply with
  | .answer .deleted | .answer .missing => ({ s with deleting := rest }, [])
  | _ =>
    if d.attempts < config.maxAttempts then
      ({ s with deleting := { d with call := s.nextCall, attempts := d.attempts + 1 } :: rest
                nextCall := s.nextCall + 1 },
        [.store ⟨s.nextCall, config.store_ms, .delete d.video⟩])
    else ({ s with deleting := rest }, [.orphan d.video])

def isChecking (call : Nat) (v : Video) : Bool :=
  match v.status with
  | .checking c _ => c == call
  | _ => false

def stored (s : Site) (call : Nat) (reply : Rpc.Reply StoreAnswer) : Site × List Out :=
  match s.videos.find? (isChecking call) with
  | some video =>
    match video.status with
    | .checking _ waiter => s.checked config video waiter reply
    | _ => (s, [])
  | none =>
    match s.deleting.find? (·.call == call) with
    | some d => s.deleteAnswered config d reply
    | none => (s, [])

def handle (s : Site) : Input → Site × List Out
  | .request c => s.request config c
  | .store call reply => s.stored config call reply

/-- A start: the answers to calls made before it may never come. A check is given up, its
waiter told to try again; each delete is sent again under a new call. -/
def recover (s : Site) : Site × List Out :=
  let waiters := s.videos.filterMap fun v => match v.status with
    | .checking _ waiter => some (Out.reply waiter none (.unconfirmed v.id))
    | _ => none
  let videos := s.videos.map fun v => match v.status with
    | .checking .. => { v with status := .pending }
    | _ => v
  let deleting := s.deleting.zipIdx.map fun (d, k) => { d with call := s.nextCall + k }
  ({ s with videos, deleting, nextCall := s.nextCall + s.deleting.length },
    waiters ++ deleting.map fun d => .store ⟨d.call, config.store_ms, .delete d.video⟩)

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
