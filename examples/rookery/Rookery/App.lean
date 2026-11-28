import Lanes

/-!
# rookery's tables and transactions

What rookery keeps is rows of PostgreSQL: its members, their posts, who follows whom, each
member's rate-limit window, the counters that number posts and sessions, the API changes acted
on, and, through `Lanes/Web/Auth/Rows.lean`, the failed log-ins and the open sessions. A request
is one transaction (`handler`), pure: the store runs it at `SERIALIZABLE` and tries it again on a
conflict. The process keeps nothing, so a restart loses nothing, and several instances behind a
load balancer serve one site.

Every bound is in `Config` (rule 2.6), and the transactions say what happens at it: a sign-up
past `maxAccounts` is `full`, a post past `maxPosts` kept is `tooManyPosts`, past
`maxPerWindow` in a window `rateLimited`, a follow past `maxFollows` `tooManyFollows`; a log-in
past `maxSessions` closes the oldest session.

A row of a member's is keyed by the member's name: `members` by it, `posts`, `follows` and
`windows` by it first, the failed log-ins by it, and an API change by the name and its `seq`.
Each write a request makes as `n` is to a row keyed by `n` (`Rookery.Proofs`), so no request
changes another member's rows.

Time is the request's: the server writes when it arrived into it (`Web.stamp`), in seconds. A
window is `window_s` from its first post; a lock lifts at the first log-in `lockout_s` after it
locked; a session ends `idle_s` after it was last used or `absolute_s` after it began
(`Auth.Rows.Sessions`).

An API change carries a sequence number its bot chooses. The change is acted on once for each
number (`Keys.once`): the same change again is answered as the first time, without acting,
another change with that number gets `reused`, and an older number than the last acted on gets
`stale`. Acting on a newer number forgets the older one's key, so a member has at most one.
-/

namespace Rookery

open Lanes Lanes.Db

/-- An account's name: one to twenty lowercase letters, digits and `_`, so that it is a path
segment, a cookie payload and text all at once without escaping, and has no `/`. -/
def Name.valid (s : String) : Bool :=
  0 < s.length && s.length ≤ 20 && s.toList.all fun c => c.isLower || c.isDigit || c == '_'

abbrev Name := {s : String // Name.valid s}

def Name.ofString? (s : String) : Option Name :=
  if h : Name.valid s then some ⟨s, h⟩ else none

/-- What a post may say: one to 280 characters. -/
def Body.valid (s : String) : Bool :=
  0 < s.length && s.length ≤ 280

abbrev Body := {s : String // Body.valid s}

def Body.ofString? (s : String) : Option Body :=
  if h : Body.valid s then some ⟨s, h⟩ else none

/-! ## The tables -/

/-- A member. `hash` is the PHC string of its password (`Auth.Stored`); `token` the generation of
its API token, `0` before the first; `lastSeq` the newest API change acted on; `lockedAt_s` when
its log-ins last locked. -/
lanes_data structure Member where
  name : String
  hash : String
  bot : Bool
  token : Int64
  lastSeq : Int64
  lockedAt_s : Int64
  deriving DecidableEq, Repr, Hashable
  table members key name

/-- A post, keyed by its author and its id: only a request made as its author names its key. Ids
come from the counter `post`, so one is never given twice and a larger id is newer. -/
lanes_data structure Post where
  author : String
  id : Int64
  body : String
  posted_s : Int64
  deriving DecidableEq, Repr, Hashable
  table posts key author, id

lanes_data structure Follow where
  follower : String
  followee : String
  deriving DecidableEq, Repr, Hashable
  table follows key follower, followee

/-- A member's rate-limit window: when it began, and the posts accepted in it. -/
lanes_data structure Window where
  name : String
  start_s : Int64
  count : Int64
  deriving DecidableEq, Repr, Hashable
  table windows key name

/-- A number that only grows: the next post's id, the next session's, the members so far. -/
lanes_data structure Counter where
  name : String
  next : Int64
  deriving DecidableEq, Repr, Hashable
  table counters key name

/-- What an API change was answered: the reply's code and number (`Reply.code`), and the change
(`Action.text`). -/
abbrev Remembered := Int64 × Int64 × String

def keys : Keys Remembered :=
  { name := "api_keys"
    payload := .pair .int64 (.pair .int64 .text Jobs.Payload.int64_colon) Jobs.Payload.int64_colon }

/-- The key of a member's API change numbered `seq`. -/
def keyOf (n : String) (seq : Int64) : String := n ++ "/" ++ toString seq.toInt

/-- The settings the transactions are built with. Every bound is here (rule 2.6). -/
structure Config where
  maxAccounts : Nat := 1000
  maxSessions : Nat := 4
  maxFailures : Nat := 5
  /-- Posts a member keeps: one more is refused until it deletes one. -/
  maxPosts : Nat := 100
  maxFollows : Nat := 100
  maxPerWindow : Nat := 10
  timelineMax : Nat := 50
  window_s : Nat := 60
  lockout_s : Nat := 300
  /-- A session ends this long after it was last used, and after it began. -/
  idle_s : Int64 := 86400
  absolute_s : Int64 := 2592000

def Config.failures (config : Config) : Auth.Rows.Failures.Config :=
  { limit := config.maxFailures }

def Config.sessions (config : Config) : Auth.Rows.Sessions.Config :=
  { idle_s := config.idle_s, absolute_s := config.absolute_s }

def schema (config : Config) : Schema :=
  [members.table, posts.table, follows.table, windows.table, counters.table, keys.table,
    (Auth.Rows.Failures.table config.failures).table, (Auth.Rows.Sessions.table config.sessions).table]

/-! ## Requests and replies -/

inductive Action where
  | post (body : {s : String // Body.valid s})
  | delete (post : Int64)
  | follow (whom : {s : String // Name.valid s})
  | unfollow (whom : {s : String // Name.valid s})
  | timeline
  deriving DecidableEq, Repr, Hashable

/-- A change as the API's memo compares it. -/
def Action.text : Action → String
  | .post body => "post " ++ body.val
  | .delete id => "delete " ++ toString id.toInt
  | .follow whom => "follow " ++ whom.val
  | .unfollow whom => "unfollow " ++ whom.val
  | .timeline => "timeline"

/-- A log-in's password, checked by the server against the stored hash before the request
enters (`Web.checkPassword`): wrong, or right, with a new hash to store when the stored one is
not as the deployment makes one now. -/
inductive Checked where
  | wrong
  | right (rehash : Option String)
  deriving DecidableEq, Repr, Hashable

/-- `name` is never read from a request's body: the bridge takes it from a session cookie or an
API token it has verified, or from the form of a sign-up or a log-in. No request carries a
password: a sign-up carries its hash, a log-in what checking it gave. -/
inductive Request where
  | signUp (name : {s : String // Name.valid s}) (hash : String) (bot : Bool)
  | logIn (name : {s : String // Name.valid s}) (checked : Checked)
  | logOut (name : {s : String // Name.valid s}) (session : Int64)
  /-- A new API token; every earlier one stops working. -/
  | newToken (name : {s : String // Name.valid s}) (session : Int64)
  | web (name : {s : String // Name.valid s}) (session : Int64) (op : Action)
  /-- `token` is the generation of the token the request carried; `seq` its sequence number. -/
  | api (name : {s : String // Name.valid s}) (token : Int64) (seq : Int64) (op : Action)
  /-- A member's posts, newest first, which anyone may read; `json` if asked through the API. -/
  | profile (name : {s : String // Name.valid s}) (json : Bool)
  deriving DecidableEq, Repr, Hashable

/-- A request, and when it arrived, in seconds. -/
structure Ask where
  at_s : Int64
  request : Request
  deriving DecidableEq, Repr, Hashable

namespace Request

/-- The account the request is made as, or, for `profile`, the account it reads. -/
def name : Request → Name
  | .signUp n .. | .logIn n .. | .logOut n .. | .newToken n .. | .web n .. | .api n ..
  | .profile n _ => n

def json : Request → Bool
  | .api .. => true
  | .profile _ json => json
  | _ => false

end Request

/-- No reply carries a password, a hash or another account's name: a session or a token is
signed by the bridge for the name of the response (`Response.name`), which is the request's. -/
inductive Reply where
  | signedUp
  | nameTaken
  | full
  /-- A session opened at `at_s`, when its cookie is signed. -/
  | loggedIn (session : Int64) (at_s : Int64)
  /-- Wrong name or wrong password: which one is not said. -/
  | refused
  | locked
  | loggedOut
  | noSession
  /-- A new API token, signed at `at_s`. -/
  | token (generation : Int64) (at_s : Int64)
  | badToken
  | stale
  /-- The sequence number was used for another change. -/
  | reused
  | posted (post : Int64)
  | rateLimited
  | tooManyPosts
  | deleted
  /-- The account has no post with that id. -/
  | notYours
  | followed
  | unfollowed
  | noSuchAccount
  | tooManyFollows
  | feed (posts : List Post)
  deriving DecidableEq, Repr, Hashable

/-- What an API change is remembered by: a code and a number. -/
def Reply.code : Reply → Int64 × Int64
  | .posted id => (1, id)
  | .deleted => (2, 0)
  | .notYours => (3, 0)
  | .followed => (4, 0)
  | .unfollowed => (5, 0)
  | .noSuchAccount => (6, 0)
  | .tooManyFollows => (7, 0)
  | .rateLimited => (8, 0)
  | .tooManyPosts => (9, 0)
  | _ => (0, 0)

def Reply.ofCode : Int64 × Int64 → Reply
  | (1, id) => .posted id
  | (2, _) => .deleted
  | (3, _) => .notYours
  | (4, _) => .followed
  | (5, _) => .unfollowed
  | (6, _) => .noSuchAccount
  | (7, _) => .tooManyFollows
  | (8, _) => .rateLimited
  | (9, _) => .tooManyPosts
  | _ => .reused

structure Response where
  /-- The account the request was made as. -/
  name : Name
  /-- Whether the request came through the API, so the bridge answers in JSON. -/
  json : Bool
  reply : Reply
  deriving DecidableEq, Repr, Hashable

/-! ## The transactions -/

variable (config : Config)

/-- The next number of a counter, which it takes. -/
def take (counter : String) : Txn Int64 := do
  let next := ((← counters.get [.text counter]).map (·.next)).getD 0
  let _ ← counters.upsert { name := counter, next := next + 1 }
  return next

def signUp (n : String) (hash : String) (bot : Bool) : Txn Reply := do
  match ← members.get [.text n] with
  | some _ => return .nameTaken
  | none =>
    let count := ((← counters.get [.text "members"]).map (·.next)).getD 0
    if config.maxAccounts ≤ count.toInt.toNat then return .full
    let _ ← members.insert { name := n, hash, bot, token := 0, lastSeq := 0, lockedAt_s := 0 }
    let _ ← counters.upsert { name := "members", next := count + 1 }
    return .signedUp

/-- Open a session for `n`, and close the oldest beyond `maxSessions`. -/
def openSession (at_s : Int64) (n : String) : Txn Reply := do
  let id ← take "session"
  let _ ← Auth.Rows.Sessions.open config.sessions id n at_s
  let open_ ← Auth.Rows.Sessions.ofUser config.sessions n (config.maxSessions + 1)
  let _ ← (open_.take (open_.length - config.maxSessions)).mapM fun s =>
    Auth.Rows.Sessions.close config.sessions s.id
  return .loggedIn id at_s

def logIn (at_s : Int64) (n : String) (checked : Checked) : Txn Reply := do
  match ← members.get [.text n] with
  | none => return .refused
  | some m =>
    let lifted := m.lockedAt_s.toInt + config.lockout_s ≤ at_s.toInt
    if (← Auth.Rows.Failures.locked config.failures n) && lifted then
      Auth.Rows.Failures.unlock config.failures n
    if ← Auth.Rows.Failures.locked config.failures n then return .locked
    match checked with
    | .wrong =>
      let a ← Auth.Rows.Failures.failed config.failures n
      if a.locked then
        let _ ← members.update { m with name := n, lockedAt_s := at_s }
      return .refused
    | .right rehash =>
      Auth.Rows.Failures.succeeded config.failures n
      if let some hash := rehash then
        let _ ← members.update { m with name := n, hash }
      openSession config at_s n

/-- Whether a session lets `n` in, open and not over at `at_s`; it is marked used. -/
def session (at_s : Int64) (n : String) (sid : Int64) : Txn Bool := do
  return (← Auth.Rows.Sessions.accepts config.sessions sid at_s) == some n

def post (at_s : Int64) (n : String) (body : String) : Txn Reply := do
  let w := (← windows.get [.text n]).getD { name := n, start_s := at_s, count := 0 }
  let (start_s, count) :=
    if w.start_s.toInt + config.window_s ≤ at_s.toInt then (at_s, 0) else (w.start_s, w.count.toInt.toNat)
  if config.maxPerWindow ≤ count then return .rateLimited
  let kept ← posts.scan { table := posts.table, eq := [.text n], limit := config.maxPosts }
  if config.maxPosts ≤ kept.length then return .tooManyPosts
  let id ← take "post"
  let _ ← posts.insert { author := n, id, body, posted_s := at_s }
  let _ ← windows.upsert { name := n, start_s, count := Int64.ofNat (count + 1) }
  return .posted id

def follow (n whom : String) : Txn Reply := do
  if whom = n then return .followed
  if (← follows.get [.text n, .text whom]).isSome then return .followed
  if (← members.get [.text whom]).isNone then return .noSuchAccount
  let following ← follows.scan { table := follows.table, eq := [.text n], limit := config.maxFollows }
  if config.maxFollows ≤ following.length then return .tooManyFollows
  let _ ← follows.insert { follower := n, followee := whom }
  return .followed

/-- The newest posts of a member, at most `timelineMax`. -/
def postsOf (n : String) : Txn (List Post) :=
  posts.scan { table := posts.table, eq := [.text n], order := .desc, limit := config.timelineMax }

/-- The posts of `n` and of the accounts it follows, newest first, at most `timelineMax`. -/
def timeline (n : String) : Txn (List Post) := do
  let following ← follows.scan { table := follows.table, eq := [.text n], limit := config.maxFollows }
  let each ← (n :: following.map (·.followee)).mapM (postsOf config)
  return (each.flatten.mergeSort fun x y => decide (y.id.toInt ≤ x.id.toInt)).take config.timelineMax

/-- What `n`, signed in, asks. -/
def act (at_s : Int64) (n : String) : Action → Txn Reply
  | .post body => post config at_s n body.val
  | .delete id => do
    if ← posts.delete [.text n, .int id] then return .deleted else return .notYours
  | .follow whom => follow config n whom.val
  | .unfollow whom => do
    let _ ← follows.delete [.text n, .text whom.val]
    return .unfollowed
  | .timeline => .feed <$> timeline config n

/-- An API change, acted on once for its `seq`; the key of the one before is forgotten. -/
def change (at_s : Int64) (n : String) (m : Member) (seq : Int64) (op : Action) : Txn Reply := do
  let (code, number, text) ← keys.once (keyOf n seq) do
    let reply ← act config at_s n op
    if m.lastSeq < seq then
      let _ ← keys.rows.delete [.text (keyOf n m.lastSeq)]
      let _ ← members.update { m with name := n, lastSeq := seq }
    return ((reply.code.1, reply.code.2, op.text) : Remembered)
  return if text = op.text then Reply.ofCode (code, number) else .reused

def api (at_s : Int64) (n : String) (token seq : Int64) (op : Action) : Txn Reply := do
  match ← members.get [.text n] with
  | none => return .badToken
  | some m =>
    if m.token = 0 ∨ token ≠ m.token then return .badToken
    if op = .timeline then act config at_s n op
    else if seq < m.lastSeq then return .stale
    else change config at_s n m seq op

def run (at_s : Int64) : Request → Txn Reply
  | .signUp n hash bot => signUp config n.val hash bot
  | .logIn n checked => logIn config at_s n.val checked
  | .logOut n sid => do
    if ← session config at_s n.val sid then
      Auth.Rows.Sessions.close config.sessions sid
      return .loggedOut
    else return .noSession
  | .newToken n sid => do
    if ← session config at_s n.val sid then
      match ← members.get [.text n.val] with
      | some m =>
        let _ ← members.update { m with name := n.val, token := m.token + 1 }
        return .token (m.token + 1) at_s
      | none => return .noSession
    else return .noSession
  | .web n sid op => do
    if ← session config at_s n.val sid then act config at_s n.val op else return .noSession
  | .api n token seq op => api config at_s n.val token seq op
  | .profile n _ => .feed <$> postsOf config n.val

/-- Each request is this one transaction. The response names the account the request was made
as, which the bridge signs a session or a token for. -/
def handler : Handler Ask Response := fun a => do
  return { name := a.request.name, json := a.request.json, reply := ← run config a.at_s a.request }

/-! ## The front

One actor that keeps nothing: it sends each request to the store as a call under the request's
own id, and answers with what the store answered. -/

inductive In where
  | request (id : Nat) (a : Ask)
  | store (reply : Db.Reply Response)
  deriving DecidableEq, Repr, Hashable

inductive Out where
  | call (c : Db.Call Ask)
  | answered (id : Nat) (r : Response)
  /-- The store failed the request, or its answer is not known. -/
  | failed (id : Nat)
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

def step : In → List (Effect sig ())
  | .request id a => [.emit (.call ⟨id, a⟩)]
  | .store ⟨id, .committed r⟩ => [.emit (.answered id r)]
  | .store ⟨id, _⟩ => [.emit (.failed id)]

def front : sig.Actor () Unit where
  init := ()
  step _ x := ((), step x)

abbrev system : System sig where
  State _ := Unit
  actor _ := front
  accept x := ⟨(), x⟩

def port : Db.Port sig Ask Response where
  call
    | .call c => some c
    | _ => none
  reply r := .store r
  replied
    | .store r => some r
    | _ => none

end Rookery
