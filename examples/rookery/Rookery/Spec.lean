import Rookery.Table

/-!
# The spec

What rookery is to the people and bots that use it, as if requests were handled one at a time.
An account signs up with a credential, logs in for a session (the web) or is issued an API
token (bots), posts short messages, deletes its own, follows other accounts and reads its
timeline: its own posts and those of the accounts it follows, newest first, at most
`Config.timelineMax` of them. Anyone may read an account's posts.

The whole state is one value, `Board`, and one request is one call of `Board.handle`. The
system runs the same function in one actor (`Rookery.System`), so the spec is also the code,
and what is proved of `Board.handle` (`Rookery.Proofs`) is proved of what runs.

Every bound is in `Config` (rule 2.6), and the spec says what happens at it: a sign-up past
`maxAccounts` is `full`, a post past `maxPosts` kept is `tooManyPosts`, past `maxPerWindow` in a
window `rateLimited`, a follow past `maxFollows` `tooManyFollows`; a log-in past `maxSessions`
closes the oldest session.

Time passes as deadlines (`Deadline`, D42): a rate-limit window ending, a session ending, a lock
lifting. Each is always armed, and one that passes with nothing to end changes nothing, so the
system's timers need no invariant tying them to the state (`Rookery.System`). How long a window
or a session lasts is the timers' delay in `Config`, which the semantics does not model.

An API request carries a sequence number its bot chooses. The board acts once on each change:
the same number again gets the answer it got, without acting, and an older one gets `stale`
(`Lanes.Once.Memo`, D48), so a bot that retries a post it got no answer to posts it once. A read
is answered afresh, so that no answer remembered shows a post deleted since.
-/

namespace Rookery

open Lanes

abbrev ReqId := Nat
abbrev PostId := Nat
/-- A session is named by the id of the log-in request that opened it, which is never reused. -/
abbrev Sid := Nat

/-- What a post may say: one to 280 characters. -/
def Body.valid (s : String) : Bool :=
  0 < s.length && s.length ≤ 280

abbrev Body := {s : String // Body.valid s}

/-- A post's id is the board's count of posts accepted before it, so ids are never reused and a
larger id is a newer post. -/
lanes_data structure Post where
  id : PostId
  body : {s : String // Body.valid s}
  deriving DecidableEq, Repr, Hashable, Codable

/-- What an account that is signed in, by a session or a token, may ask. -/
lanes_data inductive Op (N : Type) where
  | post (body : {s : String // Body.valid s})
  | delete (post : PostId)
  | follow (whom : N)
  | unfollow (whom : N)
  | timeline
  deriving DecidableEq, Repr, Hashable, Codable

/-- `name` is never read from a request's body: the bridge takes it from a session cookie or an
API token it has verified, or from the form of a sign-up or a log-in. -/
lanes_data inductive Request (N C : Type) where
  | signUp (req : ReqId) (name : N) (credential : C) (bot : Bool)
  | logIn (req : ReqId) (name : N) (credential : C)
  | logOut (req : ReqId) (name : N) (session : Sid)
  /-- A new API token for the account; every earlier one stops working. -/
  | newToken (req : ReqId) (name : N) (session : Sid)
  | web (req : ReqId) (name : N) (session : Sid) (op : Op N)
  /-- `token` is the generation of the token the request carried; `seq` its sequence number. -/
  | api (req : ReqId) (name : N) (token : Nat) (seq : Nat) (op : Op N)
  /-- An account's posts, newest first, which anyone may read; `json` if asked through the API. -/
  | profile (req : ReqId) (name : N) (json : Bool)
  deriving DecidableEq, Repr, Hashable, Codable

/-- No reply carries a credential, and none can: `Reply` does not mention its type. -/
lanes_data inductive Reply (N : Type) where
  | signedUp
  | nameTaken
  | full
  | loggedIn (name : N) (session : Sid)
  /-- Wrong name or wrong credential: which one is not said. -/
  | refused
  | locked
  | loggedOut
  | noSession
  | token (name : N) (generation : Nat)
  | badToken
  | stale
  | posted (post : PostId)
  | rateLimited
  | tooManyPosts
  | deleted
  /-- The account has no post with that id. -/
  | notYours
  | followed
  | unfollowed
  | noSuchAccount
  | tooManyFollows
  | feed (posts : List (N × Post))
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data structure Response (N : Type) where
  req : ReqId
  reply : Reply N
  /-- Whether the request came through the API, so the bridge answers in JSON. -/
  json : Bool := false
  deriving DecidableEq, Repr, Hashable, Codable

/-- An account. Its posts are kept in it, newest first, so a post's author is the account that
holds it, and nothing else can delete it. -/
lanes_data structure Profile (N C : Type) where
  credential : C
  bot : Bool := false
  attempts : Auth.Attempts := {}
  sessions : Auth.Sessions := {}
  /-- The generation of the account's API token: `0` before the first is issued. -/
  token : Nat := 0
  following : List N := []
  posts : List Post := []
  /-- Posts accepted in the current window. -/
  window : Nat := 0
  deriving DecidableEq, Repr, Hashable, Codable

instance {C E : Type} [DecidableEq C] [DecidableEq E] : DecidableEq (Once.Memo C E) := fun a b =>
  if h : a.entries = b.entries then isTrue (by cases a; cases b; simp_all)
  else isFalse fun heq => h (by rw [heq])

instance {C E : Type} [Codable C] [Codable E] : Codable (Once.Memo C E) :=
  ⟨(Codec.of (List (C × Nat × List E))).map Once.Memo.entries (fun l => some ⟨l⟩) fun _ => rfl⟩

lanes_data structure Board (N C : Type) where
  accounts : List (N × Profile N C) := []
  /-- The id the next post accepted gets. -/
  next : PostId := 0
  /-- The last API request acted on for each account, and its reply. -/
  memo : Once.Memo N (Reply N) := {}
  deriving DecidableEq, Repr, Hashable, Codable

/-- The settings the spec and the system are built with. Every bound is here (rule 2.6). -/
structure Config where
  maxAccounts : Nat := 1000
  maxSessions : Nat := 4
  maxFailures : Nat := 5
  /-- Posts an account keeps: one more is refused until it deletes one. -/
  maxPosts : Nat := 100
  maxFollows : Nat := 100
  maxPerWindow : Nat := 10
  timelineMax : Nat := 50
  window_ms : Nat := 60000
  /-- With `none` a session lasts until log-out or until it is the oldest of too many. -/
  session_ms : Option Nat := some 86400000
  /-- With `none` a locked account stays locked. -/
  lockout_ms : Option Nat := some 300000

/-- The timers a request starts and stops. Not part of the spec: the system arms them. -/
structure Timers where
  window : Bool := false
  locked : Bool := false
  opened : Option Sid := none
  closed : List Sid := []

/-- A deadline of the spec. -/
lanes_data inductive Deadline (N : Type) where
  | window (name : N)
  | expire (name : N) (session : Sid)
  | unlock (name : N)
  deriving DecidableEq, Repr, Hashable, Codable

namespace Request

variable {N C : Type}

def req : Request N C → ReqId
  | .signUp req .. | .logIn req .. | .logOut req .. | .newToken req .. | .web req ..
  | .api req .. | .profile req .. => req

/-- The account the request is made as, or, for `profile`, the account it reads. -/
def name : Request N C → N
  | .signUp _ n .. | .logIn _ n .. | .logOut _ n .. | .newToken _ n .. | .web _ n ..
  | .api _ n .. | .profile _ n _ => n

/-- Whether the request came through the API. -/
def json : Request N C → Bool
  | .api .. => true
  | .profile _ _ json => json
  | _ => false

end Request

namespace Board

variable {N C : Type} [DecidableEq N] [DecidableEq C]

def get? (b : Board N C) (n : N) : Option (Profile N C) :=
  lookup n b.accounts

def update (b : Board N C) (n : N) (f : Profile N C → Profile N C) : Board N C :=
  { b with accounts := modify n f b.accounts }

def set (b : Board N C) (n : N) (p : Profile N C) : Board N C :=
  b.update n fun _ => p

def postsOf (b : Board N C) (n : N) : List Post :=
  ((b.get? n).map (·.posts)).getD []

/-- The posts of `n` and of the accounts in `following`, newest first. -/
def feed (b : Board N C) (n : N) (following : List N) : List (N × Post) :=
  ((n :: following).flatMap fun a => (b.postsOf a).map (a, ·)).mergeSort
    fun x y => decide (y.2.id ≤ x.2.id)

def timeline (config : Config) (b : Board N C) (n : N) (following : List N) : List (N × Post) :=
  (b.feed n following).take config.timelineMax

def signUp (config : Config) (b : Board N C) (n : N) (c : C) (bot : Bool) :
    Board N C × Reply N × Timers :=
  match b.get? n with
  | some _ => (b, .nameTaken, {})
  | none =>
    if config.maxAccounts ≤ b.accounts.length then (b, .full, {})
    else ({ b with accounts := b.accounts ++ [(n, { credential := c, bot })] }, .signedUp, {})

def logIn (config : Config) (n : N) (req : ReqId) (p : Profile N C) (c : C) :
    Profile N C × Reply N × Timers :=
  if p.attempts.locked then (p, .locked, {})
  else if c = p.credential then
    let (sessions, closed) := p.sessions.start config.maxSessions req
    ({ p with attempts := p.attempts.succeed, sessions }, .loggedIn n req,
      { opened := some req, closed })
  else
    let attempts := p.attempts.fail config.maxFailures
    ({ p with attempts }, .refused, { locked := attempts.locked })

def post (config : Config) (b : Board N C) (n : N) (p : Profile N C) (body : Body) :
    Board N C × Reply N × Timers :=
  if config.maxPerWindow ≤ p.window then (b, .rateLimited, {})
  else if config.maxPosts ≤ p.posts.length then (b, .tooManyPosts, {})
  else
    ({ b.set n { p with posts := ⟨b.next, body⟩ :: p.posts, window := p.window + 1 } with
        next := b.next + 1 },
      .posted b.next, { window := p.window == 0 })

def delete (b : Board N C) (n : N) (p : Profile N C) (id : PostId) :
    Board N C × Reply N × Timers :=
  if p.posts.any (·.id == id) then
    (b.set n { p with posts := p.posts.filter (·.id != id) }, .deleted, {})
  else (b, .notYours, {})

def follow (config : Config) (b : Board N C) (n : N) (p : Profile N C) (whom : N) :
    Board N C × Reply N × Timers :=
  if whom = n ∨ whom ∈ p.following then (b, .followed, {})
  else if (b.get? whom).isNone then (b, .noSuchAccount, {})
  else if config.maxFollows ≤ p.following.length then (b, .tooManyFollows, {})
  else (b.set n { p with following := whom :: p.following }, .followed, {})

/-- What `n`, signed in with the profile `p`, asks. -/
def act (config : Config) (b : Board N C) (n : N) (p : Profile N C) :
    Op N → Board N C × Reply N × Timers
  | .post body => b.post config n p body
  | .delete id => b.delete n p id
  | .follow whom => b.follow config n p whom
  | .unfollow whom => (b.set n { p with following := p.following.erase whom }, .unfollowed, {})
  | .timeline => (b, .feed (b.timeline config n p.following), {})

/-- `f`, for a live session of `n`. -/
def withSession (b : Board N C) (n : N) (session : Sid)
    (f : Profile N C → Board N C × Reply N × Timers) : Board N C × Reply N × Timers :=
  match b.get? n with
  | some p => if p.sessions.live session then f p else (b, .noSession, {})
  | none => (b, .noSession, {})

/-- An API request: a read is answered afresh; a change is acted on once for each sequence
number (`Lanes.Once.Memo`). A read answered from the memo could show a post deleted since. -/
def api (config : Config) (b : Board N C) (n : N) (p : Profile N C) (token seq : Nat)
    (op : Op N) : Board N C × Reply N × Timers :=
  if p.token = 0 ∨ token ≠ p.token then (b, .badToken, {})
  else if op = .timeline then b.act config n p op
  else
    match b.memo.seen n seq with
    | .again replies => (b, replies.headD .stale, {})
    | .stale => (b, .stale, {})
    | .fresh =>
      let (b', reply, timers) := b.act config n p op
      ({ b' with memo := b'.memo.record n seq [reply] }, reply, timers)

def handle (config : Config) (b : Board N C) : Request N C → Board N C × Reply N × Timers
  | .signUp _ n c bot => b.signUp config n c bot
  | .logIn req n c =>
    match b.get? n with
    | some p => let (p, reply, timers) := logIn config n req p c; (b.set n p, reply, timers)
    | none => (b, .refused, {})
  | .logOut _ n session => b.withSession n session fun p =>
    (b.set n { p with sessions := p.sessions.close session }, .loggedOut, { closed := [session] })
  | .newToken _ n session => b.withSession n session fun p =>
    (b.set n { p with token := p.token + 1 }, .token n (p.token + 1), {})
  | .web _ n session op => b.withSession n session fun p => b.act config n p op
  | .api _ n token seq op =>
    match b.get? n with
    | some p => b.api config n p token seq op
    | none => (b, .badToken, {})
  | .profile _ n _ => (b, .feed (((b.postsOf n).map (n, ·)).take config.timelineMax), {})

def fire (b : Board N C) : Deadline N → Board N C
  | .window n => b.update n fun p => { p with window := 0 }
  | .expire n session => b.update n fun p => { p with sessions := p.sessions.close session }
  | .unlock n => b.update n fun p =>
    if p.attempts.locked then { p with attempts := Auth.Attempts.unlock } else p

end Board

/-- The spec: each request takes effect as one call of `Board.handle`, each deadline as one call
of `Board.fire`. -/
def spec (N C : Type) [DecidableEq N] [DecidableEq C] (config : Config) :
    Service (Request N C) (Response N) (Board N C) (Deadline N) where
  init := {}
  step b r := ((b.handle config r).1, [⟨r.req, (b.handle config r).2.1, r.json⟩])
  armed _ _ := true
  fire b d := (b.fire d, [])

/-! ## Properties

Stated of the board, so they hold of the spec's state and of the actor's. Each is checked of
every reachable state in `Check.lean` and proved in `Rookery.Proofs`. -/

namespace Board

variable {N C : Type} [DecidableEq N] [DecidableEq C]

def ids (b : Board N C) : List PostId :=
  b.accounts.flatMap fun (_, p) => p.posts.map (·.id)

/-- Every post's id is below the next one, so no post accepted later has it. -/
def fresh (b : Board N C) : Bool :=
  b.ids.all (· < b.next)

/-- Every bound of `Config` holds. -/
def bounded (config : Config) (b : Board N C) : Bool :=
  b.accounts.length ≤ config.maxAccounts && b.accounts.all fun (_, p) =>
    p.posts.length ≤ config.maxPosts && p.following.length ≤ config.maxFollows
      && p.window ≤ config.maxPerWindow && p.sessions.ids.length ≤ config.maxSessions
      && p.attempts.failures ≤ config.maxFailures

end Board

/-- The account whose secrets a reply carries: a session or the generation of a token. -/
def Reply.secretOf {N : Type} : Reply N → Option N
  | .loggedIn n _ | .token n _ => some n
  | _ => none

end Rookery
