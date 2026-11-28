import Rookery
import Lanes.Testing

/-!
# Model checks

Two accounts, `0` and `1`, with a right credential and a wrong one, and bounds small enough to
reach: one session, two failures, two posts kept, one follow, two posts a window, timelines of
two.

First the spec alone (rule 1.2): every order of a script's requests, each sent once those it
waits for are answered, and every deadline passing between them, checked against each claim
with a history kept beside the board. Then the system: the same scripts through `board`, its
timers firing at any moment, every response and every deadline checked against the spec by the
monitor, under crashes and links that lose and reorder requests. Then three seeded bugs, each
of which a check must catch.

`rookeryCheck` prints each report and fails if one is not as expected.
-/

namespace Rookery.Check

open Lanes

abbrev N := Fin 2
abbrev C := Fin 2

def right : C := 0
def wrong : C := 1

def config : Config :=
  { maxAccounts := 2, maxSessions := 1, maxFailures := 2, maxPosts := 3, maxFollows := 1,
    maxPerWindow := 2, timelineMax := 2, window_ms := 1000, session_ms := some 1000,
    lockout_ms := some 1000 }

def hi : Body := ⟨"hi", rfl⟩
def yo : Body := ⟨"yo", rfl⟩

/-- A request and the requests whose answers it waits for. -/
abbrev Script := List (Request N C × List ReqId)

def signUp (req : ReqId) (n : N) (bot := false) : Request N C := .signUp req n right bot
def logIn (req : ReqId) (n : N) (c : C := right) : Request N C := .logIn req n c 0
def web (req : ReqId) (n : N) (session : Sid) (op : Op N) : Request N C := .web req n session op
def api (req : ReqId) (n : N) (seq : Nat) (op : Op N) (token := 1) : Request N C :=
  .api req n token seq op

/-- Both sign up and log in, `1` as a bot; `1` follows `0`. -/
def setup : Script :=
  [ (signUp 1 0, []), (signUp 2 1 true, []), (logIn 3 0, [1]), (logIn 4 1, [2]),
    (web 5 1 4 (.follow 0), [3, 4]) ]

/-- `0` posts twice and deletes its first post; `1` reads its timeline as the posts land and
after the delete is answered, and anyone reads `0`'s posts. -/
def social : Script :=
  setup ++
  [ (web 6 0 3 (.post hi), [5]), (web 7 0 3 (.post yo), [6]),
    (web 8 1 4 .timeline, [6]), (web 9 0 3 (.delete 0), [7, 8]),
    (web 10 1 4 .timeline, [9]), (.profile 11 0 false, [10]), (web 12 1 4 (.delete 1), [10]) ]

/-- `1` gets a token and posts through the API: a post sent twice with one sequence number, as a
bot that retries; an older number; two more posts, the window full; a token of the wrong
generation; a read, a delete, and the read again with its `seq`, as a bot that retries it; a
post with the delete's `seq`. -/
def bots : Script :=
  [ (signUp 2 1 true, []), (logIn 4 1, [2]), (.newToken 5 1 4 0, [4]),
    (api 6 1 1 (.post hi), [5]), (api 7 1 1 (.post hi), [5]),
    (api 8 1 0 (.post yo), [6, 7]), (api 9 1 2 (.post yo), [6, 7]),
    (api 10 1 3 (.post yo), [9]), (api 11 1 4 .timeline (token := 2), [9]),
    (api 12 1 5 .timeline, [10]), (api 13 1 6 (.delete 0), [12]), (api 14 1 5 .timeline, [13]),
    (api 15 1 6 (.post hi), [14]) ]

/-- Two wrong credentials lock `0`; a second log-in of `1` closes its first session; a session
is no key to another account; a log-out ends a session. -/
def abuse : Script :=
  [ (signUp 1 0, []), (signUp 2 1, [1]), (logIn 3 0 wrong, [2]), (logIn 4 0 wrong, [3]),
    (logIn 5 0, [4]), (logIn 6 1, [5]), (logIn 7 1, [6]), (web 8 1 6 .timeline, [7]),
    (web 9 0 7 (.post hi), [7]), (.logOut 10 1 7, [8, 9]), (web 11 1 7 .timeline, [10]),
    (signUp 12 0, [11]) ]

/-! ## The spec alone -/

/-- A history kept beside the board, so that claims about runs are claims about states. -/
structure History where
  /-- Ids whose delete was answered. -/
  deleted : List PostId := []
  /-- Posts accepted for each account since its window last ended. -/
  inWindow : List (N × Nat) := []
  /-- Whatever a claim saw go wrong. -/
  broken : List String := []
  deriving BEq, Hashable, Repr

structure SpecWorld where
  board : Board N C
  todo : Script
  answered : List (Response N)
  history : History
  deriving BEq, Hashable

def count (h : History) (n : N) : Nat := ((h.inWindow.find? (·.1 == n)).map (·.2)).getD 0

def setCount (h : History) (n : N) (k : Nat) : History :=
  { h with inWindow := (n, k) :: h.inWindow.filter (·.1 != n) }

/-- The posts of the accounts `n` follows and its own, newest first, computed another way than
`Board.feed`: from every post on the board, by insertion. -/
def reference (b : Board N C) (n : N) : List (N × Post) :=
  let following := ((b.get? n).map (·.following)).getD []
  let all := b.accounts.flatMap fun (a, p) => p.posts.map (a, ·)
  let mine := all.filter fun (a, _) => a == n || following.contains a
  (mine.foldr (fun (x : N × Post) acc =>
      acc.filter (fun (y : N × Post) => y.2.id > x.2.id) ++ [x] ++ acc.filter (·.2.id < x.2.id))
    []).take config.timelineMax

def account (r : Request N C) : Option N :=
  match r with
  | .profile .. => none
  | r => some r.name

/-- What each claim says of one request taking effect, from `b` to `b'` with `reply`. -/
def judge (h : History) (b b' : Board N C) (r : Request N C) (reply : Reply N) : History :=
  let gone := b.accounts.flatMap fun (a, p) =>
    (p.posts.filter fun q => !(b'.postsOf a).contains q).map (a, ·.id)
  let byAuthor := gone.all fun (a, id) => match r with
    | .web _ n _ (.delete d) | .api _ n _ _ (.delete d) => a == n && id == d
    | _ => false
  let shown := match reply with
    | .feed list => list.map fun (x : N × Post) => x.2.id
    | _ => []
  let timelineOk := match r, reply with
    | .web _ n _ .timeline, .feed list | .api _ n _ _ .timeline, .feed list =>
      list == reference b n
    | _, _ => true
  let secretOk := match reply.secretOf with
    | some m => account r == some m
    | none => true
  let accepted := b'.ids.filter (!b.ids.contains ·)
  let h := if accepted.isEmpty then h else setCount h r.name (count h r.name + accepted.length)
  let h := match r, reply with
    | .web _ _ _ (.delete d), .deleted | .api _ _ _ _ (.delete d), .deleted =>
      { h with deleted := d :: h.deleted }
    | _, _ => h
  let fail := [("a post is gone that its author did not delete", byAuthor),
      ("a read shows a post whose delete was answered", shown.all (!h.deleted.contains ·)),
      ("a timeline is not the newest posts of the accounts followed", timelineOk),
      ("a reply carries another account's secrets", secretOk)].filterMap fun (name, ok) =>
    if ok then none else some name
  { h with broken := h.broken ++ fail }

def specStep (handle : Board N C → Request N C → Board N C × Reply N × Timers)
    (w : SpecWorld) (k : Nat) : Option SpecWorld := do
  let (r, after) ← w.todo[k]?
  if !after.all fun id => w.answered.any (·.req == id) then none
  let (b', reply, _) := handle w.board r
  some { board := b', todo := w.todo.eraseIdx k, answered := ⟨r.req, reply, r.json⟩ :: w.answered
         history := judge w.history w.board b' r reply }

def armed (b : Board N C) : List (Deadline N) :=
  b.accounts.flatMap fun (n, p) =>
    (if p.window != 0 then [.window n] else []) ++ (if p.attempts.locked then [.unlock n] else [])
      ++ p.sessions.ids.map (.expire n)

def fireStep (w : SpecWorld) (d : Deadline N) : SpecWorld :=
  let history := match d with
    | .window n => setCount w.history n 0
    | _ => w.history
  { w with board := w.board.fire d, history }

def specModel (script : Script)
    (handle : Board N C → Request N C → Board N C × Reply N × Timers := (·.handle config)) :
    Check.Model SpecWorld String where
  init := [{ board := {}, todo := script, answered := [], history := {} }]
  next w :=
    ((List.range w.todo.length).filterMap fun k =>
      (specStep handle w k).map fun w' => ("request", w')) ++
    (armed w.board).map fun d => ("deadline", fireStep w d)

def specClaims : List (Check.Property SpecWorld) :=
  [ .always "every bound of the configuration holds" fun w => w.board.bounded config,
    .always "every post's id is below the next" fun w => w.board.fresh,
    .always "no account has more than maxPerWindow posts accepted in a window" fun w =>
      w.history.inWindow.all (·.2 ≤ config.maxPerWindow),
    .always "each claim holds of every request" fun w => w.history.broken.isEmpty ]

def replied (answered : List (Response N)) (req : ReqId) (reply : Reply N) : Bool :=
  answered.any fun r => r.req == req && r.reply == reply

def feedOf (answered : List (Response N)) (req : ReqId) : Option (List PostId) :=
  answered.findSome? fun r => if r.req == req then
    match r.reply with
    | .feed list => some (list.map fun (x : N × Post) => x.2.id)
    | _ => none
  else none

def socialWitnesses (answered : SpecWorld → List (Response N)) :
    List (Check.Property SpecWorld) :=
  [ .sometimes "a timeline shows both posts, newest first" fun w =>
      feedOf (answered w) 8 == some [1, 0],
    .sometimes "a timeline read as the second post lands may show the first alone" fun w =>
      feedOf (answered w) 8 == some [0],
    .sometimes "after the delete the timeline shows only the other post" fun w =>
      feedOf (answered w) 10 == some [1],
    .sometimes "anyone reads an account's posts" fun w => feedOf (answered w) 11 == some [1],
    .sometimes "another account cannot delete a post" fun w => replied (answered w) 12 .notYours ]

def botWitnesses : List (Check.Property SpecWorld) :=
  [ .sometimes "a post retried is posted once, and both get its id" fun w =>
      replied w.answered 6 (.posted 0) && replied w.answered 7 (.posted 0),
    .sometimes "an older sequence number is stale" fun w => replied w.answered 8 .stale,
    .sometimes "a sequence number used for another change is refused" fun w =>
      replied w.answered 15 .reused,
    .sometimes "the window is full" fun w => replied w.answered 10 .rateLimited,
    .sometimes "a post is accepted again once the window ends" fun w =>
      replied w.answered 10 (.posted 2),
    .sometimes "a token of another generation is refused" fun w =>
      replied w.answered 11 .badToken,
    .sometimes "a read retried after a delete is answered afresh" fun w =>
      replied w.answered 13 .deleted && (feedOf w.answered 14).any (!·.contains 0) ]

def abuseWitnesses (answered : SpecWorld → List (Response N)) :
    List (Check.Property SpecWorld) :=
  [ .sometimes "two wrong credentials lock the account" fun w => replied (answered w) 5 .locked,
    .sometimes "the lock lifts" fun w => replied (answered w) 5 (.loggedIn 0 5 0),
    .sometimes "a second log-in closes the first session" fun w =>
      replied (answered w) 8 .noSession,
    .sometimes "a session is no key to another account" fun w =>
      replied (answered w) 9 .noSession,
    .sometimes "after a log-out the session opens nothing" fun w =>
      replied (answered w) 11 .noSession,
    .sometimes "a session ends on its own" fun w =>
      replied (answered w) 10 .noSession,
    .sometimes "a name is taken once" fun w => replied (answered w) 12 .nameTaken ]

def checkSpec (script : Script) (witnesses : List (Check.Property SpecWorld)) :=
  Check.search (specModel script) (specClaims ++ witnesses) {} id

/-! ## The system -/

instance : (sig N C).Inspect := {}
instance (cfg : Config) : (system N C cfg).Inspect := {}

/-- Without session and lock timers, for the scenarios that do not need them. -/
def quiet : Config := { config with session_ms := none, lockout_ms := none }

def clients (script : Script) : Driver (sig N C) (Waiting (Request N C)) :=
  Driver.after (fun out => some out.req) script

abbrev World' (sys : System (sig N C)) :=
  World sys (Waiting (Request N C) × Check.Monitor (Request N C) (Response N) (Board N C))

def outbox {sys : System (sig N C)} (w : World' sys) : List (Response N) := w.state.outbox

def boardOf {cfg : Config} (w : World' (system N C cfg)) : Board N C := w.state.state ()

def systemClaims (cfg : Config) : List (Check.Property (World' (system N C cfg))) :=
  [ Check.refines "every response and every deadline is one the spec allows",
    .always "every bound of the configuration holds" fun w => (boardOf w).bounded config,
    .always "every post's id is below the next" fun w => (boardOf w).fresh ]

def check {sys : System (sig N C)} [sys.Inspect] (script : Script)
    (props : List (Check.Property (World' sys))) (env : EnvModel (sig N C) := {})
    (maxCrashes : Nat := 0) :=
  Check.system sys
    { env, maxCrashes, driver := (spec N C config).monitored (clients script) deadlines } props

/-- The board may crash; it comes back with its state, as the semantics models a crash. -/
def crashing : EnvModel (sig N C) where
  mayCrash _ := true

/-- Requests lost and reordered on their way in, and the board crashing. -/
def lossyIn : EnvModel (sig N C) where
  link _ _ := { ordered := false, lossy := true }
  mayCrash _ := true

def systemWitnesses (cfg : Config) (witnesses : (SpecWorld → List (Response N)) → List (Check.Property SpecWorld)) :
    List (Check.Property (World' (system N C cfg))) :=
  (witnesses fun w => w.answered).map fun
    | .sometimes name p => .sometimes name fun w =>
      p { board := boardOf w, todo := [], answered := outbox w, history := {} }
    | .always name p => .always name fun w =>
      p { board := boardOf w, todo := [], answered := outbox w, history := {} }

/-! ## Seeded bugs -/

/-- A board like the real one, with `handle` replaced. -/
def boardWith {S : Type} (init : S)
    (handle : S → Request N C → S × Reply N × Timers) (fire : S → Deadline N → S) :
    (sig N C).Actor () S where
  init := init
  step s
    | .request r =>
      let (s', reply, timers) := handle s r
      (s', .emit ⟨r.req, reply, r.json⟩ :: timerEffects quiet r.name timers)
    | .deadline d => (fire s d, [])
  recover s := (s, [])

/-- Fan-out on write without the delete: each post accepted is also put in a list every
timeline reads, and a delete takes it out of its author's posts but not out of that list. -/
def keepsDeleted (s : Board N C × List (N × Post)) (r : Request N C) :
    (Board N C × List (N × Post)) × Reply N × Timers :=
  let (b, recent) := s
  match r with
  | .web _ n session .timeline =>
    let (b', reply, timers) := b.withSession n session fun p =>
      (b, .feed ((recent.filter fun (a, _) => a == n || p.following.contains a).take
        config.timelineMax), {})
    ((b', recent), reply, timers)
  | r =>
    let (b', reply, timers) := b.handle config r
    let new := ((b'.postsOf r.name).filter fun q => reply == .posted q.id).map (r.name, ·)
    ((b', new ++ recent), reply, timers)

abbrev keepsDeletedSystem : System (sig N C) where
  State _ := Board N C × List (N × Post)
  actor _ := boardWith ({}, []) keepsDeleted fun (b, recent) d => (b.fire d, recent)
  accept r := ⟨(), .request r⟩

/-- A delete that finds the post wherever it is, not only among the poster's own. -/
def anyoneDeletes (b : Board N C) : Request N C → Board N C × Reply N × Timers
  | .web _ n session (.delete id) => b.withSession n session fun _ =>
    match b.accounts.find? fun (_, p) => p.posts.any (·.id == id) with
    | some (a, p) => (b.set a { p with posts := p.posts.filter (·.id != id) }, .deleted, {})
    | none => (b, .notYours, {})
  | r => b.handle config r

abbrev anyoneDeletesSystem : System (sig N C) where
  State _ := Board N C
  actor _ := boardWith {} anyoneDeletes Board.fire
  accept r := ⟨(), .request r⟩

/-- A rate limit off by one: the window is full only past `maxPerWindow`. -/
def offByOne (b : Board N C) : Request N C → Board N C × Reply N × Timers
  | .api _ n token seq (.post body) =>
    match b.get? n with
    | some p =>
      if config.maxPerWindow < p.window then (b, .rateLimited, {})
      else b.api { config with maxPerWindow := config.maxPerWindow + 1 } n p token seq (.post body)
    | none => (b, .badToken, {})
  | r => b.handle config r

abbrev offByOneSystem : System (sig N C) where
  State _ := Board N C
  actor _ := boardWith {} offByOne Board.fire
  accept r := ⟨(), .request r⟩

instance : keepsDeletedSystem.Inspect := {}
instance : anyoneDeletesSystem.Inspect := {}
instance : offByOneSystem.Inspect := {}

def matchesSpec {sys : System (sig N C)} : Check.Property (World' sys) :=
  Check.refines "every response and every deadline is one the spec allows"

/-! ## The bridge, without a socket -/

namespace Bridge

open Rookery.Web Lanes.Http

def settings : Settings :=
  { keys := .of (.of "test key".toUTF8)
    password := { cost := { ops := 1, mem_kib := 8 }, pepper := "pepper".toUTF8 }
    origin := "http://127.0.0.1:8080", secure := false }

def ann : Name := ⟨"ann", rfl⟩
def bob : Name := ⟨"bob", rfl⟩

def cookieOf (name : Name) (session : Sid) : String := sessionToken settings name session 1000

def request (method : Method) (path : List String) (headers : List (String × String))
    (body : String) : Http.Request :=
  { method, path, headers := ("origin", settings.origin) :: headers, body := body.toUTF8 }

def webPost (path : String) (fields : List (String × String)) (cookie : Option String) :
    Http.Request :=
  request .post [path] ((cookie.map fun c => [("cookie", s!"{sessionCookie}={c}")]).getD [])
    ("&".intercalate (fields.map fun (k, v) => s!"{k}={v}"))

def apiPost (path : String) (body : String) (token : String) : Http.Request :=
  request .post ["api", path] [("authorization", s!"Bearer {token}")] body

def decoded (r : Http.Request) : Except Http.Response In :=
  decode settings 9 (prepare settings r)

def same : Except Http.Response In → Except Http.Response In → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

def status : Except Http.Response In → Nat
  | .ok _ => 0
  | .error r => r.status

def contains (bytes : ByteArray) (text : String) : Bool :=
  (((String.fromUTF8? bytes).getD "").splitOn text).length > 1

def tests : List (String × Bool) :=
  let csrf := Auth.formToken settings.keys (sessionOf ann 7)
  let hello : Body := ⟨"hello", rfl⟩
  [ ("bridge: a session's cookie makes a request of its account, whatever the form says",
      same (decoded (webPost "post" [("body", "hello"), ("csrf", csrf), ("name", "bob")]
          (some (cookieOf ann 7))))
        (.ok (.web 9 ann 7 (.post hello)))),
    ("bridge: a cookie whose payload names another account does not verify",
      let forged := (cookieOf ann 7).replace ".7.ann" ".7.bob"
      same (decoded (webPost "post" [("body", "hello"), ("csrf", csrf)] (some forged)))
        (.error notLoggedIn)),
    ("bridge: a form token of another session is refused",
      status (decoded (webPost "post" [("body", "hello"),
        ("csrf", Auth.formToken settings.keys (sessionOf ann 8))] (some (cookieOf ann 7)))) == 403),
    ("bridge: an API token makes a request of its account and generation",
      same (decoded (apiPost "post" "{\"text\": \"hello\", \"seq\": 4}" (apiToken settings bob 2 0)))
        (.ok (.api 9 bob 2 4 (.post hello)))),
    ("bridge: an API token is refused from its expiry on",
      status (decoded (stamp settings.apiToken_s
        (apiPost "post" "{\"text\": \"hello\", \"seq\": 4}" (apiToken settings bob 2 0)))) == 401),
    ("bridge: an API token that does not verify is refused",
      status (decoded (apiPost "post" "{\"text\": \"hello\", \"seq\": 4}"
        ((apiToken settings ann 2 0).replace ".2.ann" ".2.bob"))) == 401),
    ("bridge: a session cookie is no API token",
      status (decoded (apiPost "post" "{\"text\": \"hello\", \"seq\": 4}" (cookieOf bob 2)))
        == 401),
    ("bridge: a change through the API carries its seq",
      status (decoded (apiPost "post" "{\"text\": \"hello\"}" (apiToken settings bob 2 0))) == 400),
    ("bridge: a password enters the system only as its digest",
      same (decoded (webPost "login" [("name", "ann"), ("password", "longenough")] none))
        (.ok (.logIn 9 ann (settings.password.digest "ann" "longenough") 0))),
    ("bridge: what enters the system holds no password, no cookie and no token",
      let prepared := prepare settings (webPost "login"
        [("name", "ann"), ("password", "longenough")] (some (cookieOf ann 7)))
      let api := prepare settings (apiPost "post" "{}" (apiToken settings bob 2 0))
      !contains prepared.body "longenough" && !(prepared.headers.any (·.1 == "cookie"))
        && !(api.headers.any (·.1 == "authorization"))),
    ("bridge: a verified header a client sends itself is dropped",
      let claimed := request .post ["api", "post"] [(verifiedToken, "2.bob")]
        "{\"text\": \"hello\", \"seq\": 4}"
      status (decoded claimed) == 401),
    ("bridge: a post too long is refused before it reaches the system",
      status (decoded (webPost "post" [("body", String.ofList (List.replicate 281 'a')),
        ("csrf", csrf)] (some (cookieOf ann 7)))) == 200) ]

end Bridge

/-! ## Running them -/

/-- A check, printed as it ends unless the output is JSON, and its result. -/
def timed {S L : Type} (json : Bool) (name : String) (ok : Check.Report S L → Bool)
    (render : Check.Report S L → String) (report : Unit → Check.Report S L) :
    IO Testing.Result := do
  let start ← IO.monoMsNow
  let r := report ()
  let passed := ok r
  let ms := (← IO.monoMsNow) - start
  unless json do
    IO.println s!"== {name}: {if passed then "as expected" else "NOT AS EXPECTED"} ({ms} ms)"
    IO.println (render r)
    (← IO.getStdout).flush
  return .ofBool .check name passed (render r)

def passes {S L : Type} (r : Check.Report S L) : Bool := r.ok

def violates {S L : Type} (property : String) (r : Check.Report S L) : Bool :=
  match r.failure with
  | some (.violated p _) => p == property
  | _ => false

def renderSpec (r : Check.Report SpecWorld String) : String :=
  r.render (fun w => reprStr w.board ++ "\n" ++ reprStr w.history) id

def renderSystem {sys : System (sig N C)} [sys.Inspect] (r : Check.Report (World' sys) (Event (sig N C))) :
    String :=
  r.renderSystem

def main (args : List String) : IO UInt32 := do
  let json := Testing.wantsJson args
  let args := args.filter (· != "--json")
  let all := args.isEmpty
  let mut results : Array Testing.Result := #[]
  if all || args.contains "spec" then
    results := results.push (← timed json "the spec: posts, follows, timelines and a delete" passes
      renderSpec fun _ => checkSpec social (socialWitnesses (·.answered)))
    results := results.push (← timed json "the spec: bots, retries, tokens and the rate limit" passes
      renderSpec fun _ => checkSpec bots botWitnesses)
    results := results.push (← timed json "the spec: locks, sessions and refusals" passes
      renderSpec fun _ => checkSpec abuse (abuseWitnesses (·.answered)))
  if all || args.contains "system" then
    results := results.push (← timed json "the system: posts, follows, timelines and a delete"
      passes renderSystem fun _ =>
        check social (systemClaims quiet ++ systemWitnesses quiet socialWitnesses))
    results := results.push (← timed json "the system: bots, retries, tokens and the rate limit"
      passes renderSystem fun _ => check bots (systemClaims quiet))
    results := results.push (← timed json "the system: locks, sessions and refusals, timers at any moment"
      passes renderSystem fun _ =>
        check abuse (systemClaims config ++ systemWitnesses config abuseWitnesses))
  if all || args.contains "faults" then
    results := results.push (← timed json "the system with a crash anywhere: a delete and timelines"
      passes renderSystem fun _ => check social (systemClaims quiet) crashing 1)
    results := results.push (← timed json "the system with a crash anywhere: bots and retries"
      passes renderSystem fun _ => check bots (systemClaims quiet) crashing 1)
    results := results.push (← timed json
      "the system with requests lost and reordered and a crash anywhere: a delete and timelines"
      passes renderSystem fun _ => check social (systemClaims quiet) lossyIn 1)
  if all || args.contains "bridge" then
    for (name, ok) in Bridge.tests do
      unless json do IO.println s!"== {name}: {if ok then "as expected" else "NOT AS EXPECTED"}"
      results := results.push (.ofBool .test name ok)
  if all || args.contains "bugs" then
    let spec := "every response and every deadline is one the spec allows"
    results := results.push (← timed json "seeded: a timeline that keeps a deleted post"
      (violates spec) renderSystem fun _ => check (sys := keepsDeletedSystem) social [matchesSpec])
    results := results.push (← timed json "seeded: a delete by another account"
      (violates spec) renderSystem fun _ => check (sys := anyoneDeletesSystem) social [matchesSpec])
    results := results.push (← timed json "seeded: a rate limit off by one"
      (violates spec) renderSystem fun _ => check (sys := offByOneSystem) bots [matchesSpec])
    let claims := "each claim holds of every request"
    results := results.push (← timed json "seeded, in the spec alone: a delete by another account"
      (violates claims) renderSpec fun _ =>
        Check.search (specModel social anyoneDeletes) specClaims {} id)
    results := results.push (← timed json "seeded, in the spec alone: a rate limit off by one"
      (violates "no account has more than maxPerWindow posts accepted in a window") renderSpec
      fun _ => Check.search (specModel bots offByOne) (specClaims.drop 1) {} id)
  Testing.report (if json then ["--json"] else []) results.toList
    (shown := if json then 0 else results.size)

end Rookery.Check

def main (args : List String) : IO UInt32 := Rookery.Check.main args
