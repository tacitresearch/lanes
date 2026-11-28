import Rookery
import Rookery.Live
import Lanes.Testing

/-!
# Model checks, the bridge, and rookery on PostgreSQL

The front beside the store's model (`Lanes/Db/Model.lean`), with rookery's own transactions:
every order of a script's requests, each sent once those it waits for are answered, and in the
last scenario answers lost, a lost `COMMIT` taking effect late or never, and the process
restarting. Each claim is judged in every database the store may hold. Bounds are small enough
to reach: two accounts, one session, two failures, three posts kept, one follow, two posts a
window, timelines of two. Every `always` has `sometimes` witnesses beside it (rule 5.3).

Then the bridge, without a socket. Then, with `LANES_POSTGRES` set, rookery over HTTP on a real
PostgreSQL, killed and started again (`Rookery.Live`).
-/

namespace Rookery.Check

open Lanes Lanes.Db

instance : sig.Inspect := {}
instance : system.Inspect := {}

def config : Config :=
  { maxAccounts := 2, maxSessions := 1, maxFailures := 2, maxPosts := 3, maxFollows := 1,
    maxPerWindow := 2, timelineMax := 2, window_s := 10, lockout_s := 10 }

def ann : Name := ⟨"ann", rfl⟩
def bob : Name := ⟨"bob", rfl⟩
def hi : Body := ⟨"hi", rfl⟩
def yo : Body := ⟨"yo", rfl⟩

/-- A request, numbered, and the requests whose answers it waits for. -/
abbrev Script := List (Nat × Ask × List Nat)

def at0 (r : Request) : Ask := { at_s := 0, request := r }

/-- The browser and the bot: the requests still to send, and what came back. -/
structure Client where
  toSend : Script
  answered : List (Nat × Response) := []
  failed : List Nat := []
  deriving DecidableEq, Hashable

instance : BEq Client := instBEqOfDecidableEq

def Client.ready (d : Client) (waits : List Nat) : Bool :=
  waits.all fun w => d.answered.any (·.1 == w) || d.failed.contains w

def client (script : Script) : Outside sig Client where
  init := { toSend := script }
  allow d
    | .request n a =>
      match d.toSend.find? (·.1 == n) with
      | some (_, a', waits) =>
        if a' == a && d.ready waits then some { d with toSend := d.toSend.filter (·.1 != n) } else none
      | none => none
    | .store _ => none
  observe d
    | .answered n r => { d with answered := d.answered ++ [(n, r)] }
    | .failed n => { d with failed := d.failed ++ [n] }
    | .call _ => d

abbrev D := Client × Db.State Ask Response

def world (script : Script) :=
  (client script).both (Db.outside {} (handler config) (Db.Db.empty (schema config)) port)
    fun x => x matches .request ..

def samples (losses : Bool) (d : D) : List In :=
  d.1.toSend.map (fun (n, a, _) => .request n a) ++ Db.samples (handler config) port losses losses d.2

abbrev W := World system D

/-! ## The claims, in every database the store may hold -/

def rowsOf {α : Type} (t : TableOf α) (db : Db.Db) : List α := (db.rows t.table.name).filterMap t.ofRow

def everyDb (w : W) (p : Db.Db → Bool) : Bool := w.driver.2.worlds.all fun world => p world.db

def someDb (w : W) (p : Db.Db → Bool) : Bool := w.driver.2.worlds.any fun world => p world.db

/-- Every bound of `Config` holds. -/
def bounded (db : Db.Db) : Bool :=
  let ms := rowsOf members db
  let sessions := rowsOf (Auth.Rows.Sessions.table config.sessions) db
  let attempts := rowsOf (Auth.Rows.Failures.table config.failures) db
  ms.length ≤ config.maxAccounts && ms.all fun m =>
    ((rowsOf posts db).filter (·.author == m.name)).length ≤ config.maxPosts
      && ((rowsOf follows db).filter (·.follower == m.name)).length ≤ config.maxFollows
      && (rowsOf windows db).all (·.count.toInt ≤ config.maxPerWindow)
      && (sessions.filter (·.user == m.name)).length ≤ config.maxSessions
      && attempts.all (·.failures.toInt ≤ config.maxFailures)

/-- No two posts have one id, and every id is below the next one: an id is never given twice. -/
def freshIds (db : Db.Db) : Bool :=
  let ids := (rowsOf posts db).map (·.id)
  let next := ((rowsOf counters db).find? (·.name == "post")).map (·.next) |>.getD 0
  ids.eraseDups.length == ids.length && ids.all (· < next)

/-- A member's posts are only ever its own: each post's author is a member. -/
def authored (db : Db.Db) : Bool :=
  (rowsOf posts db).all fun p => (rowsOf members db).any (·.name == p.author)

/-- A member has at most one API change remembered. -/
def oneKey (db : Db.Db) : Bool :=
  (rowsOf members db).all fun m =>
    ((rowsOf keys.rows db).filter fun (k, _) => k.startsWith (m.name ++ "/")).length ≤ 1

def answers (w : W) : List (Nat × Response) := w.driver.1.answered

def replyOf (w : W) (n : Nat) : Option Reply := ((answers w).find? (·.1 == n)).map (·.2.reply)

def always : List (Check.Property W) :=
  [ .always "every bound of Config holds, in every database the store may hold" (everyDb · bounded),
    .always "no two posts have one id, and every id is below the next" (everyDb · freshIds),
    .always "every post's author is a member" (everyDb · authored),
    .always "a member has at most one API change remembered" (everyDb · oneKey) ]

def check (script : Script) (claims : List (Check.Property W)) (losses := false) (restarts := 0) :=
  Check.system system
    { env := { mayRestart := restarts > 0 }, driver := (world script).driver (samples losses),
      maxRestarts := restarts }
    (always ++ claims) {}

/-! ## Scripts -/

def signUp (n : Name) (bot := false) : Ask := at0 (.signUp n "hash" bot)
def logIn (n : Name) (checked : Checked := .right none) (at_s : Int64 := 0) : Ask :=
  { at_s, request := .logIn n checked }
def web (n : Name) (session : Int64) (op : Action) (at_s : Int64 := 0) : Ask :=
  { at_s, request := .web n session op }
def api (n : Name) (seq : Int64) (op : Action) (token : Int64 := 1) : Ask :=
  at0 (.api n token seq op)

/-- Both sign up and log in (sessions 0 and 1); `bob` follows `ann`; `ann` posts twice, deletes
her first post; `bob` reads his timeline after the delete, and `ann`'s posts are read; `bob`
tries to delete `ann`'s second post. -/
def social : Script :=
  [ (1, signUp ann, []), (2, signUp bob, [1]), (3, logIn ann, [2]), (4, logIn bob, [3]),
    (5, web bob 1 (.follow ann), [4]), (6, web ann 0 (.post hi), [5]), (7, web ann 0 (.post yo), [6]),
    (8, web ann 0 (.delete 0), [7]), (9, web bob 1 .timeline, [8]), (10, at0 (.profile ann false), [8]),
    (11, web bob 1 (.delete 1), [8]) ]

def feedIds (r : Option Reply) : List Int64 :=
  match r with
  | some (.feed ps) => ps.map (·.id)
  | _ => []

def socialClaims : List (Check.Property W) :=
  [ .always "a post deleted is in no read asked for after its delete was answered" fun w =>
      replyOf w 8 != some .deleted || (!(feedIds (replyOf w 9)).contains 0 && !(feedIds (replyOf w 10)).contains 0),
    .always "a member cannot delete another's post" fun w => replyOf w 11 != some .deleted,
    .sometimes "a timeline shows a post of another account" fun w => feedIds (replyOf w 9) == [1],
    .sometimes "a post is deleted" fun w => replyOf w 8 == some .deleted ]

/-- `bob`, a bot, gets a token and posts: once with `seq` 1, again with it, as a bot that retries;
an older `seq`; two more, the window full; another change with a used `seq`. -/
def bots : Script :=
  [ (1, signUp bob true, []), (2, logIn bob, [1]), (3, at0 (.newToken bob 0), [2]),
    (4, api bob 1 (.post hi), [3]), (5, api bob 1 (.post hi), [3]), (6, api bob 0 (.post yo), [4, 5]),
    (7, api bob 2 (.post yo), [4, 5]), (8, api bob 3 (.post yo), [7]), (9, api bob 3 (.follow ann), [8]),
    (10, api bob 4 .timeline (token := 2), [8]) ]

def botClaims : List (Check.Property W) :=
  [ .always "a change sent twice with one seq is acted on once" fun w =>
      everyDb w fun db => ((rowsOf posts db).filter (·.body == "hi")).length ≤ 1,
    .always "both are answered as the first was" fun w =>
      match replyOf w 4, replyOf w 5 with
      | some a, some b => a == b
      | _, _ => true,
    .always "an older seq is stale" fun w => (replyOf w 6).all (· == .stale),
    .always "another change with a used seq is refused" fun w => (replyOf w 9).all (· == .reused),
    .always "a token of another generation is refused" fun w => (replyOf w 10).all (· == .badToken),
    .sometimes "the window is full" fun w => replyOf w 8 == some .rateLimited,
    .sometimes "a retry is answered as the first" fun w =>
      (replyOf w 4).isSome && replyOf w 4 == replyOf w 5 ]

/-- Two wrong passwords lock `ann`; the right one is refused while locked, and let in once the
lock's time has passed; a second log-in of `bob` closes his first session; a session is no key
to another account; a log-out ends a session. -/
def abuse : Script :=
  [ (1, signUp ann, []), (2, signUp bob, [1]), (3, logIn ann .wrong, [2]), (4, logIn ann .wrong, [3]),
    (5, logIn ann, [4]), (6, logIn ann (at_s := 20), [5]), (7, logIn bob, [6]), (8, logIn bob, [7]),
    (9, web bob 1 .timeline, [8]), (10, web ann 2 (.post hi), [8]), (11, web bob 2 .timeline, [9, 10]),
    (12, at0 (.logOut bob 2), [11]), (13, web bob 2 .timeline, [12]) ]

def abuseClaims : List (Check.Property W) :=
  [ .always "a locked account is refused, even the right password" fun w =>
      (replyOf w 5).all (· == .locked),
    .always "a log-in past maxSessions closes the oldest session" fun w =>
      replyOf w 8 == none || (replyOf w 9).all (· == .noSession),
    .always "a session is no key to another account" fun w => (replyOf w 10).all (· == .noSession),
    .always "a session closed is closed" fun w => (replyOf w 13).all (· == .noSession),
    .sometimes "a lock lifts after its time" fun w => replyOf w 6 == some (.loggedIn 0 20),
    .sometimes "a session is let in" fun w => (replyOf w 11).any fun | .feed _ => true | _ => false ]

/-- A post, its answer lost, sent again with its `seq`, while the process restarts. -/
def lost : Script :=
  [ (1, signUp bob true, []), (2, logIn bob, [1]), (3, at0 (.newToken bob 0), [2]),
    (4, api bob 1 (.post hi), [3]), (5, api bob 1 (.post hi), [4]) ]

def lostClaims : List (Check.Property W) :=
  [ .always "a change sent twice with one seq is acted on once, with lost answers and restarts" fun w =>
      everyDb w fun db => ((rowsOf posts db).filter (·.body == "hi")).length ≤ 1,
    .sometimes "an answer is lost" fun w => w.driver.2.worlds.any fun world => !world.lost.isEmpty,
    .sometimes "the retry is answered as a post" fun w => (replyOf w 5).any fun | .posted _ => true | _ => false ]

/-! ## The bridge, without a socket -/

namespace Bridge

open Rookery.Web Lanes.Http

def settings : Settings :=
  { keys := .of (.of "test key".toUTF8)
    password := { cost := { ops := 1, mem_kib := 8 }, pepper := "pepper".toUTF8 }
    origin := "http://127.0.0.1:8080", secure := false }

def cookieOf (name : Name) (session : Int64) : String := sessionToken settings name session 1000

def request (method : Method) (path : List String) (headers : List (String × String))
    (body : String) : Http.Request :=
  { method, path, headers := ("origin", settings.origin) :: headers, body := body.toUTF8 }

def webPost (path : String) (fields : List (String × String)) (cookie : Option String) :
    Http.Request :=
  request .post [path] ((cookie.map fun c => [("cookie", s!"{sessionCookie}={c}")]).getD [])
    ("&".intercalate (fields.map fun (k, v) => s!"{k}={v}"))

def apiPost (path : String) (body : String) (token : String) : Http.Request :=
  request .post ["api", path] [("authorization", s!"Bearer {token}")] body

def salt : ByteArray := ByteArray.mk (Array.replicate 16 7)

/-- As the server takes a request: `arrive`, then `prepare`, then `decode`. -/
def decoded (r : Http.Request) (stored : Option String := none) : Except Http.Response Rookery.In :=
  decode settings 9 (prepare settings (arrive settings 0 salt stored r))

def asked (r : Http.Request) (stored : Option String := none) : Except Http.Response Request :=
  (decoded r stored).map fun | .request _ a => a.request | _ => .profile ⟨"x", rfl⟩ false

def same : Except Http.Response Request → Except Http.Response Request → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

def status : Except Http.Response Request → Nat
  | .ok _ => 0
  | .error r => r.status

def contains (bytes : ByteArray) (text : String) : Bool :=
  (((String.fromUTF8? bytes).getD "").splitOn text).length > 1

/-- The hash stored at a cost, and the same password stored at another. -/
def stored : String := (settings.password.hash salt rfl "longenough").encode
def storedOther : String :=
  ({ settings.password with cost := { ops := 1, mem_kib := 16 } }.hash salt rfl "longenough").encode

def tests : List (String × Bool) :=
  let csrf := Auth.formToken settings.keys (sessionOf ann 7)
  let hello : Body := ⟨"hello", rfl⟩
  [ ("bridge: a session's cookie makes a request of its account, whatever the form says",
      same (asked (webPost "post" [("body", "hello"), ("csrf", csrf), ("name", "bob")]
          (some (cookieOf ann 7))))
        (.ok (.web ann 7 (.post hello)))),
    ("bridge: a cookie whose payload names another account does not verify",
      let forged := (cookieOf ann 7).replace ".7.ann" ".7.bob"
      same (asked (webPost "post" [("body", "hello"), ("csrf", csrf)] (some forged)))
        (.error notLoggedIn)),
    ("bridge: a form token of another session is refused",
      status (asked (webPost "post" [("body", "hello"),
        ("csrf", Auth.formToken settings.keys (sessionOf ann 8))] (some (cookieOf ann 7)))) == 403),
    ("bridge: an API token makes a request of its account and generation",
      same (asked (apiPost "post" "{\"text\": \"hello\", \"seq\": 4}" (apiToken settings bob 2 0)))
        (.ok (.api bob 2 4 (.post hello)))),
    ("bridge: an API token that does not verify is refused",
      status (asked (apiPost "post" "{\"text\": \"hello\", \"seq\": 4}"
        ((apiToken settings ann 2 0).replace ".2.ann" ".2.bob"))) == 401),
    ("bridge: a session cookie is no API token",
      status (asked (apiPost "post" "{\"text\": \"hello\", \"seq\": 4}" (cookieOf bob 2))) == 401),
    ("bridge: a change through the API carries its seq",
      status (asked (apiPost "post" "{\"text\": \"hello\"}" (apiToken settings bob 2 0))) == 400),
    ("bridge: a sign-up's password enters the system only as its hash, with a random salt",
      same (asked (webPost "signup" [("name", "ann"), ("password", "longenough")] none))
        (.ok (.signUp ann stored false))),
    ("bridge: a log-in's password is checked against the stored hash",
      same (asked (webPost "login" [("name", "ann"), ("password", "longenough")] none) (some stored))
          (.ok (.logIn ann (.right none)))
        && same (asked (webPost "login" [("name", "ann"), ("password", "wrong one")] none) (some stored))
          (.ok (.logIn ann .wrong))
        && same (asked (webPost "login" [("name", "ann"), ("password", "longenough")] none) none)
          (.ok (.logIn ann .wrong))),
    ("bridge: a hash stored at another cost verifies, and is made again at the deployment's",
      same (asked (webPost "login" [("name", "ann"), ("password", "longenough")] none) (some storedOther))
        (.ok (.logIn ann (.right (some stored))))),
    ("bridge: what enters the system holds no password, no cookie and no token",
      let prepared := prepare settings (arrive settings 0 salt (some stored) (webPost "login"
        [("name", "ann"), ("password", "longenough")] (some (cookieOf ann 7))))
      let api := prepare settings (apiPost "post" "{}" (apiToken settings bob 2 0))
      !contains prepared.body "longenough" && !(prepared.headers.any (·.1 == "cookie"))
        && !(api.headers.any (·.1 == "authorization"))),
    ("bridge: a header the server writes that a client sends itself is dropped",
      let claimed := request .post ["api", "post"] [(verifiedToken, "2.bob")]
        "{\"text\": \"hello\", \"seq\": 4}"
      let checked := request .post ["login"] [(passwordChecked, "right")] "name=ann"
      status (asked claimed) == 401 && status (asked checked) == 500),
    ("bridge: a post too long is refused before it reaches the system",
      status (asked (webPost "post" [("body", String.ofList (List.replicate 281 'a')),
        ("csrf", csrf)] (some (cookieOf ann 7)))) == 200) ]

end Bridge

/-! ## Running them -/

def live : IO (List (String × Bool)) := do
  let some spec ← IO.getEnv "LANES_POSTGRES"
    | return [("rookery on PostgreSQL: skipped, LANES_POSTGRES is not set", true)]
  let [host, portText] := spec.splitOn ":" | return [("LANES_POSTGRES is host:port", false)]
  let pg : Postgres.Client.Config :=
    { host, port := (portText.toNat?.getD 5432).toUInt16, sslmode := .disable,
      conn := { user := "lanes_trust", database := "lanes_test" } }
  let dir : System.FilePath := ".lake/live"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDirAll dir
  Rookery.Live.run dir pg

def main (args : List String) : IO UInt32 := do
  let json := Testing.wantsJson args
  let results : List (String × Check.Report W (Event sig)) :=
    [ ("posts, a follow, a timeline after a delete, a delete by another", check social socialClaims),
      ("a bot's token, a post retried with its seq, an older seq, the window full, a seq reused",
        check bots botClaims),
      ("a lock and its lifting, a session closed by another log-in, a session of another account",
        check abuse abuseClaims),
      ("a post retried with its seq, answers lost and the process restarting",
        check lost lostClaims (losses := true) (restarts := 1)) ]
  let checks := results.map fun (name, r) =>
    Testing.Result.check s!"rookery beside the store's model: {name}" r r.renderSystem
  unless json do
    for (name, r) in results do IO.println s!"== {name}\n{r.renderSystem}"
  Testing.report args (checks ++ Testing.Result.tests Bridge.tests ++ Testing.Result.tests (← live))

end Rookery.Check

def main (args : List String) : IO UInt32 := Rookery.Check.main args
