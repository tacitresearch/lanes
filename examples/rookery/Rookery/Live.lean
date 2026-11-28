import Rookery.Serve

/-!
rookery over HTTP on PostgreSQL, as a browser and a bot use it: `rookery` started as a process
on tables that hold nothing, a person and a bot signed up, posts made, followed and read in
timelines, a post deleted, a bot's post retried, the rate limit reached, a log-out; then the
process killed with SIGKILL and started again, with everything as it was. Then started at
another Argon2id cost, after which a log-in stores the password's hash again at that cost; and
with a short lock, which five wrong passwords close and time lifts. Also what must be refused: a
delete of another account's post, a token that does not verify, a form without its token.

It needs `lake build` first (it starts `.lake/build/bin/rookery`) and `LANES_POSTGRES`.
-/

open Lanes Lanes.Http Std Std.Async

namespace Rookery.Live

def port : UInt16 := 47321

def origin : String := s!"http://127.0.0.1:{port}"

def form (fields : List (String × String)) : String :=
  "&".intercalate (fields.map fun (k, v) => percentEncode k ++ "=" ++ percentEncode v)

def send (request : Http.Request) : IO Http.Response :=
  Http.Client.fetch port request

def path (p : String) : List String := (p.splitOn "/").filter (· != "")

def call (method : Method) (p : String) (cookie : Option String := none)
    (fields : List (String × String) := []) : IO Http.Response :=
  send { method, path := path p
         headers := [("Origin", origin), ("Content-Type", "application/x-www-form-urlencoded")]
           ++ (cookie.map fun c => [("Cookie", s!"rookery_session={c}")]).getD []
         body := if method == .get then .empty else (form fields).toUTF8 }

def api (method : Method) (p : String) (token : String) (body : String := "") :
    IO Http.Response :=
  send { method, path := path p
         headers := [("Authorization", s!"Bearer {token}"), ("Content-Type", "application/json")]
         body := body.toUTF8 }

def body (r : Http.Response) : String :=
  (String.fromUTF8? r.body).getD ""

def header? (r : Http.Response) (name : String) : Option String :=
  (r.headers.find? (·.1 == name)).map (·.2)

def contains (s part : String) : Bool :=
  (s.splitOn part).length > 1

def sessionOf (r : Http.Response) : Option String := do
  let set ← header? r "set-cookie"
  let first ← (set.splitOn ";").head?
  match first.splitOn "=" with
  | ["rookery_session", value] => if value.isEmpty then none else some value
  | _ => none

def csrfOf (page : String) : Option String :=
  match page.splitOn "name=\"csrf\" value=\"" with
  | _ :: rest :: _ => (rest.splitOn "\"").head?
  | _ => none

/-- A logged-in browser: its cookie and the form token of its pages. -/
structure Browser where
  cookie : String
  csrf : String

def logIn (name password : String) : IO (Option Browser) := do
  let r ← call .post "/login" (fields := [("name", name), ("password", password)])
  let some cookie := sessionOf r | return none
  let page ← call .get "/" cookie
  return (csrfOf (body page)).map ({ cookie, csrf := · })

def signUp (name password : String) (bot := false) : IO (Option Browser) := do
  let up ← call .post "/signup"
    (fields := [("name", name), ("password", password)] ++ if bot then [("bot", "yes")] else [])
  if !contains (body up) "Signed up" then return none
  logIn name password

def post (b : Browser) (p : String) (fields : List (String × String)) : IO String := do
  return body (← call .post p b.cookie (fields ++ [("csrf", b.csrf)]))

def get (b : Browser) (p : String) : IO String := do
  return body (← call .get p b.cookie)

/-- The token a page shows after `New token`. -/
def tokenOf (fragment : String) : Option String :=
  match fragment.splitOn "Bearer " with
  | [_, rest] => (rest.splitOn "<").head?
  | _ => none

abbrev Process := IO.Process.Child { stdin := .null, stdout := .null, stderr := .inherit }

/-- `rookery` on the database, with a cost of Argon2id in KiB and a lock of `lockout_s`. -/
def start (dir : System.FilePath) (pg : Postgres.Client.Config) (mem_kib : Nat := 1000)
    (lockout_s : Nat := 300) : IO Process := do
  let child : Process ← IO.Process.spawn
    { cmd := ".lake/build/bin/rookery"
      args := #[toString port, (dir / "rookery.secrets").toString, toString mem_kib, "2",
        toString lockout_s]
      env := #[("PGHOST", some pg.host), ("PGPORT", some (toString pg.port)),
        ("PGUSER", some pg.conn.user), ("PGDATABASE", some pg.conn.database),
        ("PGSSLMODE", some "disable"), ("PGPASSWORD", none)]
      stdin := .null, stdout := .null, stderr := .inherit }
  for _ in [0:200] do
    try
      let r ← call .get "/login"
      if r.status == 200 then return child
    catch _ => IO.sleep 25
  child.kill
  throw (IO.userError "live: the server did not start")

def stop (p : Process) : IO Unit := do
  p.kill
  discard p.wait

/-- The post ids in a timeline fragment, in order. -/
def ids (page : String) : List Nat :=
  ((page.splitOn " · #").drop 1).filterMap fun rest => (rest.takeWhile Char.isDigit).toNat?

/-- The hash stored for a name. -/
def storedHash (pg : Postgres.Client.Config) (name : String) : IO (Option String) := do
  let store : Postgres.Typed.Store String (Option String) :=
    { pool := ← Postgres.Pool.new pg, handler := Serve.hashOf }
  match ← (store.call name).block with
  | .committed h => return h
  | _ => return none

def run (dir : System.FilePath) (pg : Postgres.Client.Config) : IO (List (String × Bool)) := do
  let errors ← (Postgres.Typed.reset pg (schema {}) ["0001_rookery.sql"]).block
  unless errors.isEmpty do return [(s!"live: the tables are dropped: {errors}", false)]
  let server ← start dir pg
  let some ann ← signUp "ann" "ann password" | stop server; return [("live: ann signs up", false)]
  let some bob ← signUp "bob" "bob password" (bot := true) | stop server; return [("live: bob signs up", false)]
  let first ← post ann "/post" [("body", "hello, rookery")]
  let second ← post ann "/post" [("body", "a second post <b>escaped</b>")]
  let follows ← post bob "/follow" [("name", "ann")]
  let bobTimeline ← get bob "/timeline"
  let issued ← post bob "/token" []
  let some token := tokenOf issued | stop server; return [("live: bob gets a token", false)]
  let live ← IO.asTask (Http.Client.events port
    { method := .get, path := ["timeline", "events"]
      headers := [("Cookie", s!"rookery_session={bob.cookie}")] } (·.length ≥ 2) 10000)
  IO.sleep 700
  let beep ← api .post "/api/post" token "{\"text\": \"beep\", \"seq\": 1}"
  let retried ← api .post "/api/post" token "{\"text\": \"beep\", \"seq\": 1}"
  let events ← IO.ofExcept live.get
  discard <| post ann "/follow" [("name", "bob")]
  let annTimeline ← get ann "/timeline"
  let deleted ← post ann "/delete" [("id", "0")]
  let bobAfterDelete ← get bob "/timeline"
  let annProfile ← api .get "/api/u/ann" token
  let notHers ← api .post "/api/delete" token "{\"id\": 1, \"seq\": 2}"
  let annStill ← get bob "/timeline"
  let more ← api .post "/api/post" token "{\"text\": \"boop\", \"seq\": 3}"
  let limited ← api .post "/api/post" token "{\"text\": \"one too many\", \"seq\": 4}"
  let reused ← api .post "/api/post" token "{\"text\": \"another\", \"seq\": 4}"
  let stale ← api .post "/api/post" token "{\"text\": \"old\", \"seq\": 2}"
  let forged ← api .get "/api/timeline" (String.ofList (token.toList.set 0
    (if token.front == 'f' then 'e' else 'f')))
  let noToken ← call .post "/post" ann.cookie [("body", "no form token")]
  let beforeKill ← get bob "/timeline"
  let loggedOut ← call .post "/logout" ann.cookie [("csrf", ann.csrf)]
  let afterLogOut ← call .get "/timeline" ann.cookie
  stop server
  -- Killed, and started again at another cost: everything is in the database.
  let firstHash ← storedHash pg "ann"
  let again ← start dir pg (mem_kib := 2000)
  let bobAgain ← get bob "/timeline"
  let annAgain ← logIn "ann" "ann password"
  let secondHash ← storedHash pg "ann"
  let annStillOut ← call .get "/timeline" ann.cookie
  let taken ← call .post "/signup" (fields := [("name", "ann"), ("password", "another one")])
  let retriedAgain ← api .post "/api/post" token "{\"text\": \"beep\", \"seq\": 1}"
  stop again
  -- A lock of two seconds: five wrong passwords close it, the right one is refused, time lifts it.
  let locking ← start dir pg (mem_kib := 2000) (lockout_s := 2)
  for _ in [0:5] do discard <| call .post "/login" (fields := [("name", "ann"), ("password", "wrong guess")])
  let whileLocked ← call .post "/login" (fields := [("name", "ann"), ("password", "ann password")])
  IO.sleep 2100
  let afterLock ← logIn "ann" "ann password"
  stop locking
  return [
    ("live: ann posts twice", contains first "Posted #0" && contains second "Posted #1"),
    ("live: bob follows ann and sees her posts, newest first",
      contains follows "Following" && ids bobTimeline == [1, 0]),
    ("live: a post's text is escaped", contains bobTimeline "&lt;b&gt;escaped&lt;/b&gt;"),
    ("live: bob, a bot, posts through the API with a token", beep.status == 201),
    ("live: bob's timeline as a stream of events shows it, then his post as soon as it is made",
      (events.map fun e => ids e.data) == [[1, 0], [2, 1, 0]]),
    ("live: a post retried with the same seq is posted once, with the same id",
      retried.status == 201 && body retried == body beep && contains (body beep) "\"id\":2"),
    ("live: ann follows bob and sees his post with hers", ids annTimeline == [2, 1, 0]),
    ("live: ann deletes her first post", contains deleted "Deleted"),
    ("live: the deleted post is in no timeline and no read",
      ids bobAfterDelete == [2, 1] && !contains (body annProfile) "\"id\":0"),
    ("live: bob cannot delete ann's post", notHers.status == 404 && ids annStill == [2, 1]),
    ("live: the rate limit holds: two posts a window, the third refused",
      more.status == 201 && limited.status == 429),
    ("live: a seq used for another post is refused", reused.status == 422),
    ("live: an older seq is stale", stale.status == 409),
    ("live: a token that does not verify is refused", forged.status == 401),
    ("live: a form without its token is refused", noToken.status == 403),
    ("live: bob's timeline has the posts left, newest first", ids beforeKill == [3, 2, 1]),
    ("live: after logging out the cookie opens nothing",
      loggedOut.status == 303 && header? afterLogOut "hx-redirect" == some "/login"),
    ("live: after SIGKILL and a restart, the posts, follows and sessions are as they were",
      ids bobAgain == [3, 2, 1] && annAgain.isSome && contains (body taken) "That name is taken"),
    ("live: a session closed before the restart stays closed",
      header? annStillOut "hx-redirect" == some "/login"),
    ("live: a post retried with its seq after the restart is not posted again",
      retriedAgain.status == 409 || body retriedAgain == body beep),
    ("live: the password is checked against its stored hash, and stored again at a new cost",
      firstHash.any (contains · "m=1000,") && secondHash.any (contains · "m=2000,")),
    ("live: five wrong passwords lock the account, the right one is refused while it is locked",
      whileLocked.status == 429),
    ("live: the lock lifts after its time", afterLock.isSome) ]

end Rookery.Live
