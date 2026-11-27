import Rookery

/-!
rookery over HTTP, as a browser and a bot use it: `rookery` started as a process on a journal,
a person and a bot signed up, posts made, followed and read in timelines, a post deleted, a
bot's post retried, the rate limit reached, the process killed with SIGKILL and started again
on its journal, and everything read again. Also what must be refused: a delete of another
account's post, a token that does not verify, a form without its token.
-/

open Lanes Lanes.Http Std Std.Async

namespace Rookery.Live

def port : UInt16 := 47321

def origin : String := s!"http://127.0.0.1:{port}"

def form (fields : List (String × String)) : String :=
  "&".intercalate (fields.map fun (k, v) => percentEncode k ++ "=" ++ percentEncode v)

/-- One request on a connection of its own, read with the pure reader of `Lanes.Web.Http.Wire`. -/
def send (request : Http.Request) : IO Http.Response := do
  let some bytes := request.wire s!"127.0.0.1:{port}"
    | throw (IO.userError "live: the request cannot be written")
  let received ← (do
    let socket ← TCP.Socket.Client.mk
    socket.connect (.v4 ⟨.ofParts 127 0 0 1, port⟩)
    socket.send bytes
    let mut received := ByteArray.empty
    repeat
      match ← socket.recv? 65536 with
      | some more => received := received ++ more
      | none => break
    socket.close
    return received : Async ByteArray).block
  match Http.Response.parse received with
  | some response => return response
  | none => throw (IO.userError s!"live: no response to {request.path}")

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

def start (dir : System.FilePath) : IO Process := do
  let child : Process ← IO.Process.spawn
    { cmd := ".lake/build/bin/rookery"
      args := #[toString port, (dir / "rookery.journal").toString,
        (dir / "rookery.secrets").toString, "1000", "2"]
      stdin := .null, stdout := .null, stderr := .inherit }
  for _ in [0:200] do
    try
      let r ← call .get "/login"
      if r.status == 200 then return child
    catch _ => IO.sleep 25
  child.kill
  throw (IO.userError "live: the server did not start")

def check (name : String) (ok : Bool) : IO Bool := do
  IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
  (← IO.getStdout).flush
  return ok

/-- The post ids in a timeline fragment, in order. -/
def ids (page : String) : List Nat :=
  ((page.splitOn " · #").drop 1).filterMap fun rest => (rest.takeWhile Char.isDigit).toNat?

def run (dir : System.FilePath) : IO (List Bool) := do
  let server ← start dir
  let some ann ← signUp "ann" "ann password" | server.kill; return [false]
  let some bob ← signUp "bob" "bob password" (bot := true) | server.kill; return [false]
  let first ← post ann "/post" [("body", "hello, rookery")]
  let second ← post ann "/post" [("body", "a second post <b>escaped</b>")]
  let follows ← post bob "/follow" [("name", "ann")]
  let bobTimeline ← get bob "/timeline"
  let issued ← post bob "/token" []
  let some token := tokenOf issued | server.kill; return [false]
  let beep ← api .post "/api/post" token "{\"text\": \"beep\", \"seq\": 1}"
  let retried ← api .post "/api/post" token "{\"text\": \"beep\", \"seq\": 1}"
  discard <| post ann "/follow" [("name", "bob")]
  let annTimeline ← get ann "/timeline"
  let deleted ← post ann "/delete" [("id", "0")]
  let bobAfterDelete ← get bob "/timeline"
  let annProfile ← api .get "/api/u/ann" token
  let notHers ← api .post "/api/delete" token "{\"id\": 1, \"seq\": 2}"
  let annStill ← get bob "/timeline"
  let more ← api .post "/api/post" token "{\"text\": \"boop\", \"seq\": 3}"
  let limited ← api .post "/api/post" token "{\"text\": \"one too many\", \"seq\": 4}"
  let stale ← api .post "/api/post" token "{\"text\": \"old\", \"seq\": 2}"
  let forged ← api .get "/api/timeline" (String.ofList (token.toList.set 0
    (if token.front == 'f' then 'e' else 'f')))
  let noToken ← call .post "/post" ann.cookie [("body", "no form token")]
  let journal := (← IO.FS.readBinFile (dir / "rookery.journal")).data.toList
  let beforeKill ← get bob "/timeline"
  server.kill
  discard server.wait
  let again ← start dir
  let afterKill ← get bob "/timeline"
  let botAfter ← api .get "/api/timeline" token
  let stillLimited ← api .post "/api/post" token "{\"text\": \"after the restart\", \"seq\": 5}"
  let annPosts ← api .get "/api/u/ann" token
  let loggedOut ← call .post "/logout" ann.cookie [("csrf", ann.csrf)]
  let afterLogOut ← call .get "/timeline" ann.cookie
  again.kill
  discard again.wait
  let holds (text : String) := (List.range journal.length).any fun k =>
    text.toUTF8.data.toList.isPrefixOf (journal.drop k)
  [ check "the journal holds no password, no session cookie and no API token"
      (!holds "ann password" && !holds "ann%20password" && !holds ann.cookie
        && !holds bob.cookie && !holds token),
    check "ann posts twice" (contains first "Posted #0" && contains second "Posted #1"),
    check "bob follows ann and sees her posts, newest first"
      (contains follows "Following" && ids bobTimeline == [1, 0]),
    check "a post's text is escaped" (contains bobTimeline "&lt;b&gt;escaped&lt;/b&gt;"),
    check "bob, a bot, posts through the API with a token" (beep.status == 201),
    check "a post retried with the same seq is posted once, with the same id"
      (retried.status == 201 && body retried == body beep && contains (body beep) "\"id\":2"),
    check "ann follows bob and sees his post with hers" (ids annTimeline == [2, 1, 0]),
    check "ann deletes her first post" (contains deleted "Deleted"),
    check "the deleted post is in no timeline and no read"
      (ids bobAfterDelete == [2, 1] && !contains (body annProfile) "\"id\":0"),
    check "bob cannot delete ann's post" (notHers.status == 404 && ids annStill == [2, 1]),
    check "the rate limit holds: two posts a window, the third refused"
      (more.status == 201 && limited.status == 429),
    check "an older seq is stale" (stale.status == 409),
    check "a token that does not verify is refused" (forged.status == 401),
    check "a form without its token is refused" (noToken.status == 403),
    check "after SIGKILL and a restart on the journal the timeline is the same"
      (afterKill == beforeKill && ids afterKill == [3, 2, 1]),
    check "the bot's token and the rate limit survive the restart"
      (botAfter.status == 200 && stillLimited.status == 429),
    check "the deleted post stays deleted" (!contains (body annPosts) "\"id\":0"
      && contains (body annPosts) "\"id\":1"),
    check "after logging out the cookie opens nothing"
      (loggedOut.status == 303 && header? afterLogOut "hx-redirect" == some "/login") ].mapM id

end Rookery.Live

def main : IO UInt32 := do
  let dir : System.FilePath := ".lake/live"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDirAll dir
  let results ← Rookery.Live.run dir
  let failed := results.countP (!·)
  IO.println s!"{results.length - failed} passed, {failed} failed"
  return if failed == 0 then 0 else 1
