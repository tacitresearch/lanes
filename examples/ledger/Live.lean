import Ledger

/-!
The ledger over HTTP, as a browser would use it: `ledger` started as a process on a journal, an
administrator and two users signed up, money issued and moved between them, the balances read,
the process killed with SIGKILL and started again on its journal, and everything read again.
Also what must be refused: a forged cookie, a form without its token, a form from another site,
another user's account, more than an account holds.
-/

open Lanes Lanes.Http Std Std.Async

namespace Ledger.Live

def port : UInt16 := 47311

def origin : String := s!"http://127.0.0.1:{port}"

def form (fields : List (String × String)) : String :=
  "&".intercalate (fields.map fun (k, v) => percentEncode k ++ "=" ++ percentEncode v)

/-- One request on a connection of its own, read with the pure reader of `Lanes.Web.Http.Wire`. -/
def call (method : Method) (path : String) (cookie : Option String := none)
    (fields : List (String × String) := []) (from_ : String := origin) : IO Http.Response := do
  let body := form fields
  let request : Http.Request :=
    { method, path := (path.splitOn "/").filter (· != "")
      headers := [("Origin", from_), ("Content-Type", "application/x-www-form-urlencoded")]
        ++ (cookie.map fun c => [("Cookie", s!"ledger_session={c}")]).getD []
      body := if method == .get then .empty else body.toUTF8 }
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
  | none => throw (IO.userError s!"live: no response to {path}")

def body (r : Http.Response) : String :=
  (String.fromUTF8? r.body).getD ""

def header? (r : Http.Response) (name : String) : Option String :=
  (r.headers.find? (·.1 == name)).map (·.2)

/-- The session token a log-in's `Set-Cookie` carries. -/
def sessionOf (r : Http.Response) : Option String := do
  let set ← header? r "set-cookie"
  let first ← (set.splitOn ";").head?
  match first.splitOn "=" with
  | ["ledger_session", value] => if value.isEmpty then none else some value
  | _ => none

/-- The form token in a page. -/
def csrfOf (page : String) : Option String :=
  match page.splitOn "name=\"csrf\" value=\"" with
  | _ :: rest :: _ => (rest.splitOn "\"").head?
  | _ => none

def contains (s part : String) : Bool :=
  (s.splitOn part).length > 1

/-- A logged-in browser: its cookie and the form token of its pages. -/
structure Browser where
  cookie : String
  csrf : String

def signUpAndLogIn (name password : String) : IO (Option Browser) := do
  let up ← call .post "/signup" (fields := [("name", name), ("password", password)])
  if !contains (body up) "Signed up" then return none
  logIn name password

where
  logIn (name password : String) : IO (Option Browser) := do
    let r ← call .post "/login" (fields := [("name", name), ("password", password)])
    let some cookie := sessionOf r | return none
    let page ← call .get "/" cookie
    return (csrfOf (body page)).map ({ cookie, csrf := · })

def post (b : Browser) (path : String) (fields : List (String × String)) : IO String := do
  return body (← call .post path b.cookie (fields ++ [("csrf", b.csrf)]))

def get (b : Browser) (path : String) : IO String := do
  return body (← call .get path b.cookie)

abbrev Process := IO.Process.Child { stdin := .null, stdout := .null, stderr := .inherit }

def start (dir : System.FilePath) : IO Process := do
  let child : Process ← IO.Process.spawn
    { cmd := ".lake/build/bin/ledger"
      args := #[toString port, (dir / "ledger.journal").toString, (dir / "ledger.secrets").toString,
        "admin", "1000"]
      stdin := .null, stdout := .null, stderr := .inherit }
  for _ in [0:200] do
    try
      let r ← call .get "/login"
      if r.status == 200 then return child
    catch _ => IO.sleep 25
  child.kill
  throw (IO.userError "live: the server did not start")

def balances (b : Browser) : IO String := get b "/accounts"

def check (name : String) (ok : Bool) : IO Bool := do
  IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
  (← IO.getStdout).flush
  return ok

def run (dir : System.FilePath) : IO (List Bool) := do
  let server ← start dir
  let some admin ← signUpAndLogIn "admin" "issuer password" | server.kill; return [false]
  let some alice ← signUpAndLogIn "alice" "alice password" | server.kill; return [false]
  let some bob ← signUpAndLogIn "bob" "bob password!" | server.kill; return [false]
  let issued ← post admin "/accounts" [("currency", "eur"), ("issuer", "yes")]
  let aliceOpened ← post alice "/accounts" [("currency", "eur")]
  let bobOpened ← post bob "/accounts" [("currency", "eur")]
  let fund ← post admin "/transfer" [("src", "0"), ("dst", "1"), ("amount", "100")]
  let pay ← post alice "/transfer" [("src", "1"), ("dst", "2"), ("amount", "30")]
  let tooMuch ← post alice "/transfer" [("src", "1"), ("dst", "2"), ("amount", "1000")]
  let notHers ← post bob "/transfer" [("src", "1"), ("dst", "2"), ("amount", "5")]
  let noToken ← call .post "/transfer" alice.cookie [("src", "1"), ("dst", "2"), ("amount", "5")]
  let elsewhere ← call .post "/transfer" alice.cookie
    [("src", "1"), ("dst", "2"), ("amount", "5"), ("csrf", alice.csrf)] (from_ := "https://evil.example")
  let forged ← call .get "/accounts" (String.ofList (alice.cookie.toList.set 0 (if alice.cookie.front == 'f' then 'e' else 'f')))
  let wrong ← call .post "/login" (fields := [("name", "alice"), ("password", "not her password")])
  let taken ← call .post "/signup" (fields := [("name", "alice"), ("password", "another one")])
  let aliceBefore ← balances alice
  let bobBefore ← balances bob
  let bobTransfers ← get bob "/transfers/list"
  let audit ← get admin "/audit/list"
  let notAdmin ← get alice "/audit/list"
  let journal := (← IO.FS.readBinFile (dir / "ledger.journal")).data.toList
  server.kill
  discard server.wait
  let again ← start dir
  let aliceAfter ← balances alice
  let bobAfter ← balances bob
  let auditAfter ← get admin "/audit/list"
  let after ← post bob "/transfer" [("src", "2"), ("dst", "1"), ("amount", "10")]
  let aliceLast ← balances alice
  let loggedOut ← call .post "/logout" alice.cookie [("csrf", alice.csrf)]
  let afterLogOut ← call .get "/accounts" alice.cookie
  again.kill
  discard again.wait
  let holds (text : String) := (List.range journal.length).any fun k =>
    text.toUTF8.data.toList.isPrefixOf (journal.drop k)
  [
    check "the journal holds no password and no session cookie"
      (!holds "alice%20password" && !holds "alice password" && !holds alice.cookie
        && !holds bob.cookie && !holds admin.cookie),
    check "the administrator opens an account that may go below zero" (contains issued "#0"),
    check "each user opens an account" (contains aliceOpened "#1" && contains bobOpened "#2"),
    check "money is issued to alice" (contains fund "Done"),
    check "alice pays bob" (contains pay "Done"),
    check "alice cannot pay more than she has" (contains tooMuch "more than the account holds"),
    check "bob cannot pay from alice's account" (contains notHers "You have no account"),
    check "a form without its token is refused" (noToken.status == 403),
    check "a form from another site is refused" (elsewhere.status == 403),
    check "a forged cookie is sent to log in" (header? forged "hx-redirect" == some "/login"),
    check "a wrong password is refused" (wrong.status == 401),
    check "a name is taken once" (taken.status == 409),
    check "alice has 70, bob 30" (contains aliceBefore "<td>70</td>" && contains bobBefore "<td>30</td>"),
    check "bob sees only his own accounts" (!contains bobBefore "#1"),
    check "bob sees the transfer that touched him, and only his leg" (contains bobTransfers "<td>#2</td><td>#1</td><td>30</td>" && !contains bobTransfers "-30"),
    check "the audit lists all four entries" ((auditAfter.splitOn "<tr>").length == 6 && (audit.splitOn "<tr>").length == 6),
    check "only the administrator sees the audit" (contains notAdmin "Only the administrator"),
    check "after SIGKILL and a restart on the journal the balances are the same"
      (aliceAfter == aliceBefore && bobAfter == bobBefore),
    check "sessions survive the restart, and money moves again" (contains after "Done" && contains aliceLast "<td>80</td>"),
    check "after logging out the cookie opens nothing"
      (loggedOut.status == 303 && header? afterLogOut "hx-redirect" == some "/login") ].mapM id

end Ledger.Live

def main : IO UInt32 := do
  let dir : System.FilePath := ".lake/live"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDirAll dir
  let results ← Ledger.Live.run dir
  let failed := results.countP (!·)
  IO.println s!"{results.length - failed} passed, {failed} failed"
  return if failed == 0 then 0 else 1
