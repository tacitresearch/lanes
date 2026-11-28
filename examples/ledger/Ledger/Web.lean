import Ledger.System

/-!
# The web front

Server-rendered pages and htmx. The bridge is where a request becomes an input, and its
`prepare` the only place that sees a password or a cookie. The server runs it on the request's
own task before the request enters the system or its journal (`Http.Bridge.prepare`):

- a password becomes its digest (`Auth.Password.digest`), so the journal holds no password, and
  the slow digest is computed once, off the shard's thread, not again at a replay;
- a session cookie is a signed token of the session's id and the user's name; `prepare` puts the
  name and session of one that verifies in its place, and the request becomes `Request.act` with
  them; nothing in a request body can name a user, and a header of the names `prepare` writes
  that a client sends is dropped;
- a form that changes something carries a token bound to the session (`Auth.formToken`) and
  comes from this origin (`Request.sameOrigin`).

Pages that need no records (the log-in page and the shells of the others) are answered by the
bridge itself; the records come into them as fragments, through the system. The transfers page
asks for its list every few seconds and whenever a transfer of the user's is answered.
-/

namespace Ledger.Web

open Lanes Lanes.Http
open scoped Lanes.Html

/-- A user's name: one to twenty-four lowercase letters and digits, so that it is a path
segment, a cookie payload and text all at once without escaping. -/
def Name.valid (s : String) : Bool :=
  0 < s.length && s.length ≤ 24 && s.toList.all fun c => c.isLower || c.isDigit

structure Name where
  text : String
  wellFormed : Name.valid text = true

namespace Name

def ofString? (s : String) : Option Name :=
  if h : Name.valid s = true then some ⟨s, h⟩ else none

instance : DecidableEq Name := fun a b =>
  if h : a.text = b.text then isTrue (by cases a; cases b; simp_all)
  else isFalse (fun heq => h (heq ▸ rfl))

instance : Hashable Name := ⟨fun n => hash n.text⟩
instance : Repr Name := ⟨fun n _ => repr n.text⟩
instance : ToString Name := ⟨Name.text⟩

def codec : Codec Name :=
  Codec.string.map Name.text ofString? fun n => by simp [ofString?, n.wellFormed]

instance : Codable Name := ⟨codec⟩

end Name

abbrev Digest := Auth.Digest
abbrev Sys (config : Config Name) := system Name Digest config
abbrev In := Request Name Digest
abbrev Out := Response Name

/-- What the bridge is built with. The keys and the pepper are secrets of the deployment. -/
structure Settings where
  keys : Auth.Keys
  /-- How long a session's cookie is good for, in seconds; the system may end the session
  sooner. -/
  session_s : Nat := 30 * 24 * 3600
  password : Auth.Password
  /-- The origin pages are served from, which a cross-site form does not have. -/
  origin : String
  /-- Whether the session cookie is sent only over HTTPS: true behind TLS. -/
  secure : Bool
  admin : Name
  minPassword : Nat := 8
  maxBody_bytes : Nat := 4096
  /-- How often the transfers page asks for its list again. -/
  refresh_s : Nat := 3

namespace Routes

def home : Route Unit := .get .root
def login : Route Unit := .get (.seg "login")
def logIn : Route Unit := .post (.seg "login")
def signUp : Route Unit := .post (.seg "signup")
def logOut : Route Unit := .post (.seg "logout")
def accounts : Route Unit := .get (.seg "accounts")
def openAccount : Route Unit := .post (.seg "accounts")
def transfer : Route Unit := .post (.seg "transfer")
def transfers : Route Unit := .get (.seg "transfers")
def transferList : Route Unit := .get ("transfers" /> .seg "list")
def audit : Route Unit := .get (.seg "audit")
def auditList : Route Unit := .get ("audit" /> .seg "list")

end Routes

def sessionCookie : String := "ledger_session"

/-- Events a response fires so that the lists on the page load again. -/
def transferred : String := "transferred"
def opened : String := "opened"

/-! ## Sessions -/

/-- A session as its token's payload, and what its form tokens are bound to. -/
def sessionOf (name : Name) (session : Sid) : String := s!"{session}.{name}"

/-- The token in a session's cookie, signed at `at_s`. -/
def sessionToken (s : Settings) (name : Name) (session : Sid) (at_s : Nat) : String :=
  Auth.sign s.keys "session" (at_s + s.session_s) (sessionOf name session)

/-- The header `arrive` writes the time a request arrived in, which a client's is dropped. -/
def arrivedHeader : String := "ledger-arrived"

/-- When the request arrived, in seconds. -/
def arrived (r : Http.Request) : Nat := ((r.header? arrivedHeader).bind String.toNat?).getD 0

/-- What `arrive` does: the request with the time it arrived, and none a client wrote. -/
def stamp (now_s : Nat) (r : Http.Request) : Http.Request :=
  { r with headers := r.headers.filter (·.1 != arrivedHeader) ++ [(arrivedHeader, toString now_s)] }

/-- The user and session a request's cookie names, if its token is ours and has not expired. -/
def session? (s : Settings) (r : Http.Request) : Option (Name × Sid) := do
  let token ← r.cookie? sessionCookie
  let payload ← Auth.verify s.keys "session" (arrived r) token
  match payload.splitOn "." with
  | [sid, name] => return (← Name.ofString? name, ← sid.toNat?)
  | _ => none

/-- The headers `prepare` writes. One a client sends is dropped. -/
def verifiedSession : String := "ledger-verified-session"
def passwordDigest : String := "ledger-password-digest"

/-- A request with its cookie replaced by the session it verifies, and its password by its
digest, or by `short` when it is too short to digest. -/
def prepare (s : Settings) (r : Http.Request) : Http.Request :=
  let kept := r.headers.filter fun (name, _) =>
    name != "cookie" && name != verifiedSession && name != passwordDigest
  let session := (session? s r).map fun (name, sid) => (verifiedSession, sessionOf name sid)
  let digest := match r.field? "name" >>= Name.ofString?, r.field? "password" with
    | some name, some password =>
      [(passwordDigest, if password.length < s.minPassword then "short"
        else (s.password.digest name.text password).hex)]
    | _, _ => []
  { r with
    headers := kept ++ session.toList ++ digest
    body := if (r.field? "password").isSome
      then (encodeForm (r.form.filter (·.1 != "password"))).toUTF8 else r.body }

/-- The session `prepare` verified, as its form tokens are bound to, and its user and id. -/
def verified? (r : Http.Request) : Option (String × Name × Sid) := do
  match (← r.header? verifiedSession).splitOn "." with
  | [sid, name] =>
    let name ← Name.ofString? name
    let sid ← sid.toNat?
    return (sessionOf name sid, name, sid)
  | _ => none

def cookie (s : Settings) (value : String) : Cookie :=
  { name := sessionCookie, value, secure := s.secure, sameSite := .lax }

/-! ## Views -/

def Layout (title : String) (children : List Html) : Html :=
  <html lang="en">
    <head>
      <meta charset="utf-8"/>
      <meta name="viewport" content="width=device-width, initial-scale=1"/>
      <title>{title ++ " · Ledger"}</title>
      <script src="https://unpkg.com/htmx.org@2.0.4"></script>
    </head>
    <body>{children}</body>
  </html>

def Nav (s : Settings) (session : String) (name : Name) : Html :=
  <nav>
    <a href={Routes.home.link ()}>"Accounts"</a>" "
    <a href={Routes.transfers.link ()}>"Transfers"</a>" "
    {if name = s.admin then <a href={Routes.audit.link ()}>"Audit"</a> else Html.empty}
    <form method="post" action={Routes.logOut.link ()} style="display:inline">
      <input type="hidden" name="csrf" value={Auth.formToken s.keys session}/>
      <button type="submit">{s!"Log out {name}"}</button>
    </form>
  </nav>

def LoginPage (notice : Option Html := none) : Html :=
  Layout "Log in" [
    <main>
      <h1>"Ledger"</h1>
      <p id="notice">{notice}</p>
      <form method="post" action={Routes.logIn.link ()}>
        <h2>"Log in"</h2>
        <label>"Name " <input name="name" autocomplete="username" required/></label>
        <label>" Password " <input name="password" type="password" autocomplete="current-password" required/></label>
        <button type="submit">"Log in"</button>
      </form>
      <form method="post" action={Routes.signUp.link ()}>
        <h2>"Sign up"</h2>
        <label>"Name " <input name="name" autocomplete="username" required/></label>
        <label>" Password " <input name="password" type="password" autocomplete="new-password" required/></label>
        <button type="submit">"Sign up"</button>
      </form>
    </main>]

def AccountsPage (s : Settings) (session : String) (name : Name) : Html :=
  let csrf := Auth.formToken s.keys session
  Layout "Accounts" [
    <Nav s={s} session={session} name={name}/>,
    <main>
      <h1>"Your accounts"</h1>
      <div {Hx.request Routes.accounts ()}
        {Hx.trigger [.load, .fromBody (.event transferred), .fromBody (.event opened)]}>"…"</div>
      <form {Hx.request Routes.openAccount ()} {Hx.target "#opened"}>
        <input type="hidden" name="csrf" value={csrf}/>
        <select name="currency"><option value="eur">"EUR"</option><option value="usd">"USD"</option></select>
        {if name = s.admin then
          <label>" may go below zero " <input type="checkbox" name="issuer" value="yes"/></label>
          else Html.empty}
        <button type="submit">"Open an account"</button>
        <span id="opened"></span>
      </form>
      <h2>"Transfer"</h2>
      <form {Hx.request Routes.transfer ()} {Hx.target "#transfer-result"}>
        <input type="hidden" name="csrf" value={csrf}/>
        <label>"From account " <input name="src" type="number" min="0" required/></label>
        <label>" to account " <input name="dst" type="number" min="0" required/></label>
        <label>" amount " <input name="amount" type="number" min="1" required/></label>
        <button type="submit">"Transfer"</button>
        <p id="transfer-result" role="status"></p>
      </form>
    </main>]

def ListPage (s : Settings) (session : String) (name : Name) (title : String) (list : Route Unit) :
    Html :=
  Layout title [
    <Nav s={s} session={session} name={name}/>,
    <main>
      <h1>{title}</h1>
      <div {Hx.request list ()}
        {Hx.trigger [.load, .every s.refresh_s, .fromBody (.event transferred)]}>"…"</div>
    </main>]

def Currency.name : Currency → String
  | .eur => "EUR"
  | .usd => "USD"

def AccountTable (list : List (AccountId × Account Name)) : Html :=
  if list.isEmpty then <p>"No accounts yet."</p>
  else
    <table>
      <tr><th>"Account"</th><th>"Currency"</th><th>"Balance"</th></tr>
      {list.map fun (k, a) =>
        <tr>
          <td>{s!"#{k}"}{if a.allowsNegative then " (may go below zero)" else ""}</td>
          <td>{Currency.name a.currency}</td>
          <td>{a.balance}</td>
        </tr>}
    </table>

def EntryTable (entries : List Entry) : Html :=
  if entries.isEmpty then <p>"No transfers yet."</p>
  else
    <table>
      <tr><th>"Transfer"</th><th>"Account"</th><th>"Other account"</th><th>"Amount"</th></tr>
      {entries.map fun e =>
        <tr>
          <td>{e.transfer}</td><td>{s!"#{e.account}"}</td><td>{s!"#{e.counterparty}"}</td>
          <td>{e.amount}</td>
        </tr>}
    </table>

def Problem.explain : Problem → String
  | .notYours => "You have no account with that number."
  | .noSuchAccount => "There is no account with that number to pay into."
  | .sameAccount => "The two accounts are the same."
  | .currencies => "The two accounts are in different currencies."
  | .nothing => "The amount must be more than zero."
  | .insufficient => "That is more than the account holds."

def Error (text : String) : Html :=
  <span class="error">{text}</span>

/-! ## The bridge -/

def page (html : Html) (status : Nat := 200) : Http.Response :=
  (Http.Response.html html.document status).noStore

def fragment (html : Html) : Http.Response :=
  (Http.Response.html html.render).noStore

/-- A form's own problem, found before it reaches the system. htmx swaps only a `2xx` answer,
so a fragment that says what is wrong with a form is a `200`. -/
def invalid (text : String) : Except Http.Response In :=
  .error (fragment (Error text))

/-- The name and the digest `prepare` made of the password. -/
def credentials (s : Settings) (r : Http.Request) : Except Http.Response (Name × Digest) :=
  let badName :=
    page (LoginPage (some (Error "A name is one to twenty-four lowercase letters and digits."))) 400
  match r.field? "name" >>= Name.ofString?, r.header? passwordDigest with
  | some _, some "short" =>
    .error (page (LoginPage (some (Error s!"A password has at least {s.minPassword} characters."))) 400)
  | some name, some digest =>
    match Auth.Digest.ofHex? digest with
    | some digest => .ok (name, digest)
    | none => .error badName
  | _, _ => .error badName

def notLoggedIn : Http.Response :=
  (Http.Response.redirect (Routes.login.link ())).hxRedirect Routes.login ()

def forbidden : Http.Response :=
  Http.Response.text "forbidden\n" 403

/-- A request whose cookie names a session, as an input; or how the bridge answers it. -/
def signedIn (s : Settings) (id : ReqId) (r : Http.Request) (changes : Bool)
    (op : Http.Request → Except Http.Response Op) : Except Http.Response In :=
  match verified? r with
  | none => .error notLoggedIn
  | some (session, name, sid) =>
    if changes && !(r.sameOrigin s.origin && (r.field? "csrf").any (Auth.checkForm s.keys session))
    then .error forbidden
    else (op r).map (.act id name sid)

def shell (r : Http.Request) (view : String → Name → Html) :
    Except Http.Response In :=
  match verified? r with
  | some (session, name, _) => .error (page (view session name))
  | none => .error notLoggedIn

def transferOp (r : Http.Request) : Except Http.Response Op :=
  match r.field? "src" >>= String.toNat?, r.field? "dst" >>= String.toNat?,
    r.field? "amount" >>= String.toNat? with
  | some src, some dst, some amount => .ok (.transfer src dst amount)
  | _, _, _ => .error (fragment (Error "Accounts and amount are whole numbers."))

def openOp (r : Http.Request) : Except Http.Response Op :=
  match r.field? "currency" with
  | some "eur" => .ok (.openAccount .eur (r.field? "issuer" == some "yes"))
  | some "usd" => .ok (.openAccount .usd (r.field? "issuer" == some "yes"))
  | _ => .error (fragment (Error "Choose a currency."))

def decode (s : Settings) (id : ReqId) (r : Http.Request) : Except Http.Response In :=
  if !r.bodyWithin s.maxBody_bytes then .error (Http.Response.text "too large\n" 413)
  else
    (dispatch [
      Routes.home.handle fun () r => shell r (AccountsPage s),
      Routes.login.handle fun () _ => .error (page (LoginPage)),
      Routes.signUp.handle fun () r =>
        if r.sameOrigin s.origin then (credentials s r).map fun (n, d) => .signUp id n d
        else .error forbidden,
      Routes.logIn.handle fun () r =>
        if r.sameOrigin s.origin then (credentials s r).map fun (n, d) => .logIn id n d (arrived r)
        else .error forbidden,
      Routes.logOut.handle fun () r => signedIn s id r true fun _ => .ok .logOut,
      Routes.accounts.handle fun () r => signedIn s id r false fun _ => .ok .accounts,
      Routes.openAccount.handle fun () r => signedIn s id r true openOp,
      Routes.transfer.handle fun () r => signedIn s id r true transferOp,
      Routes.transfers.handle fun () r =>
        shell r fun session name => ListPage s session name "Transfers" Routes.transferList,
      Routes.transferList.handle fun () r => signedIn s id r false fun _ => .ok .entries,
      Routes.audit.handle fun () r =>
        shell r fun session name => ListPage s session name "Audit" Routes.auditList,
      Routes.auditList.handle fun () r => signedIn s id r false fun _ => .ok .audit
    ] r).getD (.error (Http.Response.text "not found\n" 404))

def encode (s : Settings) : Reply Name → Http.Response
  | .signedUp => page (LoginPage (some <span>"Signed up. Log in."</span>))
  | .nameTaken => page (LoginPage (some (Error "That name is taken."))) 409
  | .loggedIn name session at_s =>
    (Http.Response.redirect (Routes.home.link ())).setCookie
      (cookie s (sessionToken s name session at_s))
  | .refused => page (LoginPage (some (Error "Wrong name or password."))) 401
  | .locked => page (LoginPage (some (Error "Too many failed log-ins. Try again later."))) 429
  | .loggedOut =>
    (Http.Response.redirect (Routes.login.link ())).clearCookie (cookie s "")
  | .noSession => notLoggedIn.clearCookie (cookie s "")
  | .opened k => (fragment <span>{s!"Opened account #{k}."}</span>).trigger opened
  | .tooManyAccounts => fragment (Error "You have as many accounts as you may.")
  | .forbidden => fragment (Error "Only the administrator may do that.")
  | .transferred => (fragment <span class="ok">"Done."</span>).trigger transferred
  | .invalid problem => fragment (Error (Problem.explain problem))
  | .accounts list => fragment (AccountTable list)
  | .entries list => fragment (EntryTable list)

def bridge (s : Settings) : Bridge (sig Name Digest) where
  decode := decode s
  encode out := some (out.req, encode s out.reply)
  prepare := prepare s

/-! ## Saving -/

def actors (config : Config Name) : Kernel.Image.Codecs (Sys config) where
  id := Codec.of (Id Name)
  state
    | .user _ => Codec.of (Option (Profile Digest))
    | .ledger => Codec.of (Book Name)
  msg
    | .user _ => Codec.of (UserMsg Digest)
    | .ledger => Codec.of (LedgerMsg Name)

def saving (config : Config Name) : Http.Saving (Sys config) :=
  { actors := actors config, out := Codec.of Out }

end Ledger.Web
