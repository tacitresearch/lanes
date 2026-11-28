import Rookery.App

/-!
# The web front and the API

Server-rendered pages with htmx for people, and JSON for bots. The bridge is where a request
becomes an input. What a request holds that must not enter the system is taken out before it
does, on the request's own task:

- `arrive` (`Web.arrive`, given by the server the time, 16 random bytes and, for a log-in, the
  hash stored for the name) turns a sign-up's password into its hash
  (`Auth.Password.hash`, a PHC string with a random salt) and checks a log-in's against the
  stored hash with `Auth.Password.verify`, which reads the cost and the salt from it; a hash not
  as the deployment makes one now is made again (`Checked.right`). The password is then dropped,
  so no request that enters holds one. Argon2id is slow on purpose, and this work is done on the
  request's own task, never on a worker of the system.
- `prepare` puts in place of a session cookie, a signed token of the session's id and the
  account's name, and of an API token, a signed token of its generation and the account's name
  (`Auth.sign`), what one that verifies carried, so nothing in a request's body names an account.
  A header of the names `arrive` or `prepare` writes that a client sends is dropped.
- A form that changes something carries a token bound to the session (`Auth.formToken`) and
  comes from this origin.

The answer says whether the request came through the API (`Response.json`), so the bridge
answers in JSON or in HTML, and names the account the request was made as (`Response.name`), the
only one a cookie or a token is signed for. Pages that need no records are answered by the
bridge; the records come into them as fragments, through the system.
-/

namespace Rookery.Web

open Lanes Lanes.Http
open scoped Lanes.Html

/-- What the bridge is built with. The key and the pepper are secrets of the deployment. -/
structure Settings where
  keys : Auth.Keys
  /-- How long a session's cookie is good for, in seconds; the system may end it sooner. -/
  session_s : Nat := 30 * 24 * 3600
  /-- How long an API token is good for, in seconds; a newer one ends it sooner. -/
  apiToken_s : Nat := 365 * 24 * 3600
  password : Auth.Password
  /-- The origin pages are served from, which a cross-site form does not have. -/
  origin : String
  /-- Whether the session cookie is sent only over HTTPS: true behind TLS. -/
  secure : Bool
  minPassword : Nat := 8
  maxBody_bytes : Nat := 4096

namespace Routes

def home : Route Unit := .get .root
def style : Route Unit := .get (.seg "style.css")
def login : Route Unit := .get (.seg "login")
def logIn : Route Unit := .post (.seg "login")
def signUp : Route Unit := .post (.seg "signup")
def logOut : Route Unit := .post (.seg "logout")
def token : Route Unit := .post (.seg "token")
def timeline : Route Unit := .get (.seg "timeline")
/-- The timeline as a stream of events: each time it changes, it again. -/
def timelineEvents : Route Unit := .get ("timeline" /> .seg "events")
def post : Route Unit := .post (.seg "post")
def delete : Route Unit := .post (.seg "delete")
def follow : Route Unit := .post (.seg "follow")
def unfollow : Route Unit := .post (.seg "unfollow")
def profile : Route Slug := .get ("u" /> .slug)
def profilePosts : Route (Slug × Unit) := .get ("u" /> .append .slug (.seg "posts"))
def apiTimeline : Route Unit := .get ("api" /> .seg "timeline")
def apiPost : Route Unit := .post ("api" /> .seg "post")
def apiDelete : Route Unit := .post ("api" /> .seg "delete")
def apiFollow : Route Unit := .post ("api" /> .seg "follow")
def apiUnfollow : Route Unit := .post ("api" /> .seg "unfollow")
def apiProfile : Route Slug := .get ("api" /> "u" /> .slug)

end Routes

def sessionCookie : String := "rookery_session"

/-- The event a post answered fires, so that the timeline loads again. -/
def posted : String := "posted"

/-! ## Sessions and tokens -/

/-- A session as its token's payload, and what its form tokens are bound to. -/
def sessionOf (name : Name) (session : Int64) : String := s!"{session.toInt}.{name.val}"

/-- The token of a session's cookie, signed at `at_s`. -/
def sessionToken (s : Settings) (name : Name) (session : Int64) (at_s : Nat) : String :=
  Auth.sign s.keys "session" (at_s + s.session_s) (sessionOf name session)

def apiToken (s : Settings) (name : Name) (generation : Int64) (at_s : Nat) : String :=
  Auth.sign s.keys "api" (at_s + s.apiToken_s) s!"{generation.toInt}.{name.val}"

/-- The headers `arrive` writes: when the request arrived, a sign-up's hash, and what a
log-in's password checked against the stored hash gave. One a client sends is dropped. -/
def arrivedHeader : String := "rookery-arrived"
def passwordHash : String := "rookery-password-hash"
def passwordChecked : String := "rookery-password-checked"

/-- When the request arrived, in seconds. -/
def arrived (r : Http.Request) : Nat := ((r.header? arrivedHeader).bind String.toNat?).getD 0

/-- The request with the time it arrived, and none of the headers `arrive` writes that a client
wrote. -/
def stamp (now_s : Nat) (r : Http.Request) : Http.Request :=
  { r with headers := r.headers.filter (fun (n, _) =>
      n != arrivedHeader && n != passwordHash && n != passwordChecked) ++ [(arrivedHeader, toString now_s)] }

/-- A number and a name, as a session's and a token's payloads hold them. -/
def numbered? (payload : String) : Option (Int64 × Name) :=
  match payload.splitOn "." with
  | [k, name] => do return (Int64.ofInt (← k.toInt?), ← Name.ofString? name)
  | _ => none

/-- The headers `prepare` writes. One a client sends is dropped. -/
def verifiedSession : String := "rookery-verified-session"
def verifiedToken : String := "rookery-verified-token"

def bearer? (r : Http.Request) : Option String := do
  let value ← r.header? "authorization"
  match value.splitOn " " with
  | ["Bearer", token] => some token
  | _ => none

/-- A request with its cookie replaced by the session it verifies, and its token by the account
and generation it verifies. -/
def prepare (s : Settings) (r : Http.Request) : Http.Request :=
  let kept := r.headers.filter fun (name, _) =>
    name != "cookie" && name != "authorization" && name != verifiedSession && name != verifiedToken
  let session := (r.cookie? sessionCookie >>= Auth.verify s.keys "session" (arrived r)).map
    (verifiedSession, ·)
  let token := (bearer? r >>= Auth.verify s.keys "api" (arrived r)).map (verifiedToken, ·)
  { r with headers := kept ++ session.toList ++ token.toList }

/-- The session `prepare` verified, as its form tokens are bound to, its name and its id. -/
def verified? (r : Http.Request) : Option (String × Name × Int64) := do
  let (sid, name) ← numbered? (← r.header? verifiedSession)
  return (sessionOf name sid, name, sid)

def cookie (s : Settings) (value : String) : Cookie :=
  { name := sessionCookie, value, secure := s.secure, sameSite := .lax }

/-! ## Views -/

def style : String :=
  "body{font-family:system-ui,sans-serif;max-width:40rem;margin:2rem auto;padding:0 1rem;" ++
  "line-height:1.4;color:#222}nav{display:flex;gap:1rem;align-items:center;" ++
  "border-bottom:1px solid #ddd;padding-bottom:.5rem}article{border-bottom:1px solid #eee;" ++
  "padding:.5rem 0}.meta{color:#777;font-size:.85rem}.error{color:#b00}" ++
  "textarea{width:100%;box-sizing:border-box}form{margin:.5rem 0}"

def Layout (title : String) (children : List Html) : Html :=
  <html lang="en">
    <head>
      <meta charset="utf-8"/>
      <meta name="viewport" content="width=device-width, initial-scale=1"/>
      <title>{title ++ " · rookery"}</title>
      <link rel="stylesheet" href={Routes.style.link ()}/>
      <script src="https://unpkg.com/htmx.org@2.0.4"></script>
      <script src="https://unpkg.com/htmx-ext-sse@2.2.2/sse.js"></script>
    </head>
    <body>{children}</body>
  </html>

def Error (text : String) : Html :=
  <span class="error">{text}</span>

def LoginPage (notice : Option Html := none) : Html :=
  Layout "Log in" [
    <main>
      <h1>"rookery"</h1>
      <p>"Short posts, by people and their bots."</p>
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
        <label>" a bot " <input type="checkbox" name="bot" value="yes"/></label>
        <button type="submit">"Sign up"</button>
      </form>
    </main>]

def profileLink (n : String) : String :=
  ((Slug.ofString? n).map Routes.profile.link).getD (Routes.home.link ())

def Nav (s : Settings) (session : String) (name : Name) : Html :=
  <nav>
    <a href={Routes.home.link ()}>"rookery"</a>
    <a href={profileLink name.val}>{name.val}</a>
    <form method="post" action={Routes.logOut.link ()}>
      <input type="hidden" name="csrf" value={Auth.formToken s.keys session}/>
      <button type="submit">"Log out"</button>
    </form>
  </nav>

def csrfField (s : Settings) (session : String) : Html :=
  <input type="hidden" name="csrf" value={Auth.formToken s.keys session}/>

def HomePage (s : Settings) (session : String) (name : Name) : Html :=
  Layout "Home" [
    <Nav s={s} session={session} name={name}/>,
    <main>
      <form {Hx.request Routes.post ()} {Hx.target "#posted"}>
        {csrfField s session}
        <textarea name="body" rows="3" maxlength="280" required placeholder="What is happening?"></textarea>
        <button type="submit">"Post"</button>
        <span id="posted" role="status"></span>
      </form>
      <h2>"Timeline"</h2>
      <div {Hx.events Routes.timelineEvents ()}>"…"</div>
      <h2>"Accounts"</h2>
      <form {Hx.request Routes.follow ()} {Hx.target "#followed"}>
        {csrfField s session}
        <input name="name" required placeholder="name"/>
        <button type="submit">"Follow"</button>
        <span id="followed" role="status"></span>
      </form>
      <form {Hx.request Routes.unfollow ()} {Hx.target "#followed"}>
        {csrfField s session}
        <input name="name" required placeholder="name"/>
        <button type="submit">"Unfollow"</button>
      </form>
      <form {Hx.request Routes.delete ()} {Hx.target "#deleted"}>
        {csrfField s session}
        <input name="id" type="number" min="0" required placeholder="post number"/>
        <button type="submit">"Delete my post"</button>
        <span id="deleted" role="status"></span>
      </form>
      <h2>"API token"</h2>
      <p>"A bot posts with a token. A new one ends every earlier one."</p>
      <form {Hx.request Routes.token ()} {Hx.target "#token"}>
        {csrfField s session}
        <button type="submit">"New token"</button>
      </form>
      <pre id="token"></pre>
    </main>]

def ProfilePage (whom : Slug) : Html :=
  Layout whom.text [
    <nav><a href={Routes.home.link ()}>"rookery"</a></nav>,
    <main>
      <h1>{whom.text}</h1>
      <div {Hx.request Routes.profilePosts (whom, ())} {Hx.trigger [.load]}>"…"</div>
    </main>]

def Feed (posts : List Post) : Html :=
  if posts.isEmpty then <p>"No posts yet."</p>
  else
    <div>
      {posts.map fun q =>
        <article>
          <div class="meta"><a href={profileLink q.author}>{q.author}</a>{s!" · #{q.id.toInt}"}</div>
          <p>{q.body}</p>
        </article>}
    </div>

/-! ## The bridge -/

def page (html : Html) (status : Nat := 200) : Http.Response :=
  (Http.Response.html html.document status).noStore.noFraming

def fragment (html : Html) : Http.Response :=
  (Http.Response.html html.render).noStore.noFraming

def notLoggedIn : Http.Response :=
  (Http.Response.redirect (Routes.login.link ())).hxRedirect Routes.login ()

def forbidden : Http.Response :=
  Http.Response.text "forbidden\n" 403

def jsonError (text : String) (status : Nat) : Http.Response :=
  Http.Response.json (Json.mkObj [("error", toJson text)]).compress status

/-! ### Passwords, where the request arrives -/

/-- What a log-in's password checked against the stored hash gives; with a hash not as the
deployment makes one now, its new hash under `salt`. A name nobody has checks no hash, so it is
answered sooner; a sign-up tells as much, as it says when a name is taken. -/
def check (s : Settings) (salt : ByteArray) (h : salt.size = 16) (name password : String)
    (stored : Option String) : Checked :=
  match stored >>= Auth.Stored.read? with
  | none => .wrong
  | some st => match s.password.verify name password st with
    | .wrong => .wrong
    | .ok => .right none
    | .rehash => .right (some (s.password.hash salt h password).encode)

def _root_.Rookery.Checked.header : Checked → String
  | .wrong => "wrong"
  | .right none => "right"
  | .right (some hash) => "rehash " ++ hash

def _root_.Rookery.Checked.ofHeader? (v : String) : Option Checked :=
  if v == "wrong" then some .wrong
  else if v == "right" then some (.right none)
  else if v.startsWith "rehash " then some (.right (some (v.drop 7).toString))
  else none

/-- What `arrive` does with a request, given the time, 16 random bytes and, for a log-in, the
hash stored for its name: a sign-up's password becomes its hash, a log-in's what checking it
gave, or `short`, and the password is dropped. -/
def arrive (s : Settings) (now_s : Nat) (salt : ByteArray) (stored : Option String)
    (r : Http.Request) : Http.Request :=
  let r := stamp now_s r
  match r.field? "name" >>= Name.ofString?, r.field? "password", decide (salt.size = 16) with
  | some name, some password, true =>
    let header :=
      if password.length < s.minPassword then [(passwordHash, "short")]
      else if (Routes.signUp.match? r).isSome then
        if h : salt.size = 16 then [(passwordHash, (s.password.hash salt h password).encode)] else []
      else if (Routes.logIn.match? r).isSome then
        if h : salt.size = 16 then [(passwordChecked, (check s salt h name.val password stored).header)]
        else []
      else []
    { r with
      headers := r.headers ++ header
      body := (encodeForm (r.form.filter (·.1 != "password"))).toUTF8 }
  | _, _, _ => r

/-- The name of a log-in or sign-up form, and what `arrive` wrote of its password. -/
def credentials (s : Settings) (header : String) (r : Http.Request) :
    Except Http.Response (Name × String) :=
  let badName := page (LoginPage (some (Error
    "A name is one to twenty lowercase letters, digits and underscores."))) 400
  match r.field? "name" >>= Name.ofString?, r.header? passwordHash, r.header? header with
  | some _, some "short", _ =>
    .error (page (LoginPage (some (Error
      s!"A password has at least {s.minPassword} characters."))) 400)
  | some name, _, some value => .ok (name, value)
  | some _, _, none => .error (Http.Response.text "the password was not read\n" 500)
  | _, _, _ => .error badName

/-- A request whose cookie names a session, as an input; or how the bridge answers it. -/
def signedIn (s : Settings) (r : Http.Request) (changes : Bool)
    (input : Name → Int64 → Except Http.Response Request) : Except Http.Response Request :=
  match verified? r with
  | none => .error notLoggedIn
  | some (session, name, sid) =>
    if changes && !(r.sameOrigin s.origin && (r.field? "csrf").any (Auth.checkForm s.keys session))
    then .error forbidden
    else input name sid

def shell (s : Settings) (r : Http.Request) : Except Http.Response Request :=
  match verified? r with
  | some (session, name, _) => .error (page (HomePage s session name))
  | none => .error (page (LoginPage))

def webOp (s : Settings) (r : Http.Request)
    (op : Http.Request → Except Http.Response Action) : Except Http.Response Request :=
  signedIn s r true fun name session => (op r).map (.web name session)

def bodyOp (r : Http.Request) : Except Http.Response Action :=
  match r.field? "body" >>= Body.ofString? with
  | some body => .ok (.post body)
  | none => .error (fragment (Error "A post is one to 280 characters."))

def deleteOp (r : Http.Request) : Except Http.Response Action :=
  match r.field? "id" >>= String.toNat? with
  | some id => .ok (.delete (Int64.ofNat id))
  | none => .error (fragment (Error "A post's number is a whole number."))

def nameOp (make : Name → Action) (r : Http.Request) : Except Http.Response Action :=
  match r.field? "name" >>= Name.ofString? with
  | some whom => .ok (make whom)
  | none => .error (fragment (Error "No such account."))

/-! ### The API -/

/-- What an API change carries: its `seq`, and what the call is about, of which each call reads
what it needs. -/
lanes_data structure Change where
  seq : Nat
  text : Option Body := none
  id : Option Nat := none
  name : Option Name := none
  deriving ToJson, FromJson

def jsonBody? {α : Type} [FromJson α] (r : Http.Request) : Option α := do
  (fromJson? (← (Json.parse (← String.fromUTF8? r.body)).toOption)).toOption

/-- The account and the token's generation of a request carrying a verified token. -/
def apiAccount (r : Http.Request) : Except Http.Response (Int64 × Name) :=
  match r.header? verifiedToken >>= numbered? with
  | some account => .ok account
  | none => .error (jsonError "a token is missing or does not verify" 401)

/-- A read needs no body and no `seq`. -/
def apiRead (r : Http.Request) : Except Http.Response Request := do
  let (generation, name) ← apiAccount r
  return .api name generation 0 .timeline

/-- A `seq` past what 63 bits hold is refused, so that every `seq` taken is one the store keeps. -/
def apiChange (r : Http.Request) (op : Change → Option Action) : Except Http.Response Request := do
  let (generation, name) ← apiAccount r
  match jsonBody? r >>= fun (c : Change) => (op c).map (c.seq, ·) with
  | some (seq, op) =>
    if seq < 2 ^ 63 then .ok (.api name generation (Int64.ofNat seq) op)
    else .error (jsonError "seq is too large" 400)
  | none => .error (jsonError "the body is not what this call takes" 400)

def profileInput (whom : Slug) (json : Bool) : Except Http.Response Request :=
  match Name.ofString? whom.text with
  | some name => .ok (.profile name json)
  | none => .error (if json then jsonError "no such account" 404
      else fragment <p>"No such account."</p>)

def request (s : Settings) (r : Http.Request) : Except Http.Response Request :=
  if !r.bodyWithin s.maxBody_bytes then .error (Http.Response.text "too large\n" 413)
  else
    (dispatch [
      Routes.home.handle fun () r => shell s r,
      Routes.style.handle fun () _ => .error (Http.Response.ofText "text/css" style),
      Routes.login.handle fun () _ => .error (page (LoginPage)),
      Routes.signUp.handle fun () r =>
        if r.sameOrigin s.origin then
          (credentials s passwordHash r).map fun (n, hash) => .signUp n hash (r.field? "bot" == some "yes")
        else .error forbidden,
      Routes.logIn.handle fun () r =>
        if r.sameOrigin s.origin then
          match credentials s passwordChecked r with
          | .ok (n, v) => match Checked.ofHeader? v with
            | some checked => .ok (.logIn n checked)
            | none => .error (Http.Response.text "the password was not read\n" 500)
          | .error e => .error e
        else .error forbidden,
      Routes.logOut.handle fun () r =>
        signedIn s r true fun name session => .ok (.logOut name session),
      Routes.token.handle fun () r =>
        signedIn s r true fun name session => .ok (.newToken name session),
      Routes.timeline.handle fun () r =>
        signedIn s r false fun name session => .ok (.web name session .timeline),
      Routes.timelineEvents.handle fun () r =>
        signedIn s r false fun name session =>
          if (Stream.msg? r).isSome then .ok (.web name session .timeline)
          else .error Http.Response.events,
      Routes.post.handle fun () r => webOp s r bodyOp,
      Routes.delete.handle fun () r => webOp s r deleteOp,
      Routes.follow.handle fun () r => webOp s r (nameOp .follow),
      Routes.unfollow.handle fun () r => webOp s r (nameOp .unfollow),
      Routes.profile.handle fun whom _ => .error (page (ProfilePage whom)),
      Routes.profilePosts.handle fun (whom, ()) _ => profileInput whom false,
      Routes.apiTimeline.handle fun () r => apiRead r,
      Routes.apiPost.handle fun () r => apiChange r fun c => c.text.map .post,
      Routes.apiDelete.handle fun () r => apiChange r fun c => c.id.map (.delete ∘ Int64.ofNat),
      Routes.apiFollow.handle fun () r => apiChange r fun c => c.name.map .follow,
      Routes.apiUnfollow.handle fun () r => apiChange r fun c => c.name.map .unfollow,
      Routes.apiProfile.handle fun whom _ => profileInput whom true
    ] r).getD (.error (Http.Response.text "not found\n" 404))

/-- A request as the system takes it: its id, when it arrived, and what it asks. -/
def decode (s : Settings) (id : ReqId) (r : Http.Request) : Except Http.Response In :=
  (request s r).map fun q => .request id { at_s := Int64.ofNat (arrived r), request := q }

def postJson (q : Post) : Json :=
  Json.mkObj [("id", toJson q.id.toInt), ("author", toJson q.author), ("body", toJson q.body)]

def jsonOk (fields : List (String × Json)) (status : Nat := 200) : Http.Response :=
  Http.Response.json (Json.mkObj fields).compress status

/-- An answer to a bot. -/
def encodeJson : Reply → Http.Response
  | .posted id => jsonOk [("id", toJson id.toInt)] 201
  | .deleted => jsonOk [("deleted", toJson true)]
  | .followed => jsonOk [("following", toJson true)]
  | .unfollowed => jsonOk [("following", toJson false)]
  | .feed posts => jsonOk [("posts", .arr (posts.map postJson).toArray)]
  | .rateLimited => jsonError "too many posts in this window; wait and try again" 429
  | .tooManyPosts => jsonError "the account keeps as many posts as it may; delete one" 409
  | .tooManyFollows => jsonError "the account follows as many as it may" 409
  | .noSuchAccount => jsonError "no such account" 404
  | .notYours => jsonError "the account has no post with that id" 404
  | .badToken => jsonError "a token is missing or does not verify" 401
  | .stale => jsonError "a request with a later seq was already acted on" 409
  | .reused => jsonError "this seq was already used for another request" 422
  | _ => jsonError "not an answer the API gives" 500

/-- What a timeline shows, as the id of the event that shows it: the same posts, the same id. -/
def feedId (posts : List Post) : String :=
  toString (hash (posts.map (·.id)))

/-- An answer to a browser, for the account `name` the request was made as. -/
def encodeHtml (s : Settings) (name : Name) : Reply → Http.Response
  | .signedUp => page (LoginPage (some <span>"Signed up. Log in."</span>))
  | .nameTaken => page (LoginPage (some (Error "That name is taken."))) 409
  | .full => page (LoginPage (some (Error "No more accounts can be made."))) 503
  | .loggedIn session at_s =>
    (Http.Response.redirect (Routes.home.link ())).setCookie
      (cookie s (sessionToken s name session at_s.toInt.toNat))
  | .refused => page (LoginPage (some (Error "Wrong name or password."))) 401
  | .locked => page (LoginPage (some (Error "Too many failed log-ins. Try again later."))) 429
  | .loggedOut =>
    (Http.Response.redirect (Routes.login.link ())).clearCookie (cookie s "")
  | .noSession => notLoggedIn.clearCookie (cookie s "")
  | .token generation at_s =>
    fragment <span>{s!"Authorization: Bearer {apiToken s name generation at_s.toInt.toNat}"}</span>
  | .posted id => (fragment <span>{s!"Posted #{id.toInt}."}</span>).trigger posted
  | .rateLimited => fragment (Error "Too many posts for now. Wait a minute.")
  | .tooManyPosts => fragment (Error "You keep as many posts as you may. Delete one first.")
  | .deleted => (fragment <span>"Deleted."</span>).trigger posted
  | .notYours => fragment (Error "You have no post with that number.")
  | .followed => (fragment <span>"Following."</span>).trigger posted
  | .unfollowed => (fragment <span>"Not following."</span>).trigger posted
  | .noSuchAccount => fragment (Error "No such account.")
  | .tooManyFollows => fragment (Error "You follow as many as you may.")
  | .feed posts => (fragment (Feed posts)).withHeader "event-id" (feedId posts)
  | .badToken | .stale | .reused => forbidden

/-- The requests that stream: the timeline as events. -/
def streams (r : Http.Request) : Bool :=
  (Routes.timelineEvents.match? r).isSome

def bridge (s : Settings) : Bridge sig where
  decode := decode s
  encode
    | .answered id r => some (id, if r.json then encodeJson r.reply else encodeHtml s r.name r.reply)
    | .failed id => some (id, Http.Response.text "rookery is not available; try again.\n" 503)
    | .call _ => none
  prepare := prepare s

end Rookery.Web
