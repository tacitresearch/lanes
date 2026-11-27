import Rookery.System

/-!
# The web front and the API

Server-rendered pages with htmx for people, and JSON for bots. The bridge is where a request
becomes an input, and its `prepare` the only place that sees a password, a cookie or a token.
The server runs it on the request's own task before the request enters the system or its
journal (`Http.Bridge.prepare`, D44):

- a password becomes its digest (`Auth.Password.digest`), so the journal holds no password;
- a session cookie is a signed token of the session's id and the account's name, and an API
  token a signed token of its generation and the account's name (`Auth.sign`); `prepare` puts
  what one that verifies carried in its place, so nothing in a request's body names an account,
  and a header of the names `prepare` writes that a client sends is dropped;
- a form that changes something carries a token bound to the session (`Auth.formToken`) and
  comes from this origin.

The system's answer says whether the request came through the API (`Response.json`), so the
bridge answers in JSON or in HTML. Pages that need no records are answered by the bridge; the
records come into them as fragments, through the system.
-/

namespace Rookery.Web

open Lanes Lanes.Http
open scoped Lanes.Html

/-- An account's name: one to twenty lowercase letters, digits and `_`, so that it is a path
segment, a cookie payload and text all at once without escaping. -/
def Name.valid (s : String) : Bool :=
  0 < s.length && s.length ≤ 20 && s.toList.all fun c => c.isLower || c.isDigit || c == '_'

abbrev Name := {s : String // Name.valid s}

def Name.ofString? (s : String) : Option Name :=
  if h : Name.valid s then some ⟨s, h⟩ else none

def Body.ofString? (s : String) : Option Body :=
  if h : Body.valid s then some ⟨s, h⟩ else none

abbrev Digest := Auth.Digest
abbrev Sys (config : Config) := system Name Digest config
abbrev In := Request Name Digest
abbrev Out := Response Name

/-- What the bridge is built with. The key and the pepper are secrets of the deployment. -/
structure Settings where
  key : Hmac.Key
  password : Auth.Password
  /-- The origin pages are served from, which a cross-site form does not have. -/
  origin : String
  /-- Whether the session cookie is sent only over HTTPS: true behind TLS. -/
  secure : Bool
  minPassword : Nat := 8
  maxBody_bytes : Nat := 4096
  /-- How often a timeline asks for its posts again. -/
  refresh_s : Nat := 5

namespace Routes

def home : Route Unit := .get .root
def style : Route Unit := .get (.seg "style.css")
def login : Route Unit := .get (.seg "login")
def logIn : Route Unit := .post (.seg "login")
def signUp : Route Unit := .post (.seg "signup")
def logOut : Route Unit := .post (.seg "logout")
def token : Route Unit := .post (.seg "token")
def timeline : Route Unit := .get (.seg "timeline")
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

def sessionToken (s : Settings) (name : Name) (session : Sid) : String :=
  Auth.sign s.key "session" s!"{session}.{name.val}"

def apiToken (s : Settings) (name : Name) (generation : Nat) : String :=
  Auth.sign s.key "api" s!"{generation}.{name.val}"

/-- A number and a name, as a session's and a token's payloads hold them. -/
def numbered? (payload : String) : Option (Nat × Name) :=
  match payload.splitOn "." with
  | [k, name] => do return (← k.toNat?, ← Name.ofString? name)
  | _ => none

/-- The headers `prepare` writes. One a client sends is dropped. -/
def verifiedSession : String := "rookery-verified-session"
def verifiedToken : String := "rookery-verified-token"
def passwordDigest : String := "rookery-password-digest"

def bearer? (r : Http.Request) : Option String := do
  let value ← r.header? "authorization"
  match value.splitOn " " with
  | ["Bearer", token] => some token
  | _ => none

/-- A request with its cookie replaced by the session it verifies, its token by the account and
generation it verifies, and its password by its digest, or by `short` when too short. -/
def prepare (s : Settings) (r : Http.Request) : Http.Request :=
  let kept := r.headers.filter fun (name, _) =>
    name != "cookie" && name != "authorization" && name != verifiedSession
      && name != verifiedToken && name != passwordDigest
  let session := (r.cookie? sessionCookie >>= Auth.verify s.key "session").map
    (verifiedSession, ·)
  let token := (bearer? r >>= Auth.verify s.key "api").map (verifiedToken, ·)
  let digest := match r.field? "name" >>= Name.ofString?, r.field? "password" with
    | some name, some password =>
      [(passwordDigest, if password.length < s.minPassword then "short"
        else (s.password.digest name.val password).hex)]
    | _, _ => []
  { r with
    headers := kept ++ session.toList ++ token.toList ++ digest
    body := if (r.field? "password").isSome
      then (encodeForm (r.form.filter (·.1 != "password"))).toUTF8 else r.body }

/-- The session `prepare` verified, its name, and the session's token, signed again. -/
def verified? (s : Settings) (r : Http.Request) : Option (String × Name × Sid) := do
  let (sid, name) ← numbered? (← r.header? verifiedSession)
  return (sessionToken s name sid, name, sid)

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

def profileLink (n : Name) : String :=
  ((Slug.ofString? n.val).map Routes.profile.link).getD (Routes.home.link ())

def Nav (s : Settings) (token : String) (name : Name) : Html :=
  <nav>
    <a href={Routes.home.link ()}>"rookery"</a>
    <a href={profileLink name}>{name.val}</a>
    <form method="post" action={Routes.logOut.link ()}>
      <input type="hidden" name="csrf" value={Auth.formToken s.key token}/>
      <button type="submit">"Log out"</button>
    </form>
  </nav>

def csrfField (s : Settings) (token : String) : Html :=
  <input type="hidden" name="csrf" value={Auth.formToken s.key token}/>

def HomePage (s : Settings) (token : String) (name : Name) : Html :=
  Layout "Home" [
    <Nav s={s} token={token} name={name}/>,
    <main>
      <form {Hx.request Routes.post ()} {Hx.target "#posted"}>
        {csrfField s token}
        <textarea name="body" rows="3" maxlength="280" required placeholder="What is happening?"></textarea>
        <button type="submit">"Post"</button>
        <span id="posted" role="status"></span>
      </form>
      <h2>"Timeline"</h2>
      <div {Hx.request Routes.timeline ()}
        {Hx.trigger [.load, .every s.refresh_s, .fromBody (.event posted)]}>"…"</div>
      <h2>"Accounts"</h2>
      <form {Hx.request Routes.follow ()} {Hx.target "#followed"}>
        {csrfField s token}
        <input name="name" required placeholder="name"/>
        <button type="submit">"Follow"</button>
        <span id="followed" role="status"></span>
      </form>
      <form {Hx.request Routes.unfollow ()} {Hx.target "#followed"}>
        {csrfField s token}
        <input name="name" required placeholder="name"/>
        <button type="submit">"Unfollow"</button>
      </form>
      <form {Hx.request Routes.delete ()} {Hx.target "#deleted"}>
        {csrfField s token}
        <input name="id" type="number" min="0" required placeholder="post number"/>
        <button type="submit">"Delete my post"</button>
        <span id="deleted" role="status"></span>
      </form>
      <h2>"API token"</h2>
      <p>"A bot posts with a token. A new one ends every earlier one."</p>
      <form {Hx.request Routes.token ()} {Hx.target "#token"}>
        {csrfField s token}
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

def Feed (posts : List (Name × Post)) : Html :=
  if posts.isEmpty then <p>"No posts yet."</p>
  else
    <div>
      {posts.map fun (author, q) =>
        <article>
          <div class="meta"><a href={profileLink author}>{author.val}</a>{s!" · #{q.id}"}</div>
          <p>{q.body.val}</p>
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

/-- The name and the digest `prepare` made of the password. -/
def credentials (s : Settings) (r : Http.Request) : Except Http.Response (Name × Digest) :=
  let badName := page (LoginPage (some (Error
    "A name is one to twenty lowercase letters, digits and underscores."))) 400
  match r.field? "name" >>= Name.ofString?, r.header? passwordDigest with
  | some _, some "short" =>
    .error (page (LoginPage (some (Error
      s!"A password has at least {s.minPassword} characters."))) 400)
  | some name, some digest =>
    match Auth.Digest.ofHex? digest with
    | some digest => .ok (name, digest)
    | none => .error badName
  | _, _ => .error badName

/-- A request whose cookie names a session, as an input; or how the bridge answers it. -/
def signedIn (s : Settings) (r : Http.Request) (changes : Bool)
    (input : Name → Sid → Except Http.Response In) : Except Http.Response In :=
  match verified? s r with
  | none => .error notLoggedIn
  | some (token, name, session) =>
    if changes && !(r.sameOrigin s.origin && (r.field? "csrf").any (Auth.checkForm s.key token))
    then .error forbidden
    else input name session

def shell (s : Settings) (r : Http.Request) : Except Http.Response In :=
  match verified? s r with
  | some (token, name, _) => .error (page (HomePage s token name))
  | none => .error (page (LoginPage))

def webOp (s : Settings) (id : ReqId) (r : Http.Request)
    (op : Http.Request → Except Http.Response (Op Name)) : Except Http.Response In :=
  signedIn s r true fun name session => (op r).map (.web id name session)

def bodyOp (r : Http.Request) : Except Http.Response (Op Name) :=
  match r.field? "body" >>= Body.ofString? with
  | some body => .ok (.post body)
  | none => .error (fragment (Error "A post is one to 280 characters."))

def deleteOp (r : Http.Request) : Except Http.Response (Op Name) :=
  match r.field? "id" >>= String.toNat? with
  | some id => .ok (.delete id)
  | none => .error (fragment (Error "A post's number is a whole number."))

def nameOp (make : Name → Op Name) (r : Http.Request) : Except Http.Response (Op Name) :=
  match r.field? "name" >>= Name.ofString? with
  | some whom => .ok (make whom)
  | none => .error (fragment (Error "No such account."))

/-! ### The API -/

def jsonBody? (r : Http.Request) : Option Json :=
  (String.fromUTF8? r.body).bind fun text => (Json.parse text).toOption

def jsonField? (j : Json) (key : String) : Option Json :=
  (j.getObjVal? key).toOption

def jsonNat? (j : Json) (key : String) : Option Nat :=
  jsonField? j key >>= fun v => v.getNat?.toOption

def jsonStr? (j : Json) (key : String) : Option String :=
  jsonField? j key >>= fun v => v.getStr?.toOption

/-- An API request carrying a verified token, as an input. A change carries its `seq`; a read
needs none. -/
def apiInput (id : ReqId) (r : Http.Request) (op : Json → Option (Op Name)) :
    Except Http.Response In :=
  match r.header? verifiedToken >>= numbered? with
  | none => .error (jsonError "a token is missing or does not verify" 401)
  | some (generation, name) =>
    let j := (jsonBody? r).getD .null
    match op j, jsonNat? j "seq" with
    | some .timeline, _ => .ok (.api id name generation 0 .timeline)
    | some op, some seq => .ok (.api id name generation seq op)
    | _, _ => .error (jsonError "the body is not what this call takes" 400)

def apiPostOp (j : Json) : Option (Op Name) := do
  return .post (← jsonStr? j "text" >>= Body.ofString?)

def apiDeleteOp (j : Json) : Option (Op Name) := do
  return .delete (← jsonNat? j "id")

def apiNameOp (make : Name → Op Name) (j : Json) : Option (Op Name) := do
  return make (← jsonStr? j "name" >>= Name.ofString?)

def profileInput (id : ReqId) (whom : Slug) (json : Bool) : Except Http.Response In :=
  match Name.ofString? whom.text with
  | some name => .ok (.profile id name json)
  | none => .error (if json then jsonError "no such account" 404
      else fragment <p>"No such account."</p>)

def decode (s : Settings) (id : ReqId) (r : Http.Request) : Except Http.Response In :=
  if !r.bodyWithin s.maxBody_bytes then .error (Http.Response.text "too large\n" 413)
  else
    (dispatch [
      Routes.home.handle fun () r => shell s r,
      Routes.style.handle fun () _ => .error (Http.Response.ofText "text/css" style),
      Routes.login.handle fun () _ => .error (page (LoginPage)),
      Routes.signUp.handle fun () r =>
        if r.sameOrigin s.origin then
          (credentials s r).map fun (n, d) => .signUp id n d (r.field? "bot" == some "yes")
        else .error forbidden,
      Routes.logIn.handle fun () r =>
        if r.sameOrigin s.origin then (credentials s r).map fun (n, d) => .logIn id n d
        else .error forbidden,
      Routes.logOut.handle fun () r =>
        signedIn s r true fun name session => .ok (.logOut id name session),
      Routes.token.handle fun () r =>
        signedIn s r true fun name session => .ok (.newToken id name session),
      Routes.timeline.handle fun () r =>
        signedIn s r false fun name session => .ok (.web id name session .timeline),
      Routes.post.handle fun () r => webOp s id r bodyOp,
      Routes.delete.handle fun () r => webOp s id r deleteOp,
      Routes.follow.handle fun () r => webOp s id r (nameOp .follow),
      Routes.unfollow.handle fun () r => webOp s id r (nameOp .unfollow),
      Routes.profile.handle fun whom _ => .error (page (ProfilePage whom)),
      Routes.profilePosts.handle fun (whom, ()) _ => profileInput id whom false,
      Routes.apiTimeline.handle fun () r => apiInput id r fun _ => some .timeline,
      Routes.apiPost.handle fun () r => apiInput id r apiPostOp,
      Routes.apiDelete.handle fun () r => apiInput id r apiDeleteOp,
      Routes.apiFollow.handle fun () r => apiInput id r (apiNameOp .follow),
      Routes.apiUnfollow.handle fun () r => apiInput id r (apiNameOp .unfollow),
      Routes.apiProfile.handle fun whom _ => profileInput id whom true
    ] r).getD (.error (Http.Response.text "not found\n" 404))

def postJson (author : Name) (q : Post) : Json :=
  Json.mkObj [("id", toJson q.id), ("author", toJson author.val), ("body", toJson q.body.val)]

def jsonOk (fields : List (String × Json)) (status : Nat := 200) : Http.Response :=
  Http.Response.json (Json.mkObj fields).compress status

/-- An answer to a bot. -/
def encodeJson : Reply Name → Http.Response
  | .posted id => jsonOk [("id", toJson id)] 201
  | .deleted => jsonOk [("deleted", toJson true)]
  | .followed => jsonOk [("following", toJson true)]
  | .unfollowed => jsonOk [("following", toJson false)]
  | .feed posts => jsonOk [("posts", .arr (posts.map fun (a, q) => postJson a q).toArray)]
  | .rateLimited => jsonError "too many posts in this window; wait and try again" 429
  | .tooManyPosts => jsonError "the account keeps as many posts as it may; delete one" 409
  | .tooManyFollows => jsonError "the account follows as many as it may" 409
  | .noSuchAccount => jsonError "no such account" 404
  | .notYours => jsonError "the account has no post with that id" 404
  | .badToken => jsonError "a token is missing or does not verify" 401
  | .stale => jsonError "a request with a later seq was already acted on" 409
  | _ => jsonError "not an answer the API gives" 500

/-- An answer to a browser. -/
def encodeHtml (s : Settings) : Reply Name → Http.Response
  | .signedUp => page (LoginPage (some <span>"Signed up. Log in."</span>))
  | .nameTaken => page (LoginPage (some (Error "That name is taken."))) 409
  | .full => page (LoginPage (some (Error "No more accounts can be made."))) 503
  | .loggedIn name session =>
    (Http.Response.redirect (Routes.home.link ())).setCookie
      (cookie s (sessionToken s name session))
  | .refused => page (LoginPage (some (Error "Wrong name or password."))) 401
  | .locked => page (LoginPage (some (Error "Too many failed log-ins. Try again later."))) 429
  | .loggedOut =>
    (Http.Response.redirect (Routes.login.link ())).clearCookie (cookie s "")
  | .noSession => notLoggedIn.clearCookie (cookie s "")
  | .token name generation =>
    fragment <span>{s!"Authorization: Bearer {apiToken s name generation}"}</span>
  | .posted id => (fragment <span>{s!"Posted #{id}."}</span>).trigger posted
  | .rateLimited => fragment (Error "Too many posts for now. Wait a minute.")
  | .tooManyPosts => fragment (Error "You keep as many posts as you may. Delete one first.")
  | .deleted => (fragment <span>"Deleted."</span>).trigger posted
  | .notYours => fragment (Error "You have no post with that number.")
  | .followed => (fragment <span>"Following."</span>).trigger posted
  | .unfollowed => (fragment <span>"Not following."</span>).trigger posted
  | .noSuchAccount => fragment (Error "No such account.")
  | .tooManyFollows => fragment (Error "You follow as many as you may.")
  | .feed posts => fragment (Feed posts)
  | .badToken | .stale => forbidden

def bridge (s : Settings) : Bridge (sig Name Digest) where
  decode := decode s
  encode out := some (out.req, if out.json then encodeJson out.reply else encodeHtml s out.reply)
  prepare := prepare s

/-! ## Saving -/

def actors (config : Config) : Kernel.Image.Codecs (Sys config) where
  id := Codec.of Unit
  state _ := Codec.of (Board Name Digest)
  msg _ := Codec.of (Msg Name Digest)

def saving (config : Config) : Http.Saving (Sys config) :=
  { actors := actors config, out := Codec.of Out }

end Rookery.Web
