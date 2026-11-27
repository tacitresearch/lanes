/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.System

/-!
# The web front

Server-rendered pages, forms with tokens bound to the session, and a few lines of script for the
upload. The bridge is where a request becomes an input and an output a response:

- the sign-in (`Lanes.OAuth.SignIn`, in `serve`'s `arrive`) lets a callback in with the identity
  it verified, which becomes `Command.signIn`; no code or token reaches the system;
- `arrive` also writes the time the request arrived (`stamp`), which a create and a watch carry
  into the system, so that the bridge can sign the links for them: `encode` sees only the output;
- `prepare` puts the member and session a cookie verifies in its place, so nothing in a body
  names a member, and drops a header of that name a client sends;
- a form that changes something carries a token bound to the session (`Auth.formToken`) and
  comes from this origin;
- the store's links are signed in `encode` with the deployment's credentials: a put for the
  upload, whose content type is signed, and a get for the `<video>`. Video bytes go between the
  browser and the store; the site sees none.
-/

namespace Videos.Web

open Lanes Lanes.Http
open scoped Lanes.Html

structure Settings where
  /-- The key session cookies and form tokens are signed with. -/
  key : Hmac.Key
  /-- The origin pages are served from, which a cross-site form does not have. -/
  origin : String
  /-- Whether cookies go over HTTPS only: true behind TLS. -/
  secure : Bool
  bucket : S3.Bucket
  creds : SigV4.Credentials
  /-- The names of the sign-in's providers, for its links. -/
  providers : List String := []
  /-- How long an upload link lasts. -/
  upload_s : SigV4.Expiry := ⟨900, by decide⟩
  /-- How long a link to watch lasts. -/
  watch_s : SigV4.Expiry := ⟨21600, by decide⟩
  maxBody_bytes : Nat := 16384
  /-- What the keys of the videos' objects start with. -/
  keyPrefix : String := "videos/"

namespace Routes

def home : Route Unit := .get .root
def style : Route Unit := .get (.seg "style.css")
def script : Route Unit := .get (.seg "upload.js")
def new : Route Unit := .get (.seg "new")
def create : Route Unit := .post (.seg "videos")
def uploaded : Route (Nat × Unit) := .post ("videos" /> .append .nat (.seg "uploaded"))
def watch : Route Nat := .get ("v" /> .nat)
def like : Route (Nat × Unit) := .post ("v" /> .append .nat (.seg "like"))
def unlike : Route (Nat × Unit) := .post ("v" /> .append .nat (.seg "unlike"))
def comment : Route (Nat × Unit) := .post ("v" /> .append .nat (.seg "comment"))
def uncomment : Route (Nat × Nat × Unit) :=
  .post ("v" /> .append .nat ("comments" /> .append .nat (.seg "delete")))
def delete : Route (Nat × Unit) := .post ("v" /> .append .nat (.seg "delete"))
def channel : Route Nat := .get ("c" /> .nat)
def signOut : Route Unit := .post (.seg "sign-out")
def callback : Route (Slug × Unit) := .get ("sign-in" /> .append .slug (.seg "callback"))

end Routes

def sessionCookie : String := "videos_session"

/-- The session cookie's name: `__Host-` before it over HTTPS, so no subdomain can set it. -/
def Settings.cookieName (s : Settings) : String := hostCookie sessionCookie s.secure

/-- The headers the server writes. One a client sends is dropped. -/
def sessionHeader : String := "videos-verified-session"
def arrivedHeader : String := "videos-arrived"

/-- The key of a video's object in the bucket. -/
def Settings.objectKey (s : Settings) (v : VideoId) : String := s.keyPrefix ++ toString v

def sessionToken (s : Settings) (m : Member) (session : Sid) : String :=
  Auth.sign s.key "session" s!"{m}.{session}"

def cookie (s : Settings) (value : String) : Cookie :=
  { name := s.cookieName, value, secure := s.secure, sameSite := .lax }

/-- What `arrive` does after the sign-in: the time the request arrived, in seconds. -/
def stamp (now_s : Nat) (r : Http.Request) : Http.Request :=
  { r with headers := r.headers.filter (·.1 != arrivedHeader) ++ [(arrivedHeader, toString now_s)] }

def prepare (s : Settings) (r : Http.Request) : Http.Request :=
  let kept := r.headers.filter fun (name, _) => name != "cookie" && name != sessionHeader
  let session := (r.cookie? s.cookieName >>= Auth.verify s.key "session").map (sessionHeader, ·)
  { r with headers := kept ++ session.toList }

def session? (r : Http.Request) : Option (Member × Sid) := do
  match (← r.header? sessionHeader).splitOn "." with
  | [m, session] => return (← m.toNat?, ← session.toNat?)
  | _ => none

def arrived (r : Http.Request) : Nat := ((r.header? arrivedHeader).bind String.toNat?).getD 0

/-! ## Links to the store -/

def link (s : Settings) (method : Method) (v : VideoId) (at_s : Nat) (expiry : SigV4.Expiry)
    (contentType : Option String := none) : String :=
  match S3.Key.of? (s.objectKey v) with
  | some key => S3.presign s.bucket s.creds (Civil.DateTime.ofUnix at_s) method key expiry contentType
  | none => Html.blockedUrl

/-! ## Views -/

def style : String :=
  "body{font-family:system-ui,sans-serif;max-width:56rem;margin:1.5rem auto;padding:0 1rem;" ++
  "color:#222;line-height:1.45}nav{display:flex;gap:1rem;align-items:center;" ++
  "border-bottom:1px solid #ddd;padding-bottom:.5rem;margin-bottom:1rem}nav form{margin:0}" ++
  ".cards{display:grid;grid-template-columns:repeat(auto-fill,minmax(14rem,1fr));gap:1rem}" ++
  ".card{border:1px solid #e3e3e3;border-radius:.4rem;padding:.6rem}.meta{color:#777;" ++
  "font-size:.85rem}video{width:100%;max-height:70vh;background:#000}.error{color:#b00}" ++
  "label{display:block;margin:.4rem 0}input[type=text],textarea{width:100%;box-sizing:border-box}"

/-- Puts the chosen file to the link the page carries, with the content type the link signs,
then posts the form that asks the site to check. -/
def script : String :=
  "document.addEventListener('DOMContentLoaded',function(){" ++
  "var f=document.getElementById('upload');if(!f)return;" ++
  "f.addEventListener('submit',function(e){e.preventDefault();" ++
  "var file=f.querySelector('input[type=file]').files[0];if(!file)return;" ++
  "var s=document.getElementById('status');s.textContent='Uploading…';" ++
  "fetch(f.dataset.put,{method:'PUT',headers:{'Content-Type':f.dataset.type},body:file})" ++
  ".then(function(r){if(!r.ok)throw new Error('the store answered '+r.status);" ++
  "s.textContent='Checking…';document.getElementById('confirm').submit();})" ++
  ".catch(function(err){s.textContent='The upload failed: '+err.message;});});});"

def csrf (s : Settings) (viewer : Member × Sid) : Html :=
  <input type="hidden" name="csrf" value={Auth.formToken s.key (sessionToken s viewer.1 viewer.2)}/>

def Nav (s : Settings) (viewer : Viewer) : Html :=
  match viewer with
  | some v =>
    <nav>
      <a href={Routes.home.link ()}>"Videos"</a>
      <a href={Routes.new.link ()}>"Upload"</a>
      <a href={Routes.channel.link v.1}>"My channel"</a>
      <form method="post" action={Routes.signOut.link ()}>
        {csrf s v}
        <button type="submit">"Sign out"</button>
      </form>
    </nav>
  | none =>
    <nav>
      <a href={Routes.home.link ()}>"Videos"</a>
      {s.providers.map fun p => <a href={s!"/sign-in/{p}"}>{s!"Sign in with {p}"}</a>}
    </nav>

def Layout (s : Settings) (title : String) (viewer : Viewer) (children : List Html) : Html :=
  <html lang="en">
    <head>
      <meta charset="utf-8"/>
      <meta name="viewport" content="width=device-width, initial-scale=1"/>
      <title>{title ++ " · Videos"}</title>
      <link rel="stylesheet" href={Routes.style.link ()}/>
      <script src={Routes.script.link ()}></script>
    </head>
    <body>
      <Nav s={s} viewer={viewer}/>
      <main>{children}</main>
    </body>
  </html>

def visibilityName : Visibility → String
  | .public => "public"
  | .unlisted => "unlisted"
  | .private => "private"

def Cards (cards : List Card) : Html :=
  if cards.isEmpty then <p>"No videos yet."</p>
  else
    <div class="cards">
      {cards.map fun c =>
        <div class="card">
          <a href={Routes.watch.link c.id}>{c.title}</a>
          <div class="meta">
            <a href={Routes.channel.link c.owner}>{c.ownerName}</a>
            {s!" · {c.likes} likes · {visibilityName c.visibility}"}
          </div>
        </div>}
    </div>

def NewPage (s : Settings) (viewer : Member × Sid) : Html :=
  Layout s "Upload" (some viewer) [
    <h1>"A new video"</h1>,
    <form method="post" action={Routes.create.link ()}>
      {csrf s viewer}
      <label>"Title " <input type="text" name="title" maxlength="100" required/></label>
      <label>"Description " <textarea name="about" rows="4" maxlength="2000"></textarea></label>
      <label>"Who may watch "
        <select name="visibility">
          <option value="public">"Everyone, and it is listed"</option>
          <option value="unlisted">"Whoever has the link"</option>
          <option value="private">"Only me"</option>
        </select>
      </label>
      <label>"Format "
        <select name="media">
          <option value="mp4">"MP4"</option>
          <option value="webm">"WebM"</option>
          <option value="quicktime">"QuickTime"</option>
        </select>
      </label>
      <button type="submit">"Next: choose the file"</button>
    </form>]

def UploadPage (s : Settings) (viewer : Member × Sid) (v : VideoId) (media : Media) (at_s : Nat) :
    Html :=
  Layout s "Upload" (some viewer) [
    <h1>"Choose the file"</h1>,
    <form id="upload" data-put={link s .put v at_s s.upload_s (some media.mime)}
        data-type={media.mime}>
      <input type="file" name="file" accept={media.mime} required/>
      <button type="submit">"Upload"</button>
      <span id="status" role="status"></span>
    </form>,
    <form id="confirm" method="post" action={Routes.uploaded.link (v, ())}>
      {csrf s viewer}
      <p class="meta">"Uploaded already? "<button type="submit">"Check again"</button></p>
    </form>]

def WatchPage (s : Settings) (viewer : Viewer) (view : View) (at_s : Nat) : Html :=
  let c := view.card
  let mine := viewer.map (·.1) == some c.owner
  Layout s c.title viewer [
    <video controls preload="metadata" src={link s .get c.id at_s s.watch_s}></video>,
    <h1>{c.title}</h1>,
    <p class="meta">
      <a href={Routes.channel.link c.owner}>{c.ownerName}</a>
      {s!" · {c.likes} likes · {visibilityName c.visibility}"}
    </p>,
    <p>{view.about}</p>,
    match viewer with
    | some v =>
      <div>
        <form method="post" action={(if view.liked then Routes.unlike else Routes.like).link (c.id, ())}>
          {csrf s v}
          <button type="submit">{if view.liked then "Unlike" else "Like"}</button>
        </form>
        {if mine then
          <form method="post" action={Routes.delete.link (c.id, ())}>
            {csrf s v}
            <button type="submit">"Delete this video"</button>
          </form>
        else Html.empty}
      </div>
    | none => Html.empty,
    <h2>"Comments"</h2>,
    <div>
      {view.comments.map fun r =>
        <div class="card">
          <div class="meta">{r.authorName}</div>
          <p>{r.body}</p>
          {match viewer with
            | some v =>
              if v.1 == r.author || mine then
                <form method="post" action={Routes.uncomment.link (c.id, r.id, ())}>
                  {csrf s v}
                  <button type="submit">"Delete"</button>
                </form>
              else Html.empty
            | none => Html.empty}
        </div>}
    </div>,
    match viewer with
    | some v =>
      <form method="post" action={Routes.comment.link (c.id, ())}>
        {csrf s v}
        <textarea name="body" rows="2" maxlength="500" required></textarea>
        <button type="submit">"Comment"</button>
      </form>
    | none => Html.empty]

def FeedPage (s : Settings) (viewer : Viewer) (cards : List Card) (next : Option VideoId) : Html :=
  Layout s "Latest" viewer [
    <h1>"Latest videos"</h1>,
    Cards cards,
    match next with
    | some id => <p><a href={Routes.home.link () ++ s!"?before={id}"}>"Older"</a></p>
    | none => Html.empty]

def ChannelPage (s : Settings) (viewer : Viewer) (name : String) (cards : List Card)
    (waiting : List (VideoId × String)) : Html :=
  Layout s name viewer [
    <h1>{name}</h1>,
    Cards cards,
    match viewer, waiting with
    | some v, _ :: _ =>
      <div>
        <h2>"Not confirmed yet"</h2>
        {waiting.map fun (id, title) =>
          <form method="post" action={Routes.uploaded.link (id, ())}>
            {csrf s v}
            {title ++ " "}
            <button type="submit">"Check the upload"</button>
          </form>}
      </div>
    | _, _ => Html.empty]

def Message (s : Settings) (viewer : Viewer) (title text : String) : Html :=
  Layout s title viewer [<h1>{title}</h1>, <p>{text}</p>]

/-! ## The bridge -/

def page (html : Html) (status : Nat := 200) : Http.Response :=
  (Http.Response.html html.document status).noStore.noFraming

def forbidden : Http.Response := Http.Response.text "forbidden\n" 403

def home : Http.Response := Http.Response.redirect (Routes.home.link ())

def watchAt (v : VideoId) : Http.Response := Http.Response.redirect (Routes.watch.link v)

/-- A request whose cookie names a session, as an input, or how the bridge answers it. A form
that changes something needs its token, and must come from this origin. -/
def signedIn (s : Settings) (r : Http.Request) (f : Member → Sid → Except Http.Response Input) :
    Except Http.Response Input :=
  match session? r with
  | none => .error home
  | some (m, session) =>
    if r.sameOrigin s.origin
        && (r.field? "csrf").any (Auth.checkForm s.key (sessionToken s m session)) then
      f m session
    else .error forbidden

def bad (text : String) : Except Http.Response Input :=
  .error (Http.Response.text (text ++ "\n") 400)

def visibility? : String → Option Visibility
  | "public" => some .public
  | "unlisted" => some .unlisted
  | "private" => some .private
  | _ => none

def media? : String → Option Media
  | "mp4" => some .mp4
  | "webm" => some .webm
  | "quicktime" => some .quicktime
  | _ => none

def createInput (id : ReqId) (r : Http.Request) (m : Member) (session : Sid) :
    Except Http.Response Input :=
  let text (name : String) := (r.field? name).getD ""
  if h : Title.valid (text "title") then
    if h' : About.valid (text "about") then
      match visibility? (text "visibility"), media? (text "media") with
      | some vis, some media =>
        .ok (.request (.create id m session ⟨_, h⟩ ⟨_, h'⟩ vis media) (arrived r))
      | _, _ => bad "a visibility and a format are needed"
    else bad "a description is at most 2000 characters"
  else bad "a title is 1 to 100 characters"

def commentInput (id : ReqId) (r : Http.Request) (m : Member) (session : Sid) (v : VideoId) :
    Except Http.Response Input :=
  let body := (r.field? "body").getD ""
  if h : Remark.valid body then .ok (.request (.comment id m session v ⟨body, h⟩) (arrived r))
  else bad "a comment is 1 to 500 characters"

/-- The name a channel shows: the provider's name for the member, which anyone may choose and the
pages show as text; without one, what comes before the `@` of the address, since the whole
address would be shown to everyone. -/
def channelName (who : OAuth.Identity) : String :=
  let user := (who.email.getD "").takeWhile (· != '@') |>.toString
  let name := match who.name with
    | some n => n.val
    | none => if user.isEmpty then who.subject else user
  name.take 40 |>.toString

def decode (s : Settings) (id : ReqId) (r : Http.Request) : Except Http.Response Input :=
  let ask (c : Command) : Except Http.Response Input := .ok (.request c (arrived r))
  if !r.bodyWithin s.maxBody_bytes then .error (Http.Response.text "too large\n" 413)
  else
    (dispatch [
      Routes.home.handle fun () r => ask (.feed id (session? r) ((r.param? "before").bind String.toNat?)),
      Routes.style.handle fun () _ => .error (Http.Response.ofText "text/css" style),
      Routes.script.handle fun () _ => .error (Http.Response.ofText "text/javascript" script),
      Routes.new.handle fun () r => match session? r with
        | some v => .error (page (NewPage s v))
        | none => .error home,
      Routes.create.handle fun () r => signedIn s r (createInput id r),
      Routes.uploaded.handle fun (v, ()) r => signedIn s r fun m session =>
        ask (.uploaded id m session v),
      Routes.watch.handle fun v r => ask (.watch id (session? r) v),
      Routes.like.handle fun (v, ()) r => signedIn s r fun m session => ask (.like id m session v true),
      Routes.unlike.handle fun (v, ()) r => signedIn s r fun m session =>
        ask (.like id m session v false),
      Routes.comment.handle fun (v, ()) r => signedIn s r fun m session => commentInput id r m session v,
      Routes.uncomment.handle fun (v, c, ()) r => signedIn s r fun m session =>
        ask (.uncomment id m session v c),
      Routes.delete.handle fun (v, ()) r => signedIn s r fun m session => ask (.delete id m session v),
      Routes.channel.handle fun whom r => ask (.channel id (session? r) whom),
      Routes.signOut.handle fun () r => signedIn s r fun m session => ask (.signOut id m session),
      Routes.callback.handle fun _ r => match OAuth.identity? r with
        | some who => ask (.signIn id who.issuer who.subject (channelName who))
        | none => .error (Http.Response.text "not found\n" 404)
    ] r).getD (.error (page (Message s none "Not found" "There is no such page.") 404))

def encodeReply (s : Settings) (viewer : Viewer) : Reply → Http.Response
  | .signedIn m session => home.setCookie (cookie s (sessionToken s m session))
  | .full => page (Message s none "Full" "No more members can join.") 503
  | .signedOut | .noSession => home.clearCookie (cookie s "")
  | .created v media at_s => match viewer with
    | some who => page (UploadPage s who v media at_s)
    | none => home
  | .tooMany => page (Message s viewer "Too many"
      "There are as many videos as there may be, or you have too many waiting to be uploaded.") 429
  | .confirmed v => watchAt v
  | .notUploaded _ => page (Message s viewer "Not uploaded"
      "The store has nothing for this video yet. Upload it, then check again from your channel.") 409
  | .unconfirmed _ => page (Message s viewer "Not confirmed"
      "The store did not answer in time. Check again from your channel.") 503
  | .watch view at_s => page (WatchPage s viewer view at_s)
  | .notFound => page (Message s viewer "Not found" "There is no such video.") 404
  | .liked v _ _ | .commented v | .uncommented v => watchAt v
  | .tooManyComments _ => page (Message s viewer "Too many comments"
      "This video has as many comments as it may.") 409
  | .deleted _ => match viewer with
    | some who => Http.Response.redirect (Routes.channel.link who.1)
    | none => home
  | .feed cards next => page (FeedPage s viewer cards next)
  | .channel _ name cards waiting => page (ChannelPage s viewer name cards waiting)

def bridge (s : Settings) : Bridge sig where
  decode := decode s
  encode
    | .reply req viewer r => some (req, encodeReply s viewer r)
    | _ => none
  prepare := prepare s

/-! ## Saving -/

def actors (config : Config) : Kernel.Image.Codecs (system config) where
  id := Codec.of Unit
  state _ := Codec.of Site
  msg _ := Codec.of Input

end Videos.Web
