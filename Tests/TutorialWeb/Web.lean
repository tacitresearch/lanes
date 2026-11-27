/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.TutorialWeb.Files

/-!
The edge of the shelf: the sign-in, the session cookie, the pages, the forms for the store and
the server. `arrive` is the only IO: the sign-in, the time, and asking the store for an upload.
-/

namespace Shelf

open Lanes Lanes.Http Std.Async
open scoped Lanes.Html

structure Settings where
  /-- The key session cookies and form tokens are signed with. -/
  key : Hmac.Key
  /-- The site's public origin: cookies are `Secure` when it is `https:`. -/
  origin : String
  bucket : S3.Bucket
  creds : SigV4.Credentials
  /-- The names of the sign-in's providers, for its links. -/
  providers : List String
  /-- The sizes of a file the store takes, in bytes. -/
  length : S3.Post.Length := ⟨1, 10 * 1024 * 1024, by decide, by decide⟩
  /-- How long an upload's form is good for. -/
  upload_s : SigV4.Expiry := ⟨900, by decide⟩
  /-- How long a link to a file is good for. -/
  link_s : SigV4.Expiry := ⟨3600, by decide⟩

def Settings.secure (s : Settings) : Bool := s.origin.startsWith "https:"

def Settings.objectKey (_ : Settings) (file : FileId) : String := s!"files/{file}"

namespace Routes

def home : Route Unit := .get .root
def script : Route Unit := .get (.seg "upload.js")
def begin : Route Unit := .post (.seg "files")
def uploaded : Route (Nat × Unit) := .post ("files" /> .append .nat (.seg "uploaded"))
def delete : Route (Nat × Unit) := .post ("files" /> .append .nat (.seg "delete"))
def callback : Route (Slug × Unit) := .get ("sign-in" /> .append .slug (.seg "callback"))

end Routes

/-! ## Sessions -/

/-- A member is the identity's issuer and subject, which do not change, in characters a cookie
and a header may hold. -/
def memberOf (who : OAuth.Identity) : Member := OAuth.b64 (who.issuer ++ " " ++ who.subject).toUTF8

def Settings.cookieName (s : Settings) : String := hostCookie "shelf-session" s.secure

def cookie (s : Settings) (value : String) : Cookie :=
  { name := s.cookieName, value, secure := s.secure, sameSite := .lax }

/-- The headers the server writes. One a client sends is dropped. -/
def memberHeader : String := "shelf-member"
def arrivedHeader : String := "shelf-arrived"
def storedHeader : String := "shelf-stored"

/-- What the server makes of a request before the system sees it: the member its cookie names,
if the cookie is signed with the key, and no cookie, so none is journalled. -/
def prepare (s : Settings) (r : Http.Request) : Http.Request :=
  let kept := r.headers.filter fun (name, _) => name != "cookie" && name != memberHeader
  let member := (r.cookie? s.cookieName).bind (Auth.verify s.key "session")
  { r with headers := kept ++ (member.map (memberHeader, ·)).toList }

def member? (r : Http.Request) : Option Member := r.header? memberHeader

def arrived (r : Http.Request) : Nat := ((r.header? arrivedHeader).bind String.toNat?).getD 0

def stored? (r : Http.Request) : Option Nat := (r.header? storedHeader).bind String.toNat?

/-! ## The store -/

/-- The form a browser posts the file with: its key exact, its size in `length`, for `upload_s`
from `at_s`. -/
def uploadForm (s : Settings) (file : FileId) (at_s : Nat) : Option S3.Post.Form :=
  (S3.Key.of? (s.objectKey file)).map fun key =>
    S3.Post.form s.bucket s.creds (Civil.DateTime.ofUnix at_s)
      { key := .exact key, length := s.length, expiry := s.upload_s }

def link (s : Settings) (file : FileId) (at_s : Nat) : String :=
  match S3.Key.of? (s.objectKey file) with
  | some key => S3.presign s.bucket s.creds (Civil.DateTime.ofUnix at_s) .get key s.link_s
  | none => Html.blockedUrl

/-- Posts the upload form to the store, then the form that asks the site to list the file. -/
def script : String :=
  "document.addEventListener('DOMContentLoaded',function(){" ++
  "var f=document.getElementById('upload');if(!f)return;" ++
  "f.addEventListener('submit',function(e){e.preventDefault();" ++
  "fetch(f.action,{method:'POST',body:new FormData(f)}).then(function(r){" ++
  "if(!r.ok)throw new Error('the store answered '+r.status);" ++
  "document.getElementById('uploaded').submit();})" ++
  ".catch(function(err){document.getElementById('status').textContent=err.message;});});});"

/-! ## Pages -/

def csrf (s : Settings) (who : Member) : Html :=
  <input type="hidden" name="csrf" value={Auth.formToken s.key who}/>

def Layout (children : List Html) : Html :=
  <html lang="en">
    <head>
      <meta charset="utf-8"/>
      <title>"Shelf"</title>
      <script src={Routes.script.link ()}></script>
    </head>
    <body>
      <h1>"Shelf"</h1>
      {children}
    </body>
  </html>

def SignedOut (s : Settings) : Html :=
  Layout [<p>{s.providers.map fun p => <a href={s!"/sign-in/{p}"}>{s!"Sign in with {p}"}</a>}</p>]

def ShelfPage (s : Settings) (who : Member) (files : List Upload) (at_s : Nat) : Html :=
  Layout [
    <ul>
      {files.map fun u =>
        <li>
          <a href={link s u.id at_s}>{s!"File {u.id}"}</a>
          {s!", {u.size.getD 0} bytes "}
          {if u.owner == who then
            <form method="post" action={Routes.delete.link (u.id, ())}>
              {csrf s who}
              <button type="submit">"Delete"</button>
            </form>
          else Html.empty}
        </li>}
    </ul>,
    <form method="post" action={Routes.begin.link ()}>
      {csrf s who}
      <button type="submit">"Upload a file"</button>
    </form>]

def UploadPage (s : Settings) (who : Member) (file : FileId) (at_s : Nat) : Html :=
  Layout [
    match uploadForm s file at_s with
    | some form =>
      <form id="upload" method="post" action={form.url} enctype="multipart/form-data">
        {form.fields.map fun (name, value) => <input type="hidden" name={name} value={value}/>}
        <input type="file" name="file" required/>
        <button type="submit">"Upload"</button>
        <span id="status" role="status"></span>
      </form>
    | none => <p>"This file cannot be uploaded."</p>,
    <form id="uploaded" method="post" action={Routes.uploaded.link (file, ())}>
      {csrf s who}
    </form>]

def Message (title text : String) : Html := Layout [<h2>{title}</h2>, <p>{text}</p>]

/-! ## The bridge -/

def page (html : Html) (status : Nat := 200) : Http.Response :=
  (Http.Response.html html.document status).noStore.noFraming

def home : Http.Response := .redirect (Routes.home.link ())

def notFound : Http.Response := page (Message "Not found" "There is no such page.") 404

/-- A form that changes something: from a member, with the member's form token, from this
origin. -/
def signed (s : Settings) (r : Http.Request) (f : Member → Request) : Except Http.Response Request :=
  match member? r with
  | none => .error home
  | some who =>
    if r.sameOrigin s.origin && (r.field? "csrf").any (Auth.checkForm s.key who) then .ok (f who)
    else .error (.text "forbidden\n" 403)

def decode (s : Settings) (id : ReqId) (r : Http.Request) : Except Http.Response Request :=
  (dispatch [
    Routes.home.handle fun () r => match member? r with
      | some who => .ok (.list id who (arrived r))
      | none => .error (page (SignedOut s)),
    Routes.script.handle fun () _ => .error (Http.Response.ofText "text/javascript" script),
    Routes.callback.handle fun _ r => match OAuth.identity? r with
      | some who => .error (home.setCookie (cookie s (Auth.sign s.key "session" (memberOf who))))
      | none => .error notFound,
    Routes.begin.handle fun () r => signed s r fun who => .begin id who (arrived r),
    Routes.uploaded.handle fun (file, ()) r => signed s r fun who => .seen id who file (stored? r),
    Routes.delete.handle fun (file, ()) r => signed s r fun who => .delete id who file
  ] r).getD (.error notFound)

def encode (s : Settings) : Answer → Http.Response
  | .shelf who files at_s => page (ShelfPage s who files at_s)
  | .form who file at_s => page (UploadPage s who file at_s)
  | .listed _ | .deleted _ => home
  | .notSeen _ => page (Message "Not uploaded" "The store does not hold this file yet.") 409
  | .refused _ => page (Message "Not yours" "Only its uploader can delete a file.") 403
  | .full => page (Message "Full" "The shelf holds as many files as it may.") 503

def bridge (s : Settings) : Bridge sig where
  decode := decode s
  encode r := some (r.req, encode s r.answer)
  prepare := prepare s

def saving (config : Config) : Http.Saving (system config) where
  actors := { id := Codec.unit, state := fun _ => Codec.of State, msg := fun _ => Request.codec }
  out := Response.codec

/-! ## Where a request arrives -/

/-- The request with the time it arrived, and no header of the server's that a client sent. -/
def stamp (now_s : Nat) (r : Http.Request) : Http.Request :=
  { r with headers := r.headers.filter (fun (n, _) => n != arrivedHeader && n != storedHeader)
      ++ [(arrivedHeader, toString now_s)] }

/-- The request with the size the store gave for its file, if the store has it. -/
def withStored (size : Option Nat) (r : Http.Request) : Http.Request :=
  match size with
  | some n => { r with headers := r.headers ++ [(storedHeader, toString n)] }
  | none => r

/-- What the store says of `file`: its size, or `none` when it has no such object or does not
answer in time. -/
def head (s : Settings) (file : FileId) : IO (Option Nat) := do
  let some key := S3.Key.of? (s.objectKey file) | return none
  let answer ← try (S3.exchange s.bucket s.creds (.head key) { timeout_ms := 5000 }).block
    catch _ => pure none
  match answer with
  | some (.found info) => return some info.size
  | _ => return none

def nowSeconds : IO Nat :=
  return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.toInt.toNat / 1000

def arrive (s : Settings) (signIn : OAuth.SignIn) (r : Http.Request) :
    IO (Except Http.Response Http.Request) := do
  match ← signIn.arrive r with
  | .error answer => return .error answer
  | .ok r =>
    let r := stamp (← nowSeconds) r
    match Routes.uploaded.match? r with
    | some (file, ()) => return .ok (withStored (← head s file) r)
    | none => return .ok r

structure Deployment where
  settings : Settings
  config : Config := {}
  server : Http.ServerConfig
  signIn : OAuth.SignIn.Config

abbrev Site (d : Deployment) := Http.served (system d.config) (bridge d.settings) d.server.gate

def start (d : Deployment) : Async (Http.Server (Site d)) := do
  let signIn ← OAuth.SignIn.start d.signIn
  Http.serve (system d.config) (bridge d.settings) d.server {} (some (saving d.config))
    (arrive := some (arrive d.settings signIn))

end Shelf
