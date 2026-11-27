/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Serve
import Lanes.Testing
import GitHub

/-!
# The site over HTTP

The site served as `Main` serves it, on a journal, with two members signing in through the
test kit's identity provider (`Lanes.Testing.OAuth`), in GitHub's shape and read by GitHub's
integration, and a store: the test kit's fake S3 (`Lanes.Testing.S3`), which checks every
signature from the bytes it receives, the presigned links' and the upload forms' policies
included, and enforces a policy's size. A browser is the kit's: it signs in, makes a video,
posts the file with the form the page carries, asks the site to check, watches through the link
the page's `<video>` carries, likes, comments, and deletes. Midway the server is stopped and
started again on its journal, and the flow goes on.

`flow` is also what `videosLive` runs against a real bucket.
-/

namespace Videos.EndToEnd

open Lanes Lanes.Http Lanes.OAuth Lanes.Testing Std Std.Async Videos Videos.Web

def origin : String := "http://videos.test"

def alice : Testing.OAuth.User := { subject := "1", login := "alice", email := some "alice@example.com" }
def bob : Testing.OAuth.User :=
  { subject := "2", login := "bob", name := some "Bob \"<b>\" & co", email := some "bob@example.com" }
def carol : Testing.OAuth.User := { subject := "3", login := "carol", email := some "carol@example.com" }

/-- The form token of the session a browser holds, as a page of the site carries it. -/
def csrf (b : Browser) : Async String := do
  return (field (← b.get ["new"]) "csrf").getD ""

/-- A form posted with the session's token. -/
def post (b : Browser) (path : List String) (form : List (String × String) := []) :
    Async (Option Http.Response) := do
  b.post path (("csrf", ← csrf b) :: form)

/-- Where an upload form posts, and its fields, as a page carries them. -/
structure Upload where
  url : String := ""
  fields : List (String × String) := []

/-- The upload form of a page: its action and its hidden fields, in order. -/
def uploadOf (page : Option Http.Response) : Upload := Id.run do
  let some form := between page "<form id=\"upload\"" "</form>" | return {}
  let url := ((form.splitOn "action=\"")[1]?.bind (·.splitOn "\"" |>.head?)).getD ""
  let fields := (form.splitOn "<input type=\"hidden\" name=\"").drop 1 |>.filterMap fun rest =>
    match rest.splitOn "\" value=\"" with
    | name :: value :: _ => some (name, (value.splitOn "\"").headD "")
    | _ => none
  return { url, fields }

/-- Makes a video and returns the form for its upload. -/
def create (b : Browser) (title : String) (visibility : String) :
    Async (Option Http.Response × Upload) := do
  let page ← post b ["videos"] [("title", title), ("about", s!"About {title}."),
    ("visibility", visibility), ("media", "mp4")]
  return (page, uploadOf page)

def clip : ByteArray := "a few bytes of video".toUTF8

/-- The most the test's deployment takes in one upload. -/
def maxUpload_bytes : Nat := 1024

def upload (form : Upload) (file : ByteArray := clip) : Async (Option Http.Response) :=
  Testing.S3.postForm form.url form.fields file

def fetchVideo (page : Option Http.Response) : Async (Option ByteArray) := do
  let some src := between page "<video controls preload=\"metadata\" src=\"" "\"" | return none
  let got ← Testing.S3.follow src .get
  return got.bind fun r => if r.status == 200 then some r.body else none

/-- The deployment the tests and the live smoke run: ops on, a journal, a store, and the kit's
provider as GitHub. -/
def deployment (bucket : S3.Bucket) (creds : SigV4.Credentials) (provider : Testing.OAuth.Fake)
    (journal : System.FilePath) (keyPrefix : String := "videos/") : Deployment :=
  { config := { pageSize := 1 }
    settings := { key := .of "the key of the test deployment".toUTF8, origin, secure := false
                  bucket, creds, providers := ["hub"], keyPrefix
                  maxUpload_bytes := ⟨maxUpload_bytes, by decide⟩ }
    server := { port := 0, system := "videos 1"
                ops := { readinessPath := some "/readyz", livenessPath := some "/healthz"
                         metricsPath := some "/metrics" } }
    journal := some journal
    signIn := { providers := [(provider.userApi "hub" GitHub.read, provider.client origin "hub")]
                secure := false, http := { timeout_ms := 5000 } } }

/-- Polls `check` for up to two seconds. -/
def eventually (check : Async Bool) : Async Bool := do
  for _ in [0:40] do
    if ← check then return true
    Async.sleep 50
  check

/-- The flow, against the store `d` names; `held` says whether the store holds a key, where the
test can see. -/
def flow (d : Deployment) (provider : Testing.OAuth.Fake) (held : String → Async Bool) :
    Async (List (String × Bool)) := do
  let server ← start d
  let port := server.port.getD 0
  let anon ← Browser.new port origin
  let aliceB ← Browser.new port origin
  let bobB ← Browser.new port origin
  let carolB ← Browser.new port origin
  let _ ← Testing.OAuth.signIn aliceB provider "hub" alice
  let _ ← Testing.OAuth.signIn bobB provider "hub" bob
  let _ ← Testing.OAuth.signIn carolB provider "hub" carol
  let aliceSession ← aliceB.cookie sessionCookie
  let bobSession ← bobB.cookie sessionCookie
  let healthz ← anon.get ["healthz"]
  let readyz ← anon.get ["readyz"]
  let metrics ← anon.get ["metrics"]
  let (made, put) ← create aliceB "Cats" "public"
  let uploaded ← upload put
  let confirmed ← post aliceB ["videos", "0", "uploaded"]
  let watched ← bobB.get ["v", "0"]
  let bytes ← fetchVideo watched
  let liked ← post bobB ["v", "0", "like"]
  let _ ← post bobB ["v", "0", "like"]
  let _ ← post aliceB ["v", "0", "like"]
  let commented ← post bobB ["v", "0", "comment"] [("body", "Nice cats")]
  let _ ← post carolB ["v", "0", "comment"] [("body", "Buy pills")]
  let afterLikes ← anon.get ["v", "0"]
  let forged ← bobB.post ["v", "0", "like"] [("csrf", "forged")]
  let notTheirs ← post bobB ["v", "0", "delete"]
  let (_, secretPut) ← create aliceB "Diary" "private"
  let _ ← upload secretPut
  let _ ← post aliceB ["videos", "1", "uploaded"]
  let secretToBob ← bobB.get ["v", "1"]
  let secretToAnon ← anon.get ["v", "1"]
  let secretToAlice ← aliceB.get ["v", "1"]
  let channelToBob ← bobB.get ["c", "0"]
  let channelToAlice ← aliceB.get ["c", "0"]
  let bobsChannel ← anon.get ["c", "1"]
  let (_, ghostPut) ← create aliceB "Ghost" "public"
  let tooLarge ← upload ghostPut (ByteArray.mk (Array.replicate (maxUpload_bytes + 1) 0))
  let early ← post aliceB ["videos", "2", "uploaded"]
  let ghostEarly ← aliceB.get ["v", "2"]
  let feedEarly ← anon.get []
  let waiting ← aliceB.get ["c", "0"]
  server.stop
  let server ← start d
  let port := server.port.getD 0
  let (anon, aliceB, bobB, carolB) := (anon.at port, aliceB.at port, bobB.at port, carolB.at port)
  let _ ← upload ghostPut
  let late ← post aliceB ["videos", "2", "uploaded"]
  let kept ← anon.get ["v", "0"]
  let feed ← anon.get []
  let older ← anon.get [] [("before", "2")]
  let uncommentedByCarol ← post carolB ["v", "0", "comments", "0", "delete"]
  let uncommented ← post bobB ["v", "0", "comments", "0", "delete"]
  let uncommentedByOwner ← post aliceB ["v", "0", "comments", "1", "delete"]
  let afterUncomment ← anon.get ["v", "0"]
  let deleted ← post aliceB ["v", "0", "delete"]
  let gone ← bobB.get ["v", "0"]
  let feedAfter ← anon.get [] [("before", "2")]
  let objectGone ← eventually do return !(← held (d.settings.objectKey 0))
  let token ← csrf bobB
  let signedOut ← bobB.post ["sign-out"] [("csrf", token)]
  let cleared ← bobB.cookie sessionCookie
  -- The browser forgot the cookie; the old one, sent again, must name no session.
  bobB.keep { name := sessionCookie, value := bobSession.getD "" }
  let stillOut ← bobB.post ["v", "2", "like"] [("csrf", token)]
  server.stop
  return [
    ("videos: ops pages answer", status healthz == 200 && status readyz == 200 && status metrics == 200),
    ("videos: a member signs in through the provider and gets a session",
      aliceSession.isSome && bobSession.isSome && aliceSession != bobSession),
    ("videos: making a video gives a page with a form whose policy is for its object, its type and the size allowed",
      status made == 200 && put.url == d.settings.bucket.url
        && put.fields.lookup "key" == some (d.settings.objectKey 0)
        && (match (put.fields.lookup "policy").bind S3.Post.decode? with
          | some doc => doc.conditions.contains (.length 1 maxUpload_bytes)
              && doc.conditions.contains (.eq "key" (d.settings.objectKey 0))
              && doc.conditions.contains (.eq "Content-Type" "video/mp4")
          | none => false)),
    ("videos: the browser posts the file to the store with the form",
      status uploaded == 204),
    ("videos: a file larger than the site takes is refused by the store",
      status tooLarge == 400 && Testing.S3.code tooLarge == "EntityTooLarge"),
    ("videos: asked to check, the site asks the store and the video is ready",
      status confirmed == 303 && location confirmed == "/v/0"),
    ("videos: the watch page's video is a signed link the store serves",
      status watched == 200 && bytes == some clip),
    ("videos: a like counts each member once",
      status liked == 303 && shows afterLikes "2 likes"),
    ("videos: a comment shows on the page", status commented == 303 && shows afterLikes "Nice cats"),
    ("videos: a form without its token is refused", status forged == 403),
    ("videos: only the owner deletes a video", status notTheirs == 404),
    ("videos: a private video is its owner's alone",
      status secretToBob == 404 && status secretToAnon == 404 && status secretToAlice == 200
        && !shows channelToBob "Diary" && shows channelToAlice "Diary"),
    ("videos: a channel is named by the provider's name or the login, never by the address",
      shows channelToBob "<h1>alice</h1>" && !shows channelToBob "@example.com"
        && !shows bobsChannel "@example.com"),
    ("videos: a name the provider gave is shown as text, escaped",
      shows bobsChannel "<h1>Bob &quot;&lt;b&gt;&quot; &amp; co</h1>" && !shows bobsChannel "<b>"),
    ("videos: a video the store does not hold is not ready, watched or listed",
      status early == 409 && status ghostEarly == 404 && shows feedEarly "Cats"
        && !shows feedEarly "Ghost" && shows waiting "Not confirmed yet"),
    ("videos: after a restart on the journal, sessions, likes and comments are kept",
      shows kept "2 likes" && shows kept "Nice cats"),
    ("videos: after a restart, an upload begun before is checked and listed",
      status late == 303 && shows feed "Ghost" && !shows feed "Diary"),
    ("videos: the feed comes a page at a time, newest first",
      shows feed "?before=2" && !shows feed "Cats" && shows older "Cats"),
    ("videos: only its author, or the video's owner, deletes a comment",
      status uncommentedByCarol == 404 && status uncommented == 303
        && status uncommentedByOwner == 303 && !shows afterUncomment "Nice cats"
        && !shows afterUncomment "Buy pills"),
    ("videos: a deleted video is not served, and its object is deleted in the store",
      status deleted == 303 && status gone == 404 && !shows feedAfter "Cats" && objectGone),
    ("videos: signed out, the cookie is cleared and the session is over",
      status signedOut == 303 && cleared.isNone && status stillOut == 303 && location stillOut == "/") ]

def scratch : IO System.FilePath := do
  return s!"{(← IO.getEnv "TMPDIR").getD "/tmp"}/videos-{← IO.monoNanosNow}.journal"

def remove (path : System.FilePath) : IO Unit := do
  for file in [path, path.addExtension "lock", path.addExtension "snapshot"] do
    if ← file.pathExists then IO.FS.removeFile file

/-! ## The bridge, without a socket -/

def creds : SigV4.Credentials :=
  { accessKeyId := "AKIAIOSFODNN7EXAMPLE", secretAccessKey := ⟨"wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY"⟩ }

def settings : Web.Settings :=
  { key := .of "a key".toUTF8, origin, secure := true
    bucket := { name := "b", region := "us-east-1", endpoint := S3.Endpoint.aws "us-east-1" }
    creds }

def decoded (r : Http.Request) : Option Input :=
  match (bridge settings).decode 0 ((bridge settings).prepare r) with
  | .ok i => some i
  | .error _ => none

def withCookie (value : String) (r : Http.Request) : Http.Request :=
  { r with headers := r.headers ++ [("cookie", s!"{settings.cookieName}={value}")] }

def bridgeTests : List (String × Bool) :=
  let watch : Http.Request := { method := .get, path := ["v", "3"] }
  let token := sessionToken settings 0 7
  let like (csrf : String) (headers : List (String × String) := []) : Http.Request :=
    withCookie token { method := .post, path := ["v", "3", "like"], headers
                       body := s!"csrf={csrf}".toUTF8 }
  let good := Auth.formToken settings.key token
  [ ("bridge: a verified cookie names its member and session, and is dropped",
      decoded (withCookie token watch) == some (.request (.watch 0 (some (0, 7)) 3) 0)
        && ((bridge settings).prepare (withCookie token watch)).headers.all (·.1 != "cookie")),
    ("bridge: a cookie whose payload is changed, and a session header a client sends, name no one",
      decoded (withCookie "0.7" watch) == some (.request (.watch 0 none 3) 0)
        && decoded { watch with headers := [(sessionHeader, "0.7")] } == some (.request (.watch 0 none 3) 0)),
    ("bridge: the time a request arrived is the server's, not the client's",
      decoded (stamp 99 { watch with headers := [(arrivedHeader, "5")] })
        == some (.request (.watch 0 none 3) 99)),
    ("bridge: a change needs the session's form token, from this origin",
      decoded (like good) == some (.request (.like 0 0 7 3 true) 0) && decoded (like "forged") == none
        && decoded (like good [("origin", "https://evil.example")]) == none),
    ("bridge: a title too long, or no format, is refused before the system",
      let make (title media : String) : Http.Request := withCookie token {
        method := .post, path := ["videos"]
        body := (encodeForm [("csrf", good), ("title", title), ("visibility", "public"),
          ("media", media)]).toUTF8 }
      (decoded (make "ok" "mp4")).isSome && decoded (make (String.ofList (List.replicate 101 'x')) "mp4") == none
        && decoded (make "ok" "avi") == none),
    ("bridge: a store call is the head or the delete of the video's key, and only those",
      (storeCall settings ⟨0, 1000, .head 4⟩).any (· matches .head _)
        && (storeCall settings ⟨0, 1000, .delete 4⟩).any (· matches .delete _)
        && storeReply none == .unknown && storeReply (some (.refused 500 "")) == .answer .failed) ]

/-- The flow against the fake S3 and the provider, both run here. -/
def run : IO (List (String × Bool)) := do
  let journal ← scratch
  try
    (do
      let store ← Testing.S3.Fake.start creds "videos"
      let provider ← Testing.OAuth.Fake.start (oidc := false)
      let d := deployment store.bucket creds provider journal
      let results ← flow d provider fun key => store.holds key
      store.stop
      provider.stop
      return results : Async _).block
  finally
    remove journal

end Videos.EndToEnd
