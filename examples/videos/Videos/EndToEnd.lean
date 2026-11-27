/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Serve
import Tests.S3
import Tests.OAuth

/-!
# The site over HTTP

The site served as `Main` serves it, on a journal, with two members signing in through a
provider run in the test (a token endpoint and a user API, as GitHub's), and a store run in the
test: Lanes' fake S3 (`Tests/S3.lean`), which checks every signature from the bytes it receives,
the presigned links' included. A browser is played with the HTTP client: it signs in, makes a
video, puts the file to the link the page carries, asks the site to check, watches through the
link the page's `<video>` carries, likes, comments, and deletes. Midway the server is stopped and
started again on its journal, and the flow goes on.

`flow` is also what `videosLive` runs against a real bucket.
-/

namespace Videos.EndToEnd

open Lanes Lanes.Http Lanes.OAuth Std Std.Async Videos Videos.Web

def json (body : String) : Http.Response := Http.Response.ofText "application/json" body

/-- A provider of OAuth 2.0 without ID tokens: any code is good, and names its user. -/
def provider (r : Http.Request) : IO Http.Response := do
  let code := match (r.header? "authorization").map (·.splitOn "Bearer at-") with
    | some [_, code] => code
    | _ => ""
  match r.method, r.path with
  | .post, ["token"] =>
    let given := ((parseForm ((String.fromUTF8? r.body).getD "")).lookup "code").getD ""
    return json s!"\{\"access_token\":\"at-{given}\",\"token_type\":\"bearer\"}"
  | .get, ["user"] => return json s!"\{\"id\":{code.length},\"login\":\"{code}\"}"
  | .get, ["emails"] =>
    return json s!"[\{\"email\":\"{code}@example.com\",\"primary\":true,\"verified\":true}]"
  | _, _ => return Http.Response.text "not found" 404

def origin : String := "http://videos.test"

def has (r : Option Http.Response) (text : String) : Bool :=
  ((r.bind fun r => String.fromUTF8? r.body).getD "" |>.splitOn text).length > 1

def status (r : Option Http.Response) : Nat := (r.map (·.status)).getD 0

def location (r : Option Http.Response) : String :=
  ((r.bind (·.headers.lookup "location")).getD "")

def unescape (s : String) : String :=
  ((s.replace "&quot;" "\"").replace "&#39;" "'").replace "&amp;" "&"

/-- The text after the first `start` in the body, up to `stop`. -/
def between (r : Option Http.Response) (start stop : String) : Option String := do
  let body ← String.fromUTF8? (← r).body
  let rest ← (body.splitOn start)[1]?
  return unescape ((rest.splitOn stop).headD "")

/-- The value a `set-cookie` of the response gives `name`. -/
def cookieOf (r : Option Http.Response) (name : String) : Option String := do
  let header ← ((← r).headers.filter (·.1 == "set-cookie")).find? (·.2.startsWith (name ++ "="))
  return ((header.2.drop (name.length + 1)).takeWhile (· != ';')).toString

structure Browser where
  port : UInt16
  session : Option String := none

def Browser.call (b : Browser) (method : Method) (path : List String)
    (form : List (String × String) := []) (query : List (String × String) := [])
    (headers : List (String × String) := []) : Async (Option Http.Response) := do
  let headers := headers ++ (b.session.map fun c => ("cookie", s!"{sessionCookie}={c}")).toList
    ++ (if method == .post then
      [("content-type", "application/x-www-form-urlencoded"), ("origin", origin)] else [])
  try
    Client.exchange { host := "127.0.0.1", port := b.port, request := {
      method, path, query, headers, body := (encodeForm form).toUTF8 } } { timeout_ms := 15000 }
  catch _ => return none

/-- Signs in through the provider as the user `code` names, as a browser: begins, comes back to
the callback with the state and the cookie of the beginning, and keeps the session cookie. -/
def Browser.signIn (b : Browser) (code : String) : Async Browser := do
  let begun ← b.call .get ["sign-in", "hub"]
  let binding := cookieOf begun "lanes-sign-in"
  let state := Tests.OAuth.get (Tests.OAuth.queryOf (location begun)) "state"
  let answer ← b.call .get ["sign-in", "hub", "callback"] (query := [("code", code),
    ("state", state.getD "")]) (headers := [("cookie", s!"lanes-sign-in={binding.getD ""}")])
  return { b with session := cookieOf answer sessionCookie }

/-- The form token a page of the browser's carries. -/
def Browser.csrf (b : Browser) : Async String := do
  return ((between (← b.call .get ["new"]) "name=\"csrf\" value=\"" "\"").getD "")

def Browser.post (b : Browser) (path : List String) (form : List (String × String) := []) :
    Async (Option Http.Response) := do
  b.call .post path (("csrf", ← b.csrf) :: form)

/-- Makes a video and returns the link for its upload. -/
def Browser.create (b : Browser) (title : String) (visibility : String) :
    Async (Option Http.Response × String) := do
  let page ← b.post ["videos"] [("title", title), ("about", s!"About {title}."),
    ("visibility", visibility), ("media", "mp4")]
  return (page, (between page "data-put=\"" "\"").getD "")

def clip : ByteArray := "a few bytes of video".toUTF8

def upload (url : String) : Async (Option Http.Response) := do
  try Tests.S3.follow url .put clip [("content-type", "video/mp4")] catch _ => return none

def fetchVideo (page : Option Http.Response) : Async (Option ByteArray) := do
  let some src := between page "<video controls preload=\"metadata\" src=\"" "\"" | return none
  let got ← try Tests.S3.follow src .get catch _ => pure none
  return got.bind fun r => if r.status == 200 then some r.body else none

def hub (at_ : String → String) : Provider :=
  { name := "hub", authorize := "https://hub.example/authorize", token := at_ "token"
    scopes := ["read:user"], source := .userApi [at_ "user", at_ "emails"] Tests.OAuth.readHub }

def client : Client :=
  { id := "app", secret := ⟨"s3cret"⟩, redirect := s!"{origin}/sign-in/hub/callback" }

/-- The deployment the tests and the live smoke run: ops on, a journal, a store. -/
def deployment (bucket : S3.Bucket) (creds : SigV4.Credentials) (providerPort : UInt16)
    (journal : System.FilePath) (keyPrefix : String := "videos/") : Deployment :=
  let at_ (path : String) := s!"http://127.0.0.1:{providerPort}/{path}"
  { config := { pageSize := 1 }
    settings := { key := .of "the key of the test deployment".toUTF8, origin, secure := false
                  bucket, creds, providers := ["hub"], keyPrefix }
    server := { port := 0, system := "videos 1"
                ops := { readinessPath := some "/readyz", livenessPath := some "/healthz"
                         metricsPath := some "/metrics" } }
    journal := some journal
    signIn := { providers := [(hub at_, client)], secure := false, http := { timeout_ms := 5000 } } }

/-- Polls `check` for up to two seconds. -/
def eventually (check : Async Bool) : Async Bool := do
  for _ in [0:40] do
    if ← check then return true
    Async.sleep 50
  check

/-- The flow, against the store `d` names; `held` says whether the store holds a key, where the
test can see. -/
def flow (d : Deployment) (held : String → Async Bool) : Async (List (String × Bool)) := do
  let server ← start d
  let port := server.port.getD 0
  let anon : Browser := { port }
  let alice ← anon.signIn "alice"
  let bob ← anon.signIn "bob"
  let healthz ← anon.call .get ["healthz"]
  let readyz ← anon.call .get ["readyz"]
  let metrics ← anon.call .get ["metrics"]
  let (made, put) ← alice.create "Cats" "public"
  let uploaded ← upload put
  let confirmed ← alice.post ["videos", "0", "uploaded"]
  let watched ← bob.call .get ["v", "0"]
  let bytes ← fetchVideo watched
  let liked ← bob.post ["v", "0", "like"]
  let _ ← bob.post ["v", "0", "like"]
  let _ ← alice.post ["v", "0", "like"]
  let commented ← bob.post ["v", "0", "comment"] [("body", "Nice cats")]
  let afterLikes ← anon.call .get ["v", "0"]
  let forged ← bob.call .post ["v", "0", "like"] [("csrf", "forged")]
  let notTheirs ← bob.post ["v", "0", "delete"]
  let (_, secretPut) ← alice.create "Diary" "private"
  let _ ← upload secretPut
  let _ ← alice.post ["videos", "1", "uploaded"]
  let secretToBob ← bob.call .get ["v", "1"]
  let secretToAnon ← anon.call .get ["v", "1"]
  let secretToAlice ← alice.call .get ["v", "1"]
  let channelToBob ← bob.call .get ["c", "0"]
  let channelToAlice ← alice.call .get ["c", "0"]
  let (_, ghostPut) ← alice.create "Ghost" "public"
  let early ← alice.post ["videos", "2", "uploaded"]
  let ghostEarly ← alice.call .get ["v", "2"]
  let feedEarly ← anon.call .get []
  let waiting ← alice.call .get ["c", "0"]
  server.stop
  let server ← start d
  let port := server.port.getD 0
  let (anon, alice, bob) := ({ anon with port }, { alice with port }, { bob with port })
  let _ ← upload ghostPut
  let late ← alice.post ["videos", "2", "uploaded"]
  let kept ← anon.call .get ["v", "0"]
  let feed ← anon.call .get []
  let older ← anon.call .get [] (query := [("before", "2")])
  let uncommentedByAlice ← alice.post ["v", "0", "comments", "0", "delete"]
  let uncommented ← bob.post ["v", "0", "comments", "0", "delete"]
  let afterUncomment ← anon.call .get ["v", "0"]
  let deleted ← alice.post ["v", "0", "delete"]
  let gone ← bob.call .get ["v", "0"]
  let feedAfter ← anon.call .get [] (query := [("before", "2")])
  let objectGone ← eventually do return !(← held (d.settings.objectKey 0))
  let signedOut ← bob.post ["sign-out"]
  let stillOut ← bob.post ["v", "2", "like"]
  server.stop
  return [
    ("videos: ops pages answer", status healthz == 200 && status readyz == 200 && status metrics == 200),
    ("videos: a member signs in through the provider and gets a session",
      alice.session.isSome && bob.session.isSome && alice.session != bob.session),
    ("videos: making a video gives a page with a signed upload link for its object",
      status made == 200 && (put.splitOn (d.settings.objectKey 0 ++ "?")).length == 2
        && (put.splitOn "X-Amz-SignedHeaders=content-type%3Bhost").length == 2),
    ("videos: the browser puts the file to the store with the link",
      status uploaded == 200),
    ("videos: asked to check, the site asks the store and the video is ready",
      status confirmed == 303 && location confirmed == "/v/0"),
    ("videos: the watch page's video is a signed link the store serves",
      status watched == 200 && bytes == some clip),
    ("videos: a like counts each member once",
      status liked == 303 && has afterLikes "2 likes"),
    ("videos: a comment shows on the page", status commented == 303 && has afterLikes "Nice cats"),
    ("videos: a form without its token is refused", status forged == 403),
    ("videos: only the owner deletes a video", status notTheirs == 404),
    ("videos: a private video is its owner's alone",
      status secretToBob == 404 && status secretToAnon == 404 && status secretToAlice == 200
        && !has channelToBob "Diary" && has channelToAlice "Diary"),
    ("videos: a video the store does not hold is not ready, watched or listed",
      status early == 409 && status ghostEarly == 404 && has feedEarly "Cats"
        && !has feedEarly "Ghost" && has waiting "Not confirmed yet"),
    ("videos: after a restart on the journal, sessions, likes and comments are kept",
      has kept "2 likes" && has kept "Nice cats"),
    ("videos: after a restart, an upload begun before is checked and listed",
      status late == 303 && has feed "Ghost" && !has feed "Diary"),
    ("videos: the feed comes a page at a time, newest first",
      has feed "?before=2" && !has feed "Cats" && has older "Cats"),
    ("videos: only its author deletes a comment",
      status uncommentedByAlice == 404 && status uncommented == 303
        && !has afterUncomment "Nice cats"),
    ("videos: a deleted video is not served, and its object is deleted in the store",
      status deleted == 303 && status gone == 404 && !has feedAfter "Cats" && objectGone),
    ("videos: signed out, the session is over",
      status signedOut == 303 && status stillOut == 303 && location stillOut == "/") ]

def scratch : IO System.FilePath := do
  return s!"{(← IO.getEnv "TMPDIR").getD "/tmp"}/videos-{← IO.monoNanosNow}.journal"

def remove (path : System.FilePath) : IO Unit := do
  for file in [path, path.addExtension "lock", path.addExtension "snapshot"] do
    if ← file.pathExists then IO.FS.removeFile file

/-- The flow against the fake S3 and the provider, both run here. -/
def run : IO (List (String × Bool)) := do
  let journal ← scratch
  try
    (do
      let (s3, s3Port, objects) ← Tests.S3.fake Tests.S3.creds
      let (hubServer, hubPort) ← Tests.OAuth.fake provider
      let d := deployment (Tests.S3.bucketAt s3Port) Tests.S3.creds hubPort journal
      let results ← flow d fun key => return ((← objects.get).lookup key).isSome
      s3.close
      hubServer.close
      return results : Async _).block
  finally
    remove journal

end Videos.EndToEnd
