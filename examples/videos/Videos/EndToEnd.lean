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
integration, a store: the test kit's fake S3 (`Lanes.Testing.S3`), which checks every
signature from the bytes it receives, the presigned links' and the upload forms' policies
included, and enforces a policy's size; and the kit's fake transcode worker
(`Lanes.Testing.Transcode`), which reads each upload from the fake S3, writes a rendition and a
thumbnail there, and posts its signed report to the site when the test says. A browser is the
kit's: it signs in, makes a video, posts the file with the form the page carries, asks the site
to check, sees it being prepared, watches the rendition through the link the page's `<video>`
carries, with the thumbnail as its poster, likes, comments, and deletes. Midway the server is
stopped and started again on its journal, and the flow goes on. Twice the store refuses a call
once, a check and a delete, and the scheduler's next attempt succeeds. A transcode fails once and
is tried again by its owner, and a report forged with another key is refused.

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

/-- What the link after `marker` in a page gives, followed as a browser does. -/
def fetchLink (page : Option Http.Response) (marker : String) : Async (Option ByteArray) := do
  let some src := between page marker "\"" | return none
  let got ← Testing.S3.follow src .get
  return got.bind fun r => if r.status == 200 then some r.body else none

/-- The rendition the watch page's `<video>` plays. -/
def fetchVideo (page : Option Http.Response) : Async (Option ByteArray) :=
  fetchLink page "\" src=\""

/-- The thumbnail the watch page's `<video>` shows before it plays. -/
def fetchPoster (page : Option Http.Response) : Async (Option ByteArray) :=
  fetchLink page "poster=\""

/-- The key the site and the test's worker share. -/
def workerKey : Hmac.Key := .of "the worker's key of the test deployment".toUTF8

/-- The deployment the tests and the live smoke run: ops on, a journal, a store, and the kit's
provider as GitHub. -/
def deployment (bucket : S3.Bucket) (creds : SigV4.Credentials) (provider : Testing.OAuth.Fake)
    (worker : Testing.Transcode.Fake) (journal : System.FilePath) (keyPrefix : String := "videos/") :
    Deployment :=
  { config := { pageSize := 1, workerKey
                checkRetry := { maxAttempts := 2, deadline_ms := 3000, base_ms := 50, cap_ms := 50 }
                transcodeRetry := { maxAttempts := 2, deadline_ms := 3000, base_ms := 50, cap_ms := 50 }
                deleteRetry := { maxAttempts := 4, deadline_ms := 3000, base_ms := 50, cap_ms := 200 } }
    settings := { keys := .of (.of "the key of the test deployment".toUTF8), origin, secure := false
                  bucket, creds, providers := ["hub"], keyPrefix
                  maxUpload_bytes := ⟨maxUpload_bytes, by decide⟩
                  worker := worker.origin, callback := s!"{origin}/transcoded" }
    server := { port := 0, system := "videos 4"
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

/-- The worker works on every job it took, and says whether it did any, and whether the site took
every report. -/
def transcode (worker : Testing.Transcode.Fake) : Async Bool := do
  let sent ← worker.work
  return !sent.isEmpty && sent.all (·.2 == 200)

/-- The flow, against the store `d` names and its worker; `held` says whether the store holds a
key, where the test can see, and `refuse` has the store refuse the next call and says whether it
did (a real store cannot be told to, and says `true`). -/
def flow (d : Deployment) (provider : Testing.OAuth.Fake) (worker : Testing.Transcode.Fake)
    (held : String → Async Bool) (refuse : Async Unit := pure ()) (refused : Async Bool := pure true) :
    Async (List (String × Bool)) := do
  let server ← start d
  let port := server.port.getD 0
  worker.reportTo port
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
  let preparing ← aliceB.get ["v", "0"]
  let notYet ← bobB.get ["v", "0"]
  let feedPreparing ← anon.get []
  let renditionEarly ← held (d.settings.renditionKey 0)
  let jobs ← eventually do return !(← worker.taken).isEmpty
  let transcoded ← transcode worker
  let watched ← bobB.get ["v", "0"]
  let bytes ← fetchVideo watched
  let poster ← fetchPoster watched
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
  refuse
  let retried ← post aliceB ["videos", "1", "uploaded"]
  let checkRefused ← refused
  let _ ← eventually do return (← worker.taken).length == 2
  let _ ← transcode worker
  let secretToBob ← bobB.get ["v", "1"]
  let secretToAnon ← anon.get ["v", "1"]
  let secretToAlice ← aliceB.get ["v", "1"]
  let channelToBob ← bobB.get ["c", "0"]
  let channelToAlice ← aliceB.get ["c", "0"]
  let bobsChannel ← anon.get ["c", "1"]
  let (_, ghostPut) ← create aliceB "Ghost" "public"
  let tooLarge ← upload ghostPut (ByteArray.mk (Array.replicate (maxUpload_bytes + 1) 0))
  let early ← post aliceB ["videos", "2", "uploaded"]
  let ghostEarly ← bobB.get ["v", "2"]
  let ghostToOwner ← aliceB.get ["v", "2"]
  let feedEarly ← anon.get []
  let waiting ← aliceB.get ["c", "0"]
  server.stop
  let server ← start d
  let port := server.port.getD 0
  worker.reportTo port
  let (anon, aliceB, bobB, carolB) := (anon.at port, aliceB.at port, bobB.at port, carolB.at port)
  let _ ← upload ghostPut
  let late ← post aliceB ["videos", "2", "uploaded"]
  let _ ← eventually do return (← worker.taken).length == 3
  let forgedReport ← worker.forge d.settings.callback (.done "2.0" [d.settings.renditionKey 2, d.settings.thumbnailKey 2])
  let ghostForged ← anon.get ["v", "2"]
  worker.fail 1
  let _ ← transcode worker
  let ghostFailed ← aliceB.get ["v", "2"]
  let ghostToBob ← bobB.get ["v", "2"]
  let tryAgain ← post aliceB ["videos", "2", "retry"]
  let _ ← eventually do return (← worker.taken).length == 4
  let ghostRetried ← transcode worker
  let kept ← anon.get ["v", "0"]
  let feed ← anon.get []
  let older ← anon.get [] [("before", "2")]
  let uncommentedByCarol ← post carolB ["v", "0", "comments", "0", "delete"]
  let uncommented ← post bobB ["v", "0", "comments", "0", "delete"]
  let uncommentedByOwner ← post aliceB ["v", "0", "comments", "1", "delete"]
  let afterUncomment ← anon.get ["v", "0"]
  refuse
  let deleted ← post aliceB ["v", "0", "delete"]
  let gone ← bobB.get ["v", "0"]
  let feedAfter ← anon.get [] [("before", "2")]
  let objectGone ← eventually do
    return !(← held (d.settings.objectKey 0)) && !(← held (d.settings.renditionKey 0))
      && !(← held (d.settings.thumbnailKey 0))
  let deleteRefused ← refused
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
    ("videos: asked to check, the site asks the store, and the video is being prepared, to its "
      ++ "owner alone, and not listed",
      status confirmed == 303 && location confirmed == "/v/0" && status preparing == 200
        && shows preparing "being prepared" && status notYet == 404 && !shows feedPreparing "Cats"),
    ("videos: a confirmed upload is given to the worker, which writes nothing before it works",
      jobs && !renditionEarly),
    ("videos: once the worker reports, signed, the video is ready: its page plays the rendition, "
      ++ "with the thumbnail as its poster, signed links the store serves",
      transcoded && status watched == 200
        && bytes == some (Testing.Transcode.rendition clip.size)
        && poster == some Testing.Transcode.thumbnail),
    ("videos: a report forged with another key is refused, and the video stays not ready",
      forgedReport == 403 && status ghostForged == 404),
    ("videos: a transcode that failed is shown to its owner with a retry, and the retry makes it ready",
      status ghostFailed == 200 && shows ghostFailed "could not be prepared"
        && shows ghostFailed "/videos/2/retry" && status ghostToBob == 404
        && status tryAgain == 303 && ghostRetried),
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
      status early == 409 && status ghostEarly == 404 && shows ghostToOwner "not confirmed yet"
        && shows feedEarly "Cats"
        && !shows feedEarly "Ghost" && shows waiting "not confirmed yet"),
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
    ("videos: a check the store refuses once is tried again, and the video is ready",
      checkRefused && status retried == 303 && location retried == "/v/1"),
    ("videos: a deleted video is not served, and its upload, rendition and thumbnail are deleted "
      ++ "in the store, though the store refused the first delete",
      status deleted == 303 && status gone == 404 && !shows feedAfter "Cats" && objectGone
        && deleteRefused),
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
  { keys := .of (.of "a key".toUTF8), origin, secure := true
    bucket := { name := "b", region := "us-east-1", endpoint := S3.Endpoint.aws "us-east-1" }
    creds, worker := "http://worker.test", callback := s!"{origin}/transcoded" }

/-- The schema of the site's snapshot, for the pinned file `schemas/snapshot.schema`: the codecs
do not depend on the settings. -/
def snapshotSchema : Schema := Web.snapshotSchema { workerKey } settings

def decoded (r : Http.Request) : Option Input :=
  match (bridge settings).decode 0 ((bridge settings).prepare r) with
  | .ok (.inr i) => some i
  | _ => none

def withCookie (value : String) (r : Http.Request) : Http.Request :=
  { r with headers := r.headers ++ [("cookie", s!"{settings.cookieName}={value}")] }

def bridgeTests : List (String × Bool) :=
  let watch : Http.Request := { method := .get, path := ["v", "3"] }
  let token := sessionToken settings 0 7 0
  let like (csrf : String) (headers : List (String × String) := []) : Http.Request :=
    withCookie token { method := .post, path := ["v", "3", "like"], headers
                       body := s!"csrf={csrf}".toUTF8 }
  let good := Auth.formToken settings.keys (sessionOf 0 7)
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
    ("bridge: a store call is the head of the upload, or the deletes of the upload, the rendition "
      ++ "and the thumbnail, and only those",
      (match exchangeOf settings workerKey (Key.check 4 0).op, exchangeOf settings workerKey (Key.expire 4).op,
          exchangeOf settings workerKey (Key.delete 4).op with
        | some (.store [.head a]), some (.store [.head b]), some (.store [.delete c, .delete d, .delete e]) =>
          a.val == "videos/4" && b.val == "videos/4" && c.val == "videos/4" && d.val == "videos/4.mp4"
            && e.val == "videos/4.jpg"
        | _, _, _ => false)
        && storeReply none == .unknown && storeReply (some (.refused 500 "")) == .answer .failed
        && storeReplies [some .deleted, some .deleted, some .deleted] == .answer .deleted
        && storeReplies [some .deleted, none, some .deleted] == .unknown),
    ("bridge: a transcode is the round's job posted to the worker, signed, and taken with a 2xx",
      (match exchangeOf settings workerKey (Key.transcode ⟨4, 1⟩).op with
        | some (.worker r) =>
          Transcode.readJob? ((String.fromUTF8? r.body).getD "")
              == some (⟨"4.1", "videos/4", ["videos/4.mp4", "videos/4.jpg"]⟩, s!"{origin}/transcoded")
            && r.header? Transcode.signatureHeader
              == some (Transcode.jobSignature workerKey ((String.fromUTF8? r.body).getD ""))
        | _ => false)
        && workerReply (some (Http.Response.text "" 202)) == .answer .accepted
        && workerReply (some (Http.Response.text "" 500)) == .answer .failed && workerReply none == .unknown),
    ("bridge: a report is read with the signature it came with, which the bridge does not judge; "
      ++ "one of no round is refused",
      let hook (job : String) (sig : String) : Http.Request :=
        { Transcode.reportRequest workerKey ["transcoded"] (.done job []) with
          headers := [(Transcode.signatureHeader, sig)] }
      decoded (hook "4.1" "anything") == some (.request (.report 0 (.done ⟨4, 1⟩) "anything") 0)
        && decoded (hook "4.01" "anything") == none && decoded (hook "4" "anything") == none) ]

/-- What a shared cache in front may keep (`Http.SharedCache.leaks`): every reply and every
answer the bridge gives without the system, as each of three viewers would get it. None is kept
and given to another viewer. -/
def sharedCacheTests : List (String × Bool) :=
  let viewers : List Viewer := [none, some (0, 7), some (1, 8)]
  let asking (viewer : Viewer) (r : Http.Request) : Http.Request :=
    match viewer with
    | some (m, session) => withCookie (sessionToken settings m session 0) r
    | none => r
  let card : Card := ⟨1, 0, "a", "t", .public, 2⟩
  let view : View := ⟨card, "about", .mp4, false, [⟨0, 1, "b", "hi"⟩]⟩
  let replies : List Reply :=
    [.signedIn 0 7 100, .full, .signedOut, .noSession, .created 1 .mp4 100, .tooMany, .confirmed 1,
      .notUploaded 1, .unconfirmed 1, .watch view 100, .notFound, .liked 1 2 true, .commented 1,
      .tooManyComments 1, .uncommented 1, .deleted 1, .feed [card] none,
      .channel 0 "a" [card] [(2, "x", .transcoding), (3, "y", .failed)],
      .preparing 2 "x" .upload, .preparing 3 "y" .failed, .retrying 3, .reported, .forged]
  let encoded := replies.zipIdx.flatMap fun (r, n) => viewers.map fun viewer =>
    (asking viewer { method := .get, path := ["reply", toString n] }, encodeReply settings viewer r)
  let paths : List (List String) :=
    [[], ["style.css"], ["upload.js"], ["new"], ["v", "3"], ["c", "0"], ["nope"],
      ["sign-in", "github", "callback"]]
  let direct := paths.flatMap fun path => viewers.filterMap fun viewer =>
    let r := asking viewer { method := .get, path }
    match (bridge settings).decode 0 ((bridge settings).prepare r) with
    | .error answer => some (r, answer)
    | .ok _ => none
  [ ("shared cache: no reply, and no answer the bridge gives itself, may be kept and given to "
      ++ "another viewer", Http.SharedCache.leaks (encoded ++ direct) == []) ]

/-- How many requests the journal at `path` holds, and how many of them are reads. -/
def journalled (d : Deployment) (path : System.FilePath) : IO (Nat × Nat) := do
  let log ← openLog d path
  let requests := log.past.filterMap fun
    | .input (.inl (_, r)) => some r
    | _ => none
  log.close
  return (requests.length, (requests.filter fun r => (read? r).isSome).length)

/-- The flow against the fake S3 and the provider, both run here. With `corpus`, the site saves
often, and its journal and snapshot are copied there at the end, each unless one is there
already (`lake exe videosTest corpus <dir>`, `Tests/Corpus.lean` in Lanes). -/
def run (corpus : Option System.FilePath := none) : IO (List (String × Bool)) := do
  let journal ← scratch
  try
    let results ← (do
      let store ← Testing.S3.Fake.start creds "videos"
      let provider ← Testing.OAuth.Fake.start (oidc := false)
      let worker ← Testing.Transcode.Fake.start workerKey store.bucket creds
      let d := deployment store.bucket creds provider worker journal
      let d := if corpus.isSome then { d with runtime := { snapshotEvery := 32 } } else d
      let results ← flow d provider worker (fun key => store.holds key) (store.refuse 1)
        (return (← store.refusing) == 0)
      let (entered, reads) ← journalled d journal
      worker.stop
      store.stop
      provider.stop
      return results ++ [("videos: the feed, the watch pages and the channel pages are answered "
        ++ "from the state, and none is journalled", 0 < entered && reads == 0)] : Async _).block
    if let some dir := corpus then
      IO.FS.createDirAll dir
      for (name, from_) in [("journal", journal), ("snapshot", journal.addExtension "snapshot")] do
        if (← from_.pathExists) && !(← (dir / name).pathExists) then
          IO.FS.writeBinFile (dir / name) (← IO.FS.readBinFile from_)
          IO.println s!"wrote {dir / name}"
    return results
  finally
    remove journal

end Videos.EndToEnd
