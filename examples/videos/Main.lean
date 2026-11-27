/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Serve
import Google
import GitHub

/-!
`videos [port] [journal] [secrets]`: the site. The journal and its snapshot keep the members,
the videos, the likes and the comments; `secrets` holds the key that signs session cookies and
form tokens, 32 random bytes made at the first start (`videos.secrets` unless given).

From the environment, read once at start (rule 2.5):

- `VIDEOS_URL`: the site's public origin (`http://localhost:<port>` if unset); cookies are
  `Secure` when it is `https:`, and each provider's redirect URI is
  `<VIDEOS_URL>/sign-in/<google|github>/callback`;
- `LANES_HOST`, `LANES_IDLE_MS` and `LANES_DRAIN_MS`, as `lanes new` reads them and the
  deployment's unit sets them (`docs/DEPLOY.md`): where to listen (`127.0.0.1` unless set), how
  long an idle connection is kept, and how long SIGTERM waits for the requests in flight;
- `VIDEOS_BUCKET` and `AWS_REGION` (`us-east-1` if unset): the bucket of the videos;
  `VIDEOS_S3_ENDPOINT`, as `http://host:port`, for a store other than AWS's (MinIO,
  LocalStack), named by path;
- `AWS_ACCESS_KEY_ID`, `AWS_SECRET_ACCESS_KEY` and `AWS_SESSION_TOKEN`: the S3 client's
  credentials (`S3.credentialsFromEnv`);
- `VIDEOS_MAX_UPLOAD_BYTES`: the largest video a member may upload, which the upload form's
  policy makes the store refuse past (2 GiB if unset, at most 5 GiB);
- `GOOGLE_CLIENT_ID` and `GOOGLE_CLIENT_SECRET`, `GITHUB_CLIENT_ID` and `GITHUB_CLIENT_SECRET`:
  a provider for each pair that is set.
-/

open Lanes Lanes.Http Lanes.OAuth Videos Videos.Web

def loadKey (path : System.FilePath) : IO ByteArray := do
  if ← path.pathExists then
    let bytes ← IO.FS.readBinFile path
    if bytes.size != 32 then throw (IO.userError s!"videos: {path} does not hold 32 bytes")
    return bytes
  let bytes ← randomBytes 32
  IO.FS.writeBinFile path bytes
  return bytes

def client (origin name : String) : IO (Option Client) := do
  let some id := (← IO.getEnv s!"{name.toUpper}_CLIENT_ID").filter (!·.isEmpty) | return none
  let some secret := (← IO.getEnv s!"{name.toUpper}_CLIENT_SECRET").filter (!·.isEmpty) | return none
  return some { id, secret := ⟨secret⟩, redirect := s!"{origin}/sign-in/{name}/callback" }

/-- The bucket the environment names, at AWS or at `VIDEOS_S3_ENDPOINT`. -/
def bucket : IO (Option S3.Bucket) := do
  let some name := (← IO.getEnv "VIDEOS_BUCKET").filter (!·.isEmpty) | return none
  let region := ((← IO.getEnv "AWS_REGION").filter (!·.isEmpty)).getD "us-east-1"
  match (← IO.getEnv "VIDEOS_S3_ENDPOINT").filter (!·.isEmpty) with
  | none => return some { name, region, endpoint := S3.Endpoint.aws region }
  | some url =>
    let some e := Endpoint.parse url | throw (IO.userError s!"videos: {url} is not a URL")
    let scheme : Client.Scheme := if e.https then .https else .http
    return some { name, region, endpoint := { host := e.host, port := e.port, scheme, addressing := .path } }

def main (args : List String) : IO UInt32 := do
  let port := (args[0]? >>= String.toNat?).getD 8080
  let journal := args[1]?.map System.FilePath.mk
  let key ← loadKey ((args[2]?.map System.FilePath.mk).getD "videos.secrets")
  let origin := ((← IO.getEnv "VIDEOS_URL").filter (!·.isEmpty)).getD s!"http://localhost:{port}"
  let ms (name : String) (default : Nat) : IO Nat := do
    let some text ← IO.getEnv name | return default
    let some n := text.toNat? | throw (IO.userError s!"videos: {name} is not a number: {text}")
    return n
  let host := (← IO.getEnv "LANES_HOST").getD "127.0.0.1"
  let idle_ms ← ms "LANES_IDLE_MS" 10000
  let drain_ms ← ms "LANES_DRAIN_MS" 10000
  let maxUpload ← ms "VIDEOS_MAX_UPLOAD_BYTES" (2 * 1024 ^ 3)
  let some maxUpload_bytes := if h : 0 < maxUpload ∧ maxUpload ≤ S3.Post.maxObject_bytes then
      some ⟨maxUpload, h⟩ else none
    | IO.eprintln "videos: VIDEOS_MAX_UPLOAD_BYTES is from 1 byte to 5 GiB"; return 2
  let some b ← bucket | IO.eprintln "videos: VIDEOS_BUCKET is not set"; return 2
  let some creds ← S3.credentialsFromEnv
    | IO.eprintln "videos: AWS_ACCESS_KEY_ID and AWS_SECRET_ACCESS_KEY are not set"; return 2
  let mut providers := []
  for p in [Google.provider, GitHub.provider] do
    if let some c ← client origin p.name then providers := providers ++ [(p, c)]
  let secure := origin.startsWith "https:"
  let settings : Web.Settings :=
    { key := .of key, origin, secure, bucket := b, creds, providers := providers.map (·.1.name)
      maxUpload_bytes }
  let server ← (Web.start {
    settings, journal
    server := { host, port := port.toUInt16, system := "videos 1", idle_ms
                ops := { readinessPath := some "/readyz", livenessPath := some "/healthz"
                         metricsPath := some "/metrics", accessLog := .stderr, requestIds := true } }
    signIn := { providers, secure } }).block
  IO.println s!"videos listening on http://{host}:{server.port.getD 0}, signing in with \
    {", ".intercalate settings.providers}, storing in {b.name}"
  (← IO.getStdout).flush
  Lanes.block (server.stopOnSignal drain_ms)
  return 0
