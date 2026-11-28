/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Services.Aws
import Tests.Aws.Fake

/-!
The credentials' sources and the provider: the answers AWS documents read; the calls of IMDSv2;
a container's endpoint from its environment; and the provider against a fake metadata service
in the test, which refuses a request without a session token, names one role, and issues new
credentials at each fetch that expire within seconds, so the refresh runs; against outages, a
closed port, and a container's endpoint that checks its token. Then the S3 client signs with
the provider's credentials against the fake S3 of Lanes's tests.
-/

namespace Checks.Imds

open Lanes Lanes.Http Aws Aws.Imds Std Std.Async

/-- The answer the EC2 documentation shows, its token shortened. -/
def documented : String :=
  "{\n  \"Code\" : \"Success\",\n  \"LastUpdated\" : \"2012-04-26T16:39:16Z\",\n"
    ++ "  \"Type\" : \"AWS-HMAC\",\n  \"AccessKeyId\" : \"ASIAIOSFODNN7EXAMPLE\",\n"
    ++ "  \"SecretAccessKey\" : \"wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY\",\n"
    ++ "  \"Token\" : \"IQoJb3JpZ2luX2VjEXAMPLETOKEN\",\n  \"Expiration\" : \"2017-05-17T15:09:54Z\"\n}"

/-- The answer of a container's endpoint, as the ECS documentation shows it. -/
def container : String :=
  "{\"AccessKeyId\":\"ASIAEXAMPLE\",\"Expiration\":\"2026-11-27T20:00:00Z\",\
  \"RoleArn\":\"arn:aws:iam::123456789012:role/task\",\"SecretAccessKey\":\"s\",\"Token\":\"t\"}"

def ok (body : String) : Response := { status := 200, body := body.toUTF8 }

def env (pairs : List (String × String)) (name : String) : Option String := pairs.lookup name

def unitTests : List (String × Bool) :=
  let src : Source := .instance
  let start := Flow.start.call src
  let tokened := (Flow.start.next src (some (ok "AQAEAexample=="))).call src
  let roled := ((Flow.token ⟨"AQAEAexample=="⟩).next src (some (ok "lanes-app\n"))).call src
  [ ("imds: the documented answer is read, its expiry in milliseconds",
      match readCredentials documented with
      | .ok h => h.creds.accessKeyId == "ASIAIOSFODNN7EXAMPLE"
          && h.creds.secretAccessKey.reveal == "wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY"
          && h.creds.sessionToken.map (·.reveal) == some "IQoJb3JpZ2luX2VjEXAMPLETOKEN"
          && h.expires_ms == 1495033794000
      | .error _ => false),
    ("imds: a container's answer is read the same way",
      (readCredentials container).toOption.any (·.creds.accessKeyId == "ASIAEXAMPLE")),
    ("imds: a Code other than Success, a bad expiry and missing keys are refused",
      (readCredentials (documented.replace "\"Success\"" "\"Failure\"")).toOption.isNone
        && (readCredentials (documented.replace "2017-05-17T15:09:54Z" "tomorrow")).toOption.isNone
        && (readCredentials "{\"AccessKeyId\":\"a\"}").toOption.isNone
        && (readCredentials "not json").toOption.isNone),
    ("imds: the token is asked for with PUT and a time to live, never a GET without one",
      start.any fun c => c.host == "169.254.169.254" && c.port == 80 && c.request.method == .put
        && c.request.target == "/latest/api/token"
        && c.request.headers == [("x-aws-ec2-metadata-token-ttl-seconds", "21600")]),
    ("imds: then the role, then its credentials, each with the token",
      (tokened.any fun c => c.request.target == "/latest/meta-data/iam/security-credentials/"
          && c.request.headers == [("x-aws-ec2-metadata-token", "AQAEAexample==")])
        && roled.any fun c => c.request.target == "/latest/meta-data/iam/security-credentials/lanes-app"
          && c.request.headers == [("x-aws-ec2-metadata-token", "AQAEAexample==")]),
    ("imds: a refused token, no role, a role IAM would not name, and no answer end the flow",
      (Flow.start.next src (some { status := 401 })).result.any (·.toOption.isNone)
        && ((Flow.token ⟨"t"⟩).next src (some { status := 404 })).result.isSome
        && ((Flow.token ⟨"t"⟩).next src (some (ok "a/b"))).result.isSome
        && (Flow.start.next src none).result.isSome),
    ("imds: a relative URI is under ECS's address, with the authorization token",
      match containerSource? (env [("AWS_CONTAINER_CREDENTIALS_RELATIVE_URI", "/v2/credentials/abc"),
          ("AWS_CONTAINER_AUTHORIZATION_TOKEN", "tok")]) with
      | some s@(.container c _) => c.host == "169.254.170.2" && c.port == 80
          && (Flow.start.call s).any fun c => c.request.target == "/v2/credentials/abc"
            && c.request.headers == [("authorization", "tok")]
      | _ => false),
    ("imds: a full URI over HTTP only to loopback or the link-local addresses, over HTTPS anywhere",
      (containerSource? (env [("AWS_CONTAINER_CREDENTIALS_FULL_URI", "http://169.254.170.23/v1/credentials")])).isSome
        && (containerSource? (env [("AWS_CONTAINER_CREDENTIALS_FULL_URI", "http://127.0.0.1:8080/creds?x=1")])).isSome
        && (containerSource? (env [("AWS_CONTAINER_CREDENTIALS_FULL_URI", "http://example.com/creds")])).isNone
        && (containerSource? (env [("AWS_CONTAINER_CREDENTIALS_FULL_URI", "https://example.com/creds")])).isSome
        && (containerSource? (env [])).isNone),
    ("imds: the token file's contents win over the variable",
      match containerSource? (env [("AWS_CONTAINER_CREDENTIALS_FULL_URI", "http://169.254.170.23/v1/credentials"),
          ("AWS_CONTAINER_AUTHORIZATION_TOKEN", "old")]) (some "from-file\n") with
      | some (.container _ (some t)) => t.reveal == "from-file"
      | _ => false),
    ("imds: credentials print nothing of their secrets",
      match readCredentials documented with
      | .ok h =>
        let r := reprStr h.creds
        (r.splitOn "EXAMPLEKEY").length == 1 && (r.splitOn "EXAMPLETOKEN").length == 1
          && (r.splitOn "<secret>").length == 3
      | .error _ => false) ]

/-- Which source a process's credentials come from, and how long what is signed with them
lasts. -/
def chainTests : List (String × Bool) :=
  let keys := [("AWS_ACCESS_KEY_ID", "AKIAEXAMPLE"), ("AWS_SECRET_ACCESS_KEY", "s")]
  let ecs := [("AWS_CONTAINER_CREDENTIALS_RELATIVE_URI", "/v2/credentials/abc")]
  [ ("credentials chain: keys in the environment come first, with their session token",
      match chain (env (keys ++ ("AWS_SESSION_TOKEN", "t") :: ecs)) with
      | .keys c => c.accessKeyId == "AKIAEXAMPLE" && c.sessionToken.map (·.reveal) == some "t"
      | _ => false),
    ("credentials chain: then a container's endpoint, then the instance's metadata service",
      (match chain (env ecs) with | .role (.container c _) => c.host == "169.254.170.2" | _ => false)
        && (match chain (env [("AWS_ACCESS_KEY_ID", "AKIAEXAMPLE")]) with
            | .role (.instance ..) => true
            | _ => false)),
    ("credentials chain: with the metadata service turned off there are none, and keys still come first",
      (match chain (env [("AWS_EC2_METADATA_DISABLED", "TRUE")]) with | .none => true | _ => false)
        && (match chain (env (("AWS_EC2_METADATA_DISABLED", "true") :: keys)) with
            | .keys _ => true
            | _ => false)),
    ("signing: a link or a form lasts as asked, or until its credentials expire, whichever is sooner",
      S3.expiryWithin ⟨900, by decide⟩ 1000 none == some ⟨900, by decide⟩
        && S3.expiryWithin ⟨900, by decide⟩ 1000 (some 121500) == some ⟨120, by decide⟩
        && S3.expiryWithin ⟨60, by decide⟩ 0 (some 3600000) == some ⟨60, by decide⟩
        && S3.expiryWithin ⟨900, by decide⟩ 1000 (some 1999) == none
        && S3.expiryWithin ⟨900, by decide⟩ 5000 (some 1000) == none) ]

/-! ## A fake metadata service -/

structure Metadata where
  /-- How long each credential issued is good for. -/
  life_s : Nat
  /-- Credentials requests answered `500` first. -/
  failures : IO.Ref Nat
  issued : IO.Ref Nat
  /-- A new key at each fetch, or the same one. -/
  rotate : Bool := true
  /-- Requests that came without a valid token, besides the token's own. -/
  untokened : IO.Ref Nat

def Metadata.new (life_s : Nat) (failures : Nat := 0) (rotate : Bool := true) : IO Metadata :=
  return { life_s, failures := ← IO.mkRef failures, issued := ← IO.mkRef 0, rotate,
           untokened := ← IO.mkRef 0 }

def keysOf (n : Nat) : SigV4.Credentials :=
  { accessKeyId := s!"ASIA{n}", secretAccessKey := ⟨s!"secret-{n}"⟩, sessionToken := some ⟨s!"token-{n}"⟩ }

def credentialsJson (n : Nat) (expires_s : Nat) : String :=
  let k := keysOf n
  s!"\{\"Code\":\"Success\",\"LastUpdated\":\"{Fake.rfc3339 (expires_s - 3600)}\",\"Type\":\"AWS-HMAC\",\
    \"AccessKeyId\":\"{k.accessKeyId}\",\"SecretAccessKey\":\"{k.secretAccessKey.reveal}\",\
    \"Token\":\"{(k.sessionToken.map (·.reveal)).getD ""}\",\"Expiration\":\"{Fake.rfc3339 expires_s}\"}"

def Metadata.handle (m : Metadata) (r : Tests.S3.Raw) : IO (Option ByteArray) := do
  let token := "AQAE-session"
  if r.verb == "PUT" && r.target == "/latest/api/token" then
    return some (if (r.headers.lookup "x-aws-ec2-metadata-token-ttl-seconds").isSome
      then Fake.text 200 token else Fake.text 400 "")
  unless r.headers.lookup "x-aws-ec2-metadata-token" == some token do
    m.untokened.modify (· + 1)
    return some (Fake.text 401 "")
  match r.verb, r.target with
  | "GET", "/latest/meta-data/iam/security-credentials/" => return some (Fake.text 200 "lanes-app")
  | "GET", "/latest/meta-data/iam/security-credentials/lanes-app" =>
    if (← m.failures.modifyGet fun n => (n, n - 1)) > 0 then return some (Fake.text 500 "")
    let n ← m.issued.modifyGet fun n => (if m.rotate then n else 0, n + 1)
    let now_s := (← Credentials.nowMs) / 1000
    return some (Fake.json 200 (credentialsJson n (now_s + m.life_s)))
  | _, _ => return some (Fake.text 404 "")

/-- A configuration for seconds, not hours: fetched 2.5 s before expiry, given up after one. -/
def quick : Refresh.Config :=
  { margin_ms := 2500, jitter_ms := 200, skew_ms := 500, deadline_ms := 1000, backoff_ms := 100,
    maxBackoff_ms := 800 }

def instanceAt (port : UInt16) : Source := .instance 21600 "127.0.0.1" port

def keyOf (p : Credentials.Provider) : IO (Option String) := do
  return (← p.read).map (·.accessKeyId)

def refreshes : Async (List (String × Bool)) := do
  let m ← Metadata.new 4
  let (server, port) ← Fake.serve m.handle
  let p ← Credentials.start (instanceAt port) quick
  let first ← Fake.waitFor 2000 do return (← keyOf p).isSome
  let firstKey ← keyOf p
  -- Expiring in four seconds, they are fetched again within two, and are never missing.
  let mut missing := false
  let mut changed := false
  for _ in [0:150] do
    let k ← keyOf p
    if k.isNone then missing := true
    if k.isSome && k != firstKey then changed := true; break
    Async.sleep 20
  let held ← p.state.get
  p.stop
  server.close
  return [
    ("imds provider: credentials are fetched at once, with a session token",
      first && firstKey == some "ASIA0" && (← m.untokened.get) == 0),
    ("imds provider: they are fetched again before they expire, and are never missing meanwhile",
      changed && !missing && (held.held.any fun h => h.creds.accessKeyId != "ASIA0")) ]

def outages : Async (List (String × Bool)) := do
  let m ← Metadata.new 3600 (failures := 3)
  let (server, port) ← Fake.serve m.handle
  let p ← Credentials.start (instanceAt port) quick
  let failedFirst ← Fake.waitFor 1000 do return (← p.failure).isSome
  let recovered ← Fake.waitFor 4000 do return (← keyOf p).isSome
  let clean ← p.failure
  p.stop
  server.close
  -- A port where nothing listens.
  let (closed, closedPort) ← Fake.serve fun _ => pure (some (Fake.text 200 ""))
  closed.close
  let q ← Credentials.start (instanceAt closedPort) quick
  Async.sleep 500
  let nothing ← q.read
  let why ← q.failure
  let state ← q.state.get
  q.stop
  return [
    ("imds provider: after three failures it retries with a backoff, and gets credentials",
      failedFirst && recovered && clean.isNone),
    ("imds provider: with no service, no credentials, a reason, and a bounded wait",
      nothing.isNone && why.isSome && state.backoff_ms ≤ quick.maxBackoff_ms) ]

def containerEndpoint : Async (List (String × Bool)) := do
  let handle (r : Tests.S3.Raw) : IO (Option ByteArray) := do
    if r.target != "/v2/credentials/abc" then return some (Fake.text 404 "")
    unless r.headers.lookup "authorization" == some "Bearer-ish tok" do return some (Fake.text 401 "")
    let now_s := (← Credentials.nowMs) / 1000
    return some (Fake.json 200 (credentialsJson 7 (now_s + 3600)))
  let (server, port) ← Fake.serve handle
  let url := s!"http://127.0.0.1:{port}/v2/credentials/abc"
  let some good := containerSource? (env [("AWS_CONTAINER_CREDENTIALS_FULL_URI", url),
      ("AWS_CONTAINER_AUTHORIZATION_TOKEN", "Bearer-ish tok")])
    | return [("imds container: the source is made", false)]
  let some bad := containerSource? (env [("AWS_CONTAINER_CREDENTIALS_FULL_URI", url),
      ("AWS_CONTAINER_AUTHORIZATION_TOKEN", "wrong")])
    | return [("imds container: the source is made", false)]
  let p ← Credentials.start good quick
  let q ← Credentials.start bad quick
  let got ← Fake.waitFor 2000 do return (← keyOf p).isSome
  Async.sleep 200
  let refused ← q.read
  p.stop; q.stop
  server.close
  return [
    ("imds container: the endpoint's credentials, with its authorization token",
      got && (← keyOf p) == some "ASIA7"),
    ("imds container: a wrong token gets none", refused.isNone) ]

/-- The S3 client signs with the provider's credentials, which the fake S3 checks. -/
def s3 : Async (List (String × Bool)) := do
  let m ← Metadata.new 3600 (rotate := false)
  let (server, port) ← Fake.serve m.handle
  let p ← Credentials.start (instanceAt port) quick
  let _ ← Fake.waitFor 2000 do return (← keyOf p).isSome
  let (store, storePort, _) ← Tests.S3.fake (keysOf 0)
  let b := Tests.S3.bucketAt storePort
  let k := Tests.S3.key "thumbs/a.png"
  let put ← S3.exchange b p.source (.put k "png".toUTF8 (some "image/png")) Tests.S3.config
  let got ← S3.exchange b p.source (.get k) Tests.S3.config
  let none_ ← S3.exchange b (⟨pure none⟩ : SigV4.Source) (.get k) Tests.S3.config
  p.stop
  store.close; server.close
  return [
    ("s3 with the instance's role: a put and a get signed with its credentials and token",
      put.any (· matches .stored _) && got.any (· matches .object _ _)),
    ("s3 with no credentials: nothing is sent, and there is no answer", none_.isNone) ]

/-- What `X-Amz-Expires` a link says. -/
def expiresOf (link : String) : Option Nat :=
  ((link.splitOn "X-Amz-Expires=")[1]?).bind fun rest =>
    (String.ofList (rest.toList.takeWhile (· != '&'))).toNat?

/-- A form and a link signed at the moment with the instance role's credentials and their token,
which the fake S3 takes; the link lasts no longer than the credentials. -/
def signNow : Async (List (String × Bool)) := do
  let m ← Metadata.new 100 (rotate := false)
  let (server, port) ← Fake.serve m.handle
  let p ← Credentials.start (instanceAt port) quick
  let _ ← Fake.waitFor 2000 do return (← keyOf p).isSome
  let store ← Lanes.Testing.S3.Fake.start (keysOf 0) "videos"
  let b := store.bucket
  let k := Tests.S3.key "up/a.mp4"
  let policy : S3.Post.Policy :=
    { key := .exact k, length := ⟨1, 100, by decide, by decide⟩, expiry := ⟨900, by decide⟩ }
  let form ← S3.Post.formNow b p.source policy
  let posted ← match form with
    | some f => Lanes.Testing.S3.postForm f.url f.fields "a clip".toUTF8
    | none => pure none
  let link ← S3.presignNow b p.source .get k ⟨3600, by decide⟩
  let got ← match link with
    | some l => Lanes.Testing.S3.follow l .get
    | none => pure none
  let none_ ← S3.presignNow b (⟨pure none⟩ : SigV4.Source) .get k ⟨60, by decide⟩
  p.stop
  store.stop
  server.close
  return [
    ("s3 with the instance's role: a form signed at the moment, with the session token, uploads",
      (form.any fun f => f.fields.any (·.1 == "x-amz-security-token"))
        && posted.any (·.status == 204)),
    ("s3 with the instance's role: a link signed at the moment, with the session token, gets the file",
      (link.any fun l => (l.splitOn "X-Amz-Security-Token").length == 2)
        && (got.map (·.body)) == some "a clip".toUTF8),
    ("s3 with the instance's role: an hour asked, with 100 s of credentials left, the link lasts at most 100 s",
      (link.bind expiresOf).any fun e => 90 ≤ e && e ≤ 100),
    ("s3 with no credentials: no link", none_.isNone) ]

def live : Async (List (String × Bool)) := do
  return (← refreshes) ++ (← outages) ++ (← containerEndpoint) ++ (← s3) ++ (← signNow)

end Checks.Imds
