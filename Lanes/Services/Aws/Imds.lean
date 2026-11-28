/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Services.Aws.Refresh
public import Lanes.Services.S3.Basic

/-!
# A role's credentials, from where AWS gives them to a machine

Two sources, each a few HTTP calls whose answers are read here; the edge
(`Aws/IO/Credentials.lean`) only makes the calls `Flow.call` names and hands the answers to
`Flow.next`.

- **An EC2 instance's metadata service, IMDSv2**: `PUT /latest/api/token` with the token's time
  to live in `X-aws-ec2-metadata-token-ttl-seconds`; then, with the token in
  `X-aws-ec2-metadata-token`, `GET /latest/meta-data/iam/security-credentials/` for the name of
  the instance's role, and `GET` of that name under it for the credentials. IMDSv1, a `GET`
  without a token, is never used, so an instance that requires tokens answers.
- **A container's credentials endpoint** (ECS, and EKS Pod Identity): one `GET` of the URL in
  `AWS_CONTAINER_CREDENTIALS_RELATIVE_URI` (under `http://169.254.170.2`) or
  `AWS_CONTAINER_CREDENTIALS_FULL_URI`, with `AWS_CONTAINER_AUTHORIZATION_TOKEN`, or the
  contents of the file `AWS_CONTAINER_AUTHORIZATION_TOKEN_FILE` names, in `Authorization`. A
  full URI over plain HTTP is taken only for a loopback address or the two link-local addresses
  ECS and EKS use, as AWS's SDKs do.

Both answer the same JSON: `AccessKeyId`, `SecretAccessKey`, `Token` and `Expiration`, the last
in RFC 3339, and the metadata service a `Code` that must be `Success`.

Which of them a process uses is `Imds.chain`, the order AWS's SDKs look in: keys in the
environment, then a container's endpoint, then the instance's metadata service, unless
`AWS_EC2_METADATA_DISABLED` is `true`.
-/

@[expose] public section

namespace Aws.Imds

open Lanes Lanes.Http

inductive Source where
  /-- An instance's metadata service. `host` and `port` are for a test. -/
  | instance (tokenTtl_s : Nat := 21600) (host : String := "169.254.169.254") (port : UInt16 := 80)
  /-- A container's credentials endpoint: where, and the authorization token it wants. -/
  | container (endpoint : Client.Call) (authorization : Option SigV4.Secret)

/-- How far a fetch has got. -/
inductive Flow where
  | start
  | token (token : SigV4.Secret)
  | role (token : SigV4.Secret) (role : String)
  | done (result : Except String (Refresh.Held SigV4.Credentials))

def tokenHeader : String := "x-aws-ec2-metadata-token"

def rolesPath : List String := ["latest", "meta-data", "iam", "security-credentials"]

def metadata (host : String) (port : UInt16) (request : Request) : Client.Call :=
  { host, port, scheme := .http, request }

/-- The call to make next, if any. -/
def Flow.call : Source → Flow → Option Client.Call
  | .instance ttl host port, .start =>
    some (metadata host port
      { method := .put, path := ["latest", "api", "token"],
        headers := [("x-aws-ec2-metadata-token-ttl-seconds", toString ttl)] })
  | .instance _ host port, .token t =>
    some (metadata host port
      { method := .get, path := rolesPath ++ [""], headers := [(tokenHeader, t.reveal)] })
  | .instance _ host port, .role t name =>
    some (metadata host port
      { method := .get, path := rolesPath ++ [name], headers := [(tokenHeader, t.reveal)] })
  | .container endpoint auth, .start =>
    some { endpoint with request := { endpoint.request with
      headers := endpoint.request.headers ++ (auth.map (("authorization", ·.reveal))).toList } }
  | _, _ => none

/-- A name IAM allows for a role: letters, digits and `+=,.@_-`, up to 64 of them. -/
def roleName? (s : String) : Option String :=
  let ok (c : Char) := c.isAlphanum || "+=,.@_-".contains c
  if 0 < s.length && s.length ≤ 64 && s.all ok then some s else none

/-- The body of a `200`, as text. -/
def text? (r : Response) : Except String String :=
  if r.status != 200 then .error s!"answered {r.status}"
  else match String.fromUTF8? r.body with
    | some s => .ok s
    | none => .error "an answer that is not UTF-8"

/-- Milliseconds since the epoch of an RFC 3339 time. -/
def millis? (s : String) : Option Nat := do
  let t ← TimeFormat.parseRfc3339 s
  let seconds := t.toUnix
  if seconds < 0 then none else some (seconds.toNat * 1000)

/-- The credentials in the JSON both sources answer. -/
def readCredentials (body : String) : Except String (Refresh.Held SigV4.Credentials) := do
  let j ← Json.parse body
  if let .ok code := j.getObjValAs? String "Code" then
    unless code == "Success" do throw s!"the metadata service says {code}"
  let id ← j.getObjValAs? String "AccessKeyId"
  let secret ← j.getObjValAs? String "SecretAccessKey"
  let token ← j.getObjValAs? String "Token"
  let expiration ← j.getObjValAs? String "Expiration"
  let some expires_ms := millis? expiration | throw "an expiration that is not RFC 3339"
  if id.isEmpty || secret.isEmpty then throw "empty credentials"
  return { creds := { accessKeyId := id, secretAccessKey := ⟨secret⟩,
                      sessionToken := if token.isEmpty then none else some ⟨token⟩ }
           expires_ms }

/-- What the answer to the flow's call makes of it. No answer, or an answer refused, ends it. -/
def Flow.next (source : Source) (flow : Flow) (answer : Option Response) : Flow :=
  match answer with
  | none => .done (.error "no answer by the deadline")
  | some r =>
    match source, flow with
    | .instance .., .start =>
      match text? r with
      | .ok text =>
        let text := text.trimAscii.toString
        if text.isEmpty then .done (.error "an empty token") else .token ⟨text⟩
      | .error e => .done (.error ("the token: " ++ e))
    | .instance .., .token t =>
      match text? r with
      | .ok names =>
        match ((names.splitOn "\n").map (·.trimAscii.toString)).head?.bind roleName? with
        | some name => .role t name
        | none => .done (.error "no role")
      | .error e => .done (.error ("the role: " ++ e))
    | .instance .., .role .. | .container .., .start =>
      .done ((text? r).bind readCredentials)
    | _, _ => .done (.error "nothing was asked")

/-- The result, once the flow is done: at most three calls are made. -/
def Flow.result : Flow → Option (Except String (Refresh.Held SigV4.Credentials))
  | .done result => some result
  | _ => none

/-! ## A container's endpoint, from its environment -/

def ecsHost : String := "169.254.170.2"

/-- Plain HTTP is taken only for these: loopback, ECS's and EKS Pod Identity's addresses. -/
def plainAllowed (host : String) : Bool :=
  host == ecsHost || host == "169.254.170.23" || host == "localhost"
    || (host.startsWith "127." && (Std.Net.IPv4Addr.ofString host).isSome)

def decodePair (pair : String) : Option (String × String) :=
  match pair.splitOn "=" with
  | [k] => (percentDecode k).map (·, "")
  | k :: v => do return (← percentDecode k, ← percentDecode ("=".intercalate v))
  | [] => none

/-- The call to the endpoint at `url`: its origin, path and query. -/
def endpoint? (url : String) : Option Client.Call := do
  let (scheme, rest) ← match url.splitOn "://" with
    | [scheme, rest] => some (scheme, rest)
    | _ => none
  let (authority, target) := match rest.splitOn "/" with
    | authority :: path => (authority, "/" ++ "/".intercalate path)
    | [] => (rest, "/")
  let (pathText, queryText) := match target.splitOn "?" with
    | [p] => (p, "")
    | p :: q => (p, "?".intercalate q)
    | [] => (target, "")
  let segments ← ((pathText.drop 1).toString.splitOn "/").mapM fun s => percentDecode s
  let query ← if queryText.isEmpty then some [] else (queryText.splitOn "&").mapM decodePair
  let call ← Client.Call.at (scheme ++ "://" ++ authority) { method := .get, path := segments, query }
  if call.scheme == .http && !plainAllowed call.host then none
  return call

/-- A container's source, from the values of its environment `get` gives; the token file's
contents, if `AWS_CONTAINER_AUTHORIZATION_TOKEN_FILE` named one, as `tokenFile`. `none` when
neither URI is set, or the one set is not taken. -/
def containerSource? (get : String → Option String) (tokenFile : Option String := none) :
    Option Source :=
  let url := match (get "AWS_CONTAINER_CREDENTIALS_RELATIVE_URI").filter (!·.isEmpty) with
    | some relative => some ("http://" ++ ecsHost ++ relative)
    | none => (get "AWS_CONTAINER_CREDENTIALS_FULL_URI").filter (!·.isEmpty)
  let token := (tokenFile.map (·.trimAscii.toString)).orElse fun _ =>
    get "AWS_CONTAINER_AUTHORIZATION_TOKEN"
  (url.bind endpoint?).map fun call => .container call ((token.filter (!·.isEmpty)).map (⟨·⟩))

/-! ## Where a process's credentials come from -/

inductive Origin where
  /-- Keys in the environment, used as they are: they do not expire, or their owner renews
  them. -/
  | keys (creds : SigV4.Credentials)
  /-- A role's, fetched from `source` and again before they expire. -/
  | role (source : Source)
  /-- None: no keys, no container's endpoint, and the metadata service turned off. -/
  | none

/-- Whether `AWS_EC2_METADATA_DISABLED` turns the metadata service off, as the SDKs read it. -/
def metadataDisabled (get : String → Option String) : Bool :=
  (get "AWS_EC2_METADATA_DISABLED").any (·.toLower == "true")

/-- The first source, in the order AWS's SDKs look, that the environment `get` gives: keys
(`S3.credentialsOf?`), then a container's endpoint (`containerSource?`, with the token file's
contents), then the instance's metadata service. -/
def chain (get : String → Option String) (tokenFile : Option String := none) : Origin :=
  match S3.credentialsOf? get with
  | some creds => .keys creds
  | none =>
    match containerSource? get tokenFile with
    | some source => .role source
    | none => if metadataDisabled get then .none else .role .instance

theorem chain_keys {get : String → Option String} {tokenFile : Option String}
    {creds : SigV4.Credentials} (h : S3.credentialsOf? get = some creds) :
    chain get tokenFile = .keys creds := by
  simp [chain, h]

theorem chain_container {get : String → Option String} {tokenFile : Option String}
    {source : Source} (hk : S3.credentialsOf? get = none)
    (hc : containerSource? get tokenFile = some source) : chain get tokenFile = .role source := by
  simp [chain, hk, hc]

theorem containerSource?_container {get : String → Option String} {tokenFile : Option String}
    {s : Source} (h : containerSource? get tokenFile = some s) :
    ∃ call auth, s = .container call auth := by
  simp only [containerSource?, Option.map_eq_some_iff] at h
  obtain ⟨_, _, rfl⟩ := h
  exact ⟨_, _, rfl⟩

/-- The metadata service is asked only when nothing comes before it and it is not turned off. -/
theorem chain_instance {get : String → Option String} {tokenFile : Option String}
    (h : chain get tokenFile = .role .instance) :
    S3.credentialsOf? get = none ∧ metadataDisabled get = false := by
  unfold chain at h
  split at h
  · cases h
  · rename_i hk
    split at h
    · rename_i hc
      cases h
      obtain ⟨_, _, h⟩ := containerSource?_container hc
      cases h
    · constructor
      · exact hk
      · cases hm : metadataDisabled get <;> simp_all

end Aws.Imds
