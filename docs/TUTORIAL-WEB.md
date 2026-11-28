# Tutorial: a web app

The sequel to `docs/TUTORIAL.md`. It builds a shelf of files: members sign in with an OpenID
Connect provider, upload files straight from the browser to S3, see everyone's files, and
delete their own. The shelf is a table of PostgreSQL. Then it tests the whole site against fakes, checks and proves one property,
and says what running it needs. Read the first tutorial before this one.

The code of each step is kept in `Tests/TutorialWeb/`: `lake build` compiles it, and `lake test`
fails if this page quotes anything but that code and what the checker prints for it, and runs
the test of step 4. Imports there read `Tests.TutorialWeb.` where an app's read `Shelf.`.

## 1. Start from `lanes new`

```bash
lake exe lanes new shelf --dir ../shelf
cd ../shelf
lake test
```

This is the counter of the first tutorial: a stateless app whose data is a table of
PostgreSQL, each request one pure transaction, and a front that keeps nothing. The shelf keeps
its list of files the same way, in a table, and the files themselves in S3. Neither is in the
process, so a restart loses nothing and several instances serve one shelf.

**The tables.** Replace `Shelf/Counter.lean` with `Shelf/Files.lean`. A member is a string the
bridge makes from the identity the sign-in verified (step 2). An upload is begun, then seen in
the store, then listed. It is keyed by its uploader and its id, so that only a request made as
its uploader names it; the ids come from a counter that only grows, so that no two uploads share
an object of the store:

```lean
lanes_data structure Upload where
  owner : String
  id : Int64
  /-- The size the store gave when it was asked; `none` until it held the file. -/
  size : Option Int64
  deriving DecidableEq, Repr, Hashable
  table uploads key owner, id
```

with a migration that makes them, in `migrations/0001_shelf.sql`, in place of the counter's:

```sql
CREATE TABLE uploads (
  owner text COLLATE "C" NOT NULL,
  id bigint NOT NULL,
  size bigint,
  PRIMARY KEY (owner, id)
);
CREATE TABLE counters (
  name text COLLATE "C" NOT NULL PRIMARY KEY,
  next bigint NOT NULL
);
```

At its start the app checks the tables the migrations made against `Shelf.schema`, and refuses
to start on any difference: a column misspelled here, or one nullable that the declaration
says is not, stops it before it serves.

**The transactions.** What each request does, as one transaction. The shelf holds at most
`maxFiles` uploads (rule 2.6), so a `begin` past it is refused with `full`. A file is listed
only once the store said it holds it, and only its uploader can have it listed or take it off:
both name the upload by its key, which starts with the member who asks:

```lean
def handler (config : Config) : Handler Request Answer
  | .list who at_s => do
    return .shelf who ((← onShelf config).filter (·.size.isSome)) at_s
  | .begin who at_s => do
    if config.maxFiles ≤ (← onShelf config).length then return .full
    let id ← nextId
    let _ ← uploads.insert { owner := who, id, size := none }
    return .form who id at_s
  | .seen who file size =>
    match size with
    | some n => do
      if ← uploads.update { owner := who, id := file, size := some (Int64.ofNat n) } then
        return .listed file
      else return .notSeen file
    | none => return .notSeen file
  | .delete who file => do
    if ← uploads.delete [.text who, .int file] then return .deleted file else return .refused file
```

**Why one transaction.** Every request is one atomic step against the database, run at
`SERIALIZABLE`: a delete and a listing never interleave, so no list shows half a delete, even
from two instances at once, and every claim below is about one function.

**Why the time is in the request.** The pages carry links signed for the store, and a signature
names a time. A transaction cannot read a clock, so the server writes the time a request arrived
into it (step 3) and the bridge reads it as `at_s`. The answer carries it back, and the bridge
signs with it. Every link a page carries is then a function of the request.

The front is the counter's, with the shelf's requests and answers. Move the bridge and the pages
from `Shelf/Web.lean`'s counter to the shelf's, so that the test of step 4 can import them, and
keep only `main` in `Main.lean`. The code of this step is `Tests/TutorialWeb/Files.lean`.

## 2. Sign in

The sign-in is Lanes' (`Lanes/Web/IO/SignIn.lean`, `docs/decisions/D72-sign-in-with-oauth.md`).
It runs where a request arrives, in the server's `arrive`, before the request enters the
system. It answers `/sign-in/<provider>` with the redirect to the provider, takes the
provider's callback, exchanges the code, checks the ID token, and lets the callback in with the
identity it verified in its headers. No code, token or client secret reaches the system.

A provider is OpenID Connect or OAuth 2.0 with a user API. For GitHub, import
`Lanes.Services.Oidc.GitHub` and use `GitHub.provider`. Any
OpenID Connect provider (Google, Okta, Keycloak) is read from its discovery document, kept with
the deployment so that nothing is fetched at start. In `Main.lean`:

```lean
def provider (origin : String) : IO (OAuth.Provider × OAuth.Client) := do
  let path ← need "SHELF_OIDC_DISCOVERY"
  let some d := OAuth.Discovery.read (← IO.FS.readFile path)
    | throw (IO.userError s!"shelf: {path} is not a discovery document")
  let id ← need "SHELF_OIDC_CLIENT_ID"
  let secret ← need "SHELF_OIDC_CLIENT_SECRET"
  return (d.provider "oidc",
    { id, secret := ⟨secret⟩, redirect := s!"{origin}/sign-in/oidc/callback" })
```

A member is the identity's issuer and subject, which do not change; the address can. The
callback does not enter the system: the bridge answers it with a session cookie signed with the
site's current key, which expires `session_s` after the request arrived, and a
redirect home:

```lean
def memberOf (who : OAuth.Identity) : Member := OAuth.b64 (who.issuer ++ " " ++ who.subject).toUTF8
```

```lean
    Routes.callback.handle fun _ r => match OAuth.identity? r with
      | some who => .error (home.setCookie
          (cookie s (Auth.sign s.keys "session" (arrived r + s.session_s) (memberOf who))))
      | none => .error notFound,
```

Every later request names its member through that cookie. `prepare` runs before the request
gets its id: it checks the cookie's signature, writes the member into a header of its own, and
drops the cookies, so none enters the system:

```lean
def prepare (s : Settings) (r : Http.Request) : Http.Request :=
  let kept := r.headers.filter fun (name, _) => name != "cookie" && name != memberHeader
  let member := (r.cookie? s.cookieName).bind (Auth.verify s.keys "session" (arrived r))
  { r with headers := kept ++ (member.map (memberHeader, ·)).toList }
```

A form that changes something also carries the member's form token and must come from the
site's origin (`signed` in `Tests/TutorialWeb/Web.lean`).

**What is proved.** Each is a theorem with an axiom gate in `Tests/Axioms/Web.lean`:

- `OAuth.check_ok`: a callback is accepted only with the ticket the server's key tagged and this
  browser's cookie carries, for its state, on its provider's route, before it expires.
- `OAuth.Used.accepted_once`: over any run, no state is accepted twice, so a callback cannot be
  replayed.
- `OAuth.IdToken.verify_accepted`: an ID token is accepted only if its header names RS256 or
  ES256, a key of the provider's set checks its signature, and every claim passes (issuer,
  audience, expiry, nonce).
- `OAuth.identity?_strip` and `OAuth.identity?_withIdentity`: identity headers a client sends are
  dropped, so the system reads back only what the sign-in wrote.
- `Auth.verify_eq_some` and `Auth.checkForm_iff`: a cookie is accepted exactly when it is the
  signature of its payload by a key of the site's, before it expires, and a form token exactly
  when it is the member's.

**What is trusted.** The sign-in's IO, which performs those decisions in order and calls only the
provider it was given (its row in `TRUSTED.md`); the signature check, OpenSSL's
(`native/verify.c`); HMAC-SHA-256, so that nobody without the key makes a cookie; the provider
itself; and the bridge, which is tested in step 4, not proved. A session ends when its cookie's
token expires, `session_s` after the sign-in (`Auth.verify_expired`), or when the site's keys
drop the key that signed it. For sessions the system keeps, which a log-out closes and an idle
lifetime ends, see `Auth.Sessions` (`Lanes/Web/Auth/Login.lean`).

In the test, the provider is the test kit's (`Lanes/Testing/OAuth.lean`): an OpenID Connect
provider on a local port, which signs ID tokens with an RSA key that the `openssl` command makes.
It checks the code, the client, the redirect and the PKCE verifier as a provider does. The code
of this step is `Tests/TutorialWeb/Web.lean` and `Tests/TutorialWeb/Main.lean`.

## 3. Upload to S3, with a size limit

The file never passes through the site. A `begin` answers a page with a form that posts the file
to the bucket under a policy: a JSON document, signed with the site's S3 credentials, that says
what the store may take (`Lanes.S3.Post`). Unlike a presigned `PUT`, a policy bounds the size,
and S3 refuses a file past it (`EntityTooLarge`). The key is exact, so a member cannot write
over another's file:

```lean
def uploadForm (s : Settings) (file : Int64) (at_s : Nat) : Option S3.Post.Form :=
  (S3.Key.of? (s.objectKey file)).map fun key =>
    S3.Post.form s.bucket s.creds (Civil.DateTime.ofUnix at_s)
      { key := .exact key, length := s.length, expiry := s.upload_s }
```

The sizes are a `S3.Post.Length`, whose type keeps the minimum below the maximum and the maximum
within the 5 GiB S3 takes in one `POST`:

```lean
  /-- The sizes of a file the store takes, in bytes. -/
  length : S3.Post.Length := ⟨1, 10 * 1024 * 1024, by decide, by decide⟩
```

**What is proved** (`Lanes/Services/S3/PostSound.lean`). `S3.Post.form_policy`: the policy a form
carries reads back, as S3 reads it, as exactly the conditions written, the size range among
them, and the expiry given. `S3.Post.admitted_bounded`: a file that S3 admits under the policy
of a form has a size within its range and was posted before it expired. What is trusted is that
S3 checks a policy as its documentation says; the test kit's fake S3 checks it the same way,
and `Tests/S3Upload.lean` compares the forms with botocore's.

**A file is listed only once the store holds it.** The browser posts the file to the store with
`fetch`, then posts `/files/<id>/uploaded` to the site (`script` in `Shelf/Web.lean`; templates
refuse inline code, so the bridge serves it). The browser's word is not taken. Where that
request arrives, the server asks the store for the object with a `HEAD`, and writes the size the
store gave into the request, after dropping any such header a client sent:

```lean
def arrive (s : Settings) (signIn : OAuth.SignIn) (r : Http.Request) :
    IO (Except Http.Response Http.Request) := do
  match ← signIn.arrive r with
  | .error answer => return .error answer
  | .ok r =>
    let r := stamp (← nowSeconds) r
    match Routes.uploaded.match? r with
    | some (file, ()) => return .ok (withStored (← head s file) r)
    | none => return .ok r
```

The `seen` request then carries `some size` or `none`, and `handler` lists only the former. This
is the only IO of the app but the database's, and it is trusted to write the size only from the
store's answer; step 4 tests that a forged header is not believed. The same check can be an
output of the system, as the database's calls are, which takes more code.

The pages link each file with a `GET` presigned at the time of the listing, for an hour. A
delete takes the record off the shelf, not the object out of the bucket: deleting it is a call
to the store (`S3.handler`). The code of this step is `Tests/TutorialWeb/Web.lean`.

## 4. Test the whole site

The test kit (`Lanes.Testing`, `docs/decisions/D77-a-test-kit.md`) runs locally, with no
network: a fake S3 that checks every signature and every policy as S3 does, a fake identity
provider, a browser that keeps cookies and posts forms, and the typed store in memory
(`Lanes.Testing.Store`), which runs each transaction on a database held in the test, as
`Txn.run` says. Import it from tests only, so no binary that serves links it. The site runs as
`main` runs it, with the fakes in place of AWS, the provider and PostgreSQL:

```lean
def deployment (store : Testing.S3.Fake) (creds : SigV4.Credentials)
    (provider : Testing.OAuth.Fake) : Deployment :=
  { settings := { keys := .of (.of "the key of the test".toUTF8), origin, bucket := store.bucket, creds
                  providers := ["id"], length := ⟨1, 1024, by decide, by decide⟩ }
    server := { port := 0 }
    signIn := { providers := [(provider.oidc "id", provider.client origin "id")], secure := false
                http := { timeout_ms := 5000 } } }
```

```lean
  let rows ← Testing.Store.empty schema (handler {})
  let call := fun (r : Request) => (do return ← rows.call r : Async (Db.Result Answer))
  let server ← start d call
```

Alice and Bob sign in. Alice begins an upload, posts the file with the form her page carries,
and asks the site to list it. Bob sees it and fetches it through its link:

```lean
  let _ ← Testing.OAuth.signIn a provider "id" alice
  let _ ← Testing.OAuth.signIn b provider "id" bob
  let shelf ← a.get []
  let form ← a.submit shelf ["files"]
  let (url, fields) := uploadOf form
  let posted ← Testing.S3.postForm url fields "twelve bytes".toUTF8
  let listed ← a.submit form ["files", "0", "uploaded"]
  let seenByBob ← b.get []
  let fetched ← Testing.S3.follow (firstLink seenByBob) .get
  let notTheirs ← b.submit seenByBob ["files", "0", "delete"]
```

The test then posts a file over the limit, which the store refuses, and asks for it to be
listed, with and without a forged header, which the site refuses. It stops the server, starts it
again on the same store and finds the shelf as it was; Alice deletes her file. Each check is a
line of `lake test`, such as `tutorial web: another member's delete is refused`. In the app, put
this in `Shelf/EndToEnd.lean` and run `EndToEnd.live` from the `main` of `Check.lean`. The code of
this step is `Tests/TutorialWeb/EndToEnd.lean`.

## 5. Check a property, then prove it

**The property: only its uploader takes a file off the shelf.** Check it first (rule 5.1), beside
the store's model, as the counter's check was. Alice uploads file 0; Bob tries to delete it;
Alice deletes it; Alice begins a second upload, which a shelf of one refuses while the first is
there. Each request is sent once those it waits for are answered, and the checker tries every
order that leaves:

```lean
def requests : List (Nat × Request × List Nat) :=
  [(1, .begin "alice" 0, []), (2, .seen "alice" 0 (some 5), [1]), (3, .delete "bob" 0, [1]),
    (4, .delete "alice" 0, [2]), (5, .begin "alice" 0, [1])]
```

The tables do not remember who deleted a file, but the checker's world does: `w.driver.1.toSend`
is the requests not yet sent. So the property reads: in every database the store may hold, if
file 0 was begun and Alice no longer holds it, Alice's delete has been sent. Each `always` has a
`sometimes` beside it, so a check that never reaches a delete fails (rule 5.3):

```lean
    [ .always "the shelf holds at most one upload" fun w =>
        w.driver.2.worlds.all fun world => (uploadsOf world.db).length ≤ 1,
      .sometimes "the shelf is full" fun w => w.driver.1.answered.any (·.2 == .full),
      .sometimes "a file is listed" fun w =>
        w.driver.2.worlds.any fun world => (uploadsOf world.db).any (·.size.isSome),
      .always "only its uploader deletes a file" fun w =>
        w.driver.2.worlds.all fun world => holds world.db "alice" 0 || !begun world.db
          || !w.driver.1.toSend.contains (4, .delete "alice" 0, [2]),
      .sometimes "a file is deleted" fun w =>
        w.driver.2.worlds.any fun world => begun world.db && !holds world.db "alice" 0 ]
```

```text
PASS (complete): every reachable state explored
reached "the shelf is full" in 13 steps
reached "a file is listed" in 11 steps
reached "a file is deleted" in 17 steps
states: 1877, transitions: 4312, depth: 31
coverage: input 2063, output 1126, deliver 1122, start 1, crash 0 (never fired), drop 0 (never fired), duplicate 0 (never fired), restart 0 (never fired), timeout 0 (never fired)
```

Now seed the bug: a delete that does not ask whose file it is.

```lean
  | .delete _ file => do
    match (← onShelf config).find? (·.id == file) with
    | some u =>
      let _ ← uploads.delete [.text u.owner, .int file]
      return .deleted file
    | none => return .refused file
```

```text
FAIL: "only its uploader deletes a file" is violated after 11 steps
  1. input request 1 (begin "alice" 0)
  2. start ()
  3. deliver outside → (): request 1 (begin "alice" 0)
  4. output call { id := 1, request := begin "alice" 0 }
  5. input store { id := 1, result := committed (form "alice" 0 0) }
  6. deliver outside → (): store { id := 1, result := committed (form "alice" 0 0) }
  7. output answered 1 (form "alice" 0 0)
  8. input request 3 (delete "bob" 0)
  9. deliver outside → (): request 3 (delete "bob" 0)
  10. output call { id := 3, request := delete "bob" 0 }
  11. input store { id := 3, result := committed (deleted 0) }
  state reached:
  () [up] ()
  in flight: outside → (): store { id := 3, result := committed (deleted 0) }
reached "a file is listed" in 11 steps
reached "a file is deleted" in 11 steps
states: 45, transitions: 54, depth: 11
coverage: input 31, deliver 15, output 7, start 1, crash 0 (never fired), drop 0 (never fired), duplicate 0 (never fired), restart 0 (never fired), timeout 0 (never fired)
```

Alice begins file 0 and Bob deletes it, before she has even uploaded it.

**The proof.** The check covered two members and five requests. The theorem covers every
database, every request and every member: a transaction of a request made as `who` leaves every
upload of another member as it was. It rests on one fact of each transaction, that every write
it may ask of `uploads` is under a key that starts with `who` (`writes`), and on a theorem of
Lanes, `Txn.All.others`: a transaction that writes a table only under some keys leaves every
row of another key as it was:

```lean
/-- **Only its uploader takes a file off the shelf.** A transaction of a request made as `who`
leaves every upload of another member on the shelf if it was there, and off it if it was not. -/
theorem only_uploader_deletes (config : Config) (r : Request) {db : Db} {a : Answer} {db' : Db}
    (h : (handler config r).run db = .ok (a, db')) (u : Upload) (other : u.owner ≠ r.who) :
    uploads.toRow u ∈ db'.rows uploads.table.name ↔ uploads.toRow u ∈ db.rows uploads.table.name :=
  Txn.All.others (writes config r) h (by simpa [uploads, Columns.table, Table.keyOf] using other)
```

`writes` takes the request apart and each operation in turn (`TableOf.scan_all`,
`TableOf.insert_all`, `TableOf.delete_all`, …). With the bug, it cannot be proved: the delete
names a key read from the table, which may start with anyone. Gate it as the first tutorial did:

```lean
/-- info: 'Shelf.only_uploader_deletes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Shelf.only_uploader_deletes
```

The member in a request is the one the bridge read from a signed cookie (step 2): that is the
bridge's, tested. The code of this step is `Tests/TutorialWeb/Check.lean`,
`Tests/TutorialWeb/Files.lean` and `Tests/TutorialWeb/Proofs.lean`.

## 6. Run it

The configuration is read once, in `main` (rule 2.5). Nothing secret is in the code or the
repository. The database is named as libpq's variables name it, and at the start `main` runs
the migrations not yet run and checks the tables (`Postgres.Typed.prepare`); `docs/DEPLOY.md`
says how to run it as a container, several at once:

```lean
  let origin := ((← IO.getEnv "LANES_URL").filter (!·.isEmpty)).getD s!"http://localhost:{port}"
  let region := ((← IO.getEnv "AWS_REGION").filter (!·.isEmpty)).getD "us-east-1"
  let bucket : S3.Bucket :=
    { name := ← need "LANES_MEDIA_BUCKET", region, endpoint := S3.Endpoint.aws region }
  let some creds ← S3.credentialsFromEnv
```

The shelf signs its upload forms and links in the bridge, a pure function given its credentials
once at start, so `main` reads a key of a user that may use the media bucket from the
environment, with `SHELF_OIDC_DISCOVERY`, the path of the provider's discovery document, and
`SHELF_OIDC_CLIENT_ID` and `SHELF_OIDC_CLIENT_SECRET`. The bucket allows a form's `POST` and a
presigned `GET` from the site's origin. Register `<LANES_URL>/sign-in/oidc/callback` with the
provider. The session key is made at the first start in `shelf.secrets`, or the path given
after the port; losing it ends every session and nothing else.

## 7. Where next

What this shelf leaves out, and where to see it done:

- Taking the object out of the bucket when its upload is deleted: an effect written in the
  delete's transaction to an outbox, which a worker performs (`Lanes.Db.Jobs`, as
  `examples/payments` charges an order).
- An upload begun and never finished keeps its place on the shelf.
- Uploads larger than one `POST`: `Lanes.S3.Multipart` and `S3.presignPart`.
