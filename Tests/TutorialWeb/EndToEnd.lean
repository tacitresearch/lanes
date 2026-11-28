/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Testing
import Tests.TutorialWeb.Web
import Lanes.Services.S3.Testing

/-!
Step 4 of `docs/TUTORIAL-WEB.md`: the shelf over HTTP, against the test kit's fake identity
provider and fake S3, driven by its browser, then started again.
-/

namespace Shelf.EndToEnd

open Lanes Lanes.Http Lanes.Testing Std.Async

def origin : String := "http://shelf.test"

def alice : Testing.OAuth.User := { subject := "alice" }
def bob : Testing.OAuth.User := { subject := "bob" }

/-- Where a page's upload form posts, and its hidden fields, in order. -/
def uploadOf (page : Option Http.Response) : String × List (String × String) := Id.run do
  let some form := between page "<form id=\"upload\"" "</form>" | return ("", [])
  let url := ((form.splitOn "action=\"")[1]?.bind (·.splitOn "\"" |>.head?)).getD ""
  let fields := (form.splitOn "<input type=\"hidden\" name=\"").drop 1 |>.filterMap fun rest =>
    match rest.splitOn "\" value=\"" with
    | name :: value :: _ => some (name, (value.splitOn "\"").headD "")
    | _ => none
  return (url, fields)

/-- The link of the first file on a page of the shelf. -/
def firstLink (page : Option Http.Response) : String :=
  (between page "<li><a href=\"" "\"").getD ""

def deployment (store : Testing.S3.Fake) (creds : SigV4.Credentials)
    (provider : Testing.OAuth.Fake) : Deployment :=
  { settings := { keys := .of (.of "the key of the test".toUTF8), origin, bucket := store.bucket, creds
                  providers := ["id"], length := ⟨1, 1024, by decide, by decide⟩ }
    server := { port := 0 }
    signIn := { providers := [(provider.oidc "id", provider.client origin "id")], secure := false
                http := { timeout_ms := 5000 } } }

def flow (store : Testing.S3.Fake) (creds : SigV4.Credentials) (provider : Testing.OAuth.Fake) :
    Async (List (String × Bool)) := do
  let d := deployment store creds provider
  let server ← start d
  let a ← Browser.new (server.port.getD 0) origin
  let b ← Browser.new (server.port.getD 0) origin
  let signedOut ← a.get []
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
  let big ← a.submit shelf ["files"]
  let (bigUrl, bigFields) := uploadOf big
  let tooLarge ← Testing.S3.postForm bigUrl bigFields (ByteArray.mk (Array.replicate 2048 0))
  let bigChecked ← a.submit big ["files", "1", "uploaded"]
  let forged ← a.post ["files", "1", "uploaded"] [("csrf", (field big "csrf").getD "")]
    (headers := [(storedHeader, "2048")])
  let deleted ← a.submit (← a.get []) ["files", "0", "delete"]
  let gone ← a.get []
  server.stop
  let again ← start d
  let a := a.at (again.port.getD 0)
  let afterRestart ← a.get []
  again.stop
  return [
    ("tutorial web: signed out, the shelf offers the sign-in", shows signedOut "Sign in with id"),
    ("tutorial web: a member signed in sees the shelf", shows shelf "Upload a file"),
    ("tutorial web: the store takes the file the form posts", status posted == 204),
    ("tutorial web: the store held it, so it is listed", status listed == 303),
    ("tutorial web: another member sees it, and the link gets its bytes",
      shows seenByBob "File 0" && shows seenByBob "12 bytes"
        && (fetched.map (·.body) == some "twelve bytes".toUTF8)),
    ("tutorial web: another member's delete is refused", status notTheirs == 403),
    ("tutorial web: the store refuses a file over the policy's size",
      Testing.S3.code tooLarge == "EntityTooLarge"),
    ("tutorial web: a file the store does not hold is not listed, whatever the browser says",
      status bigChecked == 409 && status forged == 409),
    ("tutorial web: its uploader deletes it", status deleted == 303 && !shows gone "File 0"),
    ("tutorial web: the shelf lives as long as its process: a restart starts it empty",
      shows afterRestart "Upload a file" && !shows afterRestart "File 1") ]

def live : Async (List (String × Bool)) := do
  unless ← Testing.OAuth.hasOpenssl do
    IO.println "tutorial web: skipped the flow end to end, there is no openssl command"
    return []
  let creds : SigV4.Credentials := { accessKeyId := "AKIDTUTORIAL", secretAccessKey := ⟨"secret"⟩ }
  let store ← Testing.S3.Fake.start creds
  let provider ← Testing.OAuth.Fake.start
  let results ← try flow store creds provider
    finally
      store.stop
      provider.stop
  return results

end Shelf.EndToEnd
