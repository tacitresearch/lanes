/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Testing

/-!
The test kit itself (`Lanes/Testing/`): what its fakes refuse, a form beyond its policy
included, since a fake that lets through what the real service refuses makes a test pass that
should fail; how the browser keeps and sends cookies; and the helpers that read a response.
`Tests/S3.lean`, `Tests/S3Upload.lean` and `Tests/OAuth.lean` run the S3 client, uploads and
the sign-in against the fakes.
-/

namespace Tests.Testing

open Lanes Lanes.Http Lanes.Testing Std Std.Async

def creds : SigV4.Credentials := { accessKeyId := "AKIDEXAMPLE", secretAccessKey := ⟨"secret"⟩ }

def at_ : Civil.DateTime := Civil.DateTime.ofUnix 1700000000

def key (s : String) : S3.Key := (S3.Key.of? s).getD ⟨"k", by decide⟩

def bucket : S3.Bucket :=
  { name := "test", region := "us-east-1",
    endpoint := { host := "127.0.0.1", port := 9000, scheme := .http, addressing := .path } }

/-- A presigned link as the fake reads it off the wire. -/
def linkRaw (url : String) (verb : String := "GET") : S3.Raw :=
  { verb, target := "/" ++ "/".intercalate ((url.splitOn "/").drop 3), headers := [("host", "127.0.0.1:9000")], body := .empty }

def answered (r : S3.Raw) (objects : S3.Objects := [("a", "body".toUTF8, "text/plain")]) : String :=
  (((String.fromUTF8? (S3.serve creds "test" "us-east-1" objects r).1).getD "").splitOn "\r\n").headD ""

def s3Tests : List (String × Bool) :=
  let get := S3.presign bucket creds at_ .get (key "a") ⟨600, by decide⟩
  [ ("kit s3: a presigned link the fake's secret signed is answered",
      answered (linkRaw get) == "HTTP/1.1 200 S3"),
    ("kit s3: a link signed with another secret, or changed, is refused as S3 refuses it",
      answered (linkRaw (S3.presign bucket { creds with secretAccessKey := ⟨"other"⟩ } at_ .get
          (key "a") ⟨600, by decide⟩)) == "HTTP/1.1 403 S3"
        && answered (linkRaw (get.replace "/test/a?" "/test/b?")) == "HTTP/1.1 403 S3"
        && answered (linkRaw get "DELETE") == "HTTP/1.1 403 S3"),
    ("kit s3: a request with no signature is refused",
      answered { verb := "GET", target := "/test/a", headers := [], body := .empty } == "HTTP/1.1 403 S3"),
    ("kit s3: a link for another bucket is not found",
      answered (linkRaw (S3.presign { bucket with name := "other" } creds at_ .get (key "a")
        ⟨600, by decide⟩)) == "HTTP/1.1 404 S3"),
    ("kit s3: ranges as S3 reads them",
      S3.range? "bytes=2-5" 10 == some (2, 6) && S3.range? "bytes=-3" 10 == some (7, 10)
        && S3.range? "bytes=4-" 10 == some (4, 10) && S3.range? "items=1-2" 10 == none) ]

/-- A form posted to the fake's bucket, as the fake reads it off the wire. -/
def formRaw (fields : List (String × String)) (file : ByteArray) : S3.Raw :=
  let boundary := "kit-boundary"
  let body := S3.formBody boundary fields "clip.mp4" file
  { verb := "POST", target := "/test", body
    headers := [("host", "127.0.0.1:9000"), ("content-length", toString body.size),
      ("content-type", s!"multipart/form-data; boundary={boundary}")] }

/-- The status line and the error code the fake answers a form at `now_s`, and what it then holds. -/
def posted (r : S3.Raw) (now_s : Int := at_.toUnix + 1) : String × String × S3.Objects :=
  let (reply, st) := S3.serveAll creds "test" "us-east-1" now_s {} r
  let text := (String.fromUTF8? reply).getD ""
  let code := (((text.splitOn "<Code>")[1]?).map (·.splitOn "</Code>" |>.headD "")).getD ""
  ((text.splitOn "\r\n").headD "", code, st.objects)

def formTests : List (String × Bool) :=
  let policy : S3.Post.Policy := { key := .exact (key "up/a"), length := ⟨2, 10, by decide, by decide⟩
                                   contentType := some "video/mp4", expiry := ⟨600, by decide⟩ }
  let form := S3.Post.form bucket creds at_ policy
  let set (name value : String) := form.fields.map fun (n, v) => if n == name then (n, value) else (n, v)
  let clip := "a clip".toUTF8
  let (stored, _, held) := posted (formRaw form.fields clip)
  [ ("kit s3: a form under its policy, its file in range, is stored with its type",
      stored == "HTTP/1.1 204 S3" && held.lookup "up/a" == some (clip, "video/mp4")),
    ("kit s3: a file larger or smaller than the policy's range is refused as S3 refuses it",
      (posted (formRaw form.fields (ByteArray.mk (Array.replicate 11 0)))).1 == "HTTP/1.1 400 S3"
        && (posted (formRaw form.fields (ByteArray.mk (Array.replicate 11 0)))).2.1 == "EntityTooLarge"
        && (posted (formRaw form.fields "a".toUTF8)).2.1 == "EntityTooSmall"),
    ("kit s3: a form signed with another secret, or its policy changed, is refused",
      let other := S3.Post.form bucket { creds with secretAccessKey := ⟨"other"⟩ } at_ policy
      let wider := S3.Post.document bucket creds at_ { policy with length := ⟨2, 100, by decide, by decide⟩ }
      (posted (formRaw other.fields clip)).2.1 == "SignatureDoesNotMatch"
        && (posted (formRaw (set "policy" wider.encode) clip)).2.1 == "SignatureDoesNotMatch"),
    ("kit s3: another key, another type, a field the policy does not name, and expired, refused",
      (posted (formRaw (set "key" "up/b") clip)).2.1 == "AccessDenied"
        && (posted (formRaw (set "Content-Type" "text/html") clip)).2.1 == "AccessDenied"
        && (posted (formRaw (("acl", "public-read") :: form.fields) clip)).2.1 == "AccessDenied"
        && (posted (formRaw form.fields clip) (at_.toUnix + 600)).2.1 == "AccessDenied") ]

def browserTests : List (String × Bool) :=
  [ ("kit browser: a set-cookie keeps its name, value and path, and Max-Age=0 clears",
      Kept.parse "s=abc; Path=/sign-in; Max-Age=600; HttpOnly" == some ({ name := "s", value := "abc", path := "/sign-in" }, false)
        && Kept.parse "s=; Path=/; Max-Age=0" == some ({ name := "s", value := "", path := "/" }, true)
        && Kept.parse "no value" == none
        && Kept.parse "__Host-lanes-sign-in=t.v; Path=/; Max-Age=600; HttpOnly; Secure; SameSite=Lax"
          == some ({ name := "__Host-lanes-sign-in", value := "t.v", path := "/" }, false)),
    ("kit browser: a cookie goes where its path covers the request",
      let c : Kept := { name := "s", value := "v", path := "/sign-in" }
      c.covers ["sign-in", "id", "callback"] && c.covers ["sign-in"] && !c.covers ["sign-inx"]
        && !c.covers [] && ({ c with path := "/" } : Kept).covers []) ]

def page : Option Response :=
  some { (Response.ofText "text/html"
    "<form><input name=\"csrf\" value=\"a&amp;b\"/></form><p>&lt;x&gt; &quot;y&quot;</p>")
    with headers := [("set-cookie", "s=1; Path=/"), ("set-cookie", "t=2; Path=/"), ("location", "/v/3")] }

def httpTests : List (String × Bool) :=
  [ ("kit http: a page's hidden field, unescaped", field page "csrf" == some "a&b"),
    ("kit http: the text between two markers, unescaped",
      between page "<p>" "</p>" == some "<x> \"y\"" && between page "<q>" "</q>" == none),
    ("kit http: a cookie a response sets, by name", setCookie page "t" == some "2"
      && setCookie page "u" == none),
    ("kit http: the status, the location and the text, and none without a response",
      status page == 200 && location page == "/v/3" && shows page "&lt;x&gt;"
        && status none == 0 && text none == ""),
    ("kit http: a URL's query, decoded, and a path's segments",
      queryOf "https://a.example/p?x=1&y=a%20b" == [("x", "1"), ("y", "a b")] && segments "/v/3/" == ["v", "3"]) ]

def providerTests : List (String × Bool) :=
  let u : OAuth.User := { subject := "7", login := "octo", name := some "Mona \"the\" Cat" }
  let parse (s : String) := (Json.parse s).toOption.getD .null
  [ ("kit provider: the user API's answers read back as the identity of the user",
      (OAuth.readUser "https://hub.example" [parse (OAuth.userJson u), parse (OAuth.emailsJson u)]).toOption
        == some { issuer := "https://hub.example", subject := "7", email := some "7@example.com",
                  emailVerified := true, name := Lanes.OAuth.DisplayName.of? "Mona \"the\" Cat" }),
    ("kit provider: a subject that is not a number is a string, and no address no email",
      (OAuth.readUser "i" [parse (OAuth.userJson { subject := "x\"y", email := none }),
        parse (OAuth.emailsJson { subject := "x\"y", email := none })]).toOption.any
        fun id => id.subject == "x\"y" && id.email.isNone && id.name.map (·.val) == some "x\"y") ]

def tests : List (String × Bool) := s3Tests ++ formTests ++ browserTests ++ httpTests ++ providerTests

/-- The browser against a site of `listen` that sets a cookie, clears it, and has a form. -/
def live : Async (List (String × Bool)) := do
  let (server, port) ← listen fun r => do
    let cookie := (r.header? "cookie").getD "none"
    let origin := (r.header? "origin").getD "none"
    let answer := Response.text s!"{r.method == .post} {cookie} {origin} {(String.fromUTF8? r.body).getD ""}"
    match r.path with
    | ["set"] => return { answer with headers := answer.headers ++ [("set-cookie", "s=1; Path=/")] }
    | ["clear"] => return { answer with headers := answer.headers ++ [("set-cookie", "s=; Path=/; Max-Age=0")] }
    | ["form"] => return json "<input name=\"csrf\" value=\"t&amp;1\">"
    | _ => return answer
  let b ← Browser.new port "http://site.test"
  let first ← b.get ["show"]
  let _ ← b.get ["set"]
  let kept ← b.post ["show"] [("a", "b c")]
  let _ ← b.get ["clear"]
  let cleared ← b.get ["show"]
  let _ ← b.get ["set"]
  b.forget "s"
  let forgotten ← (b.at port).get ["show"]
  let form ← b.get ["form"]
  let submitted ← b.submit form ["show"] [("x", "y")]
  server.close
  return [
    ("kit browser: a cookie the site set is sent back, a form from its origin, then cleared",
      text first == "false none none "
        && text kept == "true s=1 http://site.test a=b%20c"
        && text cleared == "false none none "),
    ("kit browser: a cookie forgotten is not sent, and a form goes with the token its page carries",
      text forgotten == "false none none "
        && text submitted == "true none http://site.test csrf=t%261&x=y") ]

end Tests.Testing
