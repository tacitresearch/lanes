/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Gate

/-!
`multipart/form-data` (`Lanes/Web/Http/Multipart.lean`): a body as Chrome sends one, read; parts
written and read back; the limits; a request's form and file, and a form posted through a front
end with no socket.
-/

namespace Tests.FormData

open Lanes Lanes.Http Lanes.Multipart

/-- A form with a text field and a file as Chrome 131 posts it, with a preamble Chrome does not
send and blanks after a delimiter. -/
def chrome : ByteArray :=
  "ignored preamble\r\n".toUTF8
  ++ "------WebKitFormBoundaryx7Gq2gNTjDo4Ah0S\r\n".toUTF8
  ++ "Content-Disposition: form-data; name=\"title\"\r\n\r\nHello, world\r\n".toUTF8
  ++ "------WebKitFormBoundaryx7Gq2gNTjDo4Ah0S  \r\n".toUTF8
  ++ "Content-Disposition: form-data; name=\"photo\"; filename=\"café.png\"\r\n".toUTF8
  ++ "Content-Type: image/png\r\n\r\n".toUTF8
  ++ ⟨#[0x89, 0x50, 0x4e, 0x47, 13, 10, 0x1a, 10, 0, 45, 45]⟩
  ++ "\r\n------WebKitFormBoundaryx7Gq2gNTjDo4Ah0S--\r\nepilogue".toUTF8

def chromeBoundary : String := "----WebKitFormBoundaryx7Gq2gNTjDo4Ah0S"

/-- Parts whose bytes hold line breaks, dashes and most of the delimiter, but not all of it. -/
def sample : List Part :=
  [ Part.field "name" "Ada Lovelace",
    Part.field "note" "a\r\n--B\r\n--Boun, never the whole delimiter\r\n",
    Part.file "upload" "notes \"draft\".txt" "text/plain" "line\r\n\r\nline\r\n-".toUTF8,
    {},
    { headers := [("x-empty", "")], body := ⟨#[13, 10, 13, 10]⟩ } ]

def roundTrips (limits : Limits) (b : String) (ps : List Part) : Bool :=
  match parse limits b (write b ps) with
  | .ok qs => qs == ps
  | .error _ => false

def refused (r : Except Error (List Part)) (e : Error) : Bool :=
  match r with
  | .error e' => e' == e
  | .ok _ => false

def request (b : String) (parts : List Part) : Request :=
  { method := .post, path := ["upload"], body := write b parts
    headers := [("content-type", s!"multipart/form-data; boundary=\"{b}\"")] }

/-- Answers a form with its text fields and the name, type and size of its file, before the
system sees it. -/
def formBridge : Bridge Tests.Gate.echoSig where
  decode _ r :=
    let file := (r.file? "upload").map fun p =>
      s!"{p.filename?.getD "?"} {p.contentType?.getD "?"} {p.body.size}"
    .error (.text s!"{r.form} {file}")
  encode id := some (id, .text "ok")

def tests : List (String × Bool) :=
  let chromeParts := parse {} chromeBoundary chrome
  let lb := Loopback.start (Server.system Tests.Gate.echo) formBridge
  let (lb, posted) := lb.postParts ["upload"]
    [Part.field "title" "Hi", Part.file "upload" "a.bin" "application/octet-stream" ⟨#[0, 1, 2]⟩]
  let (_, plain) := lb.post ["upload"] [("title", "plain & simple")]
  [ ("form-data: a form as Chrome posts it, with a preamble, padding and an epilogue",
      match chromeParts with
      | .ok ps =>
        fields ps == [("title", "Hello, world")]
          && ((file? ps "photo").map fun p => (p.filename?, p.contentType?, p.body.size))
            == some (some "café.png", some "image/png", 11)
      | .error _ => false),
    ("form-data: header names are kept in lowercase",
      match chromeParts with
      | .ok (p :: _) => p.headers.map (·.1) == ["content-disposition"]
      | _ => false),
    ("form-data: the sample is valid and clear of its boundary, and reads back",
      sample.all Part.valid && sample.all (clear "Bound")
        && roundTrips {} "Bound" sample && roundTrips {} "x" []),
    ("form-data: a part holding the delimiter is not clear, and does not read back",
      let bad := [Part.field "a" "x\r\n--Bound--\r\n"]
      !bad.all (clear "Bound") && !roundTrips {} "Bound" bad),
    ("form-data: a body over bytes_max is refused",
      refused (parse { bytes_max := 10 } "Bound" (write "Bound" sample)) .tooLarge),
    ("form-data: more parts than parts_max are refused, as many are read",
      refused (parse { parts_max := 4 } "Bound" (write "Bound" sample)) .tooManyParts
        && roundTrips { parts_max := 5 } "Bound" sample),
    ("form-data: more header lines than headers_max are refused",
      refused (parse { headers_max := 1 } "Bound" (write "Bound" sample)) .tooManyHeaders
        && roundTrips { headers_max := 2 } "Bound" sample),
    ("form-data: refused: no delimiter, no last delimiter, no line break after a delimiter",
      refused (parse {} "B" "nothing here".toUTF8) .malformed
        && refused (parse {} "B" "--B\r\n\r\nx\r\n".toUTF8) .malformed
        && refused (parse {} "B" "--Bx\r\n\r\nx\r\n--B--".toUTF8) .malformed),
    ("form-data: a part with no header and no body, as RFC 2046's grammar allows",
      match parse {} "B" "--B\r\n\r\n--B--\r\n".toUTF8 with
      | .ok [p] => p == {}
      | _ => false),
    ("form-data: a header line with no colon, or a name that is no token, is refused",
      refused (parse {} "B" "--B\r\nno colon\r\n\r\nx\r\n--B--".toUTF8) .malformed
        && refused (parse {} "B" "--B\r\nbad name: v\r\n\r\nx\r\n--B--".toUTF8) .malformed),
    ("form-data: names and file names read back, quoted when they must be",
      (Part.field "my field" "v").name? == some "my field"
        && (Part.file "f" "a\\b\".txt" "text/plain" .empty).filename? == some "a\\b\".txt"),
    ("form-data: a request's form is its text fields, and its file is there by name",
      let r := request "Bound" sample
      r.form == [("name", "Ada Lovelace"), ("note", "a\r\n--B\r\n--Boun, never the whole delimiter\r\n")]
        && ((r.file? "upload").map (·.filename?)) == some (some "notes \"draft\".txt")
        && (r.file? "name").isNone),
    ("form-data: a form that is not multipart is still read as urlencoded",
      ({ method := .post, path := [], body := "a=1&b=2".toUTF8 } : Request).form
        == [("a", "1"), ("b", "2")]),
    ("form-data: a form with a file posted through the front end",
      match posted with
      | .ok r => r.body == "[(title, Hi)] (some (a.bin application/octet-stream 3))".toUTF8
      | .error _ => false),
    ("form-data: an urlencoded form posted through the front end",
      match plain with
      | .ok r => r.body == "[(title, plain & simple)] none".toUTF8
      | .error _ => false) ]

end Tests.FormData
