import Upload.Web

/-!
Run by `lake test`. The service model-checked against itself as the spec, on pieces in any order
(rule 5.1); then uploads through the whole front end, with no socket (`Http.Loopback`): bodies
far larger than a piece, framed by their length and in chunks, each answered with the size and
the checksum of its bytes, and what must be refused.
-/

open Lanes Upload Upload.Web

instance : sig.Inspect := {}
instance : (system { uploads_max := 1 }).Inspect := {}

def bytes (s : String) : ByteArray := s.toUTF8

def requests : List Request :=
  [.start 1, .piece 2 1 0 (bytes "ab") false, .piece 3 1 1 (bytes "c") true,
    .piece 4 9 0 (bytes "x") true, .start 5]

def check : IO Bool := do
  let report := Check.system (system { uploads_max := 1 })
    { driver := (service { uploads_max := 1 }).monitored (Driver.anyOrder requests) }
    [ Check.refines "every answer is allowed by the spec",
      .always "no more uploads are under way than the bound" fun w =>
        (w.state.state () : State).length ≤ 1,
      .always "an upload is answered with the size and the checksum of its pieces in order" fun w =>
        w.state.outbox.all fun r => match r.answer with
          | .done size sum => r.req == 1 && size == 3 && sum == checksum (bytes "abc")
          | _ => true,
      .sometimes "an upload is answered" fun w =>
        w.state.outbox.any fun r => r.answer matches .done ..,
      .sometimes "a piece out of order is refused" fun w =>
        w.state.outbox.any fun r => r.answer matches .outOfOrder,
      .sometimes "an upload beyond the bound is refused" fun w =>
        w.state.outbox.any fun r => r.answer matches .busy ]
  IO.println report.renderSystem
  return report.ok

def body (n : Nat) : ByteArray :=
  ByteArray.mk ((Array.range n).map fun k => (k * 7 + k / 251).toUInt8)

def chunked (data : ByteArray) (size : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut pos := 0
  while pos < data.size do
    let n := min size (data.size - pos)
    out := out ++ Http.Response.chunk (data.extract pos (pos + n))
    pos := pos + n
  return out ++ bytes "0\r\n\r\n"

def text (written : ByteArray) : String :=
  match Http.Response.read written.size written true with
  | .done (some r) => s!"{r.status} {(String.fromUTF8? r.body).getD ""}"
  | _ => "no response"

def front : List (String × Bool) :=
  let lb := Http.Loopback.start (system {}) bridge (conn := { streams := some uploading, piece_max := 4096 })
  let large := body 300000
  let (lb, byLength) := lb.send { method := .put, path := ["upload"], body := large }
  let head := bytes "POST /upload HTTP/1.1\r\nHost: h\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n"
  let (lb, inChunks) := lb.converse [head, chunked (body 50000) 1000]
  let (lb, empty) := lb.send { method := .put, path := ["upload"] }
  let bad := bytes "POST /upload HTTP/1.1\r\nHost: h\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n3\r\nabcX"
  let (_, refused) := lb.converse [bad]
  let answer := fun (r : Except String Http.Response) => match r with
    | .ok r => s!"{r.status} {(String.fromUTF8? r.body).getD ""}"
    | .error e => e
  [ ("an upload of 300 KB framed by its length, in pieces of 4 KiB, is answered with its size and checksum",
      answer byLength == s!"200 300000 bytes, Adler-32 {checksum large}\n"),
    ("an upload of 50 KB in chunks of 1000 bytes likewise",
      text inChunks == s!"200 50000 bytes, Adler-32 {checksum (body 50000)}\n"),
    ("an upload with no body is answered at once", answer empty == s!"200 0 bytes, Adler-32 1\n"),
    ("a chunk without its CRLF refuses the body with 400", (text refused).startsWith "400") ]

def main : IO UInt32 := do
  let ok ← check
  for (name, passed) in front do
    IO.println s!"{if passed then "ok  " else "FAIL"} {name}"
  return if ok && front.all (·.2) then 0 else 1
