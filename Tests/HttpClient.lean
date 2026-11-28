/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Gate

/-!
The HTTP client adapter: the wire format as pure functions, a caller model-checked against what
a called service may do, and the same caller run against a real server, a closed port, and
servers that never answer, keep the connection or send too much.
-/

namespace Tests.HttpClient

open Lanes Lanes.Http Std Std.Async

def bytes (s : String) : ByteArray := s.toUTF8

def body? (response : Option Response) : Option String :=
  response.bind fun r => String.fromUTF8? r.body

def get (headers : List (String × String)) : Request := { method := .get, path := [], headers }

def own : List String :=
  ["GET / HTTP/1.1", "Host: 10.0.0.1", "Connection: close", "Content-Length: 0"]

def headLines (r : Request) (host : String := "10.0.0.1") : Option (List String) := do
  let text ← String.fromUTF8? (← r.wire host)
  return ((text.splitOn "\r\n\r\n").headD "").splitOn "\r\n"

def calm (c : Char) : Bool := c == '\t' || (c.val ≥ 32 && c.val != 127)

/-- What a server must find in whatever is written: one of each header that frames the message
and no `Transfer-Encoding`, however leniently it reads a name; no control character but tab in
any line, and a request line of three parts; the body right after the first blank line. A
request is refused only for its host. -/
def framed (r : Request) (host : String) : Bool :=
  match r.wire host with
  | none => host.isEmpty || !host.toList.all fun c => 33 ≤ c.val && c.val ≤ 126
  | some wire =>
    match headEnd wire with
    | none => false
    | some bodyStart =>
      let lines := ((String.fromUTF8? (wire.extract 0 (bodyStart - 4))).getD "\n").splitOn "\r\n"
      let names := (lines.drop 1).map fun line =>
        ((line.splitOn ":").headD "").trimAscii.toString.toLower
      wire.extract bodyStart wire.size == r.body && lines.all (·.toList.all calm)
        && ((lines.headD "").splitOn " ").length == 3 && !(lines.headD "").toList.contains '\t'
        && names.count "content-length" == 1 && names.count "host" == 1
        && names.count "connection" == 1 && !names.contains "transfer-encoding"
        && !names.contains ""

def hostileNames : List String :=
  ["X-Ok", "Content-Length", "content-length ", " content-length", "Content-Length\t",
    "Transfer-Encoding", "transfer-encoding ", "TRANSFER-ENCODING", "\tTransfer-Encoding", "Host",
    "Host ", "Connection", "", " ", "a b", "a:b", "X\r\nContent-Length", "X\nTransfer-Encoding",
    "X\r", "X\x00", "é"]

def hostileValues : List String :=
  ["1", "chunked", "", "a\r\nContent-Length: 5", "a\nTransfer-Encoding: chunked", "a\rb", "a\x00",
    "a\tb", " padded ", "é", "\r\n\r\nGET / HTTP/1.1"]

def hostileRequests : List (Request × String) :=
  ["10.0.0.1", "h\r\nTransfer-Encoding: chunked", "h h", "h\x00", ""].flatMap fun host =>
    hostileNames.flatMap fun name =>
      (hostileValues.flatMap fun value =>
        ["", "hi", "\r\n\r\n"].map fun body =>
          ({ method := .post, path := ["a\r\nb c"], query := [(value, name)]
             headers := [(name, value)], body := bytes body }, host))
      ++ hostileNames.map fun other =>
        ({ method := .get, path := [], headers := [(name, "1"), (other, "chunked")] }, host)

def chunkedHead : String := "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n"

def parse (text : String) : Option Response := Response.parse (bytes text)

def refused (text : String) : Bool := (parse text).isNone

def lengthResponse : String := "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello"

def chunkedResponse : String := chunkedHead ++ "3\r\nhel\r\n2;x=y\r\nlo\r\n0\r\n\r\n"

def trailerResponse : String := chunkedHead ++ "5\r\nhello\r\n0\r\nX-Sum: 1\r\nX-More: 2\r\n\r\n"

/-- The response is whole exactly when its last byte has arrived, with the connection still
open; before that more is awaited, and a connection that ends before that is refused. -/
def wholeAtLastByte (text : String) : Bool :=
  let all := bytes text
  let whole := fun (reading : Reading Response) =>
    match reading with
    | .done (some r) => r.status == 200 && String.fromUTF8? r.body == some "hello"
    | _ => false
  (List.range all.size).all (fun n =>
      Response.read 4096 (all.extract 0 n) false == .more
        && Response.read 4096 (all.extract 0 n) true == .done none)
    && whole (Response.read 4096 all false) && whole (Response.read 4096 all true)
    && whole (Response.read 4096 (all ++ bytes "HTTP/1.1 500 Extra\r\n\r\n") false)

def manyChunks (count : Nat) : ByteArray :=
  (List.range count).foldl (init := bytes chunkedHead) (fun wire n =>
    wire.push 49 |>.push 13 |>.push 10 |>.push (97 + n % 26).toUInt8 |>.push 13 |>.push 10)
    ++ bytes "0\r\n\r\n"

def manyChunksBody (count : Nat) : ByteArray :=
  ⟨(Array.range count).map fun n => (97 + n % 26).toUInt8⟩

/-- info: 'Lanes.Http.Request.fields_framing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Request.fields_framing

/-- info: 'Lanes.Http.Request.head_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Request.head_plain

/-- info: 'Lanes.Http.Response.read_ended' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Response.read_ended

def requestTests : List (String × Bool) :=
  [ ("http wire: a request is written with its path and query escaped and no smuggled header",
      (({ method := .post, path := ["a b", "c"], query := [("q", "x&y")]
          headers := [("X-Test", "1"), ("Evil", "a\r\nInjected: 1")], body := bytes "hi" } :
        Request).wire "10.0.0.1")
        == some (bytes ("POST /a%20b/c?q=x%26y HTTP/1.1\r\nHost: 10.0.0.1\r\nConnection: close\r\n"
          ++ "Content-Length: 2\r\nX-Test: 1\r\n\r\nhi"))),
    ("http wire: the caller's framing headers are dropped in favour of the writer's own",
      headLines (get [("Transfer-Encoding", "chunked"), ("transfer-encoding", "gzip"),
        ("Content-Length", "99"), ("HOST", "evil"), ("connection", "keep-alive"), ("X-Kept", "1")])
        == some (own ++ ["X-Kept: 1"])),
    ("http wire: a header whose name is not a token is not written",
      headLines (get [("Content-Length ", "9"), ("content-length\t", "9"), ("Host ", "evil"),
        ("", "empty"), ("X Y", "space"), ("X:Y", "colon"), ("X\r\nY", "break"), ("X\x00", "nul"),
        ("X-Kept", "1")])
        == some (own ++ ["X-Kept: 1"])),
    ("http wire: a header whose value has a control character other than tab is not written",
      headLines (get [("A", "a\rb"), ("B", "a\nb"), ("C", "a\x00b"), ("D", "a\x7fb"),
        ("E", "a\tb")])
        == some (own ++ ["E: a\tb"])),
    ("http wire: a host with a control character or a space is refused",
      ["10.0.0.1\r\nX-Injected: 1", "10.0.0.1 x", "10.0.0.1\x00", "10.0.0.1\t", "a\nb", "a\rb",
        ""].all fun host => ((get []).wire host).isNone),
    ("http wire: a control character or a space in the path or the query is written escaped",
      headLines { method := .get, path := ["a b\r\nX: 1", "\x00"], query := [("k\r\n", "v \t")] }
        == some ("GET /a%20b%0D%0AX%3A%201/%00?k%0D%0A=v%20%09 HTTP/1.1" :: own.drop 1)),
    ("http wire: whatever the headers, host and body, what is written is framed once",
      hostileRequests.all fun (r, host) => framed r host) ]

def responseTests : List (String × Bool) :=
  [ ("http wire: a response with a length is read to that length",
      let r := parse "HTTP/1.1 201 Created\r\nContent-Length: 2\r\nX-A: b\r\n\r\nokEXTRA"
      r.map (·.status) == some 201 && body? r == some "ok"
        && (r.bind (·.headers.lookup "x-a")) == some "b"),
    ("http wire: a chunked response is put together",
      body? (parse (chunkedHead ++ "4\r\nWiki\r\n5;ext=1\r\npedia\r\n0\r\n\r\n"))
        == some "Wikipedia"),
    ("http wire: without a length the body runs to the end",
      body? (parse "HTTP/1.0 200 OK\r\n\r\nall of it") == some "all of it"),
    ("http wire: a cut body, a cut chunk, a cut head, what is not HTTP or not UTF-8 are refused",
      [ "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\nshort",
        chunkedHead ++ "4\r\nWi",
        "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n",
        "SSH-2.0-OpenSSH\r\n\r\n", "" ].all refused
        && (Response.parse
          (bytes "HTTP/1.1 200 OK\r\nX-A: " ++ ⟨#[0xff]⟩ ++ bytes "\r\n\r\n")).isNone),
    ("http wire: two lengths that differ are refused; two that agree are one",
      refused "HTTP/1.1 200 OK\r\nContent-Length: 2\r\nContent-Length: 3\r\n\r\nabc"
        && refused "HTTP/1.1 200 OK\r\nContent-Length: 2\r\nContent-Length: x\r\n\r\nabc"
        && body? (parse "HTTP/1.1 200 OK\r\nContent-Length: 2\r\ncontent-length: 2\r\n\r\nabc")
          == some "ab"),
    ("http wire: a length that is not all digits is refused",
      ["abc", "-1", "1_0", "+1", "0x10", "1 0", "1,1", "", "١", "10000000000000000000"].all
        fun length => refused s!"HTTP/1.1 200 OK\r\nContent-Length: {length}\r\n\r\n0123456789"),
    ("http wire: a status that is not three digits is refused",
      ["20", "2000", "2x0", "200OK", "-20", "2_0", "", "099", "٢٠٠"].all fun code =>
        refused s!"HTTP/1.1 {code} OK\r\nContent-Length: 0\r\n\r\n"),
    ("http wire: a version other than HTTP/1.0 and HTTP/1.1 is refused",
      ["HTTP/1.2", "HTTP/1.", "HTTP/1.10", "HTTP/2", "HTTP/0.9", "http/1.1", "HTTP/1.1x", ""].all
          (fun version => refused s!"{version} 200 OK\r\nContent-Length: 0\r\n\r\n")
        && ["HTTP/1.0", "HTTP/1.1"].all fun version =>
          (parse s!"{version} 200 OK\r\nContent-Length: 0\r\n\r\n").map (·.status) == some 200),
    ("http wire: a transfer coding other than chunked alone is refused",
      ["gzip", "gzip, chunked", "chunked, gzip", "identity", "chunkedx", "chunked;q=1", ""].all
          (fun coding =>
            refused s!"HTTP/1.1 200 OK\r\nTransfer-Encoding: {coding}\r\n\r\n2\r\nok\r\n0\r\n\r\n")
        && refused ("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nTransfer-Encoding: chunked"
          ++ "\r\n\r\n2\r\nok\r\n0\r\n\r\n")
        && refused ("HTTP/1.1 200 OK\r\nContent-Length: 2\r\nTransfer-Encoding: chunked"
          ++ "\r\n\r\n2\r\nok\r\n0\r\n\r\n")
        && body? (parse
            "HTTP/1.1 200 OK\r\ntransfer-encoding: \t CHUNKED \r\n\r\n2\r\nok\r\n0\r\n\r\n")
          == some "ok"),
    ("http wire: chunk data not followed by CRLF is refused",
      ["2\r\nokXX0\r\n\r\n", "2\r\nok0\r\n\r\n", "2\r\nok\n0\r\n\r\n", "2\r\nok\r0\r\n\r\n",
        "2\r\nok\r\r\n0\r\n\r\n", "1\r\nok\r\n0\r\n\r\n", "3\r\nok\r\n0\r\n\r\n"].all fun body =>
          refused (chunkedHead ++ body)),
    ("http wire: a last chunk without the final CRLF is refused; trailers are skipped",
      ["0\r\n", "0\r\n\r", "0", "0\r", "2\r\nok\r\n", "2\r\nok\r\n0\r\nX-Sum: 1\r\n"].all
          (fun body => refused (chunkedHead ++ body))
        && body? (parse (chunkedHead ++ "2\r\nok\r\n0\r\nX-Sum: 1\r\n\r\n")) == some "ok"
        && body? (parse (chunkedHead ++ "0\r\n\r\n")) == some ""),
    ("http wire: a chunk size that is not one to sixteen hex digits is refused",
      ["", "g", "0x2", "-2", " 2", "2 2", "2\n", "00000000000000002", "2;\x00", "2x",
          "2;" ++ String.ofList (List.replicate 300 'e')].all
          (fun size => refused (chunkedHead ++ size ++ "\r\nok\r\n0\r\n\r\n"))
        && ["2", "0000000000000002", "2 \t", "2;a=b", "2 ; a=\"b c\""].all fun size =>
          body? (parse (chunkedHead ++ size ++ "\r\nok\r\n0\r\n\r\n")) == some "ok"),
    ("http wire: a header name with whitespace before the colon, or no colon, is refused",
      ["Content-Length : 2", "Content-Length\t: 2", "X-A : b", "X-A", ": b", "X A: b"].all
        fun line => refused s!"HTTP/1.1 200 OK\r\n{line}\r\nContent-Length: 2\r\n\r\nok"),
    ("http wire: a header line that starts with a space or a tab is refused",
      [" X-A: b", "\tX-A: b", "X-A: b\r\n c", "X-A: b\r\n\tc"].all fun lines =>
        refused s!"HTTP/1.1 200 OK\r\n{lines}\r\nContent-Length: 2\r\n\r\nok"),
    ("http wire: a control character in a header's value is refused",
      ["X-A: a\rb", "X-A: a\nb", "X-A: a\x00b", "X-A: b\r"].all fun line =>
        refused s!"HTTP/1.1 200 OK\r\n{line}\r\nContent-Length: 2\r\n\r\nok"),
    ("http wire: an interim 1xx response is skipped and the one after it is read",
      let r := parse ("HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 103 Early Hints\r\nLink: </a>\r\n\r\n"
        ++ "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok")
      r.map (·.status) == some 200 && body? r == some "ok" && r.map (·.headers.length) == some 1
        && refused "HTTP/1.1 100 Continue\r\n\r\n"
        && refused "HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 2 OK\r\n\r\n"),
    ("http wire: a 204 and a 304 have no body, whatever their headers say",
      [204, 304].all fun status =>
        let r := parse s!"HTTP/1.1 {status} X\r\nContent-Length: 9\r\n\r\n"
        r.map (·.status) == some status && body? r == some ""),
    ("http wire: three hundred chunks are put together in order",
      (Response.parse (manyChunks 300)).map (·.body) == some (manyChunksBody 300)) ]

def readingTests : List (String × Bool) :=
  [ ("http wire: a response with a length is whole at its last byte and not before",
      wholeAtLastByte lengthResponse),
    ("http wire: a chunked response is whole at its last byte and not before",
      wholeAtLastByte chunkedResponse && wholeAtLastByte trailerResponse),
    ("http wire: a response after an interim one is whole at its last byte and not before",
      wholeAtLastByte ("HTTP/1.1 100 Continue\r\n\r\n" ++ lengthResponse)),
    ("http wire: a body without a length is whole only when the connection ends",
      let wire := bytes "HTTP/1.1 200 OK\r\n\r\nall of it"
      Response.read 4096 wire false == .more
        && (match Response.read 4096 wire true with
          | .done r => body? r == some "all of it"
          | .more => false)),
    ("http wire: a 304 is whole at the end of its head",
      Response.read 4096 (bytes "HTTP/1.1 304 X\r\nContent-Length: 9\r\n\r\n") false
        == .done (some { status := 304, headers := [("content-length", "9")] })),
    ("http wire: what cannot become a response is refused without waiting for more",
      ["HTTP/1.1 200 OK\r\nContent-Length: x\r\n\r\n", "SSH-2.0-OpenSSH\r\n\r\n",
        chunkedHead ++ "2\r\nokX", chunkedHead ++ "z"].all fun text =>
          Response.read 4096 (bytes text) false == .done none),
    ("http wire: bytes past the limit are refused, whole response or not",
      let wire := bytes lengthResponse
      Response.read (wire.size - 1) wire false == .done none
        && Response.read (wire.size - 1) wire true == .done none
        && Response.read 10 (wire.extract 0 11) false == .done none
        && Response.read 10 (wire.extract 0 10) false == .more
        && Response.read wire.size wire false != .done none) ]

def split (body : ByteArray) (size : Nat) : List ByteArray :=
  (List.range ((body.size + size - 1) / size)).map fun i =>
    body.extract (i * size) (i * size + size)

/-- Responses the writer can send: statuses, headers and bodies that try the reader's edges. -/
def written : List Response :=
  let statuses := [200, 201, 204, 206, 304, 404, 500, 599, 999]
  let headerSets : List (List (String × String)) :=
    [[], [("x-a", "b")], [("X-A", "b c"), ("Set-Cookie", "k=v; Path=/"), ("y", "ü\tz")],
      [("x-empty", "")], [("connection", "close"), ("x-a", "1"), ("x-a", "2"), ("host", "h:1")],
      [("x-colon", "a: b"), ("x-quote", "\"q\"")]]
  let bodies := ["", "hello", "\r\n\r\n", "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n",
    "0\r\n\r\n", String.ofList ((List.range 120).map fun n => Char.ofNat (n % 95 + 32))]
  statuses.flatMap fun status => headerSets.flatMap fun headers => bodies.filterMap fun body =>
    let r : Response := { status, headers, body := bytes body }
    if r.writable then some r else none

def wholeOnlyAtEnd (wire : ByteArray) (expected : Response) : Bool :=
  (List.range wire.size).all (fun n =>
      Response.read wire.size (wire.extract 0 n) false == .more
        && Response.read wire.size (wire.extract 0 n) true == .done none)
    && [false, true].all fun ended =>
      [ByteArray.empty, bytes "HTTP/1.1 500 Extra\r\n\r\n", bytes "\r\n\r\n"].all fun tail =>
        Response.read wire.size (wire ++ tail) ended == .done (some expected)

def interims : List Response :=
  [{ status := 100 }, { status := 103, headers := [("Link", "</a>; rel=preload")] }]

def roundTrip (r : Response) : Bool :=
  let framed := { r with
    headers := ("content-length", toString r.body.size) :: Response.lowered r.headers }
  let toEnd := r.wireToEnd
  wholeOnlyAtEnd r.wire framed && wholeOnlyAtEnd (r.wireAfter interims) framed
    && (r.status == 204 || r.status == 304
      || ([1, 7, r.body.size].all (fun size =>
          size == 0 || wholeOnlyAtEnd (r.wireChunked (split r.body size))
            { r with headers := ("transfer-encoding", "chunked") :: Response.lowered r.headers })
        && Response.read toEnd.size toEnd true
          == .done (some { r with headers := Response.lowered r.headers })
        && (List.range (toEnd.size + 1)).all fun n =>
          Response.read toEnd.size (toEnd.extract 0 n) false == .more))

def roundTripTests : List (String × Bool) :=
  [ (s!"http wire: {written.length} responses, each written five ways, are read back as written",
      written.length ≥ 200 && written.all roundTrip),
    ("http wire: a response the writer cannot send is not writable",
      interims.all (·.interim) && [({ status := 199 } : Response), { status := 1000 },
        { status := 204, body := bytes "x" }, { headers := [("Content-Length", "1")] },
        { headers := [("content-length", "1")] }, { headers := [("Transfer-Encoding", "chunked")] },
        { headers := [("x", " padded")] }, { headers := [("x", "a\r\nb")] },
        { headers := [("a b", "1")] }].all (!·.writable)),
    ("http wire: forms a server may send that the writers do not write are read",
      body? (parse "HTTP/1.1 200 OK\r\nContent-Length:002\r\nX-A:b\r\n\r\nokEXTRA") == some "ok"
        && (parse "HTTP/1.1 200 OK\r\nX-A:\tb \t\r\nContent-Length: 0\r\n\r\n").map (·.headers)
          == some [("x-a", "b"), ("content-length", "0")]
        && body? (parse (chunkedHead ++ "A\r\n0123456789\r\n0\r\n\r\n")) == some "0123456789"
        && body? (parse ("HTTP/1.1 100 Continue\r\n\r\n" ++ chunkedHead ++ "2\r\nok\r\n0\r\n\r\n"))
          == some "ok"
        && body? (parse "HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 200 OK\r\n\r\nto the end")
          == some "to the end"),
    ("http wire: a bare CR or another control character in the reason is refused",
      ["HTTP/1.1 200 O\rK", "HTTP/1.1 200 O\nK", "HTTP/1.1 200 O\x00K"].all fun line =>
        refused s!"{line}\r\nContent-Length: 2\r\n\r\nok"),
    ("http wire: a whole response within the limit is read whatever arrives after it",
      let wire := bytes lengthResponse
      Response.read wire.size (wire ++ bytes "more than the limit") false
          != .done none
        && Response.read wire.size (wire ++ bytes "more than the limit") true != .done none) ]

/-! A caller: asked to fetch, it calls a service and reports the status it got, or that it got
none. -/

inductive In where
  | fetch (id : Nat) (target : Client.Call)
  | reply (id : Nat) (response : Option Response)
  deriving DecidableEq, Repr, Hashable

inductive Out where
  | call (id : Nat) (target : Client.Call)
  | done (id : Nat) (status : Option Nat)
  deriving DecidableEq, Repr, Hashable

abbrev callerSig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

/-- The state is how many calls are open. -/
abbrev caller : System callerSig where
  State _ := Nat
  actor _ :=
    { init := 0
      step := fun calls msg =>
        match msg with
        | .fetch id target => (calls + 1, [.emit (.call id target)])
        | .reply id response => (calls - 1, [.emit (.done id (response.map (·.status)))])
      recover := fun s => (s, []) }
  accept x := ⟨(), x⟩

def port : Client.Port callerSig where
  called
    | .call id target => some (id, target)
    | .done .. => none
  reply id response := .reply id response
  replied
    | .reply id _ => some id
    | .fetch .. => none

/-- Clients ask for each fetch once and remember what they were told. -/
def clients : Outside callerSig (List Nat × List (Nat × Option Nat)) where
  init := ([], [])
  allow d x :=
    match x with
    | .fetch id _ => if id ∈ d.1 then none else some (id :: d.1, d.2)
    | .reply .. => none
  observe d out :=
    match out with
    | .done id status => (d.1, (id, status) :: d.2)
    | .call .. => d

def world := clients.both (Client.outside port) fun x => x matches .fetch ..

instance : callerSig.Inspect := {}
instance : caller.Inspect := {}

def target (tcpPort : UInt16) (path : List String := []) : Client.Call :=
  { host := "127.0.0.1", port := tcpPort, request := { method := .get, path } }

def check :=
  Check.system caller
    { driver := world.driver fun d =>
        [.fetch 0 (target 80), .fetch 1 (target 80)] ++ d.2.flatMap fun id =>
          [.reply id (some { status := 200 }), .reply id none] }
    [ .always "nothing is reported that was not asked for" fun w =>
        w.driver.1.2.all fun (id, _) => id ∈ w.driver.1.1,
      .always "no fetch is reported twice" fun w =>
        (w.driver.1.2.map (·.1)).eraseDups.length == w.driver.1.2.length,
      .always "the caller knows how many calls are open" fun w =>
        w.state.state () ≥ w.driver.2.length,
      .sometimes "a fetch succeeds and another finds no service" fun w =>
        w.driver.1.2.any (·.2 == some 200) && w.driver.1.2.any (·.2 == none) ]

def tests : List (String × Bool) :=
  requestTests ++ responseTests ++ readingTests ++ roundTripTests ++
  [ ("http client: a caller is right against everything a service may do, answers or not",
      check.ok && check.complete),
    ("http client: a call takes an output's id as its idempotency key, unless it has one",
      let call : Client.Call := { host := "127.0.0.1", port := 80, request := { method := .post, path := [] } }
      let own := { call with request := { call.request with headers := [("Idempotency-Key", "mine")] } }
      (call.keyed "j-3-0").request.headers == [("idempotency-key", "j-3-0")]
        && (own.keyed "j-3-0").request.headers == [("Idempotency-Key", "mine")]
        && Journal.OutputId.key ⟨"j", ⟨3, 0⟩⟩ == "j-3-0") ]

/-- A server on a local port. To whoever connects it sends `reply` (nothing, when that is
empty) and then holds the connection open until the other side leaves. -/
def holding (reply : ByteArray) : Async (TCP.Socket.Server × UInt16) := do
  let server ← TCP.Socket.Server.mk
  server.bind (.v4 ⟨.ofParts 127 0 0 1, 0⟩)
  server.listen 128
  let tcpPort := (← server.getSockName).port
  background do
    try
      repeat
        let client ← server.accept
        background do
          try
            unless reply.isEmpty do client.send reply
            while (← client.recv? 4096).isSome do pure ()
          catch _ => pure ()
          client.close
    catch _ => pure ()
  return (server, tcpPort)

/-- One fetch to each port, all at once. Answers what came back and after how many
milliseconds the last of it did; an answer that takes longer than `patience_ms` is missing.
The wait is on `result?`: `await` on a promise dropped unresolved blocks the thread that drops
it, here the shard as it stops. -/
def fetchAll (config : Client.Config) (ports : List UInt16) (patience_ms : Nat) :
    Async (List (Nat × Option Nat) × Nat) := do
  let reported ← IO.mkRef #[]
  let all ← IO.Promise.new
  let rt ← Runtime.startWith caller {} fun rt outputId out => do
    Client.handlerKeyed port config rt outputId out
    if let .done id status := out then
      if (← reported.modifyGet fun r => ((r.push (id, status)).size, r.push (id, status)))
          == ports.length
      then all.resolve ()
  let start ← IO.monoMsNow
  for (tcpPort, id) in ports.zipIdx do rt.input (.fetch id (target tcpPort))
  let answered : Async Unit := discard <| await all.result?
  Async.race answered (Async.sleep (.ofNat patience_ms))
  let elapsed_ms := (← IO.monoMsNow) - start
  rt.stop
  return ((← reported.get).toList, elapsed_ms)

/-- `none` where there is no `/proc`. -/
def openFiles : IO (Option Nat) := do
  let dir : System.FilePath := "/proc/self/fd"
  if ← dir.pathExists then return some (← dir.readDir).size else return none

/-- The count of open files once it is back to `settled` or below, or after a second. -/
def openFilesSettled (settled : Nat) : Async (Option Nat) := do
  let mut count ← openFiles
  for _ in [0:50] do
    if count.all (· ≤ settled) then break
    Async.sleep 20
    count ← openFiles
  return count

@[noinline] def timedChunks (count : Nat) : IO (String × Bool) := do
  let wire := manyChunks count
  let expected := manyChunksBody count
  let start ← IO.monoMsNow
  let right := (Response.parse wire).map (·.body) == some expected
  let elapsed_ms := (← IO.monoMsNow) - start
  return (s!"http wire: {count} one-byte chunks are read in well under 200 ms ({elapsed_ms} ms)",
    right && elapsed_ms < 200)

def framingTest : Async (List (String × Bool)) := do
  let large := bytes ("HTTP/1.1 200 OK\r\nContent-Length: 5000\r\n\r\n"
    ++ String.ofList (List.replicate 5000 'x'))
  let (keeping, keepingPort) ← holding (bytes ("HTTP/1.1 200 OK\r\nContent-Length: 2\r\n"
    ++ "Connection: keep-alive\r\n\r\nok"))
  let (sending, sendingPort) ← holding large
  let (kept, kept_ms) ← fetchAll { timeout_ms := 4000 } [keepingPort] 6000
  let (fits, _) ← fetchAll { timeout_ms := 4000, maxResponseBytes := large.size } [sendingPort] 6000
  let (over, over_ms) ←
    fetchAll { timeout_ms := 4000, maxResponseBytes := large.size - 1 } [sendingPort] 6000
  keeping.close
  sending.close
  return [
    (s!"http client: a whole response on a connection kept open is answered at once ({kept_ms} ms)",
      kept == [(0, some 200)] && kept_ms < 2000),
    (s!"http client: a response over the size limit is refused, at once ({over_ms} ms)",
      fits == [(0, some 200)] && over == [(0, none)] && over_ms < 2000) ]

def deadlineTest : Async (List (String × Bool)) := do
  let calls := 20
  let (silent, silentPort) ← holding .empty
  let before ← openFiles
  let (answers, elapsed_ms) ← fetchAll { timeout_ms := 200 } (List.replicate calls silentPort) 4000
  let after ← openFilesSettled (before.getD 0 + 2)
  silent.close
  return [
    (s!"http client: a server that never answers is given up on at the deadline ({elapsed_ms} ms)",
      answers.length == calls && answers.all (·.2 == none) && 190 ≤ elapsed_ms
        && elapsed_ms < 2000),
    (s!"http client: a call given up on leaves no socket open ({before} before, {after} after)",
      match before, after with
      | some before, some after => after < before + calls
      | _, _ => true) ]

def live : Async (List (String × Bool)) := do
  let server ← serve (Server.system Tests.Gate.echo) Tests.Gate.bridge { port := 0 }
  let some tcpPort := server.port | return [("http client: the server reports its port", false)]
  let reported ← IO.mkRef #[]
  let all ← IO.Promise.new
  let rt ← Runtime.startWith caller { record := true } fun rt _ out => do
    Client.handler port { timeout_ms := 3000 } rt out
    if let .done id status := out then
      if (← reported.modifyGet fun r => ((r.push (id, status)).size, r.push (id, status))) == 4
      then all.resolve ()
  rt.input (.fetch 0 (target tcpPort))
  rt.input (.fetch 1 (target tcpPort ["bad"]))
  rt.input (.fetch 2 (target 1))
  rt.input (.fetch 3 { (target tcpPort) with host := "not an address" })
  await all
  rt.idle
  let events := (← rt.trace).toList
  rt.stop
  server.stop
  let statuses := (← reported.get).toList
  return [
    ("http client: a real call brings back the server's answer",
      statuses.lookup 0 == some (some 200) && statuses.lookup 1 == some (some 400)),
    ("http client: a closed port and a bad address are reported as no answer",
      statuses.lookup 2 == some none && statuses.lookup 3 == some none),
    ("http client: the real service does only what its model allows", world.allows events),
    ← timedChunks 20000 ] ++ (← framingTest) ++ (← deadlineTest)

end Tests.HttpClient
