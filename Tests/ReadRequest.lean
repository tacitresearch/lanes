/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.HttpClient

/-!
The request reader: the verdicts on the corpus `Tests/ReadRequest.corpus`, which
`scripts/requests.py` compares with other parsers; requests written by `Request.wire` read back
at every split; the smuggling shapes refused; each limit at its edge.
-/

namespace Tests.ReadRequest

open Lanes Lanes.Http

def bytes (s : String) : ByteArray := s.toUTF8

def hexDigit? (c : Char) : Option Nat := hexValue? c

/-- The bytes a corpus line writes: `\r`, `\n`, `\t`, `\\`, `\xHH`, and `\*N(text)` for `text`
repeated `N` times. -/
def unescape : (fuel : Nat) → List Char → Option (List UInt8)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, '\\' :: 'r' :: rest => (13 :: ·) <$> unescape fuel rest
  | fuel + 1, '\\' :: 'n' :: rest => (10 :: ·) <$> unescape fuel rest
  | fuel + 1, '\\' :: 't' :: rest => (9 :: ·) <$> unescape fuel rest
  | fuel + 1, '\\' :: '\\' :: rest => (92 :: ·) <$> unescape fuel rest
  | fuel + 1, '\\' :: 'x' :: hi :: lo :: rest => do
    let byte := (← hexDigit? hi) * 16 + (← hexDigit? lo)
    (byte.toUInt8 :: ·) <$> unescape fuel rest
  | fuel + 1, '\\' :: '*' :: rest =>
    let count := rest.takeWhile Char.isDigit
    match rest.dropWhile Char.isDigit with
    | '(' :: after => do
      let once ← unescape fuel (after.takeWhile (· != ')'))
      let tail ← unescape fuel ((after.dropWhile (· != ')')).drop 1)
      return (List.replicate (String.ofList count).toNat! once).flatten ++ tail
    | _ => none
  | _ + 1, '\\' :: _ => none
  | fuel + 1, c :: rest => (String.utf8EncodeChar c ++ ·) <$> unescape fuel rest

def methodName (incoming : Request.Incoming) : String :=
  if incoming.headOnly then "HEAD"
  else match incoming.request.method with
    | .get => "GET" | .post => "POST" | .put => "PUT" | .patch => "PATCH" | .delete => "DELETE"

/-- What reading from `pos` and again from where each request ended gives. -/
def verdicts (limits : Request.Limits) (wire : ByteArray) : (fuel pos : Nat) → List String
  | 0, _ => ["fuel"]
  | fuel + 1, pos =>
    match Request.read limits wire pos with
    | .more => ["more"]
    | .refuse why => [toString why.status]
    | .done incoming stop =>
      s!"ok:{methodName incoming}:{incoming.request.body.size}" :: verdicts limits wire fuel stop

structure Case where
  name : String
  verdict : String
  wire : ByteArray

def corpus (text : String) : Except String (List Case) :=
  (text.splitOn "\n").filterMap (fun line => if line.isEmpty || line.startsWith "#" then none
    else some line) |>.mapM fun line =>
      match line.splitOn "\t" ++ [""] with
      | name :: verdict :: escaped :: _ =>
        match unescape (escaped.length + 1) escaped.toList with
        | some wire => .ok { name, verdict, wire := ⟨wire.toArray⟩ }
        | none => .error s!"{name}: bad escape"
      | _ => .error s!"no verdict: {line}"

/-- An answer once given stays, whatever arrives after it: every start of the bytes reads as
needing more or as the whole of them does. Of a long case, one start in a hundred. -/
def stays (limits : Request.Limits) (wire : ByteArray) : Bool :=
  let whole := Request.read limits wire 0
  let step := if wire.size ≤ 1000 then 1 else 100
  ((List.range (wire.size / step + 1)).map (· * step)).all fun n =>
    let cut := Request.read limits (wire.extract 0 n) 0
    cut == .more || cut == whole

def corpusTests : IO (List (String × Bool)) := do
  match corpus (← IO.FS.readFile "Tests/ReadRequest.corpus") with
  | .error e => return [(s!"request corpus: {e}", false)]
  | .ok cases =>
    return (cases.map fun c =>
      (s!"request corpus: {c.name}: {c.verdict}",
        " ".intercalate (verdicts {} c.wire (c.wire.size + 2) 0) == c.verdict))
      ++ [("request corpus: every start of every case reads as needing more or as the whole",
            cases.length ≥ 100 && cases.all fun c => stays {} c.wire)]

/-! Requests `Request.wire` writes, read back -/

def hosts : List String := ["example.com", "10.0.0.1:8080", "[::1]", "a"]

def requests : List Request :=
  let methods := [Method.get, .post, .put, .patch, .delete]
  let paths := [[], ["a"], ["a b", "c/d", "é"], ["", "x", ""], ["?#&="]]
  let queries := [[], [("q", "1")], [("a b", "c&d=e"), ("", ""), ("+", "%")]]
  let headerSets : List (List (String × String)) :=
    [[], [("x-a", "b")], [("X-A", " padded \t"), ("Content-Length", "9"), ("x-b", "")],
      [("Transfer-Encoding", "chunked"), ("host", "evil"), ("Connection", "keep-alive")],
      [("expect", "100-continue"), ("x-u", "ü"), ("bad name", "1"), ("x-c", "a\r\nb")]]
  let bodies := ["", "hello", "\r\n\r\nGET / HTTP/1.1\r\n\r\n", "0\r\n\r\n"]
  methods.flatMap fun method => paths.flatMap fun path => queries.flatMap fun query =>
    headerSets.flatMap fun headers => bodies.map fun body =>
      { method, path, query, headers, body := bytes body }

def readsBack (r : Request) (host : String) : Bool :=
  match r.wire host with
  | none => false
  | some wire =>
    let tail := bytes "GET / HTTP/1.1\r\nHost: a\r\n\r\n"
    (List.range wire.size).all (fun n => Request.read {} (wire.extract 0 n) 0 == .more)
      && Request.read {} wire 0 == .done (r.sent host) wire.size
      && Request.read {} (wire ++ tail) 0 == .done (r.sent host) wire.size
      && Request.read {} (tail ++ wire) tail.size == .done (r.sent host) (tail.size + wire.size)

def roundTripTests : List (String × Bool) :=
  let fitting := (requests.zipIdx.map fun (r, i) => (r, hosts[i % hosts.length]!)).filter
    fun (r, host) => r.fits {} host
  [ (s!"read request: {fitting.length} requests Request.wire writes are read back at every split",
      fitting.length ≥ 1000 && fitting.all fun (r, host) => readsBack r host),
    ("read request: the path [\"\"] is written as the empty path and is the one left out",
      requests.all fun r => hosts.all fun host => r.fits {} host || r.path == [""]) ]

/-! The smuggling shapes, refused -/

def head (lines : List String) : ByteArray :=
  bytes ("\r\n".intercalate lines ++ "\r\n\r\n")

def refusedNow (wire : ByteArray) : Bool :=
  match Request.read {} wire 0 with
  | .refuse _ => true
  | _ => false

def start : List String := ["POST / HTTP/1.1", "Host: a"]

def lengthLines : List String :=
  ["Content-Length: 0", "content-length: 5", "CONTENT-LENGTH:5", "Content-Length:\t5\t",
    "Content-Length: x", "Content-Length: 5, 5"]

def codingLines : List String :=
  ["Transfer-Encoding: chunked", "transfer-encoding: CHUNKED", "Transfer-Encoding: x",
    "Transfer-Encoding: gzip, chunked", "Transfer-Encoding:chunked"]

def smugglingTests : List (String × Bool) :=
  let rest := bytes "5\r\nhello\r\n0\r\n\r\n"
  [ ("read request: a length beside a coding is refused, in either order, whatever follows",
      lengthLines.all fun l => codingLines.all fun c =>
        refusedNow (head (start ++ [l, c]) ++ rest) && refusedNow (head (start ++ [c, "X: 1", l])
          ++ rest)),
    ("read request: two lengths are refused, alike or not",
      lengthLines.all fun a => lengthLines.all fun b => refusedNow (head (start ++ [a, b]) ++ rest)),
    ("read request: two codings are refused",
      codingLines.all fun a => codingLines.all fun b => refusedNow (head (start ++ [a, b]) ++ rest)),
    ("read request: a line that starts with a blank is refused, wherever it is",
      ([" ", "\t", " \t"].all fun blank => (List.range 3).all fun i =>
        let lines := ["X-A: 1", "X-B: 2", "Content-Length: 5"]
        refusedNow (head (start ++ lines.set i (blank ++ lines[i]!)) ++ rest))
        && refusedNow (head ["GET / HTTP/1.1", " Host: a"])),
    ("read request: a blank before a colon is refused",
      ["Host : a", "Host\t: a", "X-A : b", "Content-Length : 5", "Transfer-Encoding : chunked"].all
        fun l => refusedNow (head ["GET / HTTP/1.1", "Host: a", l] ++ rest)
          && refusedNow (head ["GET / HTTP/1.1", l, "Host: a"] ++ rest)),
    ("read request: a bare LF or CR in a head is refused",
      ["\n", "\r", "a\nb", "a\rb", "\x00"].all fun bad =>
        (List.range 3).all fun i =>
          let lines := ["GET / HTTP/1.1", "Host: a", "X-A: b"]
          refusedNow (head (lines.set i (lines[i]! ++ bad))) ),
    ("read request: a chunk size that is not one to sixteen hex digits and a CRLF is refused",
      ["", " 5", "5 ", "+5", "0x5", "5;a", "5\n", "5\r", "00000000000000005", "g", "5\r\r"].all
        fun size => refusedNow (head (start ++ ["Transfer-Encoding: chunked"])
          ++ bytes (size ++ "\r\nhello\r\n0\r\n\r\n"))
          && refusedNow (head (start ++ ["Transfer-Encoding: chunked"])
            ++ bytes ("2\r\nok\r\n" ++ size ++ "\r\nhello\r\n0\r\n\r\n"))) ]

/-! Each limit, at its edge -/

def limits : Request.Limits :=
  { line_max := 40, head_max := 120, fields_max := 3, body_max := 10, chunks_max := 2 }

def verdict (wire : ByteArray) : String :=
  " ".intercalate (verdicts limits wire (wire.size + 2) 0)

def limitTests : List (String × Bool) :=
  let line (n : Nat) := "GET /" ++ String.ofList (List.replicate (n - 14) 'a') ++ " HTTP/1.1"
  let chunked := ["POST / HTTP/1.1", "Host: a", "Transfer-Encoding: chunked"]
  [ ("read request: a request line of line_max bytes is read, one more is refused with 414",
      (line 40).length == 40 && verdict (head [line 40, "Host: a"]) == "ok:GET:0 more"
        && verdict (head [line 41, "Host: a"]) == "414"
        && verdict (bytes (line 42)) == "414" && verdict (bytes (line 41)) == "more"),
    ("read request: a head of head_max bytes is read, one more is refused with 431",
      let filler (n : Nat) := "X: " ++ String.ofList (List.replicate n 'b')
      let size (n : Nat) := (head ["GET / HTTP/1.1", "Host: a", filler n]).size
      size 88 == 120 && verdict (head ["GET / HTTP/1.1", "Host: a", filler 88]) == "ok:GET:0 more"
        && verdict (head ["GET / HTTP/1.1", "Host: a", filler 89]) == "431"
        && verdict ((head ["GET / HTTP/1.1", "Host: a", filler 89]).extract 0 120) == "431"
        && verdict ((head ["GET / HTTP/1.1", "Host: a", filler 89]).extract 0 119) == "more"),
    ("read request: fields_max fields are read, one more is refused with 431",
      verdict (head ["GET / HTTP/1.1", "Host: a", "X: 1", "Y: 2"]) == "ok:GET:0 more"
        && verdict (head ["GET / HTTP/1.1", "Host: a", "X: 1", "Y: 2", "Z: 3"]) == "431"),
    ("read request: a body of body_max bytes is read, one more is refused with 413 at once",
      verdict (head ["POST / HTTP/1.1", "Host: a", "Content-Length: 10"] ++ bytes "0123456789")
          == "ok:POST:10 more"
        && verdict (head ["POST / HTTP/1.1", "Host: a", "Content-Length: 11"]) == "413"
        && verdict (head chunked ++ bytes "5\r\n01234\r\n5\r\n56789\r\n0\r\n\r\n")
          == "ok:POST:10 more"
        && verdict (head chunked ++ bytes "5\r\n01234\r\n6\r\n") == "413"
        && verdict (head chunked ++ bytes "B\r\n") == "413"),
    ("read request: chunks_max chunks are read, one more is refused with 413",
      verdict (head chunked ++ bytes "1\r\na\r\n1\r\nb\r\n0\r\n\r\n") == "ok:POST:2 more"
        && verdict (head chunked ++ bytes "1\r\na\r\n1\r\nb\r\n1\r\nc\r\n0\r\n\r\n") == "413"),
    ("read request: with the default limits, a body of 4096 one-byte chunks is read",
      let wire := (List.range 4096).foldl (init := head chunked) (fun w _ =>
        w ++ bytes "1\r\nx\r\n") ++ bytes "0\r\n\r\n"
      match Request.read {} wire 0 with
      | .done incoming stop => incoming.request.body.size == 4096 && stop == wire.size
      | _ => false) ]

def headTests : List (String × Bool) :=
  let expecting := head ["POST / HTTP/1.1", "Host: a", "Expect: 100-CONTINUE", "Content-Length: 5"]
  [ ("read request: the head says it expects 100 Continue before its body has arrived",
      match Request.readHead {} expecting 0, Request.read {} expecting 0 with
      | .done h start, .more => h.expectsContinue && start == expecting.size
      | _, _ => false),
    ("read request: a head without Expect does not",
      match Request.readHead {} (head ["POST / HTTP/1.1", "Host: a", "Content-Length: 5"]) 0 with
      | .done h _ => !h.expectsContinue
      | _ => false) ]

def tests : List (String × Bool) :=
  roundTripTests ++ smugglingTests ++ limitTests ++ headTests

end Tests.ReadRequest
