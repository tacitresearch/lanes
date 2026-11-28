/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Gate

/-!
Compression (`Lanes/Lib/Compress/`, `Lanes/Web/Http/Compress.lean`): the checksums against their
definitions and published values; what the encoder writes read back, on data of many sizes and
kinds; a stream that would decode to more than its bound refused early; which responses the
server compresses; and over a socket, a server that compresses and the client that reads it.
-/

namespace Tests.Compress

open Lanes Lanes.Http Std Std.Async

instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

def page (n : Nat) : ByteArray :=
  (String.join ((List.range n).map fun i =>
    s!"<li class=\"item\"><a href=\"/items/{i}\">Item {i}</a> of the list</li>\n")).toUTF8

/-- Bytes that compress badly: a linear congruential sequence. -/
def noise (n : Nat) : ByteArray :=
  ⟨((List.range n).foldl (fun (acc, x) _ => (acc.push (x >>> 16).toUInt8, (x * 1103515245 + 12345) % 2147483648))
    ((#[] : Array UInt8), 7)).1⟩

def samples : List ByteArray :=
  [.empty, "a".toUTF8, "abcabcabcabcabcabcabc".toUTF8, page 1, page 500, page 3000, noise 1000,
    noise 70000, ⟨Array.replicate 100000 0⟩, ⟨Array.replicate 300 7⟩ ++ noise 40000 ++ page 50]

def roundTrips (data : ByteArray) : Bool :=
  Inflate.inflate data.size (Deflate.compress data) == .ok data
    && Inflate.inflate data.size (Deflate.stored data) == .ok data
    && Gzip.decompress data.size (Gzip.compress data) == .ok data
    && Zlib.decompress data.size (Zlib.compress data) == .ok data

def tests : List (String × Bool) :=
  let bomb := Gzip.compress ⟨Array.replicate 2000000 0⟩
  let big : Response := { headers := [("content-type", "text/html; charset=utf-8"), ("etag", "\"v1\"")]
                          body := page 100 }
  let c : Compression := {}
  [ ("compress: CRC-32 and Adler-32 of the published check values",
      Crc32.hash "123456789".toUTF8 == 0xCBF43926 && Crc32.hash .empty == 0
        && Adler32.hash "Wikipedia".toUTF8 == 0x11E60398 && Adler32.hash .empty == 1),
    ("compress: the CRC-32 table is the bitwise definition, byte by byte and on long input",
      (List.range 256).all (fun b => Crc32.hash ⟨#[b.toUInt8]⟩ == Crc32.bitwise ⟨#[b.toUInt8]⟩)
        && Crc32.hash (noise 5000) == Crc32.bitwise (noise 5000)),
    ("compress: Adler-32 past 5552 bytes, where its sums are reduced",
      Adler32.hash ⟨Array.replicate 100000 255⟩ == 0x149A302C),
    ("compress: every sample reads back, raw, stored, gzip and zlib",
      samples.all roundTrips),
    ("compress: text compresses to well under a third, noise is stored",
      (Deflate.compress (page 3000)).size * 3 < (page 3000).size
        && (Deflate.compress (noise 70000)).size ≤ 70000 + 10),
    ("compress: a stream that decodes past its bound is refused, a byte too few",
      Gzip.decompress 1999999 bomb == .error .tooLarge
        && Gzip.decompress 2000000 bomb == .ok ⟨Array.replicate 2000000 0⟩),
    ("compress: a gzip body with two members reads as both",
      Gzip.decompress 100 (Gzip.compress "ab".toUTF8 ++ Gzip.compress "cd".toUTF8)
        == .ok "abcd".toUTF8),
    ("compress: refused: a bad checksum, a wrong size, garbage after a member, a cut stream",
      let g := Gzip.compress (page 10)
      let flip (i : Nat) := g.set! i (g[i]! ^^^ 1)
      (Gzip.decompress 10000 (flip (g.size - 5))).isOk == false
        && (Gzip.decompress 10000 (flip (g.size - 1))).isOk == false
        && (Gzip.decompress 10000 (g ++ ⟨#[0]⟩)).isOk == false
        && (Gzip.decompress 10000 (g.extract 0 (g.size - 1))).isOk == false),
    ("compress: Accept-Encoding: gzip named, by x-gzip or *, and not at q=0",
      accepts "gzip" && accepts "deflate, gzip;q=0.5" && accepts "x-gzip" && accepts "*"
        && accepts "GZIP ; Q=1" && !accepts "gzip;q=0" && !accepts "identity"
        && !accepts "*;q=0" && !accepts "gzip;q=0.0, *" && !accepts ""),
    ("compress: a page is compressed for a client that takes gzip, its ETag made weak",
      let r := c.respond (some "gzip, br") big
      headerValue? r.headers "content-encoding" == some "gzip"
        && headerValue? r.headers "vary" == some "Accept-Encoding"
        && headerValue? r.headers "etag" == some "W/\"v1\""
        && Gzip.decompress 1000000 r.body == .ok big.body),
    ("compress: not for a client that does not take it, but it says Vary",
      let r := c.respond none big
      r.body == big.body && headerValue? r.headers "vary" == some "Accept-Encoding"
        && (headerValue? r.headers "content-encoding").isNone),
    ("compress: not a small body, an image, an encoded body, a 304, or no-transform",
      let same (r : Response) := c.respond (some "gzip") r == r
      same { big with body := "short".toUTF8 }
        && same { big with headers := [("content-type", "image/png")] }
        && same { big with headers := big.headers ++ [("content-encoding", "br")] }
        && same { big with status := 304 }
        && same { big with headers := big.headers ++ [("cache-control", "public, no-transform")] }),
    ("compress: the client decodes gzip and deflate, both zlib's and raw, within its bound",
      let r (enc : String) (body : ByteArray) : Response :=
        { headers := [("content-encoding", enc), ("content-length", "1")], body }
      ((decode 10000 (r "gzip" (Gzip.compress (page 20)))).map (·.body)) == .ok (page 20)
        && ((decode 10000 (r "deflate" (Zlib.compress (page 20)))).map (·.body)) == .ok (page 20)
        && ((decode 10000 (r "deflate" (Deflate.compress (page 20)))).map (·.body)) == .ok (page 20)
        && ((decode 10000 (r "gzip" (Gzip.compress (page 20)))).map (·.headers)) == .ok []
        && (decode 100 (r "gzip" (Gzip.compress (page 20)))).isOk == false) ]

def bigBridge : Bridge Tests.Gate.echoSig where
  decode _ r :=
    if r.path == ["page"] then .error { headers := [("content-type", "text/html")], body := page 200 }
    else .ok 0
  encode id := some (id, .text "ok")

/-- A server that compresses, and the client that reads it. -/
def live : IO (List (String × Bool)) := do
  let server ← (serve (Server.system Tests.Gate.echo) bigBridge
    { port := 0, compression := some {} }).block
  let some port := server.port | return [("compress: the server reports its port", false)]
  let raw ← Client.fetch port
    { method := .get, path := ["page"], headers := [("accept-encoding", "gzip")] }
  let plain ← Client.fetch port
    { method := .get, path := ["page"], headers := [("accept-encoding", "identity")] }
  let decoded ← Client.fetch port { method := .get, path := ["page"] }
  let undecoded ← Client.fetch port { method := .get, path := ["page"] } { acceptGzip := false }
  server.stop.block
  return [
    ("compress: over a socket, a client that takes gzip gets it",
      headerValue? raw.headers "content-encoding" == some "gzip"
        && headerValue? raw.headers "vary" == some "Accept-Encoding"
        && raw.body.size * 3 < plain.body.size
        && Gzip.decompress 1000000 raw.body == .ok (page 200)),
    ("compress: one that does not gets the page as it is",
      (headerValue? plain.headers "content-encoding").isNone && plain.body == page 200),
    ("compress: the client asks for gzip and decodes it, unless told not to",
      decoded.body == page 200 && (headerValue? decoded.headers "content-encoding").isNone
        && undecoded.body == page 200) ]

end Tests.Compress
