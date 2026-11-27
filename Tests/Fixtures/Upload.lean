/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
# Reference app: uploads, a stream of bytes and a stream of events

`examples/upload`'s service, which keeps the size and the Adler-32 checksum of each upload as its
pieces come, behind a bridge that also answers two streamed responses itself: `GET /count`, the
lines `0`, `1`, `2`, and `GET /events`, the events `e0`, `e1`, `e2` with ids `0`, `1`, `2`, from
after the one the client last read.
-/

namespace Tests.Fixtures.Upload

open Lanes Lanes.Http

structure Sum where
  a : Nat := 1
  b : Nat := 0
  deriving DecidableEq, Repr, Hashable

def Sum.add (s : Sum) (byte : UInt8) : Sum :=
  let a := (s.a + byte.toNat) % 65521
  { a, b := (s.b + a) % 65521 }

def Sum.feed (s : Sum) (data : ByteArray) : Sum := data.data.toList.foldl Sum.add s

def checksum (data : ByteArray) : Nat :=
  let s := ({} : Sum).feed data
  s.b * 65536 + s.a

structure Progress where
  next : Nat := 0
  size : Nat := 0
  sum : Sum := {}
  deriving DecidableEq, Repr, Hashable

inductive In where
  | start (req : ReqId)
  | piece (req head index : Nat) (data : ByteArray) (last : Bool)
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature := Server.sig In (ReqId × Response)

def done (size sum : Nat) : Response := .text s!"{size} bytes, Adler-32 {sum}\n"

def service : Service sig.In sig.Out (List (ReqId × Progress)) where
  init := []
  step uploads
    | .start req => ((req, {}) :: uploads, [])
    | .piece req head index data last =>
      match uploads.lookup head with
      | none => (uploads, [(req, .text "no such upload\n" 400)])
      | some p =>
        if index != p.next then (uploads, [(req, .text "out of order\n" 400)])
        else
          let p := { next := p.next + 1, size := p.size + data.size, sum := p.sum.feed data }
          let rest := uploads.filter (·.1 != head)
          if last then (rest, [(req, Response.taken), (head, done p.size (p.sum.b * 65536 + p.sum.a))])
          else ((head, p) :: rest, [(req, Response.taken)])

def streams (r : Request) : Bool :=
  r.path == ["upload"] || r.path == ["count"] || r.path == ["events"]

def decode (id : ReqId) (r : Request) : Except Response In :=
  match Stream.msg? r with
  | some (.piece head index data last) => .ok (.piece id head index data last)
  | some (.pull _ index after) =>
    if r.path == ["count"] then
      .error (if index < 3 then Response.part s!"{index}\n".toUTF8 else Response.finished)
    else
      let next := ((after.bind String.toNat?).map (· + 1)).getD 0
      .error (if next < 3 then Sse.Event.response { data := s!"e{next}", id := some s!"{next}" }
        else Response.finished)
  | none =>
    if r.path == ["upload"] then .ok (.start id)
    else if r.path == ["count"] then .error Response.stream
    else if r.path == ["events"] then .error Response.events
    else .error (.text "not found\n" 404)

def bridge : Bridge sig where
  decode := decode
  encode out := some out

def system : System sig := Server.system service

def body (n : Nat) : ByteArray :=
  ByteArray.mk ((Array.range n).map fun k => (k * 7 + k / 251).toUInt8)

def chunked (data : ByteArray) (size : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut pos := 0
  while pos < data.size do
    let n := min size (data.size - pos)
    out := out ++ Response.chunk (data.extract pos (pos + n))
    pos := pos + n
  return out ++ "0\r\n\r\n".toUTF8

end Tests.Fixtures.Upload
