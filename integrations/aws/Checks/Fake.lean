/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.S3

/-!
A local HTTP server for the fakes, on the reader and the writer of the fake S3 of Lanes's tests
(`Tests/S3.lean`): each request is read whole and handed to a function, whose answer is written
before the connection is closed; `none` answers nothing and keeps the connection open, as a
service that does not answer.
-/

namespace Checks.Fake

open Lanes Std Std.Async Tests.S3

/-- The time in RFC 3339, to the second, as AWS writes an expiration. -/
def rfc3339 (seconds : Nat) : String :=
  let t := Civil.DateTime.ofUnix seconds
  String.ofList (TimeFormat.d4 t.date.year.toNat ++ '-' :: TimeFormat.d2 t.date.month ++ '-' ::
    TimeFormat.d2 t.date.day ++ 'T' :: TimeFormat.clock t.time ++ ['Z'])

def json (status : Nat) (body : String) (headers : List (String × String) := []) : ByteArray :=
  answer status (("Content-Type", "application/json") :: headers) body.toUTF8

def text (status : Nat) (body : String) : ByteArray :=
  answer status [("Content-Type", "text/plain")] body.toUTF8

/-- A server on a local port. -/
def serve (handle : Raw → IO (Option ByteArray)) : Async (TCP.Socket.Server × UInt16) := do
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
            let mut received := ByteArray.empty
            repeat
              let some arrived ← client.recv? 65536 | break
              received := received ++ arrived
              if let some r := raw? received then
                match ← handle r with
                | some reply => client.send reply
                | none => Async.sleep 5000
                break
          catch _ => pure ()
          client.close
    catch _ => pure ()
  return (server, tcpPort)

/-- Waits up to `patience_ms` for `ready`, looking every 20 ms. -/
def waitFor (patience_ms : Nat) (ready : IO Bool) : Async Bool := do
  for _ in [0:patience_ms / 20] do
    if ← ready then return true
    Async.sleep 20
  ready

end Checks.Fake
