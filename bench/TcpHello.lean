/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std.Async

/-! The floor under `Std.Http`: `Std.Net` TCP on libuv, one `Async` task per connection, and
a fixed response for every blank line that ends a request head. No parsing beyond that:
`benchTcp [port] [park]`. With `park` the main thread sleeps instead of waiting on the accept
loop's task: Lean's task manager wakes every thread waiting on a task whenever any task ends. -/

open Std Std.Async Std.Net

def response : ByteArray :=
  ("HTTP/1.1 200 OK\r\ncontent-type: text/plain; charset=utf-8\r\ncontent-length: 6\r\n" ++
    "\r\nhello\n").toUTF8

/-- How far into `\r\n\r\n` the bytes so far are, and how many heads have ended. -/
def scan (state : Nat × Nat) (bytes : ByteArray) : Nat × Nat :=
  bytes.foldl (init := state) fun (matched, heads) b =>
    let expected : UInt8 := if matched % 2 == 0 then 13 else 10
    if b == expected then
      if matched == 3 then (0, heads + 1) else (matched + 1, heads)
    else if b == 13 then (1, heads)
    else (0, heads)

def serveClient (client : TCP.Socket.Client) : Async Unit := do
  let mut matched := 0
  repeat
    let some bytes ← client.recv? 8192 | break
    let (m, heads) := scan (matched, 0) bytes
    matched := m
    if heads > 0 then client.sendAll (Array.replicate heads response)
  client.close

def main (args : List String) : IO Unit := do
  let port := (args.head? >>= String.toNat?).getD 8092
  let server ← TCP.Socket.Server.mk
  server.bind (.v4 ⟨.ofParts 127 0 0 1, port.toUInt16⟩)
  server.listen 1024
  server.noDelay
  IO.println s!"listening on {port}"
  (← IO.getStdout).flush
  let accept : Async Unit := do
    repeat
      let client ← server.accept
      client.noDelay
      background (try serveClient client catch _ => client.close)
  if args[1]? == some "park" then
    discard accept.asTask
    repeat IO.sleep 60000
  else accept.block
