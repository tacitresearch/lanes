/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Gate

/-! End-to-end tests of the HTTP adapter over a real socket. -/

namespace Tests.Web

open Lanes Lanes.Http Std Std.Async Tests.Gate

/-- Std has no HTTP client, so this speaks HTTP/1.1 over a TCP socket. -/
def fetch (port : UInt16) (path : String) : Async String := do
  let socket ← TCP.Socket.Client.mk
  socket.connect (.v4 ⟨.ofParts 127 0 0 1, port⟩)
  socket.send s!"GET {path} HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n".toUTF8
  let mut received := ByteArray.empty
  repeat
    match ← socket.recv? 4096 with
    | some bytes => received := received ++ bytes
    | none => break
  socket.close
  return (String.fromUTF8? received).getD ""

def serveTest : Async (List (String × Bool)) := do
  let server ← serve (Server.system echo) bridge { port := 0 }
  let some port := server.port | return [("web: the server reports its port", false)]
  let ok ← fetch port "/"
  let refused ← fetch port "/bad"
  let many ← Async.concurrentlyAll ((List.range 50).toArray.map fun _ => fetch port "/")
  server.stop
  return [
    ("web: a request is answered through the gate",
      ok.startsWith "HTTP/1.1 200" && ok.endsWith "ok"),
    ("web: a request the bridge refuses gets its response",
      refused.startsWith "HTTP/1.1 400" && refused.endsWith "bad"),
    ("web: fifty concurrent requests are each answered",
      many.all fun response => response.startsWith "HTTP/1.1 200" && response.endsWith "ok") ]

def tests : IO (List (String × Bool)) := serveTest.block

end Tests.Web
