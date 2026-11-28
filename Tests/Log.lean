/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Structured logs (`Lanes/Lib/Log.lean`, `Lanes/Runtime/IO/Log.lean`): records whose message and
attributes hold newlines, quotes and control characters stay on one line and read back as JSON;
the fields come in `slog`'s order; a logger writes only at or above its level, with the
attributes and the request of its context.
-/

namespace Tests.Log

open Lanes Lanes.Log

def nasty : Record :=
  { time_ms := 1700000000000, level := .warn, msg := "line one\nline two\r\t\"quoted\" \\ \x01"
    attrs := [("user", .str "a\nb"), ("count", .num 3), ("ok", .bool true),
      ("nested", Json.mkObj [("k", .str "\x1b[31m")])]
    requestId := some "r-1" }

def field (line key : String) : Option Json :=
  (Json.parse line).toOption.bind fun j => (j.getObjVal? key).toOption

def tests : List (String × Bool) :=
  [ ("log: a record is written in slog's field order",
      render { time_ms := 1700000000123, level := .info, msg := "hi", attrs := [("n", .num 1)],
               requestId := some "abc" }
        == "{\"time\":\"2023-11-14T22:13:20.123Z\",\"level\":\"INFO\",\"msg\":\"hi\",\"n\":1,"
          ++ "\"request_id\":\"abc\"}"),
    ("log: no request id, no field",
      !(render { nasty with requestId := none }).contains "request_id"),
    ("log: control characters, quotes and newlines stay on one line",
      !(render nasty).toList.any fun c => c.toNat < 0x20),
    ("log: the line reads back as its record",
      field (render nasty) "msg" == some (.str nasty.msg)
        && field (render nasty) "user" == some (.str "a\nb")
        && field (render nasty) "request_id" == some (.str "r-1")
        && field (render nasty) "level" == some (.str "WARN")
        && (field (render nasty) "nested").bind (·.getObjVal? "k" |>.toOption)
          == some (.str "\x1b[31m")),
    ("log: levels",
      Level.warn.atLeast .info && !Level.debug.atLeast .info && Level.error.atLeast .error) ]

def live : IO (List (String × Bool)) := do
  let lines ← IO.mkRef (#[] : Array String)
  let logger : Logger := { sink := .call fun l => lines.modify (·.push l), level := .info }
  logger.debug "not written"
  logger.info "written" [("a", .num 1)]
  (logger.withAttrs [("service", .str "web")] |>.withRequest "r-9").error "failed\nbadly"
  let got ← lines.get
  return [("log: a logger writes at or above its level, with its context",
    got.size == 2
      && field got[0]! "msg" == some (.str "written") && field got[0]! "a" == some (.num 1)
      && field got[1]! "service" == some (.str "web")
      && field got[1]! "request_id" == some (.str "r-9")
      && field got[1]! "msg" == some (.str "failed\nbadly")
      && got.all fun l => !l.contains '\n')]

end Tests.Log
