/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Services.Postgres.IO.Db
public import Lanes.Web.IO.Server

/-!
A system served over HTTP whose calls to the typed store run on PostgreSQL. It decides nothing
(rule 3.9): an output the port reads as a call goes to the typed store's driver
(`Postgres.Typed.Store.call`) on a task of its own, and its result comes back as an input; any
other output the bridge does not answer goes to `onOutput`. `serveWith` takes any way to run a
call, such as the store in memory of the test kit (`Lanes.Testing.Store`).
-/

public section

namespace Lanes.Postgres.Typed

open Std.Async Lanes.Http

/-- Serve `sys` behind the gate, its calls to the store run by `call`, each on a task of its
own. A result that finds the inbox full is dropped, which the store's model allows as a lost
answer. -/
def serveWith {σ : Signature} (sys : System σ) [Hashable σ.Id] {Q A : Type} (bridge : Bridge σ)
    (port : Db.Port σ Q A) (call : Q → Async (Db.Result A)) (config : ServerConfig := {})
    (runtimeConfig : Runtime.Config := {}) (onOutput : σ.Out → Async Unit := fun _ => pure ())
    (arrive : Option (Http.Request → IO (Except Http.Response Http.Request)) := none) :
    Async (Server (admittedFronted sys bridge)) := do
  let running : IO.Promise (Option (Server (admittedFronted sys bridge))) ← IO.Promise.new
  let out : σ.Out → Async Unit := fun o =>
    match port.call o with
    | some c => background do
      let result ← try call c.request catch _ => pure .unknown
      if let some (some server) ← await running.result? then
        discard <| server.tryInput (port.reply { id := c.id, result })
    | none => onOutput o
  let server ← serveFronted sys bridge config runtimeConfig out arrive
  running.resolve (some server)
  return server

/-- Serve `sys` behind the gate, its calls to the store run on PostgreSQL by `store`. -/
def serve {σ : Signature} (sys : System σ) [Hashable σ.Id] {Q A : Type} (bridge : Bridge σ)
    (port : Db.Port σ Q A) (store : Store Q A) (config : ServerConfig := {})
    (runtimeConfig : Runtime.Config := {}) (onOutput : σ.Out → Async Unit := fun _ => pure ())
    (arrive : Option (Http.Request → IO (Except Http.Response Http.Request)) := none) :
    Async (Server (admittedFronted sys bridge)) :=
  serveWith sys bridge port store.call config runtimeConfig onOutput arrive

end Lanes.Postgres.Typed
