/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
# A shelf of files

The tables, the transactions and the front. Members put files on a shared shelf and take their
own off. This file is logic only: no IO (Lanes rule 2.4), and no theorems.
-/

namespace Shelf

open Lanes Lanes.Db

/-- Who signed in, as the bridge names an identity the sign-in verified. -/
abbrev Member := String

/-- An upload, keyed by its uploader and its id, so that only a request made as its uploader
names its key. -/
lanes_data structure Upload where
  owner : String
  id : Int64
  /-- The size the store gave when it was asked; `none` until it held the file. -/
  size : Option Int64
  deriving DecidableEq, Repr, Hashable
  table uploads key owner, id

/-- A number that only grows: the next upload's id, so that no two uploads share an object. -/
lanes_data structure Counter where
  name : String
  next : Int64
  deriving DecidableEq, Repr, Hashable
  table counters key name

def schema : Schema := [uploads.table, counters.table]

lanes_data inductive Request where
  | list (who : String) (at_s : Nat)
  /-- Begin an upload: the answer is a form to post the file to the store. -/
  | begin (who : String) (at_s : Nat)
  /-- The browser says it posted the file; `size` is what the store answered when asked. -/
  | seen (who : String) (file : Int64) (size : Option Nat)
  | delete (who : String) (file : Int64)
  deriving DecidableEq, Repr, Hashable

lanes_data inductive Answer where
  | shelf (viewer : String) (files : List Upload) (at_s : Nat)
  | form (viewer : String) (file : Int64) (at_s : Nat)
  | listed (file : Int64)
  | notSeen (file : Int64)
  | deleted (file : Int64)
  | refused (file : Int64)
  | full
  deriving DecidableEq, Repr, Hashable

structure Config where
  /-- Uploads on the shelf at once, begun or seen (rule 2.6), at most `Scan.limit_max`. -/
  maxFiles : Nat := 100

/-- The member a request is made as. -/
def Request.who : Request → Member
  | .list who _ | .begin who _ | .seen who .. | .delete who _ => who

def nextId : Txn Int64 := do
  let next := ((← counters.get [.text "upload"]).map (·.next)).getD 0
  let _ ← counters.upsert { name := "upload", next := next + 1 }
  return next

/-- The uploads on the shelf, at most `maxFiles`. -/
def onShelf (config : Config) : Txn (List Upload) :=
  uploads.scan { table := uploads.table, limit := config.maxFiles }

/-- What each request does. A `begin` past `maxFiles` is refused with `full`. A file is listed
only once the store said it holds it, and only its uploader can have it listed or take it off:
both name the upload by its key, which starts with the member. -/
def handler (config : Config) : Handler Request Answer
  | .list who at_s => do
    return .shelf who ((← onShelf config).filter (·.size.isSome)) at_s
  | .begin who at_s => do
    if config.maxFiles ≤ (← onShelf config).length then return .full
    let id ← nextId
    let _ ← uploads.insert { owner := who, id, size := none }
    return .form who id at_s
  | .seen who file size =>
    match size with
    | some n => do
      if ← uploads.update { owner := who, id := file, size := some (Int64.ofNat n) } then
        return .listed file
      else return .notSeen file
    | none => return .notSeen file
  | .delete who file => do
    if ← uploads.delete [.text who, .int file] then return .deleted file else return .refused file

/-! ## The front: it sends each request to the store and answers with what the store answered -/

abbrev ReqId := Nat

inductive In where
  | request (id : ReqId) (r : Request)
  | store (reply : Db.Reply Answer)
  deriving DecidableEq, Repr, Hashable

inductive Out where
  | call (c : Db.Call Request)
  | answered (id : ReqId) (a : Answer)
  | failed (id : ReqId)
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

def step : In → List (Effect sig ())
  | .request id r => [.emit (.call ⟨id, r⟩)]
  | .store ⟨id, .committed a⟩ => [.emit (.answered id a)]
  | .store ⟨id, _⟩ => [.emit (.failed id)]

abbrev system : System sig where
  State _ := Unit
  actor _ := { init := (), step := fun _ x => ((), step x) }
  accept x := ⟨(), x⟩

def port : Db.Port sig Request Answer where
  call
    | .call c => some c
    | _ => none
  reply r := .store r
  replied
    | .store r => some r
    | _ => none

end Shelf
