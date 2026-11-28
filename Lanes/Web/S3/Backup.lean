/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.S3.Basic
public import Lanes.Durable.Ship

/-!
What S3's answers mean to a journal's shipper (`Lanes.Journal.Ship`): a conditional put that is
refused with `412` found the object there, and the key names the SHA-256 of its bytes, so it is
these bytes. The calls are made by `S3.backup` (`Lanes/Web/IO/S3.lean`).
-/

@[expose] public section

namespace Lanes.S3

/-- The put an upload is: a conditional write, so a segment handed over again is never written
twice. -/
def backupPut (key : Key) (bytes : ByteArray) : Op :=
  .put key bytes (some "application/octet-stream") (ifAbsent := true)

def shipped : Option Answer → Journal.Ship.Outcome
  | some (.stored _) => .stored
  | some (.refused 412 _) => .present
  | _ => .failed

/-- A page of a listing as keys with when they were last written, and the token of the next. -/
def listedPage : Option Answer → Option (List (String × String) × Option String)
  | some (.listed page) => some (page.entries.map fun e => (e.key, e.lastModified), page.next)
  | _ => none

end Lanes.S3
