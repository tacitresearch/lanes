/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-! Pinned schemas (`Lanes/Data/Diff.lean`, `Lanes/Durable/Pin.lean`): a pinned file reads back
as what was pinned; the build's schema against it is the same, a change old files read (each
listed), or one opening refuses, naming the field; a corpus file that holds a removed
constructor fails, and one that does not passes; a declared migration reads a changed type.
`Schema.compare_reads_iff` says that the verdict is `Schema.Plan.of`'s. -/

namespace Tests.Pin

open Lanes Lanes.Journal

-- The version pinned.
namespace A

lanes_data inductive Cmd where
  | put (key : String) (value : Nat)
  | drop (key : String)
  | clear
  deriving DecidableEq, Repr, Codable

lanes_data structure Point where
  x : Int
  y : Int
  deriving DecidableEq, Repr, Codable

end A

-- Changes old files read: an argument added with a default, a constructor renamed with its
-- former name, one added, one removed; and the fields of a structure reordered.
namespace B

lanes_data inductive Cmd where
  | set (was put) (key : String) (value : Nat) (ttl_s : Nat := 0)
  | drop (key : String)
  | reset
  deriving DecidableEq, Repr, Codable

lanes_data structure Point where
  y : Int
  x : Int
  deriving DecidableEq, Repr, Codable

end B

-- An argument added with no default: refused.
namespace C

lanes_data inductive Cmd where
  | put (key : String) (value : Nat) (owner : String)
  | drop (key : String)
  | clear
  deriving DecidableEq, Repr, Codable

end C

-- A type changed: the value is text. Refused, unless a migration is declared.
namespace D

lanes_data inductive Cmd where
  | put (key : String) (value : String)
  | drop (key : String)
  | clear
  deriving DecidableEq, Repr, Codable

end D

def D.Cmd.ofA : A.Cmd → D.Cmd
  | .put key value => .put key (toString value)
  | .drop key => .drop key
  | .clear => .clear

abbrev sigA : Signature := { Id := Unit, Msg := fun _ => A.Cmd, In := A.Cmd, Out := Nat }

def counter : System sigA where
  State _ := Nat
  actor _ := { init := 0, step := fun n _ => (n + 1, []), recover := fun n => (n, []) }
  accept x := ⟨(), x⟩

def journalOf (α : Type) [Codable α] : Schema := Journal.Entry.schemaOf (Codec.of α).schema

def header : Pin.Header :=
  { kind := .journal, schema := "Tests.Pin.journalOf Tests.Pin.A.Cmd", imports := ["Tests.Pin"],
    corpus := ["Tests/Journals/kv"] }

def pinned : String := Pin.render header (journalOf A.Cmd)

def migration : Schema.Migration := .of (Codec.of A.Cmd).toOf (Codec.of D.Cmd).toOf D.Cmd.ofA

def file (cmds : List A.Cmd) : ByteArray :=
  Journal.file (σ := sigA) (Codec.of A.Cmd) "kv" (cmds.map (Journal.Entry.input (σ := sigA)) ++ [.batch 8])

def findingsOf (r : Pin.Result) : List String := r.findings.map (·.text)

def changesOf : Pin.Result → List Schema.Change
  | { findings := [.changed changes], .. } => changes
  | _ => []

def refusedWith : Pin.Result → Option Codec.Error
  | { findings := [.refused e], .. } => some e
  | _ => none

def failsOnCorpus : Pin.Result → Bool
  | { findings, fixed := none } =>
    findings.any fun | .corpus .. => true | _ => false
  | _ => false

def tests : List (String × Bool) :=
  let b := Pin.check pinned (journalOf B.Cmd) [] []
  [ ("pin: a pinned file reads back as its header and its schema",
      match Pin.parse pinned with
      | .ok (h, some s) => h == header && s == journalOf A.Cmd
      | .ok (_, none) => false
      | .error _ => false),
    ("pin: the build's own schema finds nothing and needs no fix",
      let r := Pin.check pinned (journalOf A.Cmd) [] []
      r.findings.isEmpty && r.fixed == some pinned),
    ("pin: a change old files read lists each change, and --fix pins the build's schema",
      let cs := changesOf b
      cs.contains (.renamed "Tests.Pin.B.Cmd.set" "put")
        && cs.contains (.addedField "Tests.Pin.B.Cmd.set.ttl_s")
        && cs.contains (.addedCtor "Tests.Pin.B.Cmd.reset")
        && cs.contains (.removedCtor "Tests.Pin.A.Cmd.clear")
        && cs.all (fun c => c matches .renamed .. | .addedField _ | .addedCtor _
          | .removedCtor _ | .renamedType .. | .redeclared _)
        && b.fixed == some (Pin.render header (journalOf B.Cmd))),
    ("pin: fields reordered are reported",
      Schema.changes [] (Codec.of A.Point).schema (Codec.of B.Point).schema
        == [.renamedType "Tests.Pin.A.Point" "Tests.Pin.B.Point", .reordered "Tests.Pin.B.Point"]),
    ("pin: an argument added with no default is refused, naming it, and not fixed",
      let r := Pin.check pinned (journalOf C.Cmd) [] []
      r.fixed.isNone && match refusedWith r with
        | some e => e.problem == .noDefault && (toString e).contains "owner"
        | none => false),
    ("pin: a changed type is refused, naming both types",
      match refusedWith (Pin.check pinned (journalOf D.Cmd) [] []) with
      | some e => e.problem == .changed "Nat" "String" && (toString e).contains "value"
      | none => false),
    ("pin: a changed type with a declared migration reads, and the corpus reads through it",
      let r := Pin.check pinned (journalOf D.Cmd) [migration] [("j", file [.put "a" 1, .clear])]
      changesOf r == [.migrated "Tests.Pin.D.Cmd"] && r.fixed.isSome),
    ("pin: a migration as lint declares it, from the two schemas, reads as the application's",
      let ms := [Pin.declared (Codec.of A.Cmd).schema (Codec.of D.Cmd).schema]
      let r := Pin.check pinned (journalOf D.Cmd) ms [("j", file [.put "a" 1, .clear])]
      changesOf r == [.migrated "Tests.Pin.D.Cmd"] && r.fixed.isSome),
    ("pin: each change reads as text that names its place",
      ((changesOf b).map (·.text)).contains
        "`Tests.Pin.B.Cmd.set` renamed from `put`, read through its former name"),
    ("pin: a removed constructor still in the corpus fails, naming the file and the constructor",
      let r := Pin.check pinned (journalOf B.Cmd) [] [("j", file [.put "a" 1, .clear])]
      failsOnCorpus r && (findingsOf r).any fun t => t.contains "`j`" && t.contains "clear"),
    ("pin: a removed constructor absent from the corpus is compatible",
      let r := Pin.check pinned (journalOf B.Cmd) [] [("j", file [.put "a" 1, .drop "a"])]
      !(changesOf r).isEmpty && r.fixed.isSome),
    ("pin: a corpus file of another kind is not read against a journal's schema",
      let other := Journal.saved (sys := counter) ⟨Codec.unit, fun _ => Codec.nat,
        fun _ => Codec.of A.Cmd⟩ "kv" 0 (Journal.recover counter []).1.image
      (Pin.check pinned (journalOf A.Cmd) [] [("s", other)]).findings.isEmpty),
    ("pin: a file not as --fix writes it, with the same schema, is stale and fixed",
      let edited := "-- a note\n" ++ pinned
      let r := Pin.check edited (journalOf A.Cmd) [] []
      (r.findings matches [.stale]) && r.fixed == some pinned),
    ("pin: a header alone pins nothing yet, and --fix pins the build's schema",
      let r := Pin.check "kind: journal\nschema: x\n" (journalOf A.Cmd) [] []
      (r.findings matches [.unpinned])
        && r.fixed == some (Pin.render { kind := .journal, schema := "x" } (journalOf A.Cmd))),
    ("pin: a file that is no pinned schema is unreadable, and not fixed",
      let r := Pin.check "schema: x\n" (journalOf A.Cmd) [] []
      (r.findings matches [.unreadable _]) && r.fixed.isNone),
    ("pin: the verdict is the plan's: compatible exactly when Schema.Plan.of makes one",
      [journalOf A.Cmd, journalOf B.Cmd, journalOf C.Cmd, journalOf D.Cmd].all fun s =>
        (Schema.compare [] (journalOf A.Cmd) s).reads
          == (Schema.Plan.of [] (journalOf A.Cmd) s).toBool) ]

end Tests.Pin
