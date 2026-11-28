/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.MatchSound

/-!
What changed between a schema that was pinned, the writer's of the files on disk, and the one a
build derives, the reader's (`docs/decisions/D97-data-format.md`, 3.9). `Schema.compare` decides
with `Schema.Plan.of` alone, as opening a file does: the change is compatible exactly when the
plan is made (`Schema.compare_reads_iff`), and refused with the error the plan gives, which names
the type and the field. `Schema.changes` only lists, for a reader of the report, what matching by
name will do: the fields added and dropped, the renames read through a former name, the
constructors added and removed, the reorders. A removed constructor is compatible here; whether
data still holds it is a question for the files (`lanes lint` reads the corpus).
-/

@[expose] public section

namespace Lanes.Schema

open Codec (Error)

/-- A change that matching by name reads, at its place: the type, then the constructor or the
field. -/
inductive Change where
  /-- A field the old data lacks, so it takes its default. -/
  | addedField (place : String)
  /-- A field the old data has and the reader drops. -/
  | droppedField (place : String)
  /-- A field or a constructor read through its former name `old`. -/
  | renamed (place old : String)
  | addedCtor (place : String)
  /-- A constructor the reader's type lacks: data that holds it is refused when it is met. -/
  | removedCtor (place : String)
  /-- Fields or constructors in another order. Harmless to the format, but a reorder often comes
  with a rename, and a codec written by hand is still positional. -/
  | reordered (place : String)
  /-- A type of another name in the same place: types are matched by place, not by name. -/
  | renamedType (old new : String)
  /-- A field's default, or a field's or a constructor's former names, changed. -/
  | redeclared (place : String)
  /-- A type changed and read through a declared migration. -/
  | migrated (type : String)
  deriving DecidableEq, Repr

def Change.text : Change → String
  | .addedField place => s!"`{place}` added, with a default"
  | .droppedField place => s!"`{place}` dropped: old data's values are skipped"
  | .renamed place old => s!"`{place}` renamed from `{old}`, read through its former name"
  | .addedCtor place => s!"`{place}` added"
  | .removedCtor place => s!"`{place}` removed: data that holds it is refused"
  | .reordered place => s!"`{place}`: fields or constructors reordered"
  | .renamedType old new => s!"`{old}` is now `{new}`"
  | .redeclared place => s!"`{place}`: its default or former names changed"
  | .migrated type => s!"`{type}` changed, read through its declared migration"

/-- The index of the writer's field or constructor each of the reader's takes, in the reader's
order. -/
def claims (names : List String) (rs : List (String × List String)) : List Nat :=
  rs.filterMap fun (name, aliases) => Plan.claim names name aliases

/-- `[.reordered place]` if the reader takes the writer's in another order. -/
def reorder (place : String) (taken : List Nat) : List Change :=
  if (taken.zip taken.tail).any fun (a, b) => b < a then [.reordered place] else []

def added (make : String → Change) (place : String) (names : List String)
    (rs : List (String × List String)) : List Change :=
  rs.filterMap fun (name, aliases) =>
    if (Plan.claim names name aliases).isSome then none else some (make (place ++ "." ++ name))

def fieldNames (fs : List (Field Schema)) : List (String × List String) :=
  fs.map fun f => (f.name, f.aliases)

def ctorNames (cs : List (Ctor Schema)) : List (String × List String) :=
  cs.map fun c => (c.name, c.aliases)

variable (ms : List Migration)

mutual

/-- What matching by name does between `w`, the writer's schema, and `r`, the reader's, where
the two differ. Read where `Plan.of` makes a plan; a part it would refuse lists nothing. -/
def changes (w r : Schema) : List Change :=
  if w == r then []
  else if ms.any (fun m => m.old == w && m.new == r) then [.migrated r.name]
  else
    match w with
    | .list a =>
      match r with
      | .list b => changes a b
      | _ => []
    | .map k v =>
      match r with
      | .map k' v' => changes k k' ++ changes v v'
      | _ => []
    | .record t _ wfs =>
      match r with
      | .record t' _ rfs =>
        let names := wfs.map (·.name)
        (if t = t' then [] else [.renamedType t t'])
          ++ fieldChanges t t' names rfs 0 wfs
          ++ added .addedField t' names (fieldNames rfs)
          ++ reorder t' (claims names (fieldNames rfs))
      | _ => []
    | .sum t _ wcs =>
      match r with
      | .sum t' _ rcs =>
        let names := wcs.map (·.name)
        (if t = t' then [] else [.renamedType t t'])
          ++ ctorChanges t t' names rcs 0 wcs
          ++ added .addedCtor t' names (ctorNames rcs)
          ++ reorder t' (claims names (ctorNames rcs))
      | _ => []
    | _ => []

/-- The changes of the writer's fields from the `k`th, each against the reader's field that
takes it, if one does. -/
def fieldChanges (old place : String) (names : List String) (rfs : List (Field Schema)) :
    Nat → List (Field Schema) → List Change
  | _, [] => []
  | k, ⟨name, aliases, s, default⟩ :: wfs =>
    let here := match rfs.find? (fun f => Plan.claim names f.name f.aliases == some k) with
      | none => [Change.droppedField (old ++ "." ++ name)]
      | some f =>
        (if f.name = name then [] else [.renamed (place ++ "." ++ f.name) name])
          ++ (if f.default == default && (f.name ≠ name || f.aliases == aliases) then []
            else [.redeclared (place ++ "." ++ f.name)])
          ++ changes s f.schema
    here ++ fieldChanges old place names rfs (k + 1) wfs

/-- The changes of the writer's constructors from the `k`th, each against the reader's
constructor that takes it, if one does. -/
def ctorChanges (old place : String) (names : List String) (rcs : List (Ctor Schema)) :
    Nat → List (Ctor Schema) → List Change
  | _, [] => []
  | k, ⟨name, aliases, fields⟩ :: wcs =>
    let here := match rcs.find? (fun c => Plan.claim names c.name c.aliases == some k) with
      | none => [Change.removedCtor (old ++ "." ++ name)]
      | some c =>
        let at_ := place ++ "." ++ c.name
        let inner := fields.map (·.name)
        (if c.name = name then [] else [.renamed at_ name])
          ++ (if c.name ≠ name || c.aliases == aliases then [] else [.redeclared at_])
          ++ fieldChanges (old ++ "." ++ name) at_ inner c.fields 0 fields
          ++ added .addedField at_ inner (fieldNames c.fields)
          ++ reorder at_ (claims inner (fieldNames c.fields))
    here ++ ctorChanges old place names rcs (k + 1) wcs

end

/-- What a build's schema of a type is to the one pinned: the same, a change that matching by
name reads, or one it refuses, with the error that names where. -/
inductive Verdict where
  | same
  | compatible (changes : List Change)
  | refused (error : Error)
  deriving Repr

/-- Whether data written under the pinned schema reads with the build's. -/
def Verdict.reads : Verdict → Bool
  | .refused _ => false
  | _ => true

/-- The build's schema `current` against the pinned one, through the plan opening a file makes,
with the declared migrations `ms`. -/
def compare (pinned current : Schema) : Verdict :=
  if pinned == current then .same
  else
    match Plan.of ms pinned current with
    | .ok _ => .compatible (changes ms pinned current)
    | .error e => .refused e

/-- The same schema is the same. -/
theorem compare_self (s : Schema) : compare ms s s = .same := by
  simp [compare]

theorem compare_eq_same_iff {pinned current : Schema} :
    compare ms pinned current = .same ↔ pinned = current := by
  constructor
  · intro h
    unfold compare at h
    split at h
    · exact beq_iff_eq.mp ‹_›
    · split at h <;> simp at h
  · rintro rfl; exact compare_self ms pinned

/-- A change is compatible exactly when `Schema.Plan.of`, the matching a file is opened with,
makes a plan: lint and opening never disagree. -/
theorem compare_reads_iff {pinned current : Schema} :
    (compare ms pinned current).reads = true ↔ ∃ plan, Plan.of ms pinned current = .ok plan := by
  unfold compare
  split
  · rename_i h
    rw [beq_iff_eq.mp h, Plan.of_self]
    simp [Verdict.reads]
  · split <;> simp_all [Verdict.reads]

/-- A refused change is refused with the error opening gives. -/
theorem compare_refused_iff {pinned current : Schema} {e : Error} :
    compare ms pinned current = .refused e ↔ pinned ≠ current ∧ Plan.of ms pinned current = .error e := by
  unfold compare
  split
  · rename_i h
    simp [beq_iff_eq.mp h]
  · rename_i h
    have hne : pinned ≠ current := fun heq => by simp [heq] at h
    split <;> simp_all

/-- A field added with a default, anywhere, is compatible (`Schema.Plan.of_insertIdx`). -/
theorem compare_insertIdx {t t' : String} {a a' : List Schema} {ws : List (Field Schema)}
    {f : Field Schema} {i : Nat} {d : Value} (hi : i ≤ ws.length)
    (hn : (ws.map (·.name)).Nodup) (hname : f.name ∉ ws.map (·.name))
    (halias : ∀ x ∈ f.aliases, x ∉ ws.map (·.name)) (hd : f.default = some d)
    (hm : ∀ m ∈ ms, m.old ≠ .record t a ws ∨ m.new ≠ .record t' a' (ws.insertIdx i f)) :
    (compare ms (.record t a ws) (.record t' a' (ws.insertIdx i f))).reads = true := by
  obtain ⟨p, hp, -⟩ := Plan.of_insertIdx hi hn hname halias hd hm
  exact (compare_reads_iff ms).mpr ⟨p, hp⟩

/-- A constructor renamed with its former name is compatible (`Schema.Plan.of_rename`). -/
theorem compare_rename {t t' : String} {a a' : List Schema} {cs : List (Ctor Schema)}
    {k : Nat} (hk : k < cs.length) {c : Ctor Schema}
    (hn : (cs.map (·.name)).Nodup) (hname : c.name ∉ cs.map (·.name))
    (hwas : cs[k].name ∈ c.aliases)
    (halias : ∀ x ∈ c.aliases, x ∈ cs.map (·.name) → x = cs[k].name)
    (hfields : c.fields = cs[k].fields)
    (hm : ∀ m ∈ ms, m.old ≠ .sum t a cs ∨ m.new ≠ .sum t' a' (cs.set k c)) :
    (compare ms (.sum t a cs) (.sum t' a' (cs.set k c))).reads = true := by
  obtain ⟨p, hp, -⟩ := Plan.of_rename hk hn hname hwas halias hfields hm
  exact (compare_reads_iff ms).mpr ⟨p, hp⟩

end Lanes.Schema
