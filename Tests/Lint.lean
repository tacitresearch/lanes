/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LanesCli.Lint

/-! `lanes lint` and `lanes lint --fix` on a small project written to a temporary directory. -/

namespace Tests.Lint

open Lanes.Cli Lanes.Cli.Lint

def write (root : System.FilePath) (path text : String) : IO Unit := do
  if let some dir := (root / path).parent then IO.FS.createDirAll dir
  IO.FS.writeFile (root / path) text

def read (root : System.FilePath) (path : String) : IO String :=
  IO.FS.readFile (root / path)

def rules (report : Report) : List String :=
  report.findings.map (·.rule)

def project (root : System.FilePath) : IO Unit := do
  write root "Shell.lean" (String.join (List.replicate 60 "-- a line\n"))
  write root "TRUSTED.md" "| The shell | `Shell.lean`, 7 lines | |\n"
  write root "README.md" "Trusted code.\n"
  write root "docs/decisions/README.md" "# Decisions\n\nPreamble.\n"
  write root "docs/decisions/D1-first.md" "# D1. First\n\nStatus: Superseded by D2\n\nText.\n"
  write root "docs/decisions/D2-second.md" "# D2. Second, `code`\n\nStatus: Accepted\n\nMore.\n"
  write root "docs/decisions/new-third.md"
    "# D?. Third\n\nStatus: Partly superseded by D2 (a part)\n\nNewest, after `new-third.md`.\n"
  write root "docs/GUIDE.md" "The third: `docs/decisions/new-third.md`.\n"

def expectedIndex (third : Bool) : String :=
  "# Decisions\n\nPreamble.\n\n## Index\n\n### Current\n\n"
    ++ "- [D2. Second, `code`](D2-second.md)\n"
    ++ (if third then "- [D3. Third](D3-third.md): partly superseded by D2 (a part)\n" else "")
    ++ "\n### Superseded\n\n- [D1. First](D1-first.md): superseded by D2\n"

def scratch : IO System.FilePath := do
  let dir := (← IO.getEnv "TMPDIR").getD "/tmp"
  return s!"{dir}/lanes-lint-{← IO.monoNanosNow}"

def fixTests (root : System.FilePath) : IO (List (String × Bool)) := do
  project root
  let before ← lint root
  let fixed ← lint root { fix := true }
  let again ← lint root { fix := true }
  let trusted ← read root "TRUSTED.md"
  let readme ← read root "README.md"
  let index ← read root "docs/decisions/README.md"
  let unnumbered ← lint root { main := true }
  let numbered ← lint root { fix := true, main := true }
  let numberedAgain ← lint root { fix := true, main := true }
  let third ← read root "docs/decisions/D3-third.md"
  let gone := !(← (root / "docs/decisions/new-third.md").pathExists)
  let guide ← read root "docs/GUIDE.md"
  let indexAfter ← read root "docs/decisions/README.md"
  return [
    ("lint: a wrong count and a stale index are each reported",
      rules before == ["trusted-size", "decisions"]),
    ("lint --fix: no findings after it", fixed.findings.isEmpty && fixed.fixed.length == 2),
    ("lint --fix: a second run changes nothing", again.fixed.isEmpty && again.findings.isEmpty),
    ("lint --fix: the count is the file's", trusted == "| The shell | `Shell.lean`, 60 lines | |\n"),
    ("lint --fix: the README holds no total", readme == "Trusted code.\n"),
    ("lint --fix: the index lists the numbered decisions, current ones first, not a new one",
      index == expectedIndex false),
    ("lint --main: a decision without a number is reported",
      unnumbered.findings.any fun f => f.rule == "decisions"
        && f.file.toString == "docs/decisions/new-third.md"),
    ("lint --fix --main: the new decision is numbered, and its references and index follow",
      numbered.findings.isEmpty && gone
        && third == "# D3. Third\n\nStatus: Partly superseded by D2 (a part)\n\nNewest, after `D3-third.md`.\n"
        && guide == "The third: `docs/decisions/D3-third.md`.\n" && indexAfter == expectedIndex true),
    ("lint --fix --main: a second run changes nothing",
      numberedAgain.fixed.isEmpty && numberedAgain.findings.isEmpty)]

def problemTests (root : System.FilePath) : IO (List (String × Bool)) := do
  project root
  discard <| lint root { fix := true }
  write root "docs/decisions/D2-again.md" "# D2. Again\n\nStatus: Accepted\n"
  write root "docs/decisions/D4-wrong.md" "# D5. Wrong\n\nStatus: Accepted\n"
  write root "docs/decisions/notes.md" "# Notes\n"
  write root "docs/decisions/D6-unsaid.md" "# D6. Unsaid\n\nText.\n"
  write root "docs/decisions/D7-other.md" "# D7. Other\n\nStatus: Rejected\n"
  let report ← lint root { fix := true }
  let decisions := report.findings.filter (·.rule == "decisions")
  let unsaid := decisions.filter fun f => f.line == 3
  return [
    ("lint: two decisions with one number, a heading that is not its file's and a stray file "
        ++ "are reported, and --fix leaves them",
      decisions.length == 6
        && (← (root / "docs/decisions/D2-again.md").pathExists)),
    ("lint: a decision without a status line, or with another status, is reported",
      unsaid.map (·.file.toString) == ["docs/decisions/D6-unsaid.md", "docs/decisions/D7-other.md"])]

def citing : String :=
  "See `Lanes/A.lean`, `Lanes/{A,B}.lean` and `Lanes/`.\n"
    ++ "Gone: `Lanes/Gone.lean`, and `Lanes/{A,Lost}.lean`.\n"
    ++ "Not paths: `net/http`, `Lanes.A`, `docs/changes/<slug>.md`, `Lanes/*.lean`, `a / b`, "
    ++ "`https://example.com/x`, `/dev/urandom`, `.lake/packages`.\n"
    ++ "```bash\nlake env lean Lanes/InAFence.lean\n```\n"
    ++ "A span `across\nlines` keeps the rest paired: `Lanes/Missing/`.\n"

def linkTests (root : System.FilePath) : IO (List (String × Bool)) := do
  project root
  discard <| lint root { fix := true }
  write root "Lanes/A.lean" ""
  write root "Lanes/B.lean" ""
  write root "README.md" ("Trusted code.\n" ++ citing)
  write root "docs/GUIDE.md" "Cites `Lanes/Nowhere.lean`.\n"
  write root "docs/area/notes.md" "- `Lanes/Away.lean`.\n"
  write root "docs/decisions/D3-past.md" "# D3. Past\n\nStatus: Accepted\n\nWas `Lanes/Past.lean`.\n"
  let report ← lint root { fix := true }
  let links := report.findings.filter (·.rule == "links")
  let found := links.map fun f => (f.file.toString, f.line, f.message)
  return [
    ("lint links: a missing path is reported, at its file and line, and one in braces by name",
      found == [("README.md", 3, "`Lanes/Gone.lean` does not exist"),
        ("README.md", 3, "`Lanes/Lost.lean` does not exist"),
        ("README.md", 9, "`Lanes/Missing/` does not exist"),
        ("docs/GUIDE.md", 1, "`Lanes/Nowhere.lean` does not exist"),
        ("docs/area/notes.md", 1, "`Lanes/Away.lean` does not exist")]),
    ("lint links: the decisions are not checked",
      !links.any fun f => f.file.toString.startsWith "docs/decisions"),
    ("codeSpans: double backquotes, and spans outside fences only",
      codeSpans "a ``x ` y`` b `z`\n```\n`no`\n```\n`w`" == [(1, "x ` y"), (1, "z"), (5, "w")]),
    ("expandBraces", expandBraces "a/{b,c}/{d,e}.lean"
      == ["a/b/d.lean", "a/b/e.lean", "a/c/d.lean", "a/c/e.lean"]
      && expandBraces "a/b.lean" == ["a/b.lean"])]

def manifest : String :=
  "# Oracles\n\n## References\n\n| Folder | Reference |\n| --- | --- |\n| `oracles/go` | Go |\n"
    ++ "| `oracles/gone` | none |\n\n## Protocol modules\n\n| Module | Oracle | Or why not |\n"
    ++ "| --- | --- | --- |\n| `Lanes/Lib/A.lean` | `oracles/go` | |\n"
    ++ "| `Lanes/Lib/B.lean` | | A reason |\n| `Lanes/Lib/C.lean` | | |\n"
    ++ "| `Lanes/Lib/Gone.lean` | `oracles/go/lost` | |\n\n## Outside models\n\n"
    ++ "| Model | Recorded run | Or why not |\n| --- | --- | --- |\n"

def oracleTests (root : System.FilePath) : IO (List (String × Bool)) := do
  project root
  discard <| lint root { fix := true }
  for path in ["Lanes/Lib/A.lean", "Lanes/Lib/B.lean", "Lanes/Lib/C.lean", "Lanes/Lib/ASound.lean",
      "Lanes/Lib/IO/D.lean", "Lanes/Web/E.lean", "Lanes/Outside/M.lean", "oracles/go/main.go",
      "oracles/py/main.py"] do
    write root path ""
  write root "oracles/README.md" manifest
  let report ← lint root { fix := true }
  let found := (report.findings.filter (·.rule == "oracles")).map fun f => (f.line, f.message)
  return [
    ("lint oracles: a module gone, a path gone, a row without a reason, a module or a folder without a row",
      found == [(8, "`oracles/gone` is not a folder"),
        (1, "`oracles/py` has no row under References: its reference, version and pin"),
        (16, "Lanes/Lib/C.lean names no oracle and gives no reason"),
        (17, "`Lanes/Lib/Gone.lean` does not exist"), (17, "`oracles/go/lost` does not exist"),
        (1, "`Lanes/Web/E.lean` has no row under Protocol modules: name its oracle, or why it has none"),
        (1, "`Lanes/Outside/M.lean` has no row under Outside models: name its oracle, or why it has none")])]

def changelog : String :=
  "# Changelog\n\nIntro.\n\n## [Unreleased]\n\nNote.\n\n## [0.1.0] - 2026-01-01\n\nOld.\n"

def changelogTests (root : System.FilePath) : IO (List (String × Bool)) := do
  project root
  discard <| lint root { fix := true }
  write root "CHANGELOG.md" (changelog.replace "Note.\n" "Note.\n\n- A line here.\n")
  write root "docs/changes/README.md" "# Unreleased changes\n\nNot a fragment.\n"
  write root "docs/changes/good.md" "### Added\n\n- Good.\n"
  write root "docs/changes/bad.md" "### Improved\n\n- Bad.\n"
  let report ← lint root { fix := true }
  let found := (report.findings.filter (·.rule == "changelog")).map fun f => (f.file.toString, f.line)
  let parsed := Changelog.parse "### Added\n\n- One.\n  Continued.\n\n### Fixed\n\n- Two.\n"
  let refused := fun text => match Changelog.parse text with
    | .error (line, _) => some line
    | .ok _ => none
  let a : Changelog.Fragment := [("Fixed", ["- A fix."]), ("Added", ["- A."])]
  let b : Changelog.Fragment := [("Added", ["- B."])]
  return [
    ("lint changelog: a fragment that does not read, and an entry in CHANGELOG.md's Unreleased "
        ++ "section, are reported; the folder's README is no fragment",
      found == [("docs/changes/bad.md", 1), ("CHANGELOG.md", 9)]),
    ("Changelog.parse: sections in order, an entry with its next line",
      parsed matches .ok [("Added", ["- One.\n  Continued."]), ("Fixed", ["- Two."])]),
    ("Changelog.parse: an entry before a heading, a heading with no entry, another section's name "
        ++ "and a line of text are refused at their lines",
      refused "- No heading.\n" == some 1 && refused "### Added\n" == some 1
        && refused "### Improved\n- x\n" == some 1 && refused "### Added\n- x\nText.\n" == some 3),
    ("Changelog.assemble: each section once, in Keep a Changelog's order, the fragments in order",
      Changelog.assemble [a, b] == "### Added\n\n- A.\n- B.\n\n### Fixed\n\n- A fix.\n"),
    ("Changelog.insertRelease: the release goes after the Unreleased section's text",
      (Changelog.insertRelease changelog "0.2.0" "2026-02-01" "### Added\n\n- New.\n").toOption
        == some ("# Changelog\n\nIntro.\n\n## [Unreleased]\n\nNote.\n\n## [0.2.0] - 2026-02-01\n\n"
          ++ "### Added\n\n- New.\n\n## [0.1.0] - 2026-01-01\n\nOld.\n"))]

/-- Lint `schema` finds the project's pinned files, not another package's, and reads what the
program printed. -/
def schemaTests (root : System.FilePath) : IO (List (String × Bool)) := do
  for path in ["a.schema", "sub/b.schema", ".hidden/c.schema", "docs/d.schema"] do
    write root path "kind: journal\n"
  write root "sub/lakefile.toml" "name = \"sub\"\n"
  let found ← Schemas.files root
  let s := Lanes.Schema.nat
  let t := Lanes.Schema.list .string
  let text := Lanes.Journal.schemaText
  let out := "\n".intercalate ["noise", s!"lanes-pin 0 {text s}", s!"lanes-pin 1 {text t}",
    s!"lanes-migration 1 {text s} {text t}"]
  return [
    ("lint schema: the pinned files are the project's, not another package's nor a hidden one's",
      found == ["a.schema", "docs/d.schema"]),
    ("lint schema: each pinned file's schema and migrations are read from what Lean printed",
      Schemas.readOutput 3 out == [(some s, []), (some t, [some (s, t)]), (none, [])]) ]

def tests : IO (List (String × Bool)) := do
  let root ← scratch
  let other ← scratch
  let third ← scratch
  let fourth ← scratch
  let fifth ← scratch
  let sixth ← scratch
  try
    let results := (← fixTests root) ++ (← problemTests other) ++ (← linkTests third)
      ++ (← oracleTests fourth) ++ (← changelogTests fifth) ++ (← schemaTests sixth)
    return results ++ [
      ("withCommas", Generated.withCommas 1587 == "1,587" && Generated.withCommas 50 == "50"
        && Generated.withCommas 1000000 == "1,000,000"),
      ("replaceName: a reference is rewritten, the end of another name is not",
        Generated.replaceName "D4-new-one.md, `new-one.md` (new-one.md)" "new-one.md" "D5-one.md"
          == "D4-new-one.md, `D5-one.md` (D5-one.md)"),
      ("indexText: the index is sorted by slug, each line with its number",
        Generated.indexText none [⟨"D1-zeta.md", some 1, "zeta", "Zeta", "\nStatus: Accepted"⟩,
            ⟨"D2-alpha.md", some 2, "alpha", "Alpha", "\nStatus: Accepted"⟩,
            ⟨"new-beta.md", none, "beta", "Beta", "\nStatus: Accepted"⟩]
          == "# Decisions\n\n## Index\n\n### Current\n\n- [D2. Alpha](D2-alpha.md)\n"
            ++ "- [D1. Zeta](D1-zeta.md)\n"),
      ("countless: an entry whose count a merge dropped is found, prose after a comma is not",
        Generated.countless "| a | `A/B.lean`,  lines  It | `C.c`, 12 lines | `T.lean`, against x |"
          == ["A/B.lean"]),
      ("--json: a string is quoted with JSON's escapes",
        jsonString "a \"b\"\\\n\x01" == "\"a \\\"b\\\"\\\\\\n\\u0001\""),
      ("--json: a `sorry` is a proof's failure, a failed inventory a build's, the rest checks",
        (Finding.mk "A.lean" 3 "no-sorry" "x").kind == "proof"
          && (Finding.mk "docs/INVENTORY.md" 1 "inventory" "`lake exe lanesInventory` failed: y").kind
            == "build"
          && (Finding.mk "B.md" 1 "links" "z").kind == "check"),
      ("--json: the report gives the files, what was fixed, and each finding with its place",
        (Report.mk [⟨"A.lean", 3, "no-sorry", "no"⟩] [] 2).json
          == "{\"files\":2,\"fixed\":[],\"failed\":1,\"results\":[{\"name\":\"no-sorry\",\"kind\":\"proof\",\"status\":\"failed\",\"path\":\"A.lean\",\"line\":3,\"detail\":\"no\"}]}")]
  finally
    for dir in [root, other, third, fourth, fifth, sixth] do
      if ← dir.pathExists then IO.FS.removeDirAll dir

end Tests.Lint
