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

def page : String :=
  "# Status\n\n| Area | What |\n| --- | --- |\n<!-- rows: areas -->\n\n| App | What |\n"
    ++ "| --- | --- |\n<!-- rows: apps -->\n\n## Known limits\n\n<!-- limits -->\n"

def project (root : System.FilePath) : IO Unit := do
  write root "Shell.lean" (String.join (List.replicate 60 "-- a line\n"))
  write root "TRUSTED.md" "| The shell | `Shell.lean`, 7 lines | |\n"
  write root "README.md" "About 1,150 lines of trusted code.\n"
  write root "docs/decisions/README.md" "# Decisions\n\nPreamble.\n"
  write root "docs/decisions/D1-first.md" "# D1. First\n\nText.\n"
  write root "docs/decisions/D2-second.md" "# D2. Second, `code`\n\nMore text.\n"
  write root "docs/decisions/new-third.md" "# D?. Third\n\nNewest, after `new-third.md`.\n"
  write root "docs/status/page.md" page
  write root "docs/status/areas/runtime.md"
    "| Runtime | a kernel (`docs/decisions/new-third.md`) |\n\n- Runtime limit.\n  Continued.\n"
  write root "docs/status/areas/actors.md" "| Actors | `Actor` |\n"
  write root "docs/status/apps/bank.md" "| Bank | conserves money |\n\n- Bank limit.\n"

def expectedStatus (third : String) : String :=
  Generated.generatedNote ++ "\n# Status\n\n| Area | What |\n| --- | --- |\n"
    ++ "| Actors | `Actor` |\n"
    ++ s!"| Runtime | a kernel (`docs/decisions/{third}`) |\n\n| App | What |\n| --- | --- |\n"
    ++ "| Bank | conserves money |\n\n## Known limits\n\n"
    ++ "- Runtime limit.\n  Continued.\n- Bank limit.\n"

def expectedIndex (third : Bool) : String :=
  "# Decisions\n\nPreamble.\n\n## Index\n\n- [D1. First](D1-first.md)\n"
    ++ "- [D2. Second, `code`](D2-second.md)\n"
    ++ (if third then "- [D3. Third](D3-third.md)\n" else "")

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
  let status ← read root "docs/STATUS.md"
  let index ← read root "docs/decisions/README.md"
  let unnumbered ← lint root { main := true }
  let numbered ← lint root { fix := true, main := true }
  let numberedAgain ← lint root { fix := true, main := true }
  let third ← read root "docs/decisions/D3-third.md"
  let gone := !(← (root / "docs/decisions/new-third.md").pathExists)
  let statusAfter ← read root "docs/STATUS.md"
  let indexAfter ← read root "docs/decisions/README.md"
  return [
    ("lint: a wrong count, a stale total, index and status page are each reported",
      rules before == ["trusted-size", "trusted-size", "decisions", "status"]),
    ("lint --fix: no findings after it", fixed.findings.isEmpty && fixed.fixed.length == 4),
    ("lint --fix: a second run changes nothing", again.fixed.isEmpty && again.findings.isEmpty),
    ("lint --fix: the count is the file's", trusted == "| The shell | `Shell.lean`, 60 lines | |\n"),
    ("lint --fix: the total is rounded to 50", readme == "About 50 lines of trusted code.\n"),
    ("lint --fix: the status page has the rows by name and the limits after them",
      status == expectedStatus "new-third.md"),
    ("lint --fix: the index lists the numbered decisions, not a new one",
      index == expectedIndex false),
    ("lint --main: a decision without a number is reported",
      unnumbered.findings.any fun f => f.rule == "decisions"
        && f.file.toString == "docs/decisions/new-third.md"),
    ("lint --fix --main: the new decision is numbered, and its references, index and page follow",
      numbered.findings.isEmpty && gone
        && third == "# D3. Third\n\nNewest, after `D3-third.md`.\n" && statusAfter == expectedStatus "D3-third.md" && indexAfter == expectedIndex true),
    ("lint --fix --main: a second run changes nothing",
      numberedAgain.fixed.isEmpty && numberedAgain.findings.isEmpty)]

def problemTests (root : System.FilePath) : IO (List (String × Bool)) := do
  project root
  discard <| lint root { fix := true }
  write root "docs/decisions/D2-again.md" "# D2. Again\n"
  write root "docs/decisions/D4-wrong.md" "# D5. Wrong\n"
  write root "docs/decisions/notes.md" "# Notes\n"
  write root "docs/status/areas/broken.md" "Not a row.\n"
  let report ← lint root { fix := true }
  let decisions := report.findings.filter (·.rule == "decisions")
  return [
    ("lint: two decisions with one number, a heading that is not its file's and a stray file "
        ++ "are reported, and --fix leaves them",
      decisions.length == 4
        && (← (root / "docs/decisions/D2-again.md").pathExists)),
    ("lint: a status fragment that does not start with a row is reported",
      report.findings.any fun f => f.rule == "status"
        && f.file.toString == "docs/status/areas/broken.md")]

def citing : String :=
  "See `Lanes/A.lean`, `Lanes/{A,B}.lean` and `Lanes/`.\n"
    ++ "Gone: `Lanes/Gone.lean`, and `Lanes/{A,Lost}.lean`.\n"
    ++ "Not paths: `net/http`, `Lanes.A`, `docs/status/<area>.md`, `Lanes/*.lean`, `a / b`, "
    ++ "`https://example.com/x`, `/dev/urandom`, `.lake/packages`.\n"
    ++ "```bash\nlake env lean Lanes/InAFence.lean\n```\n"
    ++ "A span `across\nlines` keeps the rest paired: `Lanes/Missing/`.\n"

def linkTests (root : System.FilePath) : IO (List (String × Bool)) := do
  project root
  discard <| lint root { fix := true }
  write root "Lanes/A.lean" ""
  write root "Lanes/B.lean" ""
  write root "README.md" ("About 50 lines of trusted code.\n" ++ citing)
  write root "docs/GUIDE.md" "Cites `Lanes/Nowhere.lean`.\n"
  write root "docs/status/areas/actors.md" "| Actors | `Lanes/Away.lean` |\n"
  write root "docs/history/old.md" "Was `Lanes/Old.lean`.\n"
  write root "docs/decisions/D3-past.md" "# D3. Past\n\nWas `Lanes/Past.lean`.\n"
  let report ← lint root { fix := true }
  let links := report.findings.filter (·.rule == "links")
  let found := links.map fun f => (f.file.toString, f.line, f.message)
  return [
    ("lint links: a missing path is reported, at its file and line, and one in braces by name",
      found == [("README.md", 3, "`Lanes/Gone.lean` does not exist"),
        ("README.md", 3, "`Lanes/Lost.lean` does not exist"),
        ("README.md", 9, "`Lanes/Missing/` does not exist"),
        ("docs/GUIDE.md", 1, "`Lanes/Nowhere.lean` does not exist"),
        ("docs/status/areas/actors.md", 1, "`Lanes/Away.lean` does not exist")]),
    ("lint links: the history, the decisions and the generated status page are not checked",
      !links.any fun f => f.file.toString.startsWith "docs/history"
        || f.file.toString.startsWith "docs/decisions" || f.file.toString == "docs/STATUS.md"),
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

def tests : IO (List (String × Bool)) := do
  let root ← scratch
  let other ← scratch
  let third ← scratch
  let fourth ← scratch
  try
    let results := (← fixTests root) ++ (← problemTests other) ++ (← linkTests third)
      ++ (← oracleTests fourth)
    return results ++ [
      ("withCommas", Generated.withCommas 1587 == "1,587" && Generated.withCommas 50 == "50"
        && Generated.withCommas 1000000 == "1,000,000"),
      ("replaceName: a reference is rewritten, the end of another name is not",
        Generated.replaceName "D4-new-one.md, `new-one.md` (new-one.md)" "new-one.md" "D5-one.md"
          == "D4-new-one.md, `D5-one.md` (D5-one.md)"),
      ("roundedTotal", Generated.roundedTotal 1587 == 1600 && Generated.roundedTotal 1574 == 1550)]
  finally
    for dir in [root, other, third, fourth] do
      if ← dir.pathExists then IO.FS.removeDirAll dir

end Tests.Lint
