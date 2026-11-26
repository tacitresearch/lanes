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

def tests : IO (List (String × Bool)) := do
  let root ← scratch
  let other ← scratch
  try
    let results := (← fixTests root) ++ (← problemTests other)
    return results ++ [
      ("withCommas", Generated.withCommas 1587 == "1,587" && Generated.withCommas 50 == "50"
        && Generated.withCommas 1000000 == "1,000,000"),
      ("replaceName: a reference is rewritten, the end of another name is not",
        Generated.replaceName "D4-new-one.md, `new-one.md` (new-one.md)" "new-one.md" "D5-one.md"
          == "D4-new-one.md, `D5-one.md` (D5-one.md)"),
      ("roundedTotal", Generated.roundedTotal 1587 == 1600 && Generated.roundedTotal 1574 == 1550)]
  finally
    for dir in [root, other] do
      if ← dir.pathExists then IO.FS.removeDirAll dir

end Tests.Lint
