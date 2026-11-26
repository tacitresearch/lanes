import Lake
open Lake DSL System

/-! A Lake file in Lean rather than TOML because TOML cannot build C. -/

package lanes where
  version := v!"0.1.0"
  testDriver := "lanesTest"

require cslib from git "https://github.com/leanprover/cslib" @ "910210f7d155e22a2244591e394bd16fbb0ddbb3"

/-- `native/lanes.c`, compiled by the system's C compiler against its libsodium headers. -/
target native pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "native" / "lanes.c")
  buildO (pkg.buildDir / "native" / "lanes.o") src #["-I", (← getLeanIncludeDir).toString]
    #["-O2", "-fPIC", "-DNDEBUG", "-Wall"]

/-- The system's libsodium, linked statically: a binary does not need it installed to run. -/
target sodium : FilePath := do
  let some dir ← captureProc? { cmd := "pkg-config", args := #["--variable=libdir", "libsodium"] }
    | error "lanes needs libsodium and pkg-config: install libsodium-dev and pkg-config"
  inputBinFile (FilePath.mk dir.trimAscii.toString / "libsodium.a")

@[default_target]
lean_lib Lanes where
  roots := #[`Lanes, `Lanes.Semantics]
  moreLinkObjs := #[native, sodium]

@[default_target]
lean_lib Examples

@[default_target]
lean_lib Tests where
  globs := #[.submodules `Tests]

@[default_target]
lean_exe lanesTest where
  root := `Tests.Main

@[default_target]
lean_exe lanesCheck where
  root := `Tests.CheckMain

@[default_target]
lean_exe bankWeb where
  root := `Examples.BankWebMain

lean_lib LanesCli where
  globs := #[.submodules `LanesCli]

/-- The `lanes` command. -/
@[default_target]
lean_exe lanes where
  root := `LanesCli.Main
