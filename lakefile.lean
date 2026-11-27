import Lake
open Lake DSL System

/-! A Lake file in Lean rather than TOML because TOML cannot build C. -/

package lanes where
  version := v!"0.1.0"
  description := "Verified software in Lean 4: actors with pure step functions, a model checker, proofs and a runtime"
  keywords := #["software-verification", "actors", "model-checking", "distributed-systems", "web"]
  license := "Apache-2.0"
  testDriver := "lanesTest"

require cslib from git "https://github.com/leanprover/cslib" @ "910210f7d155e22a2244591e394bd16fbb0ddbb3"

def needSodium : String :=
  "lanes links libsodium statically and finds it with pkg-config: install them \
  (apt-get install libsodium-dev pkg-config, or brew install libsodium pkg-config)"

def pkgConfigSodium (option : String) : FetchM String := do
  let some out ← captureProc? { cmd := "pkg-config", args := #[option, "libsodium"] }
    | error needSodium
  return out.trimAscii.toString

/-- `native/lanes.c`, compiled by the system's C compiler against its libsodium headers, which
Homebrew on Apple silicon puts outside the compiler's search path. -/
target native pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "native" / "lanes.c")
  let sodiumFlags := (← pkgConfigSodium "--cflags").splitOn " " |>.filter (· != "") |>.toArray
  buildO (pkg.buildDir / "native" / "lanes.o") src
    (#["-I", (← getLeanIncludeDir).toString] ++ sodiumFlags) #["-O2", "-fPIC", "-DNDEBUG", "-Wall"]

/-- `native/tls.c`, which declares the OpenSSL functions it calls itself: they come from the
OpenSSL that Lean's toolchain ships and links into every executable, which has no headers. -/
target tls pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "native" / "tls.c")
  buildO (pkg.buildDir / "native" / "tls.o") src
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC", "-DNDEBUG", "-Wall"]

/-- `native/verify.c`, a signature checked by the same OpenSSL, declared in the same way. -/
target verify pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "native" / "verify.c")
  buildO (pkg.buildDir / "native" / "verify.o") src
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC", "-DNDEBUG", "-Wall"]

/-- The system's libsodium, linked statically: a binary does not need it installed to run. -/
target sodium : FilePath := do
  let lib := FilePath.mk (← pkgConfigSodium "--variable=libdir") / "libsodium.a"
  unless ← lib.pathExists do
    error s!"lanes links libsodium statically, and {lib} is not there: install the static \
      library too (libsodium-static on Fedora)"
  inputBinFile lib

@[default_target]
lean_lib Lanes where
  roots := #[`Lanes, `Lanes.Proofs, `Lanes.Semantics]
  moreLinkObjs := #[native, tls, verify, sodium]

@[default_target]
lean_lib Tests where
  globs := #[.submodules `Tests]

@[default_target]
lean_exe lanesTest where
  root := `Tests.Main

@[default_target]
lean_exe lanesCheck where
  root := `Tests.CheckMain

/-- The pure oracles (`oracles/README.md`): ours against reference implementations; needs `go` and `python3`. -/
@[default_target]
lean_exe lanesOracle where
  root := `Tests.OracleMain

/-- The service oracles (`oracles/README.md`): our clients against real or reference services,
checked against our models of them; each skipped unless its service is named. -/
@[default_target]
lean_exe lanesServiceOracle where
  root := `Tests.ServiceMain

lean_lib LanesCli where
  globs := #[.submodules `LanesCli]

/-- The `lanes` command. -/
@[default_target]
lean_exe lanes where
  root := `LanesCli.Main

/-- `docs/INVENTORY.md`. It links `Lean` and reads the built modules, so it builds them first. -/
@[default_target]
lean_exe lanesInventory where
  root := `LanesCli.InventoryMain
  needs := #[`@/Lanes, `@/Tests, `+LanesCli.Main]
