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

/-- `native/lanes.c`: SHA-256, HMAC, a comparison and Argon2id from the OpenSSL that `native/tls.c`
uses, declared in the same way, and `fsync` and a timed wait. -/
target native pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "native" / "lanes.c")
  buildO (pkg.buildDir / "native" / "lanes.o") src
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC", "-DNDEBUG", "-Wall"]

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

/-- `native/sign.c`, signatures made by the same OpenSSL with a private key, declared in the same way. -/
target sign pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "native" / "sign.c")
  buildO (pkg.buildDir / "native" / "sign.o") src
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC", "-DNDEBUG", "-Wall"]

@[default_target]
lean_lib Lanes where
  roots := #[`Lanes, `Lanes.Proofs, `Lanes.Semantics, `Lanes.Testing]
  moreLinkObjs := #[native, tls, verify, sign]

@[default_target]
lean_lib Tests where
  globs := #[.submodules `Tests]

@[default_target]
lean_exe lanesTest where
  root := `Tests.Main
  needs := #[`@/lanesStopChild]

/-- The process the stop test of `lanesTest` stops: a binary of its own, which imports `Lanes`
alone, so that each start is not the initialisation of every test module. -/
lean_exe lanesStopChild where
  root := `Tests.StopChild

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
