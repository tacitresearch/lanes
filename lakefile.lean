import Lake
open Lake DSL System

/-! A Lake file in Lean rather than TOML because TOML cannot build C. -/

package lanes where
  version := v!"0.1.0"
  description := "Verified software in Lean 4: actors with pure step functions, a model checker, proofs and a runtime"
  keywords := #["software-verification", "actors", "model-checking", "distributed-systems", "web"]
  license := "Apache-2.0"
  testDriver := "lanesTest"
  -- Lake's local artifact cache (D99, section 6): each output is stored once per toolchain, by
  -- its content, and shared by every checkout and application on the machine (AGENTS.md, "Build
  -- and checks"). A dependency that sets neither option takes the workspace root's.
  enableArtifactCache := true
  -- The outputs are also hard-linked into `.lake/build`, where `lake exe`, `lanes lint`,
  -- `docs/api`, CI's caches and the scripts read them.
  restoreAllArtifacts := true
  -- No remote cache yet (#98). It goes here: `downloadCacheService := "<name>"`, with a
  -- `cache_service <name> := …` declared below the package.

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
  -- The services and the optional parts of the standard library are roots of their own, not
  -- imported by `Lanes`: a program that does not import one does not build it or link it.
  roots := #[`Lanes, `Lanes.Proofs, `Lanes.Semantics, `Lanes.Testing, `Lanes.Services,
    `Lanes.Services.S3.Testing, `Lanes.Lib.Encoding.Csv, `Lanes.Lib.Encoding.CsvSound, `Lanes.Lib.Path,
    `Lanes.Lib.PathSound, `Lanes.Lib.Glob, `Lanes.Web.Html.Sanitize, `Lanes.Web.Html.SanitizeSound,
    `Lanes.Web.Http.WebSocket, `Lanes.Web.Http.WebSocketSound]
  moreLinkObjs := #[native, tls, verify, sign]

/-! Files that modules embed with `include_str`, which Lake does not track. A library that `needs`
them mixes their hashes into each of its modules' traces, so that neither `.lake/build` nor the
artifact cache serves a module built from older copies. A new `include_str` adds its file here. -/

/-- The template of `lanes new`, embedded by `LanesCli.New` and `Tests.New`. -/
input_dir templates where
  text := true

/-- The `lean-toolchain` that `LanesCli.New` copies into a new app. -/
input_file leanToolchain where
  path := "lean-toolchain"
  text := true

/-- The test keys `Tests.Sign` and `Tests.Aws.CloudFront` embed. -/
input_dir botocoreKeys where
  path := "oracles/botocore/keys"
  text := true

/-- Google's discovery document and keys as recorded, which `Tests.Oidc.Google` embeds. -/
input_dir googleRecorded where
  path := "oracles/google"
  text := true

@[default_target]
lean_lib Tests where
  globs := #[.submodules `Tests]
  needs := #[`@/templates, `@/botocoreKeys, `@/googleRecorded]

@[default_target]
lean_exe lanesTest where
  root := `Tests.Main
  needs := #[`@/lanesStopChild]

/-- The process the stop test of `lanesTest` stops: a binary of its own, which imports `Lanes`
alone, so that each start is not the initialisation of every test module. -/
lean_exe lanesStopChild where
  root := `Tests.StopChildMain

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
  needs := #[`@/templates, `@/leanToolchain]

/-- The `lanes` command. -/
@[default_target]
lean_exe lanes where
  root := `LanesCli.Main
