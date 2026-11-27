/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Testing.Http
public import Lanes.Testing.Browser
public import Lanes.Testing.S3
public import Lanes.Testing.OAuth

/-!
The test kit: what an application's tests run against, imported as `Lanes.Testing` beside
`Lanes`, and never by `import Lanes`, so no deployed binary links it
(`docs/decisions/new-a-test-kit.md`). A fake S3 that checks signatures, a fake identity
provider, a scripted browser, and helpers for HTTP.
-/
