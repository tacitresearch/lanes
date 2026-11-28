/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Service.S3
import Tests.Oracle.Service.S3Post
import Tests.Oracle.Service.S3Multipart
import Tests.Oracle.Service.Postgres
import Tests.Oracle.Service.Db

/-! The service oracles of Lanes, and the check of their records for `lake test`. -/

namespace Tests.Oracle.Service

def oracles : List Oracle :=
  [S3.oracle, S3Post.oracle, S3Multipart.oracle, Postgres.oracle, Typed.oracle]

def replayAll : IO (List (String × Bool)) :=
  return (← oracles.mapM (·.replayFile)).flatten

end Tests.Oracle.Service
