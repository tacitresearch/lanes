/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Base64
import Tests.Oracle.Ip
import Tests.Oracle.Jose
import Tests.Oracle.Json
import Tests.Oracle.MediaType
import Tests.Oracle.Metrics
import Tests.Oracle.Multipart
import Tests.Oracle.RateLimit
import Tests.Oracle.SigV4
import Tests.Oracle.Time
import Tests.Oracle.Url
import Tests.Oracle.Xml

/-! The packages compared with Go, and the replay of their recorded answers for `lake test`. -/

namespace Tests.Oracle

def packages : List Package :=
  [Base64.package, Ip.package, Time.package, Json.package, MediaType.package, RateLimit.package,
    Url.package, Xml.package, Metrics.package, SigV4.package, Jose.package,
    Multipart.package]

def unitTests : List (String × Bool) := Base64.tests ++ Ip.tests ++ Jose.tests ++ MediaType.tests ++ RateLimit.tests ++ Time.tests ++ Url.tests

def replayAll : IO (List (String × Bool)) :=
  return (← packages.mapM Package.replay).flatten

end Tests.Oracle
