/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Behaviours.Jobs.IO.Pool
public import Lanes.Web.IO.Client

/-!
A worker of the jobs pool (`Lanes/Behaviours/Jobs/IO/Pool.lean`) that calls another service
through the HTTP client (`Jobs.call`). It sends the job's key with every attempt, so the service
can tell a retry from a new request.
-/

public section

namespace Lanes.Jobs

open Std Std.Async

variable {K : Type}

/-- The call with `name: value` among its headers, in place of any header of that name. -/
def withHeader (name value : String) (call : Http.Client.Call) : Http.Client.Call :=
  { call with request := { call.request with
      headers := (name, value) :: call.request.headers.filter
        fun (n, _) => n.toLower != name.toLower } }

/-- A worker that makes the call through the HTTP client, with the job's key in the header
`header`, the same for every attempt of the job. -/
def call (config : Http.Client.Config) (keyText : K → String)
    (header : String := "Idempotency-Key") : K → Nat → Http.Client.Call →
      Async (Option Http.Response) :=
  fun key _ job => Http.Client.exchange (withHeader header (keyText key) job) config

end Lanes.Jobs
