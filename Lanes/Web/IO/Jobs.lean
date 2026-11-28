/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.IO.Client

/-!
An attempt of a job whose work is a call to another service, through the HTTP client, for the
worker of a jobs table (`Postgres.Typed.Worker.start`): the job's id goes in the header `header`,
the same for every attempt of the job, so that the service can tell a repeat from a new request
and take it once.
-/

public section

namespace Lanes.Db.Jobs

open Std Std.Async

/-- The call with `name: value` among its headers, in place of any header of that name. -/
def withHeader (name value : String) (call : Http.Client.Call) : Http.Client.Call :=
  { call with request := { call.request with
      headers := (name, value) :: call.request.headers.filter
        fun (n, _) => n.toLower != name.toLower } }

/-- Make the call under the job's id, cut off at the attempt's deadline: the response, or `none`
when there is none. `keyPrefix` makes the key unique beyond the table (the table's name, say). -/
def http (config : Http.Client.Config) (keyPrefix : String) (header : String := "Idempotency-Key") :
    Int64 → Nat → Http.Client.Call → Async (Option Http.Response) :=
  fun id deadline_ms call =>
    Http.Client.exchange (withHeader header s!"{keyPrefix}{id}" call) { config with timeout_ms := deadline_ms }

end Lanes.Db.Jobs
