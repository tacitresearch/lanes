/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Http.ReadRequest

/-!
What the request reader of `Lanes.Http.ReadRequest` does, for every input and every limit.
-/

@[expose] public section

namespace Lanes.Http

namespace Request

/-- Whether what `wire` writes of `r` for `host` is within `limits`, and is a request the
reader can give back as it was: a host the reader takes, and a path other than `[""]`, which is
written as `/` like the empty path. -/
def fits (limits : Limits) (r : Request) (host : String) : Bool :=
  ((r.head host).headD "").utf8ByteSize ≤ limits.line_max
    && ("\r\n".intercalate (r.head host)).utf8ByteSize + 4 ≤ limits.head_max
    && (r.fields host).length ≤ limits.fields_max
    && r.body.size ≤ limits.body_max && r.body.size < 10 ^ 18
    && host.toList.all hostChar && r.path != [""]

/-- What the reader gives back of the bytes `wire` writes of `r` for `host`: the writer's own
headers and the caller's that are written, in lowercase and without the blanks around their
values. -/
def sent (r : Request) (host : String) : Incoming where
  request := { r with
    headers := (r.fields host).map fun (name, value) =>
      (name.toLower, String.ofList (trimOws value.toList)) }
  headOnly := false
  close := true

end Request

end Lanes.Http
