/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Transcode
public import Lanes.Web.Auth.Token
public import Lanes.Web.Http.Basic
public import Lanes.Lib.Encoding.Json
public import Lanes.Proof.Utf8

/-!
# A transcode worker over HTTP

The wire format of a worker that is not a vendor's (`Lanes.Transcode`, D61): a job is a JSON
object posted to the worker, and the worker posts its report back as JSON to the callback the
job names. Both carry a signature in the `lanes-signature` header, the HMAC-SHA-256 tag of a
text under a key the caller and the worker share (`Auth.tag`):

- a job, `{"callback":…,"id":…,"source":…,"targets":[…]}`, is signed over its body, for the
  purpose `transcode-job`. Its targets are, in order, the playable rendition (MP4) and the
  thumbnail (JPEG) the worker writes to the store the source is in.
- a report, `{"job":…,"status":"done","written":[…]}` or `{"job":…,"status":"failed"}`, is
  signed over its job and its status, one line each (`signed`), for the purpose `transcode`.
  That is all a caller acts on, and a worker computes it from its fields however it writes its
  JSON, as SNS signs a canonical string of its fields.

A caller checks a report's signature with `verify`, which accepts exactly the tag `signature`
gives (`verify_iff`). That nobody without the key makes one is the assumption `TRUSTED.md`
makes of HMAC-SHA-256. The functions here only build and read: the call is the application's.
-/

@[expose] public section

namespace Lanes.Transcode

open Lanes.Http

def signatureHeader : String := "lanes-signature"

def Report.status {J K : Type} : Report J K → String
  | .done .. => "done"
  | .failed _ => "failed"

/-- The text a report's signature is over: its job and its status. -/
def signed (job status : String) : String := job ++ "\n" ++ status

def signature (key : Hmac.Key) (job status : String) : String :=
  Auth.tag key "transcode" (signed job status)

/-- Whether `sig` is the signature of a report of `job` with `status`, compared in time that does
not depend on where they differ. -/
def verify (key : Hmac.Key) (job status sig : String) : Bool :=
  Bytes.same (signature key job status).toUTF8 sig.toUTF8

private theorem eq_of_toUTF8 {s t : String} (h : s.toUTF8 = t.toUTF8) : s = t := by
  rw [String.toUTF8_eq_toByteArray, String.toUTF8_eq_toByteArray] at h
  exact toByteArray_inj.mp h

/-- `verify` accepts exactly the signature `signature` gives. -/
theorem verify_iff {key : Hmac.Key} {job status sig : String} :
    verify key job status sig = true ↔ sig = signature key job status := by
  rw [verify, Bytes.same_iff]
  exact ⟨fun h => (eq_of_toUTF8 h).symm, fun h => h ▸ rfl⟩

theorem verify_signature (key : Hmac.Key) (job status : String) :
    verify key job status (signature key job status) = true :=
  verify_iff.mpr rfl

/-! ## A job -/

def jobJson (job : Job String String) (callback : String) : Json :=
  Json.mkObj [("id", .str job.id), ("source", .str job.source),
    ("targets", .arr (job.targets.map Json.str).toArray), ("callback", .str callback)]

def jobBody (job : Job String String) (callback : String) : String :=
  Json.compress (jobJson job callback)

def jobSignature (key : Hmac.Key) (body : String) : String := Auth.tag key "transcode-job" body

/-- The request that posts `job` to a worker's `path`, with the callback its report goes to. -/
def jobRequest (key : Hmac.Key) (path : List String) (job : Job String String) (callback : String) :
    Http.Request :=
  let body := jobBody job callback
  { method := .post, path
    headers := [("content-type", "application/json"), (signatureHeader, jobSignature key body)]
    body := body.toUTF8 }

/-- The string field `name` of an object. -/
def field? (j : Json) (name : String) : Option String :=
  (j.getObjVal? name >>= Json.getStr?).toOption

/-- A job and its callback, as a worker reads a request's body. -/
def readJob? (body : String) : Option (Job String String × String) := do
  let j ← (Json.parse body).toOption
  let targets ← (j.getObjVal? "targets" >>= Json.getArr?).toOption
  let targets ← targets.toList.mapM fun t => (Json.getStr? t).toOption
  return (⟨← field? j "id", ← field? j "source", targets⟩, ← field? j "callback")

/-! ## A report -/

def reportJson : Report String String → Json
  | .done job written =>
    Json.mkObj [("job", .str job), ("status", .str "done"),
      ("written", .arr (written.map Json.str).toArray)]
  | .failed job => Json.mkObj [("job", .str job), ("status", .str "failed")]

def reportBody (r : Report String String) : String := Json.compress (reportJson r)

/-- A report, as a caller reads a webhook's body. -/
def readReport? (body : String) : Option (Report String String) := do
  let j ← (Json.parse body).toOption
  let job ← field? j "job"
  match ← field? j "status" with
  | "done" =>
    let written ← (j.getObjVal? "written" >>= Json.getArr?).toOption
    return .done job (← written.toList.mapM fun t => (Json.getStr? t).toOption)
  | "failed" => return .failed job
  | _ => none

/-- The request a worker posts `r` with, signed, to the callback's `path`. -/
def reportRequest (key : Hmac.Key) (path : List String) (r : Report String String) : Http.Request :=
  { method := .post, path
    headers := [("content-type", "application/json"),
      (signatureHeader, signature key r.job r.status)]
    body := (reportBody r).toUTF8 }

end Lanes.Transcode
