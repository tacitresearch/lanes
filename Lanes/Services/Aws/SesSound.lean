/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Services.Aws.Ses
public import Lanes.Lib.Encoding.Json.ParserSound
public import Lanes.Lib.Encoding.Json.BasicSound

/-!
The request SES is sent is JSON that reads back with exactly the recipients given: the
document is within the reader's limits, so `Json.parse_compress` reads it back, and the
recipients survive `Json.normalize`.
-/

@[expose] public section

namespace Aws.Ses

open Lanes

theorem depth_strs (l : List String) :
    (l.map Json.str).foldl (fun d (e : Json) => max d e.depth) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a rest ih => simpa [Json.depth] using ih

theorem digits_strs (l : List String) :
    (l.map Json.str).foldl (fun d (e : Json) => max d e.digits) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a rest ih => simpa [Json.digits] using ih

theorem depth_document (m : Message) : (document m).depth ≤ 128 := by
  cases hb : m.body <;>
    simp [document, destination, content, bodyFields, hb, Json.depth, depth_strs]

theorem digits_document (m : Message) : (document m).digits ≤ 1000 := by
  cases hb : m.body <;>
    simp [document, destination, content, bodyFields, hb, Json.digits, digits_strs]

/-- The body sent is JSON, which reads back as the document. -/
theorem json_parse (m : Message) : Json.parse (json m) = .ok (document m).normalize :=
  Json.parse_compress _ (depth_document m) (digits_document m)

theorem normalize_strs (l : List String) :
    (Json.arr (l.map Json.str).toArray).normalize = .arr (l.map Json.str).toArray := by
  simp [Json.normalize]

theorem mapM_getStr (l : List String) : (l.map Json.str).mapM Json.getStr? = .ok l := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp [Json.getStr?, ih]; rfl

/-- What SES reads as the recipients of the body sent is exactly the recipients given, in order. -/
theorem toAddresses_json (m : Message) :
    ∃ j, Json.parse (json m) = .ok j ∧ toAddresses j = .ok (m.to.val.map (·.val)) := by
  refine ⟨_, json_parse m, ?_⟩
  have hdest : (document m).normalize.getObjVal? "Destination" = .ok (destination m.to).normalize := by
    rw [document, Json.normalize]
    exact Json.getObjVal?_mkObj.mpr (by simp)
  have hto : (destination m.to).normalize.getObjVal? "ToAddresses" =
      .ok (.arr ((m.to.val.map (·.val)).map Json.str).toArray) := by
    rw [destination, Json.normalize]
    refine Json.getObjVal?_mkObj.mpr ?_
    simpa using normalize_strs m.to.val.unattach
  simp only [toAddresses, hdest, hto, bind, Except.bind, Json.getArr?]
  exact mapM_getStr _

end Aws.Ses
