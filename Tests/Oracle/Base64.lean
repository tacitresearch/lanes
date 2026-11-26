/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic

/-! `Lanes.Base64` against RFC 4648 §10 and against Go's strict `encoding/base64`. -/

namespace Tests.Oracle.Base64

open Lanes Lanes.Base64

def encodings : List (String × Encoding) :=
  [("std", .std), ("rawstd", .rawStd), ("url", .url), ("rawurl", .rawUrl)]

def rfc : List (String × String) :=
  [("", ""), ("f", "Zg=="), ("fo", "Zm8="), ("foo", "Zm9v"), ("foob", "Zm9vYg=="),
    ("fooba", "Zm9vYmE="), ("foobar", "Zm9vYmFy")]

def tests : List (String × Bool) :=
  [ ("base64: RFC 4648 §10 encodes",
      rfc.all fun (plain, coded) => encode .std plain.toUTF8 == coded),
    ("base64: RFC 4648 §10 decodes",
      rfc.all fun (plain, coded) => (decode .std coded).map (·.data) == some plain.toUTF8.data),
    ("base64: the URL alphabet and no padding",
      encode .rawUrl ⟨#[0xfb, 0xff]⟩ == "-_8" && encode .std ⟨#[0xfb, 0xff]⟩ == "+/8="),
    ("base64: refused: bad padding, trailing bits, outside the alphabet, a newline",
      ["Zg", "Zg=", "Zg===", "Zh==", "Zm9=", "Zm9v\n", "Zm 9v", "Zm9v====", "=Zm9", "Zg==Zg=="].all
        fun s => (decode .std s).isNone),
    ("base64: refused without padding: a pad, one character left over",
      ["Zg==", "Z", "Zm9vY", "Zh"].all fun s => (decode .rawStd s).isNone) ]

def alphabet : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/-_=".toList
    ++ ['\n', '\r', ' ', '.', '\x00', 'é', '=']

def answer (c : Case) : Answer :=
  match c.op.splitOn "-", encodings.lookup ((c.op.splitOn "-").getD 1 "") with
  | ["encode", _], some e => some (.str (encode e c.input))
  | ["decode", _], some e =>
    (String.fromUTF8? c.input).bind (decode e) |>.map fun b => .str (Bytes.hex b)
  | _, _ => none

def case : Gen Case := do
  let (name, _) ← Gen.pick encodings
  if ← Gen.chance 20 then return ⟨s!"encode-{name}", ← Gen.bytes 40⟩
  let (_, other) ← Gen.pick encodings
  let valid := encode other (← Gen.bytes 30)
  let s ← match ← Gen.below 4 with
    | 0 => pure valid
    | 1 | 2 => Gen.mutate alphabet valid
    | _ => Gen.text alphabet 12
  return text s s!"decode-{name}"

/-- Go skips `\r` and `\n` anywhere in the input, even when strict. -/
def skipsNewlines (c : Case) (go : Answer) : Bool :=
  let stripped : Case := ⟨c.op, ⟨c.input.data.filter fun b => b != 10 && b != 13⟩⟩
  c.input.data.any (fun b => b == 10 || b == 13) && answer stripped == go

def package : Package where
  name := "base64"
  edges := (rfc.map fun (_, coded) => text coded "decode-std")
    ++ (rfc.map fun (plain, _) => text plain "encode-std")
    ++ (encodings.map fun (name, _) => text "Zm9vYg" s!"decode-{name}")
  case := case
  answer := answer
  known c go := if skipsNewlines c go then some "Go skips \\r and \\n in the input" else none

end Tests.Oracle.Base64
