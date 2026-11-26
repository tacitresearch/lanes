/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic

/-! `Lanes.Ip` against RFC 5952's examples and against Go's `net/netip`. -/

namespace Tests.Oracle.Ip

open Lanes Lanes.Ip

def canonical (s : String) : Option String := (parse s).map print

def prefixText (s : String) : Option (String × String) :=
  (Prefix.parse s).map fun p => (p.print, p.masked.print)

def contains (p a : String) : Option Bool := do
  return (← Prefix.parse p).contains (← parse a)

def tests : List (String × Bool) :=
  [ ("ip: RFC 5952 §4: leading zeros, the longest run, the leftmost of two, a lone zero",
      [("2001:0db8:0000:0000:0000:0000:0000:0001", "2001:db8::1"),
        ("2001:db8:0:1:1:1:1:1", "2001:db8:0:1:1:1:1:1"), ("2001:0:0:1:0:0:0:1", "2001:0:0:1::1"),
        ("2001:db8:0:0:1:0:0:1", "2001:db8::1:0:0:1"), ("2001:DB8::ABCD", "2001:db8::abcd"),
        ("::", "::"), ("::1", "::1"), ("1::", "1::"), ("1:2:3:4:5:6:7::", "1:2:3:4:5:6:7:0"),
        ("::ffff:192.0.2.1", "::ffff:192.0.2.1"), ("::ffff:c000:201", "::ffff:192.0.2.1"),
        ("::192.0.2.1", "::c000:201"), ("1:2:3:4:5:6:1.2.3.4", "1:2:3:4:5:6:102:304"),
        ("192.0.2.1", "192.0.2.1"), ("0.0.0.0", "0.0.0.0")].all
        fun (s, c) => canonical s == some c),
    ("ip: refused: leading zeros in IPv4, too few or many fields, two ::, zones",
      ["1.2.3.04", "1.2.3", "1.2.3.4.5", "256.1.1.1", ":::", "1::2::3", "fe80::1%eth0", "12345::",
        "1:2:3:4:5:6:7:8:9", "1:2:3:4:5:6:7::8", ":1::", "1:", "", "1.2.3.4::", "::1.2.3",
        "1:2:3:4:5:6:7:1.2.3.4", "1.2.3.4/8"].all fun s => (parse s).isNone),
    ("ip: prefixes are masked, and contain what shares their bits",
      prefixText "10.1.2.3/8" == some ("10.1.2.3/8", "10.0.0.0/8")
        && prefixText "2001:db8::1/32" == some ("2001:db8::1/32", "2001:db8::/32")
        && contains "10.1.2.3/8" "10.255.0.1" == some true
        && contains "10.1.2.3/8" "11.0.0.1" == some false
        && contains "::ffff:10.0.0.0/104" "10.0.0.1" == some false
        && (["10.0.0.0/33", "10.0.0.0/08", "10.0.0.0/", "10.0.0.0", "::/129"].all
          fun s => (Prefix.parse s).isNone)) ]

def answer (c : Case) : Answer :=
  match c.op, String.fromUTF8? c.input with
  | "parse", some s => (canonical s).map Json.str
  | "print", _ =>
    let n := Digits.join 256 (c.input.data.toList.map (·.toNat))
    if h : c.input.size = 4 ∧ n < 2 ^ 32 then some (.str (print (.v4 ⟨n, h.2⟩)))
    else if h : c.input.size = 16 ∧ n < 2 ^ 128 then some (.str (print (.v6 ⟨n, h.2⟩)))
    else none
  | "prefix", some s =>
    (prefixText s).map fun (t, m) => Json.mkObj [("text", (t : Json)), ("masked", (m : Json))]
  | "contains", some s =>
    match s.splitOn " " with
    | [p, a] => (contains p a).map Json.bool
    | _ => none
  | _, _ => none

def group : Gen Nat := do
  match ← Gen.below 5 with
  | 0 | 1 => return 0
  | 2 => return ← Gen.below 16
  | 3 => return ← Gen.below 4096
  | _ => return ← Gen.below 65536

def groups : Gen (List Nat) := do
  if ← Gen.chance 10 then return [0, 0, 0, 0, 0, 0xffff, ← Gen.below 65536, ← Gen.below 65536]
  Gen.list 8 group

def hexText (v : Nat) : Gen String := do
  let digits := Digits.toChars 16 v
  let extra := (← Gen.below (4 - digits.length + 1)) + (if ← Gen.chance 3 then 1 else 0)
  let padded := List.replicate extra '0' ++ digits
  let upper ← Gen.chance 30
  return String.ofList (padded.map fun c => if upper then c.toUpper else c)

def dotted (n : Nat) : String :=
  ".".intercalate ((Digits.split 256 4 n).map toString)

/-- A spelling of the groups that Go and RFC 4291 accept, or nearly. -/
def spelling (g : List Nat) : Gen String := do
  let texts ← g.mapM hexText
  let texts ← if ← Gen.chance 20 then
      pure (texts.take 6 ++ [dotted (g.getD 6 0 * 65536 + g.getD 7 0)])
    else pure texts
  let start ← Gen.below 8
  let run := ((g.drop start).takeWhile (· == 0)).length
  if run == 0 || (← Gen.chance 30) then return ":".intercalate texts
  let len := 1 + (← Gen.below run)
  let before := texts.take start
  let after := texts.drop (start + len)
  return ":".intercalate before ++ "::" ++ ":".intercalate after

def v4Text : Gen String := do
  let octets ← Gen.list 4 (Gen.below 256)
  let parts ← octets.mapM fun o => do
    if ← Gen.chance 5 then return "0" ++ toString o else return toString o
  return ".".intercalate parts

def alphabet : List Char := "0123456789abcdefABCDEFg:.%/ ".toList

def addrText : Gen String := do
  let s ← match ← Gen.below 4 with
    | 0 => v4Text
    | 1 => do return print (.v6 ⟨Digits.join 65536 (← groups) % 2 ^ 128, Nat.mod_lt _ (by decide)⟩)
    | _ => do spelling (← groups)
  match ← Gen.below 10 with
  | 0 | 1 | 2 => Gen.mutate alphabet s
  | 3 => return s ++ ["%eth0", "%", "%1"].getD (← Gen.below 3) ""
  | 4 => Gen.text alphabet 10
  | _ => return s

def bitsText : Gen String := do
  match ← Gen.below 10 with
  | 0 => return ["", "08", "+8", "-1", "0", "00", "129", "33"].getD (← Gen.below 8) ""
  | _ => return toString (← Gen.below 130)

def case : Gen Case := do
  match ← Gen.below 10 with
  | 0 | 1 => do
    let n := if ← Gen.chance 30 then 4 else 16
    let bytes ← Gen.list n (do
      if ← Gen.chance 50 then return (0 : UInt8) else return (← Gen.below 256).toUInt8)
    return ⟨"print", ⟨bytes.toArray⟩⟩
  | 2 | 3 => return text s!"{← addrText}/{← bitsText}" "prefix"
  | 4 => return text s!"{← addrText}/{← bitsText} {← addrText}" "contains"
  | _ => return text (← addrText) "parse"

def zone (c : Case) : Bool := c.input.data.contains '%'.toUInt8

def package : Package where
  name := "netip"
  edges := ["2001:0db8:0000:0000:0000:0000:0000:0001", "2001:0:0:1:0:0:0:1", "::ffff:192.0.2.1",
      "::192.0.2.1", "::", "1.2.3.04", "1::2::3", "1:2:3:4:5:6:7::", "fe80::1%eth0"].map
      (text · "parse")
    ++ ["10.1.2.3/8", "2001:db8::1/32", "10.0.0.0/08"].map (text · "prefix")
  case := case
  answer := answer
  known c go :=
    if zone c && go.isSome && (answer c).isNone then some "Go accepts zones; ours refuses them"
    else none

end Tests.Oracle.Ip
