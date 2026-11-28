/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Lib.Mail.Basic
import Tests.Oracle.Basic

/-!
The address check of mail, `Mail.Address.of?`, which SES and SMTP share, against Go's `net/mail.ParseAddress`
(`oracles/go/mail`). Ours takes a bare addr-spec of ASCII, a subset of RFC 5322's addresses that
SES takes and that cannot carry a header; so every address ours takes must be one Go reads as
itself, with no display name, and every one Go reads that ours does not is a known difference.
-/

namespace Checks.Mail

open Lanes Tests.Oracle
open Lanes.Mail (Address label)

def answer (c : Case) : Answer := do
  let s ← String.fromUTF8? c.input
  let a ← Address.of? s
  return Json.mkObj [("address", a.val), ("name", "")]

def locals : List String :=
  ["a", "first.last", "o'brien", "x_y-z", "a+tag", "{x}", "!#$%&'*+/=?^_`{|}~-", "é", "a..b",
    ".a", "a.", "", "\"q\"", "\"a b\"", "a b", "A", "1"]

def domains : List String :=
  ["b.co", "mail.example.com", "sub-1.example.org", "b", "[1.2.3.4]", "-b.co", "b-.co", "b_c.co",
    "é.example", "x.123", "a..co", "B.CO", String.ofList (List.replicate 64 'l') ++ ".co",
    "xn--bcher-kva.example"]

def forms (addr : String) : List String :=
  [addr, addr, addr, "Name <" ++ addr ++ ">", "<" ++ addr ++ ">", "\"Last, First\" <" ++ addr ++ ">",
    addr ++ " (comment)", " " ++ addr ++ " ", "=?utf-8?q?J=C3=B6?= <" ++ addr ++ ">",
    addr ++ "\r\nBcc: x@y.co", addr ++ ", c@d.co"]

def alphabet : List Char := "ab.@<>\"() ,;:\\[]é-_+'\r\n".toList

def case : Gen Case := do
  let addr := (← Gen.pick locals) ++ "@" ++ (← Gen.pick domains)
  let addr ← if ← Gen.chance 3 then pure (String.ofList (List.replicate 60 'a') ++ addr) else pure addr
  let s ← match ← Gen.below 10 with
    | 0 => Gen.text alphabet 12
    | 1 | 2 => Gen.mutate alphabet addr
    | _ => Gen.pick (forms addr)
  return text s "parse"

def edges : List Case :=
  ["a@b.co", "first.last+tag@mail.example.com", "Name <a@b.co>", "a@b", "\"q\"@b.co", "é@b.co",
    "a@b.co\r\nBcc: x@y.co", "", "a@[127.0.0.1]"].map (text · "parse")

/-! ## Where ours departs from Go -/

/-- The addr-spec Go read, if it read one with no display name. -/
def addrSpec (go : Answer) : Option String := do
  let j ← go
  match j.getObjVal? "address", j.getObjVal? "name" with
  | .ok (.str a), .ok (.str "") => some a
  | .ok (.str a), _ => some a
  | _, _ => none

def ascii (s : String) : Bool := s.toList.all fun c => c.toNat < 128

def package : Package where
  name := "mail"
  edges := edges
  case := case
  answer := answer
  known c go :=
    match String.fromUTF8? c.input, addrSpec go with
    | some s, some a =>
      if (answer c).isSome then none
      else if a != s then
        some "Go reads display names, angle brackets, comments and quotes; ours a bare addr-spec"
      else if !ascii s then some "Go reads UTF-8 addresses (RFC 6532); ours ASCII, as SES takes them"
      else
        match s.splitOn "@" with
        | [l, d] =>
          if !(d.splitOn ".").all label || (d.splitOn ".").length < 2 then
            some "ours takes a domain of two LDH labels or more; Go any dot-atom or literal"
          else if l.length > 64 || s.length > 254 then
            some "ours bounds a local part at 64 and an address at 254 (RFC 5321 §4.5.3.1)"
          else none
        | _ => none
    | _, _ => none

end Checks.Mail
