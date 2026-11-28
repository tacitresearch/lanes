/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Addresses and bodies of email

What every way of sending mail shares: an address checked once (`Address.of?`), a mailbox (an
address and the name shown with it) and a body. An address is a bare `local@domain` of ASCII, a
subset of RFC 5322 §3.4.1 that every relay and SES takes and that cannot carry a header, a
command or a line break; `Tests/Aws/Mail.lean` compares it with Go's `net/mail`.
-/

@[expose] public section

namespace Lanes.Mail

/-- What may stand in a dot-atom of RFC 5322, besides letters and digits. -/
def atextSpecials : String := "!#$%&'*+/=?^_`{|}~-"

def atext (c : Char) : Bool := (c.isAlphanum && c.toNat < 128) || atextSpecials.contains c

/-- A local part as a dot-atom: atoms of `atext` between single dots, up to 64 characters. -/
def localPart (s : String) : Bool :=
  0 < s.length && s.length ≤ 64 && (s.splitOn ".").all fun atom => !atom.isEmpty && atom.all atext

/-- A label of a host name: letters, digits and hyphens, not at either end, up to 63. -/
def label (s : String) : Bool :=
  let ok (c : Char) := (c.isAlphanum && c.toNat < 128) || c == '-'
  0 < s.length && s.length ≤ 63 && s.all ok && !s.startsWith "-" && !s.endsWith "-"

/-- A domain of two labels or more, up to 253 characters. Internationalized names go as
punycode. -/
def domain (s : String) : Bool :=
  s.length ≤ 253 && (s.splitOn ".").length ≥ 2 && (s.splitOn ".").all label

/-- A character that prints, in ASCII: neither a control nor a space. -/
def visible (c : Char) : Bool := 32 < c.toNat && c.toNat < 127

/-- `local@domain` with no display name, no comment and no quoted local part, up to 254
characters. `visible` follows from the rest; it is said so that what writes an address need not
read `splitOn`. -/
def Address.valid (s : String) : Bool :=
  s.length ≤ 254 && s.all visible && match s.splitOn "@" with
    | [l, d] => localPart l && domain d
    | _ => false

abbrev Address := {s : String // Address.valid s = true}

def Address.of? (s : String) : Option Address :=
  if h : Address.valid s = true then some ⟨s, h⟩ else none

instance : ToString Address := ⟨(·.val)⟩

/-- An address and the name shown with it, any text, empty for none. -/
structure Mailbox where
  name : String := ""
  address : Address
  deriving DecidableEq, Repr, Hashable

def Mailbox.of? (address : String) (name : String := "") : Option Mailbox :=
  (Address.of? address).map ({ name, address := · })

inductive Body where
  | text (text : String)
  | html (html : String)
  /-- Both, for the reader to choose: `multipart/alternative`. -/
  | both (text html : String)
  deriving DecidableEq, Repr, Hashable

end Lanes.Mail
