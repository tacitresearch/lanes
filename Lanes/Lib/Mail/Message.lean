/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Mail.Basic
public import Lanes.Lib.Net.Percent
public import Lanes.Lib.Time.Format

/-!
# A message of RFC 5322, written

A message as a mail server takes it: the header fields From, To, Cc, Reply-To, Subject, Date and
Message-ID, MIME's (RFC 2045), an empty line, and a body of text, HTML or both
(`multipart/alternative`, RFC 2046 §5.1.4). Everything is written in printable ASCII:

- text in a header (the subject, a name shown) is written as it is when it is printable ASCII
  with no `=?` and fits on its line, and otherwise as encoded words of RFC 2047 (`Q`, UTF-8), at
  most 75 characters each, never splitting a character;
- a field that holds several addresses or words is folded, one per line;
- a body is quoted-printable (RFC 2045 §6.7), lines at most 76 characters, its line breaks
  CR LF whatever the text used. The boundary of `multipart/alternative` holds `=_`, which
  quoted-printable never writes, so no line of a part is the boundary.

Bcc's addresses are the envelope's only (`Message.recipients`), never a header.

Proved, in `Lanes/Lib/Mail/MessageSound.lean`: what `Message.bytes` writes is lines ended by CR
LF, with no CR or LF in a line and none over 998 octets (`Message.wellformed`); and the header's
fields are exactly those the message's shape names, whatever text it holds, every header line
non-empty, so no text given can add a field or end the header (`Message.header_fields`).
-/

@[expose] public section

namespace Lanes.Mail

/-- What a line of a message is written with: printable ASCII and the space. -/
def safe (c : Char) : Bool := 32 ≤ c.toNat && c.toNat ≤ 126

/-- `=` and a byte in two uppercase hexadecimal digits, as both quoted-printable and `Q` write it. -/
def hexByte (b : UInt8) : List Char := ['=', Http.hexDigit (b.toNat / 16), Http.hexDigit (b.toNat % 16)]

/-- Atoms put in order on lines of at most `width` characters, an atom never split, a line
started only when the next atom does not fit. -/
def pack (width : Nat) : List Char → List (List Char) → List (List Char)
  | cur, [] => if cur.isEmpty then [] else [cur]
  | cur, a :: rest =>
    if cur.length + a.length ≤ width then pack width (cur ++ a) rest
    else (if cur.isEmpty then [] else [cur]) ++ pack width a rest

/-! ## Header text -/

def asciiAlnum (c : Char) : Bool :=
  (48 ≤ c.toNat && c.toNat ≤ 57) || (65 ≤ c.toNat && c.toNat ≤ 90) || (97 ≤ c.toNat && c.toNat ≤ 122)

/-- What `Q` writes as itself: what RFC 2047 §5 (3) allows in a phrase, so that one encoding
serves a subject and a name. -/
def qLiteral (c : Char) : Bool :=
  asciiAlnum c || c == '!' || c == '*' || c == '+' || c == '-' || c == '/'

def qChar (c : Char) : List Char :=
  if qLiteral c then [c] else if c == ' ' then ['_'] else (String.utf8EncodeChar c).flatMap hexByte

def wordStart : List Char := "=?UTF-8?Q?".toList

def wordEnd : List Char := "?=".toList

/-- `s` as encoded words, each whole characters and at most 75 characters. -/
def encodedWords (s : String) : List (List Char) :=
  (pack 63 [] (s.toList.map qChar)).map fun w => wordStart ++ w ++ wordEnd

/-- Whether `=?`, which starts an encoded word, is in the text. -/
def hasWordStart : List Char → Bool
  | '=' :: '?' :: _ => true
  | _ :: rest => hasWordStart rest
  | [] => false

/-- The longest text written as it is, so that its line stays within 998 octets. -/
def raw_max : Nat := 900

/-- Unstructured text, a subject: as it is, or as encoded words. -/
def unstructured (s : String) : List (List Char) :=
  if s.toList.all safe && !hasWordStart s.toList && s.length ≤ raw_max then [s.toList]
  else encodedWords s

/-- RFC 5322's `specials`, which an atom of a phrase may not hold. -/
def specials : List Char := "()<>[]:;@\\,.\"".toList

def phraseChar (c : Char) : Bool := c == ' ' || (visible c && !specials.contains c)

/-- The longest name shown written as it is, on the line of its address. -/
def name_max : Nat := 600

/-- Whether a name is written as it is: atoms and spaces, no `=?`, at most `name_max`. -/
def rawName (s : String) : Bool :=
  s.toList.all phraseChar && !hasWordStart s.toList && s.length ≤ name_max

/-- A mailbox, and `sep` after it: the address in angle brackets, after its name unless that
is blank, written as it is on the address's line or as encoded words on lines before it. -/
def mailbox (sep : List Char) (m : Mailbox) : List (List Char) :=
  let addr := ('<' :: m.address.val.toList) ++ '>' :: sep
  if m.name.toList.all (· == ' ') then [addr]
  else if rawName m.name then [m.name.toList ++ ' ' :: addr]
  else encodedWords m.name ++ [addr]

def mailboxes : List Mailbox → List (List Char)
  | [] => []
  | [m] => mailbox [] m
  | m :: rest => mailbox [','] m ++ mailboxes rest

/-- A field: its name, then its words, folded one to a line. -/
def field (name : String) : List (List Char) → List (List Char)
  | [] => [name.toList ++ [':']]
  | w :: rest => (name.toList ++ ':' :: ' ' :: w) :: rest.map (' ' :: ·)

/-! ## The date -/

/-- RFC 5322's date-time, in UTC: `Sat, 28 Nov 2026 09:05:00 +0000`. -/
def dateChars (t : Civil.DateTime) : List Char :=
  (TimeFormat.dayNames.getD t.date.weekday "").toList ++ ',' :: ' ' :: TimeFormat.d2 t.date.day
    ++ ' ' :: (TimeFormat.monthNames.getD (t.date.month - 1) "").toList ++ ' '
    :: TimeFormat.d4 t.date.year.toNat ++ ' ' :: TimeFormat.clock t.time ++ " +0000".toList

/-! ## Bodies -/

/-- The lines of a text, broken at CR LF, LF or CR. -/
def splitLines : List Char → List Char → List (List Char)
  | cur, [] => [cur.reverse]
  | cur, '\r' :: '\n' :: rest => cur.reverse :: splitLines [] rest
  | cur, '\n' :: rest | cur, '\r' :: rest => cur.reverse :: splitLines [] rest
  | cur, c :: rest => splitLines (c :: cur) rest

/-- A byte as quoted-printable writes it: as itself if it prints and is not `=`, a space as
itself unless it ends the line, anything else as `=XX`. -/
def qpByte (last : Bool) (b : UInt8) : List Char :=
  if (33 ≤ b.toNat && b.toNat ≤ 126 && b.toNat != 61) || (b.toNat == 32 && !last) then
    [Char.ofNat b.toNat]
  else hexByte b

def qpAtoms : List UInt8 → List (List Char)
  | [] => []
  | [b] => [qpByte true b]
  | b :: rest => qpByte false b :: qpAtoms rest

/-- Soft line breaks: `=` at the end of every line but the last. -/
def soft : List (List Char) → List (List Char)
  | [] => []
  | [l] => [l]
  | l :: rest => (l ++ ['=']) :: soft rest

/-- A line of text as quoted-printable lines of at most 76 characters. -/
def qpLine (line : List Char) : List (List Char) :=
  match pack 75 [] (qpAtoms (line.flatMap String.utf8EncodeChar)) with
  | [] => [[]]
  | chunks => soft chunks

def quotedPrintable (text : String) : List (List Char) :=
  (splitLines [] text.toList).flatMap qpLine

def boundary : List Char := "=_lanes_alternative".toList

def partHeader (kind : String) : List (List Char) :=
  [s!"Content-Type: text/{kind}; charset=UTF-8".toList,
    "Content-Transfer-Encoding: quoted-printable".toList]

def alternative : List Char :=
  "Content-Type: multipart/alternative; boundary=\"".toList ++ boundary ++ ['"']

/-- The header fields that say what the body is. -/
def Body.fields : Body → List (List Char)
  | .text _ => partHeader "plain"
  | .html _ => partHeader "html"
  | .both .. => [alternative]

def Body.content : Body → List (List Char)
  | .text t => quotedPrintable t
  | .html h => quotedPrintable h
  | .both t h =>
    (("--".toList ++ boundary) :: partHeader "plain" ++ [] :: quotedPrintable t)
      ++ (("--".toList ++ boundary) :: partHeader "html" ++ [] :: quotedPrintable h)
      ++ [("--".toList ++ boundary ++ "--".toList)]

/-! ## The message -/

structure Message where
  from_ : Mailbox
  to : List Mailbox
  cc : List Mailbox := []
  /-- Sent to, and named in no header. -/
  bcc : List Address := []
  replyTo : List Mailbox := []
  subject : String
  date : Civil.DateTime
  /-- The id, written in angle brackets; unique to the message, such as a job's id at the
  sender's domain, so that a message sent again has the same id. -/
  messageId : Address
  body : Body
  deriving DecidableEq

/-- The fields of a list of mailboxes, none when it is empty. -/
def listField (name : String) (l : List Mailbox) : List (List Char) :=
  if l.isEmpty then [] else field name (mailboxes l)

/-- The header: its fields of addresses and text, then MIME's. -/
def Message.header (m : Message) : List (List Char) :=
  field "From" (mailbox [] m.from_) ++ listField "To" m.to ++ listField "Cc" m.cc
    ++ listField "Reply-To" m.replyTo ++ field "Subject" (unstructured m.subject)
    ++ field "Date" [dateChars m.date]
    ++ field "Message-ID" [('<' :: m.messageId.val.toList) ++ ['>']]
    ++ ["MIME-Version: 1.0".toList] ++ m.body.fields

/-- The names of the fields the header holds, which only its shape decides. -/
def Message.fieldNames (m : Message) : List String :=
  ["From"] ++ (if m.to.isEmpty then [] else ["To"]) ++ (if m.cc.isEmpty then [] else ["Cc"])
    ++ (if m.replyTo.isEmpty then [] else ["Reply-To"]) ++ ["Subject", "Date", "Message-ID", "MIME-Version"]
    ++ match m.body with
      | .both .. => ["Content-Type"]
      | _ => ["Content-Type", "Content-Transfer-Encoding"]

/-- Every line of the message, without line breaks: the header, an empty line and the body. -/
def Message.lines (m : Message) : List (List Char) := m.header ++ [] :: m.body.content

def lineBytes (l : List Char) : List UInt8 := l.map (·.toNat.toUInt8)

/-- The message as sent: each line, then CR LF. -/
def Message.bytes (m : Message) : List UInt8 :=
  (m.lines.map fun l => lineBytes l ++ [13, 10]).flatten

def Message.wire (m : Message) : ByteArray := ⟨m.bytes.toArray⟩

/-- Who the message goes to, each once: To, Cc and Bcc. -/
def Message.recipients (m : Message) : List Address :=
  ((m.to ++ m.cc).map (·.address) ++ m.bcc).eraseDups

end Lanes.Mail
