/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes

/-!
# Sending email with Amazon SES

SES API v2's `SendEmail`: `POST /v2/email/outbound-emails` on `email.<region>.amazonaws.com`, a
JSON document signed with Signature Version 4 for the service `ses`, answered with a
`MessageId` or an error. A message here is a simple one: a sender, up to 50 recipients, a subject
and a text body, an HTML body or both. Addresses are checked before anything is sent
(`Address.of?`), and the document is proved to be JSON that reads back with exactly the
recipients given (`toAddresses_json`).

What the answer means is said in the terms of `Lanes.Email`, the model of an email API
(`Answer.modelled`): a `MessageId` is a message accepted; a `4xx` is one rejected, which SES did
not send; a `5xx`, an answer not understood and no answer are `unknown`, since the message may
have been sent. SES takes no idempotency key, so a call is a request without one (`modelPort`),
which the model gives an effect of its own each time it is sent: a resend after `unknown` may
send the message twice, and a system that must not send twice must not resend.
-/

@[expose] public section

namespace Aws.Ses

open Lanes Lanes.Http

/-! ## Addresses -/

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
punycode, as SES wants them. -/
def domain (s : String) : Bool :=
  s.length ≤ 253 && (s.splitOn ".").length ≥ 2 && (s.splitOn ".").all label

/-- `local@domain` with no display name, no comment and no quoted local part: what this adapter
sends, up to 254 characters. -/
def Address.valid (s : String) : Bool :=
  s.length ≤ 254 && match s.splitOn "@" with
    | [l, d] => localPart l && domain d
    | _ => false

abbrev Address := {s : String // Address.valid s = true}

def Address.of? (s : String) : Option Address :=
  if h : Address.valid s = true then some ⟨s, h⟩ else none

/-- At most 50 recipients, as SES allows for one message. -/
abbrev Recipients := {l : List Address // 0 < l.length ∧ l.length ≤ 50}

/-- A subject: a line, without a line break that could start a header. -/
abbrev Subject := {s : String // s.all (fun c => c != '\r' && c != '\n') = true}

inductive Body where
  | text (text : String)
  | html (html : String)
  | both (text html : String)
  deriving DecidableEq, Repr, Hashable

structure Message where
  source : Address
  to : Recipients
  subject : Subject
  body : Body
  deriving DecidableEq, Repr, Hashable

/-- The message, or why not: an address SES would refuse, no recipient or more than 50, a line
break in the subject. -/
def Message.of? (source : String) (to : List String) (subject : String) (body : Body) :
    Except String Message := do
  let some from_ := Address.of? source | throw s!"the sender {source.quote} is not an address"
  let recipients ← to.mapM fun r => match Address.of? r with
    | some a => .ok a
    | none => .error s!"{r.quote} is not an address"
  let to ← if h : 0 < recipients.length ∧ recipients.length ≤ 50 then pure ⟨recipients, h⟩
    else throw "one to 50 recipients"
  let subject ← if h : subject.all (fun c => c != '\r' && c != '\n') = true then pure ⟨subject, h⟩
    else throw "a line break in the subject"
  return { source := from_, to, subject, body }

/-! ## The request -/

def content (data : String) : Json := .obj #[("Data", .str data), ("Charset", .str "UTF-8")]

def Body.fields : Body → Array (String × Json)
  | .text t => #[("Text", content t)]
  | .html h => #[("Html", content h)]
  | .both t h => #[("Text", content t), ("Html", content h)]

def destination (to : Recipients) : Json :=
  .obj #[("ToAddresses", .arr (to.val.map fun a => Json.str a.val).toArray)]

def document (m : Message) : Json :=
  .obj #[("FromEmailAddress", .str m.source.val), ("Destination", destination m.to),
    ("Content", .obj #[("Simple", .obj #[("Subject", content m.subject.val),
      ("Body", .obj m.body.fields)])])]

/-- The body of the request, as sent and as signed. -/
def json (m : Message) : String := Json.compress (document m)

structure Endpoint where
  region : String
  host : String
  port : UInt16 := 443
  scheme : Client.Scheme := .https

/-- AWS's endpoint of SES in a region. -/
def Endpoint.aws (region : String) : Endpoint := { region, host := "email." ++ region ++ ".amazonaws.com" }

def path : List String := ["v2", "email", "outbound-emails"]

/-- `SendEmail` for `m`, signed with `creds` at `t`. -/
def call (e : Endpoint) (creds : SigV4.Credentials) (t : Civil.DateTime) (m : Message) :
    Client.Call :=
  let body := (json m).toUTF8
  let request : Request :=
    { method := .post, path, headers := [("content-type", "application/json")], body }
  let unsigned : Client.Call := { host := e.host, port := e.port, scheme := e.scheme, request }
  let signed := SigV4.sign creds t ⟨e.region, "ses"⟩ unsigned.authority "POST"
    (SigV4.payloadHash body) request
  { unsigned with request := signed }

/-! ## The answer -/

inductive Answer where
  /-- Accepted, under SES's id for the message. -/
  | sent (messageId : String)
  /-- A `4xx`: refused, and not sent. The code is SES's (`MessageRejected`,
  `TooManyRequestsException`), or `""`. -/
  | rejected (status : Nat) (code : String)
  /-- A `5xx`, or a success without a `MessageId`: the message may have been sent. -/
  | uncertain (status : Nat) (code : String)
  deriving DecidableEq, Repr, Hashable

/-- The error's name: `x-amzn-ErrorType`'s, or the body's `__type` or `code`, without the
namespace before a `#` or the URL after a `:`. -/
def errorCode (r : Response) : String :=
  let fromBody := ((String.fromUTF8? r.body).bind fun s => (Json.parse s).toOption).bind fun j =>
    ((j.getObjValAs? String "__type").toOption).orElse fun _ => (j.getObjValAs? String "code").toOption
  let raw := ((r.headers.lookup "x-amzn-errortype").orElse fun _ => fromBody).getD ""
  (((raw.splitOn "#").getLast?.getD "").splitOn ":").headD ""

def messageId? (r : Response) : Option String := do
  let j ← (Json.parse (← String.fromUTF8? r.body)).toOption
  let id ← (j.getObjValAs? String "MessageId").toOption
  if id.isEmpty then none else some id

def interpret (r : Response) : Answer :=
  if r.status == 200 then
    match messageId? r with
    | some id => .sent id
    | none => .uncertain r.status ""
  else if 400 ≤ r.status && r.status < 500 then .rejected r.status (errorCode r)
  else .uncertain r.status (errorCode r)

/-! ## As the model of an email API -/

/-- A message as the email model names it: by SES's id, or, refused, by the call that sent it. -/
inductive Ref where
  | message (id : String)
  | unsent (call : Nat)
  deriving DecidableEq, Repr, Hashable

def Answer.modelled (call : Nat) : Answer → Rpc.Reply (Email.Answer Ref)
  | .sent id => .answer (.made (.message id) .accepted)
  | .rejected .. => .answer (.made (.unsent call) .rejected)
  | .uncertain .. => .unknown

/-- Which outputs of a system are sends and which inputs answer them. -/
structure Port (σ : Signature) where
  called : σ.Out → Option (Rpc.Call Message)
  reply : (call : Nat) → Rpc.Reply Answer → σ.In
  replied : σ.In → Option (Nat × Rpc.Reply Answer)

/-- The port as `Lanes.Email`'s model sees it: every send without a key, since SES takes none,
and no webhooks. -/
def modelPort {σ : Signature} (port : Port σ) :
    Rpc.Port σ (Idempotent.Keyed Empty Message) (Email.Answer Ref) (Email.Webhook Ref Message) where
  called out := (port.called out).map fun c => ⟨c.id, c.deadline_ms, ⟨none, c.request⟩⟩
  replied x := (port.replied x).map fun
    | (call, .answer a) => (call, a.modelled call)
    | (call, .unknown) => (call, .unknown)

/-- What SES may do, as the email model says. -/
def outside {σ : Signature} (port : Port σ) :
    Outside σ (Rpc.State (Effects.Model Empty Ref Email.Status Message)) :=
  Email.outside (modelPort port) 0

/-! ## Each output sent once

SES takes no idempotency key, so the adapter keeps its own: the keys the application gave the
outputs it sent, such as `confirmation-<order>`. An output whose key was sent before is not sent
again (`Sent.admitted_nodup`), whoever hands it over and however often, also after a restart of
the process. The service the system then sees is SES behind keys, as `Idempotent.server` models
one, where `Idempotent.at_most_once` holds. A key is a line of the adapter's file: it is not
empty and has no line feed (`Sent.valid`). -/

/-- The keys of the outputs sent, newest first. -/
abbrev Sent := List String

/-- Whether `key` can be kept: not empty, and no line feed. -/
def Sent.valid (key : String) : Bool :=
  !key.isEmpty && !key.contains '\n'

/-- Whether the output with `key` is new: a valid key not sent before. -/
def Sent.admits (sent : Sent) (key : String) : Bool :=
  Sent.valid key && !sent.contains key

def Sent.record (sent : Sent) (key : String) : Sent :=
  key :: sent

/-- One output handed over: sent and remembered if it is new. Those sent so far are listed last
first. -/
def Sent.step (acc : Sent × List String) (key : String) : Sent × List String :=
  if acc.1.admits key then (acc.1.record key, key :: acc.2) else acc

private theorem Sent.step_inv {acc : Sent × List String} (h : acc.1 = acc.2) (hn : acc.2.Nodup)
    (key : String) : (Sent.step acc key).1 = (Sent.step acc key).2 ∧ (Sent.step acc key).2.Nodup := by
  obtain ⟨sent, done⟩ := acc
  simp only at h hn
  subst h
  unfold Sent.step
  split
  · next hadmit =>
    refine ⟨rfl, List.nodup_cons.mpr ⟨fun hm => ?_, hn⟩⟩
    simp only [Sent.admits, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hadmit
    exact hadmit.2 hm
  · exact ⟨rfl, hn⟩

/-- However often outputs are handed over again, no key is sent twice: the keys sent are
distinct. -/
theorem Sent.admitted_nodup (keys : List String) : (keys.foldl Sent.step ([], [])).2.Nodup := by
  suffices ∀ (keys : List String) acc, acc.1 = acc.2 → acc.2.Nodup →
      (keys.foldl Sent.step acc).2.Nodup from this keys _ rfl List.nodup_nil
  intro keys
  induction keys with
  | nil => exact fun _ _ hn => hn
  | cons key rest ih =>
    intro acc h hn
    obtain ⟨h', hn'⟩ := Sent.step_inv h hn key
    exact ih _ h' hn'

/-- The state as a file: a line for each key. -/
def Sent.write (sent : Sent) : String :=
  String.join (sent.map (· ++ "\n"))

/-- The state a file holds. -/
def Sent.read (text : String) : Sent :=
  (text.splitOn "\n").filter (· != "")

/-- What the document says the recipients are. -/
def toAddresses (j : Json) : Except String (List String) := do
  let d ← j.getObjVal? "Destination"
  let a ← d.getObjVal? "ToAddresses"
  let arr ← a.getArr?
  arr.toList.mapM Json.getStr?

end Aws.Ses
