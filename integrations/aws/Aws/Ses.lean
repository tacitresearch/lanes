/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

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

SES takes no idempotency key, so the adapter keeps its own: what it sent, by output id
(`Journal.OutputId`). A shard hands its outputs over in the order of their origins, and an
output handed over again after a restart comes again in that order (`Journal.recoverIds_suffix`),
so it is enough to remember, for each journal, the origin of the last output sent: one at or
before it is a repeat, and is not sent again (`Sent.admitted_nodup`). The service the system then
sees is SES behind keys, as `Idempotent.server` models one, where `Idempotent.at_most_once`
holds. -/

/-- For each journal, the origin of the last output sent. -/
abbrev Sent := List (String × Journal.Origin)

/-- Whether the output `id` is new: after the last sent of its journal. -/
def Sent.admits (sent : Sent) (id : Journal.OutputId) : Bool :=
  match sent.lookup id.journal with
  | none => true
  | some last => last.before id.origin

def Sent.record (sent : Sent) (id : Journal.OutputId) : Sent :=
  (id.journal, id.origin) :: sent.filter (·.1 != id.journal)

/-- One output handed over: sent and remembered if it is new. Those sent so far are listed last
first. -/
def Sent.step (acc : Sent × List Journal.OutputId) (id : Journal.OutputId) :
    Sent × List Journal.OutputId :=
  if acc.1.admits id then (acc.1.record id, id :: acc.2) else acc

private theorem lookup_filter (l : Sent) {a j : String} (h : j ≠ a) :
    (l.filter (·.1 != a)).lookup j = l.lookup j := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, o⟩ := e
    by_cases hk : k = a
    · subst hk
      have hjk : (j == k) = false := by simpa using h
      simp [List.lookup_cons, hjk, ih]
    · have hk' : (k != a) = true := by simpa using hk
      simp only [List.filter_cons, hk', ite_true, List.lookup_cons, ih]

theorem Sent.lookup_record (sent : Sent) (id : Journal.OutputId) (j : String) :
    (sent.record id).lookup j = if j = id.journal then some id.origin else sent.lookup j := by
  by_cases h : j = id.journal
  · simp [record, h]
  · have hj : (j == id.journal) = false := by simpa using h
    simp only [record, List.lookup_cons, hj, h, ite_false]
    exact lookup_filter sent h

private theorem before_trans {a b c : Journal.Origin} (h1 : a.before b = true)
    (h2 : b.before c = true) : a.before c = true := by
  simp only [Journal.Origin.before, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    beq_iff_eq] at *
  omega

/-- What the adapter's state says of every output it sent: its origin is at or before the last
sent of its journal. -/
private def Sent.Covers (acc : Sent × List Journal.OutputId) : Prop :=
  ∀ x ∈ acc.2, ∃ last, acc.1.lookup x.journal = some last
    ∧ (x.origin = last ∨ x.origin.before last = true)

private theorem Sent.step_covers {acc : Sent × List Journal.OutputId} (h : Sent.Covers acc)
    (hn : acc.2.Nodup) (id : Journal.OutputId) :
    Sent.Covers (Sent.step acc id) ∧ (Sent.step acc id).2.Nodup := by
  obtain ⟨sent, done⟩ := acc
  unfold Sent.step
  split
  · next hadmit =>
    simp only [Sent.admits] at hadmit
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, hn⟩⟩
    · intro x hx
      simp only [Sent.lookup_record]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨x.origin, by simp, Or.inl rfl⟩
      · obtain ⟨last, hlast, hle⟩ := h x hx
        by_cases hj : x.journal = id.journal
        · refine ⟨id.origin, by simp [hj], Or.inr ?_⟩
          rw [hj] at hlast
          rw [hlast] at hadmit
          rcases hle with heq | hlt
          · rw [heq]; exact hadmit
          · exact before_trans hlt hadmit
        · exact ⟨last, by simp [hj, hlast], hle⟩
    · intro hmem
      obtain ⟨last, hlast, hle⟩ := h id hmem
      simp only at hlast
      rw [hlast] at hadmit
      simp only at hadmit
      rcases hle with heq | hlt
      · rw [heq, Journal.Origin.before_irrefl] at hadmit; exact absurd hadmit (by simp)
      · have := before_trans hlt hadmit
        rw [Journal.Origin.before_irrefl] at this; exact absurd this (by simp)
  · exact ⟨h, hn⟩

/-- However often outputs are handed over again, none is sent twice: the outputs sent are
distinct. -/
theorem Sent.admitted_nodup (ids : List Journal.OutputId) :
    (ids.foldl Sent.step ([], [])).2.Nodup := by
  suffices ∀ (ids : List Journal.OutputId) acc, Sent.Covers acc → acc.2.Nodup →
      (ids.foldl Sent.step acc).2.Nodup from this ids _ (fun _ h => by simp at h) List.nodup_nil
  intro ids
  induction ids with
  | nil => exact fun _ _ hn => hn
  | cons id rest ih =>
    intro acc h hn
    obtain ⟨h', hn'⟩ := Sent.step_covers h hn id
    exact ih _ h' hn'

/-- The state as a file: a line for each journal, its id and the last origin sent. -/
def Sent.write (sent : Sent) : String :=
  String.join (sent.map fun (j, o) => j ++ " " ++ toString o.position ++ " " ++ toString o.place ++ "\n")

/-- The state a file holds. A line that does not read is a file not written by `write`, and the
whole is refused. -/
def Sent.read? (text : String) : Option Sent :=
  ((text.splitOn "\n").filter (· != "")).mapM fun line =>
    match line.splitOn " " with
    | [j, p, q] => do pure (j, ⟨← p.toNat?, ← q.toNat?⟩)
    | _ => none

/-- What the document says the recipients are. -/
def toAddresses (j : Json) : Except String (List String) := do
  let d ← j.getObjVal? "Destination"
  let a ← d.getObjVal? "ToAddresses"
  let arr ← a.getArr?
  arr.toList.mapM Json.getStr?

end Aws.Ses
