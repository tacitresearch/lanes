/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Postgres.Bytes
public import Lanes.Proof.ByteArray

/-!
# PostgreSQL's messages

The messages of the frontend/backend protocol, version 3.0, that a client of the extended query
protocol in text format sends (`Frontend`) and receives (`Backend`), as data; their bytes
(`Frontend.encode`, `Backend.encode`); what bytes are as messages (`Backend.decode`,
`Frontend.decode`); and the frames they come in, a type byte and a length of four bytes that
counts itself (`Frame.read`).

`Lanes/Lib/Postgres/MessageSound.lean` proves that each decoder reads back what its encoder
writes of a message within its bounds (`Backend.Ok`, `Frontend.Ok`). The client's own bytes are
`Frontend.encode`; what a server sends is read by `Frame.read` and `Backend.decode`, and recorded
exchanges with a real server are replayed through them in `Tests/Postgres.lean`.

A frontend `p` message is a password, the first SASL message or a later one, and only the
exchange so far says which, so `Frontend.decode` is told what to expect (`Frontend.Expect`).
-/

@[expose] public section

namespace Lanes.Postgres

/-- The state of the transaction that `ReadyForQuery` reports. -/
inductive TxStatus where
  | idle
  | inTx
  | failed
  deriving DecidableEq, Repr, Hashable

def TxStatus.byte : TxStatus → UInt8
  | .idle => 73
  | .inTx => 84
  | .failed => 69

def TxStatus.ofByte (b : UInt8) : Option TxStatus :=
  if b = 73 then some .idle else if b = 84 then some .inTx else if b = 69 then some .failed
  else none

/-- A column of a `RowDescription`. -/
structure Column where
  name : String
  table : Nat := 0
  position : Nat := 0
  type : Nat
  size : Nat
  modifier : Nat
  format : Nat := 0
  deriving DecidableEq, Repr, Hashable

/-- A field of an `ErrorResponse` or a `NoticeResponse`: its code (`C` for the SQLSTATE, `M`
for the message, `S` for the severity, …) and its value. -/
structure Field where
  code : UInt8
  value : String
  deriving DecidableEq, Repr, Hashable

inductive Backend where
  | authOk
  | authCleartext
  | authMd5 (salt : ByteArray)
  | authSasl (mechanisms : List String)
  | authSaslContinue (data : ByteArray)
  | authSaslFinal (data : ByteArray)
  | parameterStatus (name value : String)
  | backendKeyData (pid secret : Nat)
  | readyForQuery (status : TxStatus)
  | parseComplete
  | bindComplete
  | closeComplete
  | noData
  | portalSuspended
  | emptyQuery
  | rowDescription (columns : List Column)
  | dataRow (values : List (Option ByteArray))
  | commandComplete (tag : String)
  | errorResponse (fields : List Field)
  | noticeResponse (fields : List Field)
  | parameterDescription (types : List Nat)
  deriving DecidableEq

inductive Frontend where
  /-- The start-up message, protocol 3.0, with its parameters (`user`, `database`, …). -/
  | startup (params : List (String × String))
  | password (password : String)
  | saslInitial (mechanism : String) (data : ByteArray)
  | saslResponse (data : ByteArray)
  /-- A query of the simple protocol. -/
  | query (sql : String)
  | parse (statement sql : String) (types : List Nat)
  | bind (portal statement : String) (formats : List Nat) (params : List (Option ByteArray))
      (results : List Nat)
  | describe (portal : Bool) (name : String)
  | execute (portal : String) (rows : Nat)
  | sync
  | terminate
  deriving DecidableEq

def protocol30 : Nat := 196608

/-! ## Fields -/

def Column.put (c : Column) : List UInt8 :=
  putStr c.name ++ putU32 c.table ++ putU16 c.position ++ putU32 c.type ++ putU16 c.size
    ++ putU32 c.modifier ++ putU16 c.format

def Column.get : Parse Column := fun bytes => do
  let (name, bytes) ← getStr bytes
  let (table, bytes) ← getU32 bytes
  let (position, bytes) ← getU16 bytes
  let (type, bytes) ← getU32 bytes
  let (size, bytes) ← getU16 bytes
  let (modifier, bytes) ← getU32 bytes
  let (format, bytes) ← getU16 bytes
  pure ({ name, table, position, type, size, modifier, format }, bytes)

def Column.Ok (c : Column) : Prop :=
  Plain c.name ∧ c.table < 4294967296 ∧ c.position < 65536 ∧ c.type < 4294967296
    ∧ c.size < 65536 ∧ c.modifier < 4294967296 ∧ c.format < 65536

def Field.put (f : Field) : List UInt8 := f.code :: putStr f.value

def Field.get : Parse Field := fun bytes => do
  let (code, bytes) ← byte bytes
  let (value, bytes) ← getStr bytes
  pure ({ code, value }, bytes)

def Field.Ok (f : Field) : Prop := f.code ≠ 0 ∧ Plain f.value

def getFields (bytes : List UInt8) : Option (List Field) :=
  whole (getTerminated Field.get bytes.length) bytes

def getNames (bytes : List UInt8) : Option (List String) :=
  whole (getTerminated getStr bytes.length) bytes

/-- A name in a list ended by an empty one, as SASL's mechanisms and the start-up's parameters
are. -/
def Named (s : String) : Prop := Plain s ∧ s ≠ ""

def putParam (p : String × String) : List UInt8 := putStr p.1 ++ putStr p.2

def getParam : Parse (String × String) := fun bytes => do
  let (name, bytes) ← getStr bytes
  let (value, bytes) ← getStr bytes
  pure ((name, value), bytes)

/-! ## The backend's messages -/

namespace Backend

def tag : Backend → UInt8
  | authOk | authCleartext | authMd5 _ | authSasl _ | authSaslContinue _ | authSaslFinal _ => 82
  | parameterStatus .. => 83
  | backendKeyData .. => 75
  | readyForQuery _ => 90
  | parseComplete => 49
  | bindComplete => 50
  | closeComplete => 51
  | noData => 110
  | portalSuspended => 115
  | emptyQuery => 73
  | rowDescription _ => 84
  | dataRow _ => 68
  | commandComplete _ => 67
  | errorResponse _ => 69
  | noticeResponse _ => 78
  | parameterDescription _ => 116

def body : Backend → List UInt8
  | authOk => putU32 0
  | authCleartext => putU32 3
  | authMd5 salt => putU32 5 ++ salt.data.toList
  | authSasl mechanisms => putU32 10 ++ putTerminated putStr mechanisms
  | authSaslContinue data => putU32 11 ++ data.data.toList
  | authSaslFinal data => putU32 12 ++ data.data.toList
  | parameterStatus name value => putStr name ++ putStr value
  | backendKeyData pid secret => putU32 pid ++ putU32 secret
  | readyForQuery status => [status.byte]
  | parseComplete | bindComplete | closeComplete | noData | portalSuspended | emptyQuery => []
  | rowDescription columns => putList16 Column.put columns
  | dataRow values => putList16 putValue values
  | commandComplete tag => putStr tag
  | errorResponse fields | noticeResponse fields => putTerminated Field.put fields
  | parameterDescription types => putList16 putU32 types

def Ok : Backend → Prop
  | authMd5 salt => salt.size = 4
  | authSasl mechanisms => ∀ m ∈ mechanisms, Named m
  | parameterStatus name value => Plain name ∧ Plain value
  | backendKeyData pid secret => pid < 4294967296 ∧ secret < 4294967296
  | rowDescription columns => columns.length < 65536 ∧ ∀ c ∈ columns, c.Ok
  | dataRow values => values.length < 65536 ∧ ∀ v ∈ values, ValueOk v
  | commandComplete tag => Plain tag
  | errorResponse fields | noticeResponse fields => ∀ f ∈ fields, f.Ok
  | parameterDescription types => types.length < 65536 ∧ ∀ t ∈ types, t < 4294967296
  | _ => True

def decodeAuth (bytes : List UInt8) : Option Backend :=
  match getU32 bytes with
  | some (0, []) => some authOk
  | some (3, []) => some authCleartext
  | some (5, salt) => if salt.length = 4 then some (authMd5 ⟨salt.toArray⟩) else none
  | some (10, rest) => (getNames rest).map authSasl
  | some (11, data) => some (authSaslContinue ⟨data.toArray⟩)
  | some (12, data) => some (authSaslFinal ⟨data.toArray⟩)
  | _ => none

def decodeBody (tag : UInt8) (bytes : List UInt8) : Option Backend :=
  if tag = 82 then decodeAuth bytes
  else if tag = 83 then (whole getParam bytes).map fun (n, v) => parameterStatus n v
  else if tag = 75 then
    (whole (fun b => do
      let (pid, b) ← getU32 b
      let (secret, b) ← getU32 b
      pure ((pid, secret), b)) bytes).map fun (p, s) => backendKeyData p s
  else if tag = 90 then
    match bytes with
    | [b] => (TxStatus.ofByte b).map readyForQuery
    | _ => none
  else if tag = 84 then (whole (getList16 Column.get) bytes).map rowDescription
  else if tag = 68 then (whole (getList16 getValue) bytes).map dataRow
  else if tag = 67 then (whole getStr bytes).map commandComplete
  else if tag = 69 then (getFields bytes).map errorResponse
  else if tag = 78 then (getFields bytes).map noticeResponse
  else if tag = 116 then (whole (getList16 getU32) bytes).map parameterDescription
  else if bytes = [] then
    if tag = 49 then some parseComplete
    else if tag = 50 then some bindComplete
    else if tag = 51 then some closeComplete
    else if tag = 110 then some noData
    else if tag = 115 then some portalSuspended
    else if tag = 73 then some emptyQuery
    else none
  else none

/-- The message in a frame's body. -/
def decode (tag : UInt8) (body : ByteArray) : Option Backend :=
  decodeBody tag body.data.toList

end Backend

/-! ## The frontend's messages -/

namespace Frontend

/-- What the server expects next, which says what a `p` message is. -/
inductive Expect where
  | startup
  | password
  | saslInitial
  | saslResponse
  | query
  deriving DecidableEq

def expect : Frontend → Expect
  | startup _ => .startup
  | password _ => .password
  | saslInitial .. => .saslInitial
  | saslResponse _ => .saslResponse
  | _ => .query

def tag : Frontend → UInt8
  | startup _ => 0
  | password _ | saslInitial .. | saslResponse _ => 112
  | query _ => 81
  | parse .. => 80
  | bind .. => 66
  | describe .. => 68
  | execute .. => 69
  | sync => 83
  | terminate => 88

def body : Frontend → List UInt8
  | startup params => putU32 protocol30 ++ putTerminated putParam params
  | password p => putStr p
  | saslInitial mechanism data => putStr mechanism ++ putU32 data.size ++ data.data.toList
  | saslResponse data => data.data.toList
  | query sql => putStr sql
  | parse statement sql types => putStr statement ++ putStr sql ++ putList16 putU32 types
  | bind portal statement formats params results =>
    putStr portal ++ putStr statement ++ putList16 putU16 formats ++ putList16 putValue params
      ++ putList16 putU16 results
  | describe portal name => (if portal then 80 else 83) :: putStr name
  | execute portal rows => putStr portal ++ putU32 rows
  | sync | terminate => []

def Ok : Frontend → Prop
  | startup params => ∀ p ∈ params, Named p.1 ∧ Plain p.2
  | password p => Plain p
  | saslInitial mechanism data => Plain mechanism ∧ data.size < 0x80000000
  | query sql => Plain sql
  | parse statement sql types =>
    Plain statement ∧ Plain sql ∧ types.length < 65536 ∧ ∀ t ∈ types, t < 4294967296
  | bind portal statement formats params results =>
    Plain portal ∧ Plain statement ∧ (formats.length < 65536 ∧ ∀ f ∈ formats, f < 65536)
      ∧ (params.length < 65536 ∧ ∀ v ∈ params, ValueOk v)
      ∧ (results.length < 65536 ∧ ∀ f ∈ results, f < 65536)
  | describe _ name => Plain name
  | execute portal rows => Plain portal ∧ rows < 4294967296
  | _ => True

/-- The bytes of a message: the start-up message has no type byte. -/
def wire (m : Frontend) : List UInt8 :=
  match m with
  | startup _ => putU32 (m.body.length + 4) ++ m.body
  | _ => m.tag :: putU32 (m.body.length + 4) ++ m.body

def encode (m : Frontend) : ByteArray := ⟨m.wire.toArray⟩

def decodeBody (expect : Expect) (tag : UInt8) (bytes : List UInt8) : Option Frontend :=
  match expect with
  | .startup => none
  | .password => if tag = 112 then (whole getStr bytes).map password else none
  | .saslInitial =>
    if tag = 112 then
      (whole (fun b => do
        let (mechanism, b) ← getStr b
        let (n, b) ← getU32 b
        let (data, b) ← take n b
        pure ((mechanism, data), b)) bytes).map fun (m, d) => saslInitial m ⟨d.toArray⟩
    else none
  | .saslResponse => if tag = 112 then some (saslResponse ⟨bytes.toArray⟩) else none
  | .query =>
    if tag = 81 then (whole getStr bytes).map query
    else if tag = 80 then
      (whole (fun b => do
        let (statement, b) ← getStr b
        let (sql, b) ← getStr b
        let (types, b) ← getList16 getU32 b
        pure (parse statement sql types, b)) bytes)
    else if tag = 66 then
      (whole (fun b => do
        let (portal, b) ← getStr b
        let (statement, b) ← getStr b
        let (formats, b) ← getList16 getU16 b
        let (params, b) ← getList16 getValue b
        let (results, b) ← getList16 getU16 b
        pure (bind portal statement formats params results, b)) bytes)
    else if tag = 68 then
      match bytes with
      | k :: rest =>
        if k = 80 then (whole getStr rest).map (describe true)
        else if k = 83 then (whole getStr rest).map (describe false)
        else none
      | [] => none
    else if tag = 69 then
      (whole (fun b => do
        let (portal, b) ← getStr b
        let (rows, b) ← getU32 b
        pure (execute portal rows, b)) bytes)
    else if bytes = [] then
      if tag = 83 then some sync else if tag = 88 then some terminate else none
    else none

def decodeStartup (bytes : List UInt8) : Option Frontend :=
  match getU32 bytes with
  | some (n, body) =>
    if n = body.length + 4 then
      match getU32 body with
      | some (v, rest) =>
        if v = protocol30 then (whole (getTerminated getParam rest.length) rest).map startup
        else none
      | none => none
    else none
  | none => none

/-- One whole message, as a server reads it when it expects `expect`. -/
def decode (expect : Expect) (bytes : ByteArray) : Option Frontend :=
  match expect, bytes.data.toList with
  | .startup, list => decodeStartup list
  | _, tag :: rest =>
    match getU32 rest with
    | some (n, body) => if n = body.length + 4 then decodeBody expect tag body else none
    | none => none
  | _, [] => none

end Frontend

/-! ## Frames -/

namespace Backend

def wire (m : Backend) : List UInt8 := m.tag :: putU32 (m.body.length + 4) ++ m.body

def encode (m : Backend) : ByteArray := ⟨m.wire.toArray⟩

end Backend

inductive Frame where
  | more
  /-- A frame of type `tag`; the next starts at `next`. -/
  | done (tag : UInt8) (body : ByteArray) (next : Nat)
  /-- A length below four, which cannot be, or above `message_max`. -/
  | refuse


/-- The frame at `pos` in `buffer`, if it is all there. `message_max` bounds its length, which
counts the four bytes of the length and not the type byte. -/
def Frame.read (message_max : Nat) (buffer : ByteArray) (pos : Nat) : Frame :=
  match buffer[pos]?, buffer[pos + 1]?, buffer[pos + 2]?, buffer[pos + 3]?, buffer[pos + 4]? with
  | some tag, some a, some b, some c, some d =>
    let length := ((a.toNat * 256 + b.toNat) * 256 + c.toNat) * 256 + d.toNat
    if length < 4 ∨ message_max < length then .refuse
    else if pos + 1 + length ≤ buffer.size then
      .done tag (buffer.extract (pos + 5) (pos + 1 + length)) (pos + 1 + length)
    else .more
  | _, _, _, _, _ => .more

end Lanes.Postgres
