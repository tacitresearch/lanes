/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Http.Basic

/-!
HTTP/1.1 on the wire, as pure functions: a request as the bytes a client sends, and the bytes a
server answers with as a response. The client adapter (`Lanes.Env.HttpClient`) only moves these
bytes over a socket, and asks `Response.read` after each arrival whether to go on.

The writer frames the request itself: the caller's headers cannot change where the message ends
or add a line (`Request.fields_framing`, `Request.head_plain`). The reader is total, never
reads outside the bytes it is given, and answers `none` to anything it does not understand.
`Response.wire` and `Response.wireChunked` write responses the way a server does, so that
`Lanes.Http.WireSound` can say what the reader makes of them and of every start of them.
-/

@[expose] public section

namespace Lanes.Http

/-- A character of an RFC 7230 token, which is what a header's name is. -/
def tokenChar (c : Char) : Bool :=
  c.isAlphanum || "!#$%&'*+-.^_`|~".toList.contains c

def token (s : String) : Bool :=
  s != "" && s.toList.all tokenChar

/-- No control character but tab: what a header's value may hold. -/
def plain (c : Char) : Bool :=
  c == '\t' || (32 ≤ c.val && c.val != 127)

def visible (c : Char) : Bool :=
  33 ≤ c.val && c.val ≤ 126

/-- The blanks a header's value may have around it. -/
def ows (c : Char) : Bool :=
  c == ' ' || c == '\t'

/-- Whether a header of this name says where a message ends or whom it is for. The writer
sets those itself. -/
def frames (name : String) : Bool :=
  ["host", "connection", "content-length", "transfer-encoding"].contains name.toLower

namespace Request

def target (r : Request) : String :=
  let pairs := r.query.map fun (k, v) => percentEncode k ++ "=" ++ percentEncode v
  let query := if pairs.isEmpty then "" else "?" ++ "&".intercalate pairs
  "/" ++ "/".intercalate (r.path.map percentEncode) ++ query

/-- Whether one of the caller's headers is written. It is left out if its name is not a token,
if its value has a control character other than tab, or if it `frames` the message. -/
def kept (field : String × String) : Bool :=
  token field.1 && field.2.toList.all plain && !frames field.1

/-- The headers as written: the writer's own, then the caller's. -/
def fields (r : Request) (host : String) : List (String × String) :=
  [("Host", host), ("Connection", "close"), ("Content-Length", toString r.body.size)]
    ++ r.headers.filter kept

def head (r : Request) (host : String) : List String :=
  let method := match r.method with
    | .get => "GET" | .post => "POST" | .put => "PUT" | .patch => "PATCH" | .delete => "DELETE"
  (method ++ " " ++ r.target ++ " HTTP/1.1")
    :: (r.fields host).map fun (name, value) => name ++ ": " ++ value

/-- The bytes of a request to `host`: the lines of the head, each ended by CRLF, a blank line
and the body. `none` for a host that is empty or has a character that is not visible ASCII.
The path and query are escaped. -/
def wire (r : Request) (host : String) : Option ByteArray :=
  if host != "" && host.toList.all visible then
    some (("\r\n".intercalate (r.head host) ++ "\r\n\r\n").toUTF8 ++ r.body)
  else none

end Request

private theorem toLower_eq_iff (s t : String) :
    s.toLower = t ↔ s.toList.map Char.toLower = t.toList := by
  rw [← String.toList_inj, String.toLower, String.toList_map]

theorem visible_of_tokenChar {c : Char} (h : tokenChar c) : visible c := by
  rcases Bool.or_eq_true _ _ |>.mp h with alnum | symbol
  · simp only [Char.isAlphanum, Char.isAlpha, Char.isUpper, Char.isLower, Char.isDigit, visible,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, UInt32.le_iff_toNat_le,
      ge_iff_le] at *
    simp at *
    omega
  · have all : "!#$%&'*+-.^_`|~".toList.all visible = true := by decide
    exact List.all_eq_true.mp all c (List.contains_iff_mem.mp symbol)

theorem plain_of_visible {c : Char} (h : visible c) : plain c := by
  simp only [visible, plain, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    UInt32.le_iff_toNat_le, bne_iff_ne, ne_eq, beq_iff_eq] at *
  refine .inr ⟨h.1 |> Nat.le_trans (by decide), ?_⟩
  intro eq
  rw [eq] at h
  exact absurd h.2 (by decide)

private theorem all_plain_of_visible {chars : List Char} (h : chars.all visible) :
    chars.all plain :=
  List.all_eq_true.mpr fun c mem => plain_of_visible (List.all_eq_true.mp h c mem)

private theorem percentEncodeByte_visible : ∀ b : UInt8, (percentEncodeByte b).all visible := by
  decide

private theorem percentEncode_visible (s : String) : (percentEncode s).toList.all visible := by
  simp only [percentEncode, String.toList_ofList, List.all_flatMap]
  exact List.all_eq_true.mpr fun b _ => percentEncodeByte_visible b

private theorem all_intercalate {α : Type} (p : α → Bool) (sep : List α) (hsep : sep.all p) :
    ∀ parts : List (List α), (∀ part ∈ parts, part.all p) → (sep.intercalate parts).all p
  | [], _ => rfl
  | [part], h => by simpa using h part
  | part :: next :: parts, h => by
    rw [List.intercalate_cons_cons, List.all_append, List.all_append,
      h part (List.mem_cons_self ..), hsep, all_intercalate p sep hsep (next :: parts)
        fun part mem => h part (List.mem_cons_of_mem _ mem)]
    rfl

namespace Request

/-- Of the headers that frame the message, the writer's own are written and no other: one
`Host`, one `Connection`, one `Content-Length` and no `Transfer-Encoding`, whatever the
caller's headers are. -/
theorem fields_framing (r : Request) (host : String) :
    (r.fields host).filter (frames ·.1)
      = [("Host", host), ("Connection", "close"), ("Content-Length", toString r.body.size)] := by
  have dropped : (r.headers.filter kept).filter (frames ·.1) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro field mem
    have passed := (List.mem_filter.mp mem).2
    simp only [Request.kept, Bool.and_eq_true, Bool.not_eq_true'] at passed
    simp [passed.2]
  rw [fields, List.filter_append, dropped, List.append_nil]
  simp [frames, toLower_eq_iff]

theorem fields_contentLength (r : Request) (host : String) :
    ((r.fields host).filter (·.1.toLower == "content-length")).length = 1 := by
  have narrowed : (r.fields host).filter (·.1.toLower == "content-length")
      = ((r.fields host).filter (frames ·.1)).filter (·.1.toLower == "content-length") := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro field _
    by_cases h : field.1.toLower = "content-length" <;> simp [h, frames]
  rw [narrowed, fields_framing]
  simp [toLower_eq_iff]

theorem fields_transferEncoding (r : Request) (host : String) :
    ∀ field ∈ r.fields host, field.1.toLower ≠ "transfer-encoding" := by
  intro field mem h
  have own : field ∈ (r.fields host).filter (frames ·.1) :=
    List.mem_filter.mpr ⟨mem, by simp [h, frames]⟩
  rw [fields_framing] at own
  simp at own
  rcases own with rfl | rfl | rfl <;> simp [toLower_eq_iff] at h

/-- Every name written is a token, so it has no colon and no blank: a line of the head is read
back with the name it was written with. -/
theorem fields_token (r : Request) (host : String) : ∀ field ∈ r.fields host, token field.1 := by
  intro field mem
  rcases List.mem_append.mp mem with own | caller
  · simp at own
    rcases own with rfl | rfl | rfl <;> simp [token, tokenChar]
  · have passed := (List.mem_filter.mp caller).2
    simp only [Request.kept, Bool.and_eq_true] at passed
    exact passed.1.1

/-- The target has no blank and no control character, whatever the path and the query. -/
theorem target_visible (r : Request) : r.target.toList.all visible := by
  have pair : ∀ part ∈ (r.query.map fun (k, v) => percentEncode k ++ "=" ++ percentEncode v).map
      String.toList, part.all visible := by
    intro part mem
    simp only [List.map_map, List.mem_map, Function.comp_apply] at mem
    obtain ⟨⟨k, v⟩, _, rfl⟩ := mem
    simp only [String.toList_append, List.all_append, percentEncode_visible, Bool.and_true,
      Bool.true_and]
    decide
  have segment : ∀ part ∈ (r.path.map percentEncode).map String.toList, part.all visible := by
    intro part mem
    simp only [List.map_map, List.mem_map, Function.comp_apply] at mem
    obtain ⟨s, _, rfl⟩ := mem
    exact percentEncode_visible s
  simp only [target, String.toList_append, List.all_append, String.toList_intercalate,
    Bool.and_eq_true]
  refine ⟨⟨by decide, all_intercalate _ _ (by decide) _ segment⟩, ?_⟩
  split
  · decide
  · simp only [String.toList_append, List.all_append, String.toList_intercalate, Bool.and_eq_true]
    exact ⟨by decide, all_intercalate _ _ (by decide) _ pair⟩

private theorem fields_plain (r : Request) (host : String) (h : host.toList.all visible) :
    ∀ field ∈ r.fields host, field.2.toList.all plain := by
  intro field mem
  rcases List.mem_append.mp mem with own | caller
  · simp at own
    rcases own with rfl | rfl | rfl
    · exact all_plain_of_visible h
    · decide
    · refine List.all_eq_true.mpr fun c mem => plain_of_visible (visible_of_tokenChar ?_)
      have digit : c ∈ Nat.toDigits 10 r.body.size := by
        simpa [Nat.toString_eq_repr, Nat.toList_repr] using mem
      simp [tokenChar, Char.isAlphanum, Nat.isDigit_of_mem_toDigits (by decide) (by decide) digit]
  · have passed := (List.mem_filter.mp caller).2
    simp only [Request.kept, Bool.and_eq_true] at passed
    exact passed.1.2

/-- No line of a head that is written has a control character other than tab. So none has a
CR or an LF, and the lines a server reads are the lines written. -/
theorem head_plain (r : Request) (host : String) (sent : (r.wire host).isSome) :
    ∀ line ∈ r.head host, line.toList.all plain := by
  have h : host.toList.all visible := by
    simp only [wire] at sent
    split at sent
    · simp_all
    · simp at sent
  intro line mem
  rcases List.mem_cons.mp mem with rfl | mem
  · simp only [String.toList_append, List.all_append, Bool.and_eq_true]
    refine ⟨⟨⟨?_, by decide⟩, all_plain_of_visible r.target_visible⟩, by decide⟩
    cases r.method <;> decide
  · obtain ⟨⟨name, value⟩, written, rfl⟩ := List.mem_map.mp mem
    have name_token := r.fields_token host _ written
    simp only [token, Bool.and_eq_true] at name_token
    simp only [String.toList_append, List.all_append, Bool.and_eq_true]
    refine ⟨⟨?_, by decide⟩, r.fields_plain host h _ written⟩
    exact List.all_eq_true.mpr fun c mem =>
      plain_of_visible (visible_of_tokenChar (List.all_eq_true.mp name_token.2 c mem))

end Request

/-- What a reader makes of the bytes it has so far: it needs more, or it is done, with a value
or with `none` for bytes that are no good. -/
inductive Reading (α : Type) where
  | more
  | done (answer : Option α)
  deriving DecidableEq, Repr

def Reading.map {α β : Type} (f : α → β) : Reading α → Reading β
  | .more => .more
  | .done answer => .done (answer.map f)

/-- The index just after the first blank line (`\r\n\r\n`) that starts at `pos` or later. -/
def headEnd (bytes : ByteArray) (pos : Nat := 0) : Option Nat :=
  if h : pos + 3 < bytes.size then
    if bytes[pos] == 13 && bytes[pos + 1] == 10 && bytes[pos + 2] == 13 && bytes[pos + 3] == 10
    then some (pos + 4)
    else headEnd bytes (pos + 1)
  else none
termination_by bytes.size - pos

/-- The index just after a CRLF at `pos`. -/
def crlf (bytes : ByteArray) (pos : Nat) : Reading Nat :=
  if h : pos + 1 < bytes.size then
    if bytes[pos] == 13 && bytes[pos + 1] == 10 then .done (some (pos + 2)) else .done none
  else if h : pos < bytes.size then
    if bytes[pos] == 13 then .more else .done none
  else .more

/-- The first index from `pos` on, and at most `fuel` further, whose byte fails `keep`. -/
def skip (bytes : ByteArray) (keep : UInt8 → Bool) : (fuel pos : Nat) → Nat
  | 0, pos => pos
  | fuel + 1, pos => if bytes[pos]?.any keep then skip bytes keep fuel (pos + 1) else pos

/-- The number written in hex digits from `pos` on, at most `fuel` of them, and the index after
those read. -/
def hex (bytes : ByteArray) : (fuel pos value : Nat) → Nat × Nat
  | 0, pos, value => (value, pos)
  | fuel + 1, pos, value =>
    match bytes[pos]?.bind fun b => hexValue? (Char.ofNat b.toNat) with
    | some digit => hex bytes fuel (pos + 1) (value * 16 + digit)
    | none => (value, pos)

/-- Every limit is explicit (rule 2.6). A size of more digits, or a longer run of blanks or
extension after it, is refused. -/
def chunkSizeDigits_max : Nat := 16

def chunkExtensionBytes_max : Nat := 256

/-- Where the CRLF of a size line whose digits end at `pos` should be: after blanks, and after
the extension if a `;` starts one. -/
def sizeLineEnd (bytes : ByteArray) (pos : Nat) : Nat :=
  let blanksEnd := skip bytes (fun b => b == 32 || b == 9) chunkExtensionBytes_max pos
  if bytes[blanksEnd]? == some 59 then
    skip bytes (fun b => b == 9 || (32 ≤ b && b != 127)) chunkExtensionBytes_max blanksEnd
  else blanksEnd

/-- The size of the chunk whose size line starts at `pos`, and where its data starts. The
extension is skipped. -/
def chunkHead (bytes : ByteArray) (pos : Nat) : Reading (Nat × Nat) :=
  let (size, digitsEnd) := hex bytes chunkSizeDigits_max pos 0
  if digitsEnd == pos then
    if pos < bytes.size then .done none else .more
  else (crlf bytes (sizeLineEnd bytes digitsEnd)).map (size, ·)

/-- The chunked body from `pos` on, added to `body`, and the index after it. `fuel` bounds the
number of chunks. The trailer after the last chunk is skipped unread, up to its blank line. -/
def dechunk (bytes : ByteArray) : (fuel pos : Nat) → (body : ByteArray) → Reading (ByteArray × Nat)
  | 0, _, _ => .done none
  | fuel + 1, pos, body =>
    match chunkHead bytes pos with
    | .more => .more
    | .done none => .done none
    | .done (some (size, start)) =>
      if size = 0 then
        match crlf bytes start with
        | .done none =>
          match headEnd bytes start with
          | some stop => .done (some (body, stop))
          | none => .more
        | ending => ending.map (body, ·)
      else
        match crlf bytes (start + size) with
        | .done (some next) => dechunk bytes fuel next (body ++ bytes.extract start (start + size))
        | .done none => .done none
        | .more => .more

/-- The number that one to eighteen ASCII digits write. `String.toNat?` would also take `1_0`. -/
def decimal? (s : String) : Option Nat :=
  if s != "" && s.length ≤ 18 && s.toList.all Char.isDigit then
    some (Nat.ofDigitChars 10 s.toList 0)
  else none

/-- The lines of `text` split at each CRLF, after the `line` begun and the lines `done`, which
are reversed. -/
def splitLines : (text line : List Char) → (done : List (List Char)) → List (List Char)
  | [], line, done => (line.reverse :: done).reverse
  | '\r' :: '\n' :: rest, line, done => splitLines rest [] (line.reverse :: done)
  | c :: rest, line, done => splitLines rest (c :: line) done

/-- The status of a status line. A bare CR or another control character in the reason is
refused (RFC 9112, 2.2). -/
def statusLine? : List Char → Option Nat
  | 'H' :: 'T' :: 'T' :: 'P' :: '/' :: '1' :: '.' :: minor :: ' ' :: code =>
    let (digits, reason) := code.splitAt 3
    if (minor == '0' || minor == '1') && digits.length == 3 && reason.head?.all (· == ' ')
        && reason.all plain then
      (decimal? (String.ofList digits)).filter (100 ≤ ·)
    else none
  | _ => none

def trimOws (chars : List Char) : List Char :=
  ((chars.dropWhile ows).reverse.dropWhile ows).reverse

/-- A header, its name in lowercase and its value trimmed. The name is a token right up to the
colon, so a line that continues the one before it and a blank before the colon are refused. -/
def headerLine? (line : List Char) : Option (String × String) :=
  let name := String.ofList (line.takeWhile (· != ':'))
  match line.dropWhile (· != ':') with
  | _ :: value =>
    if token name && value.all plain then some (name.toLower, String.ofList (trimOws value))
    else none
  | [] => none

/-- The status and the headers of a head given without its blank line. -/
def head? (text : List Char) : Option (Nat × List (String × String)) :=
  match splitLines text [] [] with
  | statusLine :: headerLines => do
    let status ← statusLine? statusLine
    let headers ← headerLines.mapM headerLine?
    return (status, headers)
  | [] => none

inductive Framing where
  | length (bytes : Nat)
  | chunked
  | toEnd

/-- Where the body ends (RFC 9112, 6.3): `none` unless the headers say so in one way. -/
def framing? (status : Nat) (headers : List (String × String)) : Option Framing :=
  let codings := (headers.filter (·.1 == "transfer-encoding")).map (·.2.toLower)
  let lengths := (headers.filter (·.1 == "content-length")).map (decimal? ·.2)
  if status == 204 || status == 304 then some (.length 0)
  else
    match codings, lengths with
    | [], [] => some .toEnd
    | [], some length :: rest =>
      if rest.all (· == some length) then some (.length length) else none
    | ["chunked"], [] => some .chunked
    | _, _ => none

/-- The response whose head starts at `pos`, or the one after it when that one is interim
(`1xx`), and the index just after it. `fuel` bounds the number of interim responses. -/
def readFrom (bytes : ByteArray) (ended : Bool) : (fuel pos : Nat) → Reading (Response × Nat)
  | 0, _ => .done none
  | fuel + 1, pos =>
    match headEnd bytes pos with
    | none => .more
    | some bodyStart =>
      match (String.fromUTF8? (bytes.extract pos (bodyStart - 4))).bind (head? ·.toList) with
      | none => .done none
      | some (status, headers) =>
        if status < 200 then readFrom bytes ended fuel bodyStart
        else
          match framing? status headers with
          | none => .done none
          | some (.length length) =>
            if bodyStart + length ≤ bytes.size then
              let body := bytes.extract bodyStart (bodyStart + length)
              .done (some ({ status, headers, body }, bodyStart + length))
            else .more
          | some .chunked =>
            (dechunk bytes (bytes.size + 1) bodyStart .empty).map
              fun (body, stop) => ({ status, headers, body }, stop)
          | some .toEnd =>
            if ended then
              .done (some ({ status, headers, body := bytes.extract bodyStart bytes.size },
                bytes.size))
            else .more

/-- What the bytes received so far amount to, where `ended` says that no more will come: the
response, as soon as its last byte is there, if it ends within `limit` bytes; `none` for a
response that does not, for more than `limit` bytes without a response, for what cannot become
a response, and for a response cut short; or that more is needed. -/
def Response.read (limit : Nat) (bytes : ByteArray) (ended : Bool) : Reading Response :=
  match readFrom bytes ended (bytes.size + 1) 0 with
  | .done (some (response, stop)) => if stop ≤ limit then .done (some response) else .done none
  | .done none => .done none
  | .more => if ended || limit < bytes.size then .done none else .more

/-- A reader that asks again only on `more` stops when the connection ends. -/
theorem Response.read_ended (limit : Nat) (bytes : ByteArray) :
    Response.read limit bytes true ≠ .more := by
  unfold Response.read
  split
  · split <;> simp
  · simp
  · simp

/-- The one response in all the bytes of a connection. -/
def Response.parse (bytes : ByteArray) : Option Response :=
  match Response.read bytes.size bytes true with
  | .done answer => answer
  | .more => none

end Lanes.Http
