import Lanes

/-!
# Uploads with a running checksum

The spec, the actor and its proofs. A client sends a body as large as it likes; the server hands
it to the system in pieces (`Http.Stream`), each a request of its own through the gate, and the
system keeps, for each upload, how many bytes it has taken and their checksum, never the bytes.
The answer to the upload is the size and the
checksum of its pieces, in the order of their index.
-/

namespace Upload

open Lanes

abbrev ReqId := Nat

/-- Adler-32, as a running sum over bytes. -/
lanes_data structure Sum where
  a : Nat := 1
  b : Nat := 0
  deriving DecidableEq, Repr, Hashable, Codable

def Sum.add (s : Sum) (byte : UInt8) : Sum :=
  let a := (s.a + byte.toNat) % 65521
  { a, b := (s.b + a) % 65521 }

def Sum.feed (s : Sum) (data : ByteArray) : Sum :=
  data.data.toList.foldl Sum.add s

def Sum.value (s : Sum) : Nat := s.b * 65536 + s.a

/-- The checksum of `data`. -/
def checksum (data : ByteArray) : Nat := ({} : Sum).feed data |>.value

/-- Feeding two runs of bytes one after the other is feeding them together. -/
theorem Sum.feed_append (s : Sum) (x y : ByteArray) : s.feed (x ++ y) = (s.feed x).feed y := by
  simp [Sum.feed, ByteArray.data_append, List.foldl_append]

lanes_data structure Progress where
  /-- The index of the next piece. -/
  next : Nat := 0
  size : Nat := 0
  sum : Sum := {}
  deriving DecidableEq, Repr, Hashable, Codable

def Progress.take (p : Progress) (data : ByteArray) : Progress :=
  { next := p.next + 1, size := p.size + data.size, sum := p.sum.feed data }

lanes_data inductive Request where
  /-- The head of an upload, whose body follows in pieces. -/
  | start (req : ReqId)
  /-- Piece `index` of the body of the upload `head`. -/
  | piece (req head index : Nat) (data : ByteArray) (last : Bool)
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Answer where
  | taken
  /-- Too many uploads at once. -/
  | busy
  | unknown
  | outOfOrder
  | done (size sum : Nat)
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data structure Response where
  req : ReqId
  answer : Answer
  deriving DecidableEq, Repr, Hashable, Codable

structure Config where
  /-- Uploads under way at once; one more is answered `busy` (rule 2.6). -/
  uploads_max : Nat := 64

abbrev sig : Signature := Server.sig Request Response

abbrev State := List (ReqId × Progress)

/-- The spec, and the implementation, as the `Server` behaviour runs it. A piece of an upload
nobody started, or not the next one, is refused; the last piece answers the upload. -/
def service (config : Config) : Service sig.In sig.Out State where
  init := []
  step uploads
    | .start req =>
      if (uploads.lookup req).isSome then (uploads, [])
      else if config.uploads_max ≤ uploads.length then (uploads, [⟨req, .busy⟩])
      else ((req, {}) :: uploads, [])
    | .piece req head index data last =>
      match uploads.lookup head with
      | none => (uploads, [⟨req, .unknown⟩])
      | some p =>
        if index != p.next then (uploads, [⟨req, .outOfOrder⟩])
        else
          let p := p.take data
          let rest := uploads.filter (·.1 != head)
          if last then (rest, [⟨req, .taken⟩, ⟨head, .done p.size p.sum.value⟩])
          else ((head, p) :: rest, [⟨req, .taken⟩])

abbrev system (config : Config) : System sig :=
  Server.system (service config)

theorem mem_of_lookup : ∀ {l : State} {k : ReqId} {v : Progress}, l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by simp at h
  | (k', v') :: l, k, v, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i e
      cases h
      simp only [beq_iff_eq] at e
      simp [e]
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem step_le (config : Config) (uploads : State) (msg : Request)
    (h : uploads.length ≤ config.uploads_max) :
    ((service config).step uploads msg).1.length ≤ config.uploads_max := by
  have hf : ∀ head : ReqId, (uploads.filter (·.1 != head)).length ≤ uploads.length :=
    fun _ => List.length_filter_le _ _
  cases msg with
  | start req =>
    simp only [service]
    repeat' split
    all_goals simp_all
    omega
  | piece req head index data last =>
    simp only [service]
    split
    · exact h
    · split
      · exact h
      · split
        · exact Nat.le_trans (hf head) h
        · rename_i p hp _ _
          have hin : 0 < uploads.length := by
            cases uploads with
            | nil => simp at hp
            | cons _ _ => simp
          have hlt : (uploads.filter (·.1 != head)).length < uploads.length := by
            refine List.length_filter_lt_length_iff_exists.mpr ⟨(head, p), mem_of_lookup hp, by simp⟩
          simp only [List.length_cons]
          omega

/-- No more uploads are under way than the bound. -/
theorem uploads_le (config : Config) :
    (Server.actor (service config)).Invariant fun uploads => uploads.length ≤ config.uploads_max :=
  Actor.Inductive.invariant
    ⟨by simp [Server.actor, service], fun s msg h => step_le config s msg h, fun _ h => h⟩

/-- The piece an upload waits for is taken: the upload goes on from what it had, with the piece's
bytes after them. -/
theorem step_piece (config : Config) (uploads : State) {req head index : Nat} {data : ByteArray}
    {last : Bool} {p : Progress} (h : uploads.lookup head = some p) (hi : index = p.next) :
    (service config).step uploads (.piece req head index data last)
      = if last then (uploads.filter (·.1 != head),
          [⟨req, .taken⟩, ⟨head, .done (p.take data).size (p.take data).sum.value⟩])
        else ((head, p.take data) :: uploads.filter (·.1 != head), [⟨req, .taken⟩]) := by
  simp [service, h, hi]

/-- Pieces taken one after another leave the size and the checksum of their bytes together: the
answer to an upload is the size and the checksum of its pieces, in order. -/
theorem take_take (p : Progress) (x y : ByteArray) :
    ((p.take x).take y).size = p.size + (x ++ y).size
      ∧ ((p.take x).take y).sum = p.sum.feed (x ++ y) := by
  simp [Progress.take, Sum.feed_append, Nat.add_assoc]

/-- From the start, the answer is the size and the checksum of the bytes. -/
theorem start_take (data : ByteArray) :
    (({} : Progress).take data).size = data.size
      ∧ (({} : Progress).take data).sum.value = checksum data := by
  simp [Progress.take, checksum]

end Upload
