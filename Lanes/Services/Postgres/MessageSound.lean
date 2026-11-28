/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Services.Postgres.Message

/-!
The decoders read back what the encoders write: every backend message within its bounds, in a
frame wherever it starts in a buffer and whatever follows it (`Backend.read_encode`), and every
frontend message (`Frontend.decode_encode`). A frame is read only when it is all there, and the
reader waits only while fewer than `message_max` bytes are there (`Frame.read_more`).
-/

@[expose] public section

namespace Lanes.Postgres

theorem Column.inverse : Inverse Column.put Column.get Column.Ok := by
  intro c rest ⟨hname, htable, hpos, htype, hsize, hmod, hformat⟩
  simp only [Column.put, List.append_assoc, Column.get, inverse_str _ _ hname,
    inverse_u32 _ _ htable, inverse_u16 _ _ hpos, inverse_u32 _ _ htype, inverse_u16 _ _ hsize,
    inverse_u32 _ _ hmod, inverse_u16 _ _ hformat, Option.bind_eq_bind, Option.bind_some]
  rfl

theorem Field.inverse : Inverse Field.put Field.get Field.Ok := by
  intro f rest ⟨_, hvalue⟩
  simp only [Field.put, List.cons_append, Field.get, byte, inverse_str _ _ hvalue,
    Option.bind_eq_bind, Option.bind_some]
  rfl

theorem Field.starts : StartsNonzero Field.put Field.Ok := by
  intro f ⟨hcode, _⟩
  exact ⟨f.code, putStr f.value, rfl, hcode⟩

theorem toByteArray_ne_nil {s : String} (h : s ≠ "") : s.toByteArray.data.toList ≠ [] := by
  rw [data_toList_toByteArray]
  match hs : s.toList with
  | [] => exact absurd (String.toList_eq_nil_iff.mp hs) h
  | c :: _ =>
    rw [List.flatMap_cons]
    exact fun hnil => String.utf8EncodeChar_ne_nil (List.append_eq_nil_iff.mp hnil).1

theorem putStr_starts : StartsNonzero putStr Named := by
  intro s ⟨hplain, hne⟩
  have hz := zero_not_mem_toByteArray hplain
  match hbytes : s.toByteArray.data.toList, toByteArray_ne_nil hne with
  | b :: bs, _ =>
    refine ⟨b, bs ++ [0], by simp [putStr, hbytes], ?_⟩
    intro hb
    apply hz
    rw [hbytes, hb]
    simp

theorem param_inverse : Inverse putParam getParam fun p => Plain p.1 ∧ Plain p.2 := by
  intro p rest ⟨h1, h2⟩
  simp only [putParam, List.append_assoc, getParam, inverse_str _ _ h1, inverse_str _ _ h2,
    Option.bind_eq_bind, Option.bind_some]
  rfl

theorem param_starts : StartsNonzero putParam fun p => Named p.1 ∧ Plain p.2 := by
  intro p ⟨h1, _⟩
  obtain ⟨b, bs, henc, hb⟩ := putStr_starts p.1 h1
  exact ⟨b, bs ++ putStr p.2, by simp [putParam, henc], hb⟩

theorem getTerminated_whole {α : Type} {enc : α → List UInt8} {p : Parse α} {ok : α → Prop}
    (law : Inverse enc p ok) (starts : StartsNonzero enc ok) (as : List α) (h : ∀ a ∈ as, ok a) :
    whole (getTerminated p (putTerminated enc as).length) (putTerminated enc as) = some as := by
  have hlen := length_le_flatMap starts as h
  have := getTerminated_append law starts as h [] (putTerminated enc as).length
    (by simp only [putTerminated, List.length_append, List.length_singleton]; omega)
  rw [List.append_nil] at this
  simp [whole, this]

theorem getFields_put (fields : List Field) (h : ∀ f ∈ fields, f.Ok) :
    getFields (putTerminated Field.put fields) = some fields :=
  getTerminated_whole Field.inverse Field.starts fields h

theorem getNames_put (names : List String) (h : ∀ s ∈ names, Named s) :
    getNames (putTerminated putStr names) = some names :=
  getTerminated_whole (ok := Named) (fun s rest hs => inverse_str s rest hs.1) putStr_starts names h

theorem TxStatus.ofByte_byte (s : TxStatus) : TxStatus.ofByte s.byte = some s := by
  cases s <;> rfl

theorem length_putU32 (n : Nat) : (putU32 n).length = 4 := rfl

/-- Every backend message within its bounds is read back from its body. -/
theorem getU32_put (n : Nat) (rest : List UInt8) (h : n < 4294967296) :
    getU32 (putU32 n ++ rest) = some (n, rest) :=
  inverse_u32 _ _ h

theorem whole_putU32 {n : Nat} (h : n < 4294967296) : getU32 (putU32 n) = some (n, []) := by
  rw [← List.append_nil (putU32 n)]
  exact inverse_u32 _ _ h

/-- Every backend message within its bounds is read back from its body. -/
theorem Backend.decodeBody_body (m : Backend) (h : m.Ok) : Backend.decodeBody m.tag m.body = some m := by
  cases m with
  | authOk =>
    simp only [Backend.tag, Backend.body, Backend.decodeBody, Backend.decodeAuth,
      whole_putU32 (show 0 < 4294967296 by decide), ite_true]
  | authCleartext =>
    simp only [Backend.tag, Backend.body, Backend.decodeBody, Backend.decodeAuth,
      whole_putU32 (show 3 < 4294967296 by decide), ite_true]
  | authMd5 salt =>
    have hl : salt.data.toList.length = 4 := by rw [Array.length_toList]; exact h
    simp only [Backend.tag, Backend.body, Backend.decodeBody, Backend.decodeAuth,
      getU32_put 5 _ (by decide), hl, ite_true]
  | authSasl mechanisms =>
    simp only [Backend.tag, Backend.body, Backend.decodeBody, Backend.decodeAuth,
      getU32_put 10 _ (by decide), getNames_put mechanisms h, ite_true, Option.map_some]
  | authSaslContinue data =>
    simp only [Backend.tag, Backend.body, Backend.decodeBody, Backend.decodeAuth,
      getU32_put 11 _ (by decide), ite_true]
  | authSaslFinal data =>
    simp only [Backend.tag, Backend.body, Backend.decodeBody, Backend.decodeAuth,
      getU32_put 12 _ (by decide), ite_true]
  | parameterStatus name value =>
    have := whole_append param_inverse (a := (name, value)) h
    simp only [putParam] at this
    simp only [Backend.tag, Backend.body]
    unfold Backend.decodeBody
    simp [this]
  | backendKeyData pid secret =>
    obtain ⟨h1, h2⟩ := h
    simp only [Backend.tag, Backend.body]
    unfold Backend.decodeBody
    simp only [whole, getU32_put pid _ h1, whole_putU32 h2, Option.bind_eq_bind, Option.bind_some]
    simp
  | readyForQuery status =>
    simp only [Backend.tag, Backend.body]
    unfold Backend.decodeBody
    simp [TxStatus.ofByte_byte]
  | parseComplete => rfl
  | bindComplete => rfl
  | closeComplete => rfl
  | noData => rfl
  | portalSuspended => rfl
  | emptyQuery => rfl
  | rowDescription columns =>
    simp only [Backend.tag, Backend.body]
    unfold Backend.decodeBody
    simp [whole_append (inverse_list16 Column.inverse) h]
  | dataRow values =>
    simp only [Backend.tag, Backend.body]
    unfold Backend.decodeBody
    simp [whole_append (inverse_list16 inverse_value) h]
  | commandComplete tag =>
    simp only [Backend.tag, Backend.body]
    unfold Backend.decodeBody
    simp [whole_append inverse_str (show Plain tag from h)]
  | errorResponse fields =>
    simp only [Backend.tag, Backend.body]
    unfold Backend.decodeBody
    simp [getFields_put fields h]
  | noticeResponse fields =>
    simp only [Backend.tag, Backend.body]
    unfold Backend.decodeBody
    simp [getFields_put fields h]
  | parameterDescription types =>
    simp only [Backend.tag, Backend.body]
    unfold Backend.decodeBody
    simp [whole_append (inverse_list16 inverse_u32) h]

/-! ## Frames -/

theorem getElem?_frame (pre post : ByteArray) (bytes : List UInt8) (i : Nat) (h : i < bytes.length) :
    (pre ++ (⟨bytes.toArray⟩ ++ post))[pre.size + i]? = some bytes[i] := by
  rw [getElem?_append_front, ByteArray.data_append, Array.toList_append]
  simp [List.getElem?_append_left (show i < bytes.length from h)]

theorem size_mk (bytes : List UInt8) : (⟨bytes.toArray⟩ : ByteArray).size = bytes.length := by
  simp [ByteArray.size]

/-- A frame of type `tag` and body `body`, within `message_max`, is read whole, wherever it
starts and whatever follows it. -/
theorem Frame.read_frame (message_max : Nat) (pre post : ByteArray) (tag : UInt8) (body : List UInt8)
    (hmax : body.length + 4 ≤ message_max) (hbound : body.length + 4 < 4294967296) :
    Frame.read message_max (pre ++ (⟨(tag :: putU32 (body.length + 4) ++ body).toArray⟩ ++ post)) pre.size
      = .done tag ⟨body.toArray⟩ (pre.size + (body.length + 5)) := by
  have hlen : (tag :: putU32 (body.length + 4) ++ body).length = body.length + 5 := by
    simp [length_putU32]; omega
  have at_ (i : Nat) (hi : i < body.length + 5) := getElem?_frame pre post
    (tag :: putU32 (body.length + 4) ++ body) i (by omega)
  have h0 : (pre ++ (⟨(tag :: putU32 (body.length + 4) ++ body).toArray⟩ ++ post))[pre.size]?
      = some tag := by
    simpa using at_ 0 (by omega)
  have hsize : (pre ++ (⟨(tag :: putU32 (body.length + 4) ++ body).toArray⟩ ++ post)).size
      = pre.size + (body.length + 5) + post.size := by
    simp only [ByteArray.size_append, size_mk, hlen]; omega
  have hsplit : pre ++ (⟨(tag :: putU32 (body.length + 4) ++ body).toArray⟩ ++ post)
      = (pre ++ ⟨(tag :: putU32 (body.length + 4)).toArray⟩) ++ (⟨body.toArray⟩ ++ post) := by
    apply ByteArray.ext
    apply Array.ext'
    simp [ByteArray.data_append]
  have hextract : (pre ++ (⟨(tag :: putU32 (body.length + 4) ++ body).toArray⟩ ++ post)).extract
      (pre.size + 5) (pre.size + 1 + (body.length + 4)) = ⟨body.toArray⟩ := by
    rw [hsplit]
    have := extract_append_front (pre ++ ⟨(tag :: putU32 (body.length + 4)).toArray⟩)
      ⟨body.toArray⟩ post
    simp only [ByteArray.size_append, size_mk, List.length_cons, length_putU32] at this
    rw [show pre.size + 1 + (body.length + 4) = pre.size + (4 + 1) + body.length by omega]
    exact this
  unfold Frame.read
  rw [h0, at_ 1 (by omega), at_ 2 (by omega), at_ 3 (by omega), at_ 4 (by omega)]
  have b1 : (tag :: putU32 (body.length + 4) ++ body)[1]'(by omega)
      = ((body.length + 4) / 16777216 % 256).toUInt8 := rfl
  have b2 : (tag :: putU32 (body.length + 4) ++ body)[2]'(by omega)
      = ((body.length + 4) / 65536 % 256).toUInt8 := rfl
  have b3 : (tag :: putU32 (body.length + 4) ++ body)[3]'(by omega)
      = ((body.length + 4) / 256 % 256).toUInt8 := rfl
  have b4 : (tag :: putU32 (body.length + 4) ++ body)[4]'(by omega)
      = ((body.length + 4) % 256).toUInt8 := rfl
  have hval : (((((body.length + 4) / 16777216 % 256).toUInt8.toNat * 256
      + ((body.length + 4) / 65536 % 256).toUInt8.toNat) * 256
      + ((body.length + 4) / 256 % 256).toUInt8.toNat) * 256
      + ((body.length + 4) % 256).toUInt8.toNat) = body.length + 4 := by
    simp only [toNat_toUInt8]
    omega
  dsimp only
  rw [b1, b2, b3, b4, hval, ite_eq_right (by omega), ite_eq_left (by omega), hextract]
  congr 1
  omega

/-- Every backend message within its bounds, written as `Backend.encode` writes it, is read back
whole: its frame from wherever it starts, whatever follows, and the message from the frame. -/
theorem Backend.read_encode (message_max : Nat) (pre post : ByteArray) (m : Backend) (h : m.Ok)
    (hmax : m.body.length + 4 ≤ message_max) (hbound : message_max < 4294967296) :
    Frame.read message_max (pre ++ (m.encode ++ post)) pre.size
        = .done m.tag ⟨m.body.toArray⟩ (pre.size + m.encode.size)
      ∧ Backend.decode m.tag ⟨m.body.toArray⟩ = some m := by
  refine ⟨?_, ?_⟩
  · rw [Backend.encode, Backend.wire, Frame.read_frame message_max pre post m.tag m.body hmax (by omega)]
    simp [size_mk, length_putU32]
    omega
  · simpa [Backend.decode] using Backend.decodeBody_body m h

/-- The reader waits for more only while fewer than `message_max` bytes from `pos` are there. -/
theorem Frame.read_more {message_max : Nat} {buffer : ByteArray} {pos : Nat} (hmin : 4 ≤ message_max)
    (h : Frame.read message_max buffer pos = .more) : buffer.size - pos ≤ message_max := by
  by_cases hs : buffer.size ≤ pos + 4
  · omega
  · unfold Frame.read at h
    rw [getElem?_pos buffer pos (by omega), getElem?_pos buffer (pos + 1) (by omega),
      getElem?_pos buffer (pos + 2) (by omega), getElem?_pos buffer (pos + 3) (by omega),
      getElem?_pos buffer (pos + 4) (by omega)] at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · omega

/-- A frame read ends after where it starts and within the buffer. -/
theorem Frame.read_done {message_max : Nat} {buffer : ByteArray} {pos : Nat} {tag : UInt8}
    {body : ByteArray} {next : Nat} (h : Frame.read message_max buffer pos = .done tag body next) :
    pos < next ∧ next ≤ buffer.size ∧ body.size + 4 ≤ message_max := by
  unfold Frame.read at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · injection h with _ hbody hnext
        subst hbody hnext
        rw [ByteArray.size_extract]
        omega
      · cases h
  · cases h

/-! ## The frontend -/

theorem Frontend.decode_frame (e : Frontend.Expect) (he : e ≠ .startup) (tag : UInt8)
    (body : List UInt8) (hb : body.length + 4 < 4294967296) :
    Frontend.decode e ⟨(tag :: putU32 (body.length + 4) ++ body).toArray⟩
      = Frontend.decodeBody e tag body := by
  cases e with
  | startup => exact absurd rfl he
  | _ => simp [Frontend.decode, getU32_put _ _ hb]

theorem mk_toList (data : ByteArray) : (⟨data.data.toList.toArray⟩ : ByteArray) = data := by
  simp

theorem param_inverse' : Inverse putParam getParam fun p => Named p.1 ∧ Plain p.2 :=
  fun p rest h => param_inverse p rest ⟨h.1.1, h.2⟩

/-- Every frontend message within its bounds is read back by a server that expects it. -/
theorem Frontend.decode_encode (m : Frontend) (h : m.Ok) (hbound : m.body.length + 4 < 4294967296) :
    Frontend.decode m.expect m.encode = some m := by
  cases m with
  | startup params =>
    have hbody : (Frontend.startup params).body = putU32 protocol30 ++ putTerminated putParam params := rfl
    have hp := getTerminated_whole param_inverse' param_starts params h
    simp only [Frontend.decode, Frontend.encode, Frontend.wire, List.toList_toArray, Frontend.expect,
      Frontend.decodeStartup, getU32_put _ _ hbound, ↓reduceIte]
    rw [hbody, getU32_put _ _ (show protocol30 < 4294967296 by decide)]
    simp [hp]
  | password p =>
    simp only [Frontend.expect, Frontend.encode, Frontend.wire]
    rw [Frontend.decode_frame _ (by decide) _ _ hbound]
    simp [Frontend.decodeBody, Frontend.tag, Frontend.body, whole_append inverse_str (show Plain p from h)]
  | saslInitial mechanism data =>
    obtain ⟨h1, h2⟩ := h
    simp only [Frontend.expect, Frontend.encode, Frontend.wire]
    rw [Frontend.decode_frame _ (by decide) _ _ hbound]
    have hlen : data.data.toList.length = data.size := Array.length_toList
    simp only [Frontend.decodeBody, Frontend.tag, Frontend.body, ite_true, whole, List.append_assoc,
      inverse_str _ _ h1, Option.bind_eq_bind, Option.bind_some,
      getU32_put _ _ (show data.size < 4294967296 by omega)]
    have ht : take data.data.toList.length data.data.toList = some (data.data.toList, []) := by
      simpa using take_append data.data.toList []
    rw [← hlen, ht]
    simp
  | saslResponse data =>
    simp only [Frontend.expect, Frontend.encode, Frontend.wire]
    rw [Frontend.decode_frame _ (by decide) _ _ hbound]
    simp [Frontend.decodeBody, Frontend.tag, Frontend.body]
  | query sql =>
    simp only [Frontend.expect, Frontend.encode, Frontend.wire]
    rw [Frontend.decode_frame _ (by decide) _ _ hbound]
    simp [Frontend.decodeBody, Frontend.tag, Frontend.body, whole_append inverse_str (show Plain sql from h)]
  | parse statement sql types =>
    obtain ⟨h1, h2, h3⟩ := h
    simp only [Frontend.expect, Frontend.encode, Frontend.wire]
    rw [Frontend.decode_frame _ (by decide) _ _ hbound]
    have := inverse_list16 inverse_u32 types [] h3
    rw [List.append_nil] at this
    simp [Frontend.decodeBody, Frontend.tag, Frontend.body, whole, inverse_str _ _ h1,
      inverse_str _ _ h2, this]
  | bind portal statement formats params results =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only [Frontend.expect, Frontend.encode, Frontend.wire]
    rw [Frontend.decode_frame _ (by decide) _ _ hbound]
    have := inverse_list16 inverse_u16 results [] h5
    rw [List.append_nil] at this
    simp [Frontend.decodeBody, Frontend.tag, Frontend.body, whole, inverse_str _ _ h1,
      inverse_str _ _ h2, inverse_list16 inverse_u16 _ _ h3, inverse_list16 inverse_value _ _ h4, this]
  | describe portal name =>
    simp only [Frontend.expect, Frontend.encode, Frontend.wire]
    rw [Frontend.decode_frame _ (by decide) _ _ hbound]
    cases portal <;>
      simp [Frontend.decodeBody, Frontend.tag, Frontend.body, whole_append inverse_str (show Plain name from h)]
  | execute portal rows =>
    obtain ⟨h1, h2⟩ := h
    simp only [Frontend.expect, Frontend.encode, Frontend.wire]
    rw [Frontend.decode_frame _ (by decide) _ _ hbound]
    simp [Frontend.decodeBody, Frontend.tag, Frontend.body, whole, inverse_str _ _ h1, whole_putU32 h2]
  | sync =>
    simp only [Frontend.expect, Frontend.encode, Frontend.wire]
    rw [Frontend.decode_frame _ (by decide) _ _ hbound]
    simp [Frontend.decodeBody, Frontend.tag, Frontend.body]
  | terminate =>
    simp only [Frontend.expect, Frontend.encode, Frontend.wire]
    rw [Frontend.decode_frame _ (by decide) _ _ hbound]
    simp [Frontend.decodeBody, Frontend.tag, Frontend.body]

end Lanes.Postgres
