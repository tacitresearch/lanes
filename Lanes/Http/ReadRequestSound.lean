/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Http.ReadRequest
public import Lanes.Http.WireSound

/-!
What the request reader of `Lanes.Http.ReadRequest` does, for every input and every limit:

- an answer once given stays as more bytes arrive (`Request.read_extract`, `Request.read_append`);
- it asks for more only while fewer than `message_max` bytes have arrived from where it starts,
  and a request it gives ends within them, its body within `body_max` (`Request.read_more`,
  `Request.read_done`);
-/

@[expose] public section

namespace Lanes.Http

/-! What the theorems are stated against -/

namespace Request

/-- Whether what `wire` writes of `r` for `host` is within `limits`, and is a request the
reader can give back as it was: a host the reader takes, and a path other than `[""]`, which is
written as `/` like the empty path. -/
def fits (limits : Limits) (r : Request) (host : String) : Bool :=
  ((r.head host).headD "").utf8ByteSize ≤ limits.line_max
    && ("\r\n".intercalate (r.head host)).utf8ByteSize + 4 ≤ limits.head_max
    && (r.fields host).length ≤ limits.fields_max
    && r.body.size ≤ limits.body_max && r.body.size < 10 ^ 18
    && host.toList.all hostChar && r.path != [""]

/-- What the reader gives back of the bytes `wire` writes of `r` for `host`: the writer's own
headers and the caller's that are written, in lowercase and without the blanks around their
values. -/
def sent (r : Request) (host : String) : Incoming where
  request := { r with
    headers := (r.fields host).map fun (name, value) =>
      (name.toLower, String.ofList (trimOws value.toList)) }
  headOnly := false
  close := true

/-- The bytes of a head a sender writes as `lines`: each but the last ended by CRLF, then a
blank line. -/
def headWire (lines : List String) : ByteArray :=
  ("\r\n".intercalate lines ++ "\r\n\r\n").toUTF8

end Request

/-! Finding a pattern -/

theorem matchAt_iff {bytes : ByteArray} : ∀ {pattern : List UInt8} {i : Nat},
    matchAt bytes pattern i = true ↔ ∀ k (hk : k < pattern.length), bytes[i + k]? = some pattern[k]
  | [], i => by simp [matchAt]
  | b :: rest, i => by
    simp only [matchAt, Bool.and_eq_true, beq_iff_eq, matchAt_iff, List.length_cons]
    constructor
    · rintro ⟨h0, hrest⟩ k hk
      cases k with
      | zero => simpa using h0
      | succ k =>
        have := hrest k (by omega)
        rw [show i + (k + 1) = i + 1 + k by omega]
        simpa using this
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun k hk => ?_⟩
      have := h (k + 1) (by omega)
      rw [show i + (k + 1) = i + 1 + k by omega] at this
      simpa using this

theorem matchAt_extract {bytes : ByteArray} {n : Nat} :
    ∀ {pattern : List UInt8} {j : Nat}, j + pattern.length ≤ n →
      matchAt (bytes.extract 0 n) pattern j = matchAt bytes pattern j
  | [], _, _ => rfl
  | b :: rest, j, h => by
    simp only [List.length_cons] at h
    have ih := matchAt_extract (bytes := bytes) (n := n) (pattern := rest) (j := j + 1) (by omega)
    simp only [matchAt, getElem?_extract_zero, show j < n by omega, ↓reduceIte, ih]

theorem find_congr {b₁ b₂ : ByteArray} {pattern : List UInt8} {s₁ s₂ W : Nat}
    (hW₁ : min s₁ b₁.size = W) (hW₂ : min s₂ b₂.size = W)
    (h : ∀ j, j + pattern.length ≤ W → matchAt b₁ pattern j = matchAt b₂ pattern j) (pos : Nat) :
    find b₁ pattern pos s₁ = find b₂ pattern pos s₂ := by
  fun_induction find b₁ pattern pos s₁ with
  | case1 pos hc hm =>
    rw [find.eq_1 b₂]
    simp only [show pos + pattern.length ≤ min s₂ b₂.size by omega, ← h pos (by omega), hm,
      ↓reduceIte]
  | case2 pos hc hm ih =>
    rw [find.eq_1 b₂]
    simp only [show pos + pattern.length ≤ min s₂ b₂.size by omega, ← h pos (by omega), hm,
      ↓reduceIte, Bool.false_eq_true, ih]
  | case3 pos hc =>
    rw [find.eq_1 b₂]
    simp only [show ¬ pos + pattern.length ≤ min s₂ b₂.size by omega, ↓reduceIte]

theorem find_extract (bytes : ByteArray) (n : Nat) (pattern : List UInt8) (pos stop : Nat) :
    find (bytes.extract 0 n) pattern pos stop = find bytes pattern pos (min stop n) := by
  have hsize := size_extract_zero bytes n
  refine find_congr (W := min (min stop n) bytes.size) (by omega) rfl (fun j hj => ?_) pos
  exact matchAt_extract (by omega)

theorem find_bound {bytes : ByteArray} {pattern : List UInt8} {pos stop i : Nat}
    (h : find bytes pattern pos stop = some i) :
    pos ≤ i ∧ i + pattern.length ≤ stop ∧ i + pattern.length ≤ bytes.size
      ∧ matchAt bytes pattern i = true := by
  fun_induction find bytes pattern pos stop with
  | case1 pos hc hm =>
    cases h
    exact ⟨Nat.le_refl _, by omega, by omega, hm⟩
  | case2 pos hc hm ih =>
    have := ih h
    exact ⟨by omega, this.2⟩
  | case3 => cases h

theorem find_le (bytes : ByteArray) (pattern : List UInt8) {s stop : Nat} (hs : s ≤ stop)
    (pos : Nat) :
    find bytes pattern pos s = find bytes pattern pos stop ∨ find bytes pattern pos s = none := by
  fun_induction find bytes pattern pos stop with
  | case1 pos hc hm =>
    rw [find.eq_1 bytes pattern pos s]
    by_cases hc' : pos + pattern.length ≤ min s bytes.size
    · simp [hc', hm]
    · simp [hc']
  | case2 pos hc hm ih =>
    rw [find.eq_1 bytes pattern pos s]
    by_cases hc' : pos + pattern.length ≤ min s bytes.size
    · simpa [hc', hm] using ih
    · simp [hc']
  | case3 pos hc =>
    rw [find.eq_1 bytes pattern pos s]
    simp [show ¬ pos + pattern.length ≤ min s bytes.size by omega]

/-- What is found in fewer bytes is what is found in all of them, or nothing, in a window they
do not fill. -/
theorem find_cut (bytes : ByteArray) (n : Nat) (pattern : List UInt8) (pos stop : Nat) :
    find (bytes.extract 0 n) pattern pos stop = find bytes pattern pos stop
      ∨ (find (bytes.extract 0 n) pattern pos stop = none ∧ (bytes.extract 0 n).size < stop) := by
  have hsize := size_extract_zero bytes n
  rw [find_extract]
  by_cases h : stop ≤ n
  · exact .inl (by rw [Nat.min_eq_left h])
  · rcases find_le bytes pattern (show min stop n ≤ stop by omega) pos with e | e
    · exact .inl e
    · exact .inr ⟨e, by omega⟩

theorem find_from {bytes : ByteArray} {pattern : List UInt8} {stop i : Nat} (pos : Nat) :
    find bytes pattern pos stop = some i → ∀ pos', pos ≤ pos' → pos' ≤ i →
      find bytes pattern pos' stop = some i := by
  fun_induction find bytes pattern pos stop with
  | case1 pos hc hm =>
    intro h pos' h₁ h₂
    simp only [Option.some.injEq] at h
    subst h
    rw [show pos' = pos by omega, find.eq_1]
    simp [hc, hm]
  | case2 pos hc hm ih =>
    intro h pos' h₁ h₂
    by_cases e : pos' = pos
    · subst e
      rw [find.eq_1]
      simpa [hc, hm] using h
    · exact ih h pos' (by omega) h₂
  | case3 => intro h; cases h

/-! Bytes cut short: an answer once given stays -/

namespace Request

theorem readHead_extract (limits : Limits) (bytes : ByteArray) (n pos : Nat) :
    readHead limits (bytes.extract 0 n) pos = .more
      ∨ readHead limits (bytes.extract 0 n) pos = readHead limits bytes pos := by
  have hsize := size_extract_zero bytes n
  unfold readHead
  rcases find_cut bytes n [13, 10] pos (pos + limits.line_max + 2) with h₁ | ⟨h₁, hs₁⟩
  · rw [h₁]
    cases hf : find bytes [13, 10] pos (pos + limits.line_max + 2) with
    | none =>
      by_cases hc : pos + limits.line_max + 2 ≤ (bytes.extract 0 n).size
      · right
        simp only [hc, show pos + limits.line_max + 2 ≤ bytes.size by omega, ↓reduceIte]
      · left
        simp only [hc, ↓reduceIte]
    | some lineEnd =>
      rcases find_cut bytes n [13, 10, 13, 10] lineEnd (pos + limits.head_max) with h₂ | ⟨h₂, hs₂⟩
      · simp only
        rw [h₂]
        cases hg : find bytes [13, 10, 13, 10] lineEnd (pos + limits.head_max) with
        | none =>
          by_cases hc : pos + limits.head_max ≤ (bytes.extract 0 n).size
          · right
            simp only [hc, show pos + limits.head_max ≤ bytes.size by omega, ↓reduceIte]
          · left
            simp only [hc, ↓reduceIte]
        | some blank =>
          have hb := find_bound (h₂.trans hg)
          simp only [List.length_cons, List.length_nil] at hb
          right
          simp only [extract_extract_zero (show blank ≤ n by omega)]
      · left
        simp only [h₂, show ¬ (pos + limits.head_max ≤ (bytes.extract 0 n).size) by omega,
          ↓reduceIte]
  · left
    simp only [h₁, show ¬ (pos + limits.line_max + 2 ≤ (bytes.extract 0 n).size) by omega,
      ↓reduceIte]

theorem chunkSize_extract (bytes : ByteArray) (n pos : Nat) :
    chunkSize (bytes.extract 0 n) pos = .more
      ∨ chunkSize (bytes.extract 0 n) pos = chunkSize bytes pos := by
  have hsize := size_extract_zero bytes n
  unfold chunkSize
  rcases hex_extract bytes n chunkSizeDigits_max pos 0 with h | h
  · rw [h]
    generalize hex bytes chunkSizeDigits_max pos 0 = full
    obtain ⟨size, d⟩ := full
    simp only
    by_cases hd : d = pos
    · subst hd
      simp only [↓reduceIte]
      by_cases hpos : d < (bytes.extract 0 n).size
      · right
        simp only [hpos, show d < bytes.size by omega, ↓reduceIte]
      · left
        simp only [hpos, ↓reduceIte]
    · simp only [hd, ↓reduceIte]
      rcases crlf_extract bytes n d with hc | hc
      · left
        rw [hc]
      · right
        rw [hc]
  · left
    generalize hex (bytes.extract 0 n) chunkSizeDigits_max pos 0 = cut at h ⊢
    obtain ⟨size, d⟩ := cut
    simp only at h ⊢
    by_cases hd : d = pos
    · subst hd
      simp only [↓reduceIte, show ¬ d < (bytes.extract 0 n).size by omega]
    · simp only [hd, ↓reduceIte, crlf_of_le h]

theorem chunks_extract (limits : Limits) (bytes : ByteArray) (n : Nat) :
    ∀ fuel pos body, chunks limits (bytes.extract 0 n) fuel pos body = .more
      ∨ chunks limits (bytes.extract 0 n) fuel pos body = chunks limits bytes fuel pos body
  | 0, _, _ => .inr rfl
  | fuel + 1, pos, body => by
    have hsize := size_extract_zero bytes n
    rcases chunkSize_extract bytes n pos with h | h
    · left
      simp only [chunks, h]
    · simp only [chunks, h]
      split
      · exact .inr rfl
      · exact .inr rfl
      · rename_i size start _
        split
        · rcases crlf_extract bytes n start with hc | hc
          · left
            simp [hc]
          · exact .inr (by rw [hc])
        · split
          · exact .inr rfl
          · rcases crlf_extract bytes n (start + size) with hc | hc
            · left
              simp [hc]
            · rw [hc]
              split
              · exact .inr rfl
              · exact .inr rfl
              · rename_i next hnext
                have hn := crlf_bound (hc ▸ hnext)
                rw [extract_extract_zero (show start + size ≤ n by omega)]
                exact chunks_extract limits bytes n fuel next _

/-- What the reader makes of the first `n` bytes is that it needs more, or what it makes of all
of them. -/
theorem read_extract (limits : Limits) (bytes : ByteArray) (n pos : Nat) :
    read limits (bytes.extract 0 n) pos = .more
      ∨ read limits (bytes.extract 0 n) pos = read limits bytes pos := by
  have hsize := size_extract_zero bytes n
  unfold read
  rcases readHead_extract limits bytes n pos with h | h
  · left
    rw [h]
  · rw [h]
    cases readHead limits bytes pos with
    | more => exact .inr rfl
    | refuse why => exact .inr rfl
    | done head start =>
      simp only
      cases head.framing with
      | length len =>
        simp only
        by_cases hl : start + len ≤ (bytes.extract 0 n).size
        · right
          simp only [hl, show start + len ≤ bytes.size by omega, ↓reduceIte,
            extract_extract_zero (show start + len ≤ n by omega)]
        · left
          simp only [hl, ↓reduceIte]
      | chunked =>
        simp only
        rcases chunks_extract limits bytes n (limits.chunks_max + 1) start .empty with hc | hc
        · left
          rw [hc]
        · right
          rw [hc]

/-- An answer given is final: whatever arrives after the bytes it was given, it is the same. -/
theorem read_append {limits : Limits} {bytes : ByteArray} {pos : Nat}
    (h : read limits bytes pos ≠ .more) (tail : ByteArray) :
    read limits (bytes ++ tail) pos = read limits bytes pos := by
  have hcut : (bytes ++ tail).extract 0 bytes.size = bytes := ByteArray.extract_append_eq_left rfl
  rcases read_extract limits (bytes ++ tail) bytes.size pos with e | e
  · rw [hcut] at e
    exact absurd e h
  · rw [hcut] at e
    exact e.symm

/-! The head, taken apart -/

theorem parseHead_ok {limits : Limits} {line : List Char} {fieldLines : List (List Char)}
    {head : Head} (h : parseHead limits (line :: fieldLines) = .ok head) :
    ∃ m t v, pieces ' ' line = [m, t, v] ∧ version? v = .ok head.version
      ∧ method? m = .ok (head.method, head.headOnly) ∧ fieldLines.length ≤ limits.fields_max
      ∧ fieldLines.mapM fieldLine? = .ok head.fields ∧ host? head.version head.fields = .ok ()
      ∧ tabbedFraming fieldLines = false
      ∧ framing? limits head.version head.fields = .ok head.framing
      ∧ target? t = .ok (head.path, head.query) := by
  simp only [parseHead] at h
  split at h
  · rename_i m t v hp
    refine ⟨m, t, v, hp, ?_⟩
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i version hv
    split at h
    · cases h
    rename_i mh hm
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    rename_i hc
    split at h
    · cases h
    rename_i fields hf
    split at h
    · cases h
    rename_i u hh
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    rename_i ht
    split at h
    · cases h
    rename_i framing hfr
    split at h
    · cases h
    rename_i pq hpq
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp_all
  · cases h

theorem parseHead_of {limits : Limits} {line : List Char} {fieldLines : List (List Char)}
    {m t v : List Char} (hp : pieces ' ' line = [m, t, v]) {version : Version}
    (hv : version? v = .ok version) {method : Method} {headOnly : Bool}
    (hm : method? m = .ok (method, headOnly)) (hc : fieldLines.length ≤ limits.fields_max)
    {fields : List (String × String)} (hf : fieldLines.mapM fieldLine? = .ok fields)
    (hh : host? version fields = .ok ()) (ht : tabbedFraming fieldLines = false)
    {framing : Framing} (hfr : framing? limits version fields = .ok framing)
    {path : List String} {query : List (String × String)}
    (hpq : target? t = .ok (path, query)) :
    parseHead limits (line :: fieldLines)
      = .ok { method, headOnly, path, query, version, fields, framing } := by
  simp only [parseHead, hp, hv, hm, show ¬ limits.fields_max < fieldLines.length by omega, hf,
    hh, ht, hfr, hpq, bind, Except.bind, ↓reduceIte, Bool.false_eq_true]
  rfl

theorem framing?_length {limits : Limits} {version : Version} {fields : List (String × String)}
    {n : Nat} (h : framing? limits version fields = .ok (.length n)) : n ≤ limits.body_max := by
  simp only [framing?] at h
  split at h
  · cases h
    omega
  · split at h
    · split at h
      · cases h
      · cases h
        omega
    · cases h
  · split at h
    · cases h
    · split at h <;> cases h
  · cases h

/-! Where an answer ends, and how many bytes it waits for -/

theorem crlf_more {bytes : ByteArray} {q : Nat} (h : crlf bytes q = .more) : bytes.size ≤ q + 1 := by
  unfold crlf at h
  by_cases h₁ : q + 1 < bytes.size
  · simp only [h₁, ↓reduceDIte] at h
    split at h <;> cases h
  · omega

theorem hex_le (bytes : ByteArray) : ∀ fuel pos value, (hex bytes fuel pos value).2 ≤ pos + fuel
  | 0, pos, value => by simp [hex]
  | fuel + 1, pos, value => by
    simp only [hex]
    split
    · rename_i _ digit _
      have := hex_le bytes fuel (pos + 1) (value * 16 + digit)
      omega
    · omega

theorem chunkSize_more {bytes : ByteArray} {pos : Nat} (h : chunkSize bytes pos = .more) :
    bytes.size ≤ pos + 17 := by
  unfold chunkSize at h
  have hle := hex_le bytes chunkSizeDigits_max pos 0
  generalize hex bytes chunkSizeDigits_max pos 0 = read at h hle
  obtain ⟨size, d⟩ := read
  simp only [chunkSizeDigits_max] at h hle
  split at h
  · split at h
    · cases h
    · omega
  · split at h
    · rename_i hc
      have := crlf_more hc
      omega
    · cases h
    · cases h

theorem chunkSize_done {bytes : ByteArray} {pos size start : Nat}
    (h : chunkSize bytes pos = .done size start) :
    pos + 3 ≤ start ∧ start ≤ pos + 18 ∧ start ≤ bytes.size := by
  unfold chunkSize at h
  have hle := hex_le bytes chunkSizeDigits_max pos 0
  have hge := le_hex bytes chunkSizeDigits_max pos 0
  generalize hex bytes chunkSizeDigits_max pos 0 = read at h hle hge
  obtain ⟨v, d⟩ := read
  simp only [chunkSizeDigits_max] at h hle hge
  split at h
  · split at h <;> cases h
  · rename_i hd
    split at h
    · cases h
    · cases h
    · rename_i q hq
      cases h
      have := crlf_bound hq
      omega

theorem chunks_more {limits : Limits} {bytes : ByteArray} :
    ∀ {fuel pos : Nat} {body : ByteArray}, body.size ≤ limits.body_max →
      chunks limits bytes fuel pos body = .more →
      bytes.size < pos + 20 * fuel + (limits.body_max - body.size)
  | 0, _, _, _, h => by simp [chunks] at h
  | fuel + 1, pos, body, hbody, h => by
    unfold chunks at h
    split at h
    · have := chunkSize_more (by assumption)
      omega
    · cases h
    · rename_i size start hs
      have hstart := chunkSize_done hs
      split at h
      · split at h
        · have := crlf_more (by assumption)
          omega
        · cases h
        · cases h
      · split at h
        · cases h
        · rename_i hlimit
          split at h
          · have := crlf_more (by assumption)
            omega
          · cases h
          · rename_i next hnext
            have hn := crlf_bound hnext
            have := chunks_more (fuel := fuel) (pos := next)
              (body := body ++ bytes.extract start (start + size))
              (by simp only [ByteArray.size_append, ByteArray.size_extract]; omega) h
            simp only [ByteArray.size_append, ByteArray.size_extract] at this
            omega

theorem chunks_done {limits : Limits} {bytes : ByteArray} :
    ∀ {fuel pos : Nat} {body body' : ByteArray} {stop : Nat}, body.size ≤ limits.body_max →
      chunks limits bytes fuel pos body = .done body' stop →
      pos < stop ∧ stop ≤ bytes.size ∧ body'.size ≤ limits.body_max
        ∧ stop + body.size ≤ pos + 20 * fuel + body'.size
  | 0, _, _, _, _, _, h => by simp [chunks] at h
  | fuel + 1, pos, body, body', stop, hbody, h => by
    unfold chunks at h
    split at h
    · cases h
    · cases h
    · rename_i size start hs
      have hstart := chunkSize_done hs
      split at h
      · split at h
        · cases h
        · cases h
        · rename_i q hq
          cases h
          have := crlf_bound hq
          omega
      · split at h
        · cases h
        · rename_i hlimit
          split at h
          · cases h
          · cases h
          · rename_i next hnext
            have hn := crlf_bound hnext
            have := chunks_done (fuel := fuel) (pos := next)
              (body := body ++ bytes.extract start (start + size))
              (by simp only [ByteArray.size_append, ByteArray.size_extract]; omega) h
            simp only [ByteArray.size_append, ByteArray.size_extract] at this
            omega

theorem readHead_more {limits : Limits} {bytes : ByteArray} {pos : Nat}
    (h : readHead limits bytes pos = .more) :
    bytes.size < pos + max (limits.line_max + 2) limits.head_max := by
  unfold readHead at h
  split at h
  · split at h
    · cases h
    · omega
  · split at h
    · split at h
      · cases h
      · omega
    · split at h
      · cases h
      · split at h <;> cases h

theorem readHead_done {limits : Limits} {bytes : ByteArray} {pos : Nat} {head : Head}
    {start : Nat} (h : readHead limits bytes pos = .done head start) :
    pos + 4 ≤ start ∧ start ≤ pos + limits.head_max ∧ start ≤ bytes.size
      ∧ ∃ text, splitLines text [] [] ≠ [] ∧ parseHead limits (splitLines text [] []) = .ok head := by
  unfold readHead at h
  split at h
  · split at h <;> cases h
  · rename_i lineEnd h₁
    have b₁ := find_bound h₁
    split at h
    · split at h <;> cases h
    · rename_i blank h₂
      have b₂ := find_bound h₂
      simp only [List.length_cons, List.length_nil] at b₁ b₂
      split at h
      · cases h
      · rename_i text _
        split at h
        · cases h
        · rename_i head' hp
          cases h
          refine ⟨by omega, by omega, by omega, text.toList, ?_, hp⟩
          intro e
          rw [e] at hp
          cases hp

theorem readHead_length {limits : Limits} {bytes : ByteArray} {pos : Nat} {head : Head}
    {start n : Nat} (h : readHead limits bytes pos = .done head start)
    (hn : head.framing = .length n) : n ≤ limits.body_max := by
  obtain ⟨-, -, -, text, hne, hp⟩ := readHead_done h
  generalize splitLines text [] [] = lines at hne hp
  cases lines with
  | nil => exact absurd rfl hne
  | cons line fieldLines =>
    obtain ⟨_, _, _, -, -, -, -, -, -, -, hfr, -⟩ := parseHead_ok hp
    exact framing?_length (hn ▸ hfr)

/-- The reader asks for more only while fewer than `message_max` bytes have arrived from where it
starts: so a connection holds at most that many bytes of a request, and one read. -/
theorem read_more {limits : Limits} {bytes : ByteArray} {pos : Nat}
    (h : read limits bytes pos = .more) : bytes.size < pos + limits.message_max := by
  unfold read at h
  unfold Limits.message_max
  have := Nat.le_max_left (limits.line_max + 2) limits.head_max
  have := Nat.le_max_right (limits.line_max + 2) limits.head_max
  split at h
  · have := readHead_more (by assumption)
    omega
  · cases h
  · rename_i head start hh
    have hs := readHead_done hh
    split at h
    · rename_i n hn
      have := readHead_length hh hn
      split at h
      · cases h
      · omega
    · split at h
      · rename_i hc
        have := chunks_more (body := .empty) (by simp) hc
        simp only [ByteArray.size_empty, Nat.sub_zero] at this
        omega
      · cases h
      · cases h

/-- A request the reader gives ends within the bytes given and within `message_max` bytes from
where it starts, and its body has at most `body_max` bytes. -/
theorem read_done {limits : Limits} {bytes : ByteArray} {pos : Nat} {incoming : Incoming}
    {stop : Nat} (h : read limits bytes pos = .done incoming stop) :
    pos < stop ∧ stop ≤ bytes.size ∧ stop ≤ pos + limits.message_max
      ∧ incoming.request.body.size ≤ limits.body_max := by
  unfold read at h
  unfold Limits.message_max
  have := Nat.le_max_right (limits.line_max + 2) limits.head_max
  split at h
  · cases h
  · cases h
  · rename_i head start hh
    have hs := readHead_done hh
    split at h
    · rename_i n hn
      have := readHead_length hh hn
      split at h
      · cases h
        simp only [Head.incoming, ByteArray.size_extract]
        omega
      · cases h
    · split at h
      · cases h
      · cases h
      · rename_i body stop' hc
        cases h
        have := chunks_done (by simp) hc
        simp only [ByteArray.size_empty] at this
        simp only [Head.incoming]
        omega

end Request

/-! A head written as lines -/

/-- Where `pattern` first starts in `l`. -/
def findL (pattern : List UInt8) : List UInt8 → Option Nat
  | [] => none
  | b :: rest =>
    if (b :: rest).take pattern.length = pattern then some 0 else (findL pattern rest).map (· + 1)

theorem findL_length {pattern : List UInt8} (hp : pattern ≠ []) :
    ∀ {l : List UInt8} {k : Nat}, findL pattern l = some k → k + pattern.length ≤ l.length
  | [], _, h => by simp [findL] at h
  | b :: rest, k, h => by
    simp only [findL] at h
    split at h
    · rename_i e
      cases h
      have := congrArg List.length e
      simp only [List.length_take, List.length_cons] at this ⊢
      omega
    · cases hr : findL pattern rest with
      | none => simp [hr] at h
      | some j =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        have := findL_length hp hr
        simp only [List.length_cons]
        omega

theorem matchAt_iff_take {bytes : ByteArray} :
    ∀ {pattern : List UInt8} {i : Nat},
      matchAt bytes pattern i = true ↔ (bytes.data.toList.drop i).take pattern.length = pattern
  | [], i => by simp [matchAt]
  | p :: ps, i => by
    simp only [matchAt, Bool.and_eq_true, beq_iff_eq, matchAt_iff_take, List.length_cons,
      getElem?_data]
    by_cases hi : i < bytes.data.toList.length
    · rw [List.drop_eq_getElem_cons hi, List.take_succ_cons, List.getElem?_eq_getElem hi]
      simp
    · simp [List.drop_eq_nil_of_le (show bytes.data.toList.length ≤ i by omega),
        List.getElem?_eq_none (show bytes.data.toList.length ≤ i by omega)]

theorem find_eq {bytes : ByteArray} {pattern : List UInt8} (hp : pattern ≠ []) (pos stop : Nat) :
    find bytes pattern pos stop = (findL pattern (bytes.data.toList.drop pos)).bind fun k =>
      if pos + k + pattern.length ≤ stop then some (pos + k) else none := by
  have hlen : 0 < pattern.length := by cases pattern <;> simp_all
  fun_induction find bytes pattern pos stop with
  | case1 pos hc hm =>
    have hl : pos < bytes.data.toList.length := by simp; omega
    rw [List.drop_eq_getElem_cons hl, findL, ← List.drop_eq_getElem_cons hl,
      (matchAt_iff_take.mp hm)]
    simp only [↓reduceIte, Option.bind_some, Nat.add_zero, show pos + pattern.length ≤ stop by omega]
  | case2 pos hc hm ih =>
    have hl : pos < bytes.data.toList.length := by simp; omega
    have hne : (bytes.data.toList.drop pos).take pattern.length ≠ pattern :=
      fun e => hm (matchAt_iff_take.mpr e)
    rw [List.drop_eq_getElem_cons hl, findL, ← List.drop_eq_getElem_cons hl, ih]
    simp only [hne, ↓reduceIte]
    cases findL pattern (bytes.data.toList.drop (pos + 1)) with
    | none => rfl
    | some k =>
      simp only [Option.bind_some, Option.map_some]
      rw [show pos + (k + 1) = pos + 1 + k by omega]
  | case3 pos hc =>
    cases hk : findL pattern (bytes.data.toList.drop pos) with
    | none => rfl
    | some k =>
      have := findL_length hp hk
      simp only [List.length_drop, Array.length_toList] at this
      have : bytes.data.size = bytes.size := rfl
      simp only [Option.bind_some]
      rw [ite_eq_right (by omega)]

theorem findL_crlf : ∀ {x : List UInt8}, (∀ b ∈ x, b ≠ 10) → ∀ t,
    findL [13, 10] (x ++ 13 :: 10 :: t) = some x.length
  | [], _, t => by simp [findL]
  | b :: x, h, t => by
    have hsecond : (b :: (x ++ 13 :: 10 :: t)).take 2 ≠ [13, 10] := by
      cases x with
      | nil => simp
      | cons c x =>
        have := h c (by simp)
        simp [this]
    have ih := findL_crlf (x := x) (fun b hb => h b (List.mem_cons_of_mem _ hb)) t
    rw [List.cons_append, findL]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, hsecond, ↓reduceIte, ih,
      Option.map_some]

theorem findL_skip : ∀ {x : List UInt8}, (∀ b ∈ x, b ≠ 10) → ∀ {y : List UInt8},
    y.head? ≠ some 10 → findL [13, 10, 13, 10] (x ++ y) = (findL [13, 10, 13, 10] y).map (· + x.length)
  | [], _, y, _ => by simp
  | b :: x, h, y, hy => by
    have hsecond : (b :: (x ++ y)).take 4 ≠ [13, 10, 13, 10] := by
      cases x with
      | nil =>
        cases y with
        | nil => simp
        | cons c y => simp_all
      | cons c x =>
        have := h c (by simp)
        simp [this]
    have ih := findL_skip (x := x) (fun b hb => h b (List.mem_cons_of_mem _ hb)) hy
    rw [List.cons_append, findL]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, hsecond, ↓reduceIte, ih,
      Option.map_map]
    congr 1

theorem findL_crlf_skip {y : List UInt8} (hy : y.take 2 ≠ [13, 10]) :
    findL [13, 10, 13, 10] (13 :: 10 :: y) = (findL [13, 10, 13, 10] y).map (· + 2) := by
  have h₁ : (13 :: 10 :: y : List UInt8).take 4 ≠ [13, 10, 13, 10] := by
    intro e
    simp only [List.take_succ_cons, List.cons.injEq, true_and] at e
    exact hy e
  have h₂ : (10 :: y : List UInt8).take 4 ≠ [13, 10, 13, 10] := by simp
  rw [findL]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, h₁, ↓reduceIte]
  rw [findL]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, h₂, ↓reduceIte, Option.map_map]
  rfl

theorem ne_10_of_ne_lf {cs : List Char} (h : ∀ c ∈ cs, c ≠ '\n') :
    ∀ b ∈ cs.flatMap String.utf8EncodeChar, b ≠ 10 := by
  intro b hb e
  obtain ⟨c, hc, hbc⟩ := List.mem_flatMap.mp hb
  have := utf8EncodeChar_ascii hbc (by rw [e]; decide)
  rw [e] at this
  exact h c hc (Char.toNat_inj.mp this.symm)

theorem take_two_ne {x z : List UInt8} (hx : x ≠ []) (hx' : ∀ b ∈ x, b ≠ 10)
    (hz : z.head? ≠ some 10) : (x ++ z).take 2 ≠ [13, 10] := by
  obtain ⟨a, x, rfl⟩ := List.exists_cons_of_ne_nil hx
  cases x with
  | nil =>
    cases z with
    | nil => simp
    | cons c z => simp_all
  | cons c x =>
    have := hx' c (by simp)
    simp [this]

private theorem crlf_flatMap :
    (['\r', '\n'] : List Char).flatMap String.utf8EncodeChar = [13, 10] := by decide

/-- The first blank line after the lines `ls` of a head is the one that ends it: a CR in a line
is followed by another byte of the line or by the CR of a CRLF, never by LF. -/
theorem findL_lines (t : List UInt8) : ∀ {ls : List (List Char)}, ls ≠ [] →
    (∀ l ∈ ls, l ≠ [] ∧ ∀ c ∈ l, c ≠ '\n') →
    findL [13, 10, 13, 10] ((['\r', '\n'].intercalate ls).flatMap String.utf8EncodeChar
        ++ 13 :: 10 :: 13 :: 10 :: t)
      = some ((['\r', '\n'].intercalate ls).flatMap String.utf8EncodeChar).length
  | [l], _, h => by
    rw [List.intercalate_singleton, findL_skip (ne_10_of_ne_lf (h l (by simp)).2) (by simp)]
    simp [findL]
  | l :: l' :: ls, _, h => by
    have hl := h l (by simp)
    have hl' := h l' (by simp)
    have hrest := findL_lines t (ls := l' :: ls) (by simp) fun x hx => h x (by simp_all)
    have hsplit : ∃ z : List UInt8, z.head? = some 13 ∧
        (['\r', '\n'].intercalate (l' :: ls)).flatMap String.utf8EncodeChar
          ++ 13 :: 10 :: 13 :: 10 :: t = l'.flatMap String.utf8EncodeChar ++ z := by
      cases ls with
      | nil => exact ⟨13 :: 10 :: 13 :: 10 :: t, rfl, by simp⟩
      | cons l'' ls =>
        refine ⟨13 :: 10 :: ((['\r', '\n'].intercalate (l'' :: ls)).flatMap String.utf8EncodeChar
          ++ 13 :: 10 :: 13 :: 10 :: t), rfl, ?_⟩
        rw [List.intercalate_cons_cons, List.flatMap_append, List.flatMap_append, crlf_flatMap]
        simp
    obtain ⟨z, hz, hsplit⟩ := hsplit
    have henc : l'.flatMap String.utf8EncodeChar ≠ [] := by
      obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil hl'.1
      rw [hc, List.flatMap_cons]
      exact fun e => String.utf8EncodeChar_ne_nil (List.append_eq_nil_iff.mp e).1
    rw [List.intercalate_cons_cons, List.flatMap_append, List.flatMap_append, crlf_flatMap,
      List.append_assoc, List.append_assoc, findL_skip (ne_10_of_ne_lf hl.2) (by simp),
      List.cons_append, List.cons_append, List.nil_append, hsplit,
      findL_crlf_skip (take_two_ne henc (ne_10_of_ne_lf hl'.2) (by simp [hz])), ← hsplit, hrest]
    simp only [Option.map_some, Option.some.injEq, List.length_append, List.length_cons,
      List.length_nil]
    omega

theorem findL_crlf_noCR : ∀ {x : List UInt8}, (∀ b ∈ x, b ≠ 13) → ∀ t,
    findL [13, 10] (x ++ 13 :: 10 :: t) = some x.length
  | [], _, t => by simp [findL]
  | b :: x, h, t => by
    have hfirst : (b :: (x ++ 13 :: 10 :: t)).take 2 ≠ [13, 10] := by
      have := h b (by simp)
      simp [this]
    have ih := findL_crlf_noCR (x := x) (fun b hb => h b (List.mem_cons_of_mem _ hb)) t
    rw [List.cons_append, findL]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, hfirst, ↓reduceIte, ih,
      Option.map_some]

theorem findL_skip_noCR : ∀ {x : List UInt8}, (∀ b ∈ x, b ≠ 13) → ∀ y : List UInt8,
    findL [13, 10, 13, 10] (x ++ y) = (findL [13, 10, 13, 10] y).map (· + x.length)
  | [], _, y => by simp
  | b :: x, h, y => by
    have hfirst : (b :: (x ++ y)).take 4 ≠ [13, 10, 13, 10] := by
      have := h b (by simp)
      simp [this]
    have ih := findL_skip_noCR (x := x) (fun b hb => h b (List.mem_cons_of_mem _ hb)) y
    rw [List.cons_append, findL]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, hfirst, ↓reduceIte, ih,
      Option.map_map]
    congr 1

theorem findL_lines_noCR (t : List UInt8) : ∀ {ls : List (List Char)}, ls ≠ [] →
    (∀ l ∈ ls, l ≠ [] ∧ ∀ c ∈ l, c ≠ '\r') →
    findL [13, 10, 13, 10] ((['\r', '\n'].intercalate ls).flatMap String.utf8EncodeChar
        ++ 13 :: 10 :: 13 :: 10 :: t)
      = some ((['\r', '\n'].intercalate ls).flatMap String.utf8EncodeChar).length
  | [l], _, h => by
    rw [List.intercalate_singleton, findL_skip_noCR (ne_13_of_ne_cr (h l (by simp)).2)]
    simp [findL]
  | l :: l' :: ls, _, h => by
    have hl := h l (by simp)
    have hl' := h l' (by simp)
    have hrest := findL_lines_noCR t (ls := l' :: ls) (by simp) fun x hx => h x (by simp_all)
    obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil hl'.1
    obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil (String.utf8EncodeChar_ne_nil (c := c))
    have hb0 : b ≠ 13 :=
      ne_13_of_ne_cr (cs := [c]) (by simpa using hl'.2 c (by simp [hc])) b (by simp [hb])
    have htake : ((['\r', '\n'].intercalate (l' :: ls)).flatMap String.utf8EncodeChar
        ++ 13 :: 10 :: 13 :: 10 :: t).take 2 ≠ [13, 10] := by
      cases ls with
      | nil => simp [hc, hb, hb0]
      | cons l'' ls => simp [List.intercalate_cons_cons, hc, hb, hb0]
    rw [List.intercalate_cons_cons, List.flatMap_append, List.flatMap_append, crlf_flatMap,
      List.append_assoc, List.append_assoc, findL_skip_noCR (ne_13_of_ne_cr hl.2),
      List.cons_append, List.cons_append, List.nil_append, findL_crlf_skip htake, hrest]
    simp only [Option.map_some, Option.some.injEq, List.length_append, List.length_cons,
      List.length_nil]
    omega

theorem splitLines_noLF {l : List Char} (hl : ∀ c ∈ l, c ≠ '\n') (rest : List Char) :
    ∀ (line : List Char) (done : List (List Char)),
      splitLines (l ++ '\r' :: '\n' :: rest) line done
        = splitLines rest [] ((l.reverse ++ line).reverse :: done) := by
  induction l with
  | nil => intro line done; simp [splitLines.eq_2]
  | cons c l ih =>
    intro line done
    have hnext : ∀ rest', c = '\r' → l ++ '\r' :: '\n' :: rest = '\n' :: rest' → False := by
      intro rest' _ e
      cases l with
      | nil => simp at e
      | cons d l =>
        simp only [List.cons_append, List.cons.injEq] at e
        exact hl d (by simp) e.1
    rw [List.cons_append, splitLines.eq_3 _ _ c _ hnext, ih (fun d hd => hl d (by simp [hd]))]
    simp

theorem splitLines_noLF_end : ∀ {l : List Char}, (∀ c ∈ l, c ≠ '\n') →
    ∀ (line : List Char) (done : List (List Char)),
      splitLines l line done = ((l.reverse ++ line).reverse :: done).reverse
  | [], _, line, done => by simp [splitLines.eq_1]
  | c :: l, hl, line, done => by
    have hnext : ∀ rest', c = '\r' → l = '\n' :: rest' → False := by
      intro rest' _ e
      exact hl '\n' (by simp [e]) rfl
    rw [splitLines.eq_3 _ _ c _ hnext, splitLines_noLF_end (fun d hd => hl d (by simp [hd]))]
    simp

theorem splitLines_intercalate_noLF : ∀ {ls : List (List Char)}, ls ≠ [] →
    (∀ l ∈ ls, ∀ c ∈ l, c ≠ '\n') → ∀ done : List (List Char),
    splitLines (['\r', '\n'].intercalate ls) [] done = done.reverse ++ ls
  | [l], _, h, done => by
    rw [List.intercalate_singleton, splitLines_noLF_end (h l (by simp))]
    simp
  | l :: l' :: ls, _, h, done => by
    rw [List.intercalate_cons_cons, List.append_assoc, List.cons_append, List.cons_append,
      List.nil_append, splitLines_noLF (h l (by simp)),
      splitLines_intercalate_noLF (by simp) (fun x hx => h x (by simp_all))]
    simp

theorem find_none_from {bytes : ByteArray} {pattern : List UInt8} {stop : Nat} (pos : Nat) :
    find bytes pattern pos stop = none → ∀ pos', pos ≤ pos' → find bytes pattern pos' stop = none := by
  fun_induction find bytes pattern pos stop with
  | case1 => intro h; cases h
  | case2 pos hc hm ih =>
    intro h pos' h₁
    by_cases e : pos' = pos
    · subst e
      rw [find.eq_1]
      simpa [hc, hm] using h
    · exact ih h pos' (by omega)
  | case3 pos hc =>
    intro _ pos' h₁
    rw [find.eq_1]
    simp only [show ¬ pos' + pattern.length ≤ min stop bytes.size by omega, ↓reduceIte]

namespace Request

private theorem headWire_toList (lines : List String) :
    (headWire lines).data.toList
      = (['\r', '\n'].intercalate (lines.map String.toList)).flatMap String.utf8EncodeChar
        ++ [13, 10, 13, 10] := by
  have hsep : ("\r\n\r\n".toList.flatMap String.utf8EncodeChar) = [13, 10, 13, 10] := by decide
  rw [headWire, String.toUTF8_eq_toByteArray, data_toList_toByteArray, String.toList_append,
    List.flatMap_append, hsep, lines_toList]

/-- A head written as lines that are not empty, and none of which has an LF or none of which has
a CR, is read as those lines, unless a limit refuses it. -/
theorem readHead_headWire (limits : Limits) (pre rest : ByteArray) {lines : List String}
    (hne : lines ≠ []) (hlines : ∀ l ∈ lines, l ≠ "")
    (hclean : (∀ l ∈ lines, ∀ c ∈ l.toList, c ≠ '\n') ∨ (∀ l ∈ lines, ∀ c ∈ l.toList, c ≠ '\r')) :
    readHead limits (pre ++ (headWire lines ++ rest)) pre.size =
      if limits.line_max < (lines.headD "").utf8ByteSize then .refuse .uriTooLong
      else if limits.head_max < ("\r\n".intercalate lines).utf8ByteSize + 4 then
        .refuse .fieldsTooLarge
      else
        match parseHead limits (lines.map String.toList) with
        | .error why => .refuse why
        | .ok head => .done head (pre.size + ("\r\n".intercalate lines).utf8ByteSize + 4) := by
  obtain ⟨l₀, more, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hls : ∀ l ∈ (l₀ :: more).map String.toList, l ≠ [] := by
    intro l hl
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hl
    exact fun e => hlines s hs (String.toList_inj.mp (e.trans (by simp)))
  have hmapped : ∀ {p : Char → Prop}, (∀ l ∈ l₀ :: more, ∀ c ∈ l.toList, p c) →
      ∀ l ∈ (l₀ :: more).map String.toList, ∀ c ∈ l, p c := by
    intro p h l hl
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hl
    exact h s hs
  have hfirst : ∀ t, findL [13, 10] (l₀.toList.flatMap String.utf8EncodeChar ++ 13 :: 10 :: t)
      = some (l₀.toList.flatMap String.utf8EncodeChar).length := by
    rcases hclean with h | h
    · exact findL_crlf (ne_10_of_ne_lf (h l₀ (by simp)))
    · exact findL_crlf_noCR (ne_13_of_ne_cr (h l₀ (by simp)))
  have hblank : ∀ t, findL [13, 10, 13, 10]
      ((['\r', '\n'].intercalate ((l₀ :: more).map String.toList)).flatMap String.utf8EncodeChar
        ++ 13 :: 10 :: 13 :: 10 :: t)
      = some ((['\r', '\n'].intercalate ((l₀ :: more).map String.toList)).flatMap
          String.utf8EncodeChar).length := by
    intro t
    rcases hclean with h | h
    · exact findL_lines t (by simp) fun l hl => ⟨hls l hl, hmapped h l hl⟩
    · exact findL_lines_noCR t (by simp) fun l hl => ⟨hls l hl, hmapped h l hl⟩
  have hsplit : splitLines (['\r', '\n'].intercalate ((l₀ :: more).map String.toList)) [] []
      = (l₀ :: more).map String.toList := by
    rcases hclean with h | h
    · simpa using splitLines_intercalate_noLF (by simp) (hmapped h) []
    · simpa using splitLines_intercalate (by simp) (hmapped h) []
  generalize hE : (['\r', '\n'].intercalate ((l₀ :: more).map String.toList)).flatMap
    String.utf8EncodeChar = E
  have hEsize : E.length = ("\r\n".intercalate (l₀ :: more)).utf8ByteSize := by
    rw [← hE, ← lines_toList, length_flatMap_utf8EncodeChar]
  have hE₀ : (l₀.toList.flatMap String.utf8EncodeChar).length = l₀.utf8ByteSize :=
    length_flatMap_utf8EncodeChar l₀
  have hW : ∃ W, E = l₀.toList.flatMap String.utf8EncodeChar ++ W
      ∧ ∀ t, ∃ Z, W ++ 13 :: 10 :: 13 :: 10 :: t = 13 :: 10 :: Z := by
    rw [← hE]
    cases more with
    | nil => exact ⟨[], by simp, fun t => ⟨_, rfl⟩⟩
    | cons l₁ more =>
      refine ⟨13 :: 10 :: (['\r', '\n'].intercalate ((l₁ :: more).map String.toList)).flatMap
        String.utf8EncodeChar, ?_, fun t => ⟨_, rfl⟩⟩
      simp only [List.map_cons, List.intercalate_cons_cons, List.flatMap_append, crlf_flatMap]
      simp
  obtain ⟨W, hEW, hZ⟩ := hW
  have hdrop : (pre ++ (headWire (l₀ :: more) ++ rest)).data.toList.drop pre.size
      = E ++ 13 :: 10 :: 13 :: 10 :: rest.data.toList := by
    rw [drop_append_front, ByteArray.data_append, Array.toList_append, headWire_toList, hE]
    simp
  have hsize : (pre ++ (headWire (l₀ :: more) ++ rest)).size = pre.size + E.length + 4 + rest.size := by
    have := congrArg List.length hdrop
    simp only [List.length_drop, Array.length_toList, List.length_append, List.length_cons] at this
    have h₁ : (pre ++ (headWire (l₀ :: more) ++ rest)).data.size
        = (pre ++ (headWire (l₀ :: more) ++ rest)).size := rfl
    have h₂ : rest.data.size = rest.size := rfl
    have h₃ : pre.size ≤ (pre ++ (headWire (l₀ :: more) ++ rest)).size := by
      simp [ByteArray.size_append]
    omega
  have hle₀ : l₀.utf8ByteSize ≤ E.length := by
    rw [hEW, List.length_append]
    omega
  have hfind₁ : find (pre ++ (headWire (l₀ :: more) ++ rest)) [13, 10] pre.size
      (pre.size + limits.line_max + 2)
      = if l₀.utf8ByteSize ≤ limits.line_max then some (pre.size + l₀.utf8ByteSize) else none := by
    obtain ⟨Z, hz⟩ := hZ rest.data.toList
    rw [find_eq (by simp), hdrop, hEW, List.append_assoc, hz, hfirst, hE₀]
    simp only [Option.bind_some, List.length_cons, List.length_nil]
    by_cases h : l₀.utf8ByteSize ≤ limits.line_max
    · simp only [h, ↓reduceIte, show pre.size + l₀.utf8ByteSize + 2 ≤ pre.size + limits.line_max + 2
        by omega]
    · simp only [h, ↓reduceIte, show ¬ pre.size + l₀.utf8ByteSize + 2 ≤ pre.size + limits.line_max + 2
        by omega]
  have hfind₂ : find (pre ++ (headWire (l₀ :: more) ++ rest)) [13, 10, 13, 10] pre.size
      (pre.size + limits.head_max)
      = if E.length + 4 ≤ limits.head_max then some (pre.size + E.length) else none := by
    rw [find_eq (by simp), hdrop, ← hE, hblank, hE]
    simp only [Option.bind_some, List.length_cons, List.length_nil]
    by_cases h : E.length + 4 ≤ limits.head_max
    · simp only [h, ↓reduceIte, show pre.size + E.length + 4 ≤ pre.size + limits.head_max by omega]
    · simp only [h, ↓reduceIte, show ¬ pre.size + E.length + 4 ≤ pre.size + limits.head_max by omega]
  unfold readHead
  rw [hfind₁]
  simp only [List.headD_cons]
  by_cases hline : l₀.utf8ByteSize ≤ limits.line_max
  · simp only [hline, ↓reduceIte, show ¬ limits.line_max < l₀.utf8ByteSize by omega]
    by_cases hhead : E.length + 4 ≤ limits.head_max
    · simp only [hhead, ↓reduceIte] at hfind₂
      rw [find_from _ hfind₂ _ (by omega) (by omega)]
      simp only [show ¬ limits.head_max < ("\r\n".intercalate (l₀ :: more)).utf8ByteSize + 4 by
        omega, ↓reduceIte]
      have hwire : headWire (l₀ :: more) ++ rest
          = ("\r\n".intercalate (l₀ :: more) ++ "\r\n\r\n").toUTF8 ++ rest := rfl
      rw [hwire, hEsize, extract_head, String.toUTF8_eq_toByteArray, fromUTF8?_toByteArray]
      simp only []
      rw [lines_toList, hsplit]
      rfl
    · simp only [hhead, ↓reduceIte] at hfind₂
      rw [find_none_from _ hfind₂ _ (by omega)]
      simp only [show limits.head_max < ("\r\n".intercalate (l₀ :: more)).utf8ByteSize + 4 by
        omega, ↓reduceIte, show pre.size + limits.head_max ≤ (pre ++ (headWire (l₀ :: more) ++ rest)).size
        by omega]
  · simp only [hline, ↓reduceIte, show limits.line_max < l₀.utf8ByteSize by omega,
      show pre.size + limits.line_max + 2 ≤ (pre ++ (headWire (l₀ :: more) ++ rest)).size by omega]

end Request


/-! Requests `Request.wire` writes, read back -/

theorem pieces_of_forall {sep : Char} : ∀ {l : List Char}, (∀ c ∈ l, c ≠ sep) → pieces sep l = [l]
  | [], _ => rfl
  | c :: l, h => by
    rw [pieces, pieces_of_forall fun d hd => h d (List.mem_cons_of_mem _ hd)]
    simp [h c List.mem_cons_self]

theorem pieces_append {sep : Char} : ∀ {l : List Char}, (∀ c ∈ l, c ≠ sep) → ∀ rest,
    pieces sep (l ++ sep :: rest) = l :: pieces sep rest
  | [], _, rest => by simp [pieces]
  | c :: l, h, rest => by
    rw [List.cons_append, pieces, pieces_append (fun d hd => h d (List.mem_cons_of_mem _ hd))]
    simp [h c List.mem_cons_self]

theorem pieces_intercalate {sep : Char} : ∀ {ls : List (List Char)}, ls ≠ [] →
    (∀ l ∈ ls, ∀ c ∈ l, c ≠ sep) → pieces sep ([sep].intercalate ls) = ls
  | [l], _, h => by rw [List.intercalate_singleton, pieces_of_forall (h l (by simp))]
  | l :: l' :: ls, _, h => by
    rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append,
      pieces_append (h l (by simp)), pieces_intercalate (by simp) (fun x hx => h x (by simp_all))]

/-- The characters `percentEncode` writes. -/
def encodedChar (c : Char) : Bool :=
  c.isAlphanum || "-._~%".toList.contains c

theorem percentEncodeByte_encoded : ∀ b : UInt8, (percentEncodeByte b).all encodedChar := by
  decide

theorem encoded_percentEncode (s : String) : ∀ c ∈ (percentEncode s).toList, encodedChar c := by
  intro c hc
  simp only [percentEncode, String.toList_ofList, List.mem_flatMap] at hc
  obtain ⟨b, -, hb⟩ := hc
  exact List.all_eq_true.mp (percentEncodeByte_encoded b) c hb

theorem ne_of_encoded {c : Char} (h : encodedChar c = true) :
    c ≠ '/' ∧ c ≠ '?' ∧ c ≠ '&' ∧ c ≠ '=' ∧ c ≠ '+' ∧ c ≠ ' ' ∧ c ≠ ':' ∧ c ≠ '\t'
      ∧ Request.pchar c = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rintro rfl; exact absurd h (by decide))
    | (simp only [encodedChar, Bool.or_eq_true] at h
       simp only [Request.pchar, Bool.or_eq_true]
       rcases h with h | h
       · exact .inl h
       · refine .inr ?_
         have : ∀ d ∈ "-._~%".toList, "-._~!$&'()*+,;=:@%".toList.contains d = true := by decide
         exact this c (List.contains_iff_mem.mp h))

theorem trimOws_of_forall {v : List Char} (h : ∀ c ∈ v, ows c = false) : trimOws v = v := by
  have hd : ∀ {l : List Char}, (∀ c ∈ l, ows c = false) → l.dropWhile ows = l := by
    intro l hl
    cases l with
    | nil => rfl
    | cons c l => exact List.dropWhile_cons_of_neg (by simp [hl c List.mem_cons_self])
  rw [trimOws, hd h, hd (fun c hc => h c (List.mem_reverse.mp hc)), List.reverse_reverse]

theorem headerLine?_field {name value : String} (hname : token name = true)
    (hvalue : value.toList.all plain = true) :
    headerLine? (name ++ ": " ++ value).toList
      = some (name.toLower, String.ofList (trimOws value.toList)) := by
  have hcolon : ∀ c ∈ name.toList, (c != ':') = true := by
    intro c hc
    simp only [token, Bool.and_eq_true, List.all_eq_true] at hname
    refine bne_iff_ne.mpr fun e => ?_
    subst e
    exact absurd (hname.2 _ hc) (by decide)
  have hline : (name ++ ": " ++ value).toList = name.toList ++ ':' :: ' ' :: value.toList := by
    simp
  have hplain : (' ' :: value.toList).all plain = true := by simpa [plain] using hvalue
  rw [headerLine?, hline, List.takeWhile_append_of_pos hcolon,
    List.dropWhile_append_of_pos hcolon, List.takeWhile_cons_of_neg (by decide),
    List.dropWhile_cons_of_neg (by decide), List.append_nil, String.ofList_toList]
  simp only [hname, hplain, Bool.and_self, ↓reduceIte]
  rw [trimOws, List.dropWhile_cons_of_pos (by decide)]
  rfl


namespace Request

private def methodWord : Method → String
  | .get => "GET"
  | .post => "POST"
  | .put => "PUT"
  | .patch => "PATCH"
  | .delete => "DELETE"

private theorem head_eq (r : Request) (host : String) :
    r.head host = (methodWord r.method ++ " " ++ r.target ++ " HTTP/1.1")
      :: (r.fields host).map fun field => field.1 ++ ": " ++ field.2 := by
  cases hm : r.method <;> simp [head, methodWord, hm]

private theorem method?_word (m : Method) : method? (methodWord m).toList = .ok (m, false) := by
  cases m <;> simp [method?, methodWord]

private theorem word_ne_space (m : Method) : ∀ c ∈ (methodWord m).toList, c ≠ ' ' := by
  cases m <;> decide

private theorem encoded_ne {s : String} :
    ∀ c ∈ (percentEncode s).toList, c ≠ '/' ∧ c ≠ '?' ∧ c ≠ '&' ∧ c ≠ '=' ∧ c ≠ '+'
      ∧ c ≠ ' ' ∧ c ≠ ':' ∧ c ≠ '\t' ∧ pchar c = true :=
  fun c hc => ne_of_encoded (encoded_percentEncode s c hc)

private theorem queryPart?_encoded (s : String) :
    queryPart? (percentEncode s).toList = some s := by
  have hplus : ∀ c ∈ (percentEncode s).toList, (if c = '+' then ' ' else c) = c :=
    fun c hc => by simp [(encoded_ne c hc).2.2.2.2.1]
  rw [queryPart?, List.map_congr_left hplus, List.map_id', String.ofList_toList,
    percentDecode_percentEncode]

private theorem pair?_encoded (k v : String) :
    pair? ((percentEncode k).toList ++ '=' :: (percentEncode v).toList) = some (k, v) := by
  have hk : ∀ c ∈ (percentEncode k).toList, (c != '=') = true :=
    fun c hc => bne_iff_ne.mpr (encoded_ne c hc).2.2.2.1
  simp [pair?, List.takeWhile_append_of_pos hk, List.dropWhile_append_of_pos hk,
    queryPart?_encoded]

private theorem percentEncode_ne_nil {s : String} (h : s ≠ "") : (percentEncode s).toList ≠ [] := by
  intro e
  simp only [percentEncode, String.toList_ofList, List.flatMap_eq_nil_iff] at e
  apply h
  have hb : s.toUTF8.data.toList = [] := by
    cases hs : s.toUTF8.data.toList with
    | nil => rfl
    | cons b bs =>
      have := e b (by rw [hs]; exact List.mem_cons_self)
      simp [percentEncodeByte] at this
      split at this <;> simp at this
  have : s.toUTF8.size = 0 := by
    have := congrArg List.length hb
    simpa using this
  rw [String.toUTF8_eq_toByteArray, String.size_toByteArray] at this
  exact String.utf8ByteSize_eq_zero_iff.mp this

private theorem segments?_path {path : List String} (h : path ≠ [""]) :
    segments? (['/'].intercalate (path.map fun s => (percentEncode s).toList)) = some path := by
  have hsep : ∀ l ∈ path.map (fun s => (percentEncode s).toList), ∀ c ∈ l, c ≠ '/' := by
    intro l hl c hc
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp hl
    exact (encoded_ne c hc).1
  have hdecode : (path.map fun s => (percentEncode s).toList).mapM
      (fun s => percentDecode (String.ofList s)) = some path := by
    rw [List.mapM_map, mapM_some (g := id) fun s _ => by
      simp [String.ofList_toList, percentDecode_percentEncode]]
    simp
  cases path with
  | nil => rfl
  | cons s more =>
    have hne : ['/'].intercalate ((s :: more).map fun s => (percentEncode s).toList) ≠ [] := by
      cases more with
      | nil =>
        have : s ≠ "" := fun e => h (by rw [e])
        simpa using percentEncode_ne_nil this
      | cons s' more => simp [List.intercalate_cons_cons]
    rw [segments?, ite_eq_right (by simpa using hne), pieces_intercalate (by simp) hsep, hdecode]

private theorem query?_query {query : List (String × String)} (h : query ≠ []) :
    query? (['&'].intercalate (query.map fun (k, v) =>
      (percentEncode k).toList ++ '=' :: (percentEncode v).toList)) = some query := by
  obtain ⟨⟨k, v⟩, more, rfl⟩ := List.exists_cons_of_ne_nil h
  have hsep : ∀ l ∈ ((k, v) :: more).map (fun (k, v) =>
      (percentEncode k).toList ++ '=' :: (percentEncode v).toList), ∀ c ∈ l, c ≠ '&' := by
    intro l hl c hc
    obtain ⟨⟨k, v⟩, -, rfl⟩ := List.mem_map.mp hl
    simp only [List.mem_append, List.mem_cons] at hc
    rcases hc with hc | rfl | hc
    · exact (encoded_ne c hc).2.2.1
    · decide
    · exact (encoded_ne c hc).2.2.1
  have hne : ['&'].intercalate (((k, v) :: more).map fun (k, v) =>
      (percentEncode k).toList ++ '=' :: (percentEncode v).toList) ≠ [] := by
    cases more with
    | nil => simp
    | cons p more => simp [List.intercalate_cons_cons]
  rw [query?, ite_eq_right (by simpa using hne), pieces_intercalate (by simp) hsep, List.mapM_map,
    mapM_some (g := id) fun ⟨k, v⟩ _ => pair?_encoded k v]
  simp

theorem target?_target (r : Request) (h : r.path ≠ [""]) :
    target? r.target.toList = .ok (r.path, r.query) := by
  generalize hP : ['/'].intercalate (r.path.map fun s => (percentEncode s).toList) = P
  have hPchars : ∀ c ∈ P, c ≠ '?' ∧ targetChar c = true := by
    rw [← hP]
    refine forall_mem_intercalate (by decide) fun l hl c hc => ?_
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp hl
    have := encoded_ne c hc
    exact ⟨this.2.1, by simp [targetChar, this.2.2.2.2.2.2.2.2]⟩
  have hpath : (String.intercalate "/" (r.path.map percentEncode)).toList = P := by
    rw [← hP, String.toList_intercalate, List.map_map]
    rfl
  have hq : ∀ c ∈ P, (c != '?') = true := fun c hc => bne_iff_ne.mpr (hPchars c hc).1
  have hsegments : segments? P = some r.path := by rw [← hP]; exact segments?_path h
  have htake : P.takeWhile (· != '?') = P := by
    simpa using List.takeWhile_append_of_pos (l₂ := []) hq
  have hdrop : P.dropWhile (· != '?') = [] := by
    simpa using List.dropWhile_append_of_pos (l₂ := []) hq
  cases hquery : r.query with
  | nil =>
    have htarget : r.target.toList = '/' :: P := by
      simp [target, hquery, String.toList_append, hpath]
    rw [htarget, target?, List.all_eq_true.mpr fun c hc => (hPchars c hc).2]
    simp only [↓reduceIte, htake, hdrop, hsegments, query?, List.drop_nil, List.isEmpty_nil]
  | cons p more =>
    generalize hA : ['&'].intercalate ((p :: more).map fun (k, v) =>
      (percentEncode k).toList ++ '=' :: (percentEncode v).toList) = A
    have hAchars : ∀ c ∈ A, targetChar c = true := by
      rw [← hA]
      refine forall_mem_intercalate (by decide) fun l hl c hc => ?_
      obtain ⟨⟨k, v⟩, -, rfl⟩ := List.mem_map.mp hl
      simp only [List.mem_append, List.mem_cons] at hc
      rcases hc with hc | rfl | hc
      · simp [targetChar, (encoded_ne c hc).2.2.2.2.2.2.2.2]
      · decide
      · simp [targetChar, (encoded_ne c hc).2.2.2.2.2.2.2.2]
    have hpairs : ((p :: more).map fun (k, v) => percentEncode k ++ "=" ++ percentEncode v).map
        String.toList = (p :: more).map fun (k, v) =>
          (percentEncode k).toList ++ '=' :: (percentEncode v).toList := by
      rw [List.map_map]
      exact List.map_congr_left fun ⟨k, v⟩ _ => by simp [String.toList_append]
    have htarget : r.target.toList = '/' :: (P ++ '?' :: A) := by
      have e : r.target = "/" ++ "/".intercalate (r.path.map percentEncode)
          ++ ("?" ++ "&".intercalate (r.query.map fun (k, v) =>
            percentEncode k ++ "=" ++ percentEncode v)) := by
        simp [target, hquery]
      rw [e, String.toList_append, String.toList_append, String.toList_append, hpath,
        String.toList_intercalate, hquery, hpairs, show ("&" : String).toList = ['&'] from rfl, hA]
      rfl
    rw [htarget, target?]
    have hall : (P ++ '?' :: A).all targetChar = true := by
      simp only [List.all_append, List.all_cons, List.all_eq_true.mpr fun c hc => (hPchars c hc).2,
        List.all_eq_true.mpr hAchars]
      decide
    have hqA : query? A = some (p :: more) := by
      rw [← hA]
      exact query?_query (by simp)
    have ht : List.takeWhile (fun x => x != '?') ('?' :: A) = [] := by simp
    have hd : List.dropWhile (fun x => x != '?') ('?' :: A) = '?' :: A := by simp
    simp only [hall, ↓reduceIte, List.takeWhile_append_of_pos hq, List.dropWhile_append_of_pos hq,
      ht, hd, List.append_nil, List.drop_one, List.tail_cons, hsegments, hqA]

end Request

namespace Request

private theorem toLower_eq_iff' (s t : String) :
    s.toLower = t ↔ s.toList.map Char.toLower = t.toList := by
  rw [← String.toList_inj, String.toLower, String.toList_map]

private def readField (field : String × String) : String × String :=
  (field.1.toLower, String.ofList (trimOws field.2.toList))

private theorem fieldLine_mem {r : Request} {host : String} {field : String × String}
    (h : field ∈ r.fields host) : field.1 ++ ": " ++ field.2 ∈ r.head host := by
  rw [head_eq]
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨field, h, rfl⟩)

private theorem value_plain {r : Request} {host : String} (hsent : (r.wire host).isSome)
    {field : String × String} (h : field ∈ r.fields host) : field.2.toList.all plain = true := by
  have := head_plain r host hsent _ (fieldLine_mem h)
  simp only [String.toList_append, List.all_append, Bool.and_eq_true] at this
  exact this.2

private theorem ows_of_visible {c : Char} (h : visible c = true) : ows c = false := by
  simp only [visible, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [ows, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  constructor <;> intro e <;> rw [e] at h <;> exact absurd h.1 (by decide)

private theorem filter_host (r : Request) (host : String) :
    (r.fields host).filter (·.1.toLower == "host") = [("Host", host)] := by
  have narrowed : (r.fields host).filter (·.1.toLower == "host")
      = ((r.fields host).filter (frames ·.1)).filter (·.1.toLower == "host") := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro field _
    by_cases h : field.1.toLower = "host" <;> simp [h, frames]
  rw [narrowed, fields_framing]
  simp [toLower_eq_iff']

private theorem filter_length (r : Request) (host : String) :
    (r.fields host).filter (·.1.toLower == "content-length")
      = [("Content-Length", toString r.body.size)] := by
  have narrowed : (r.fields host).filter (·.1.toLower == "content-length")
      = ((r.fields host).filter (frames ·.1)).filter (·.1.toLower == "content-length") := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro field _
    by_cases h : field.1.toLower = "content-length" <;> simp [h, frames]
  rw [narrowed, fields_framing]
  simp [toLower_eq_iff']

private theorem filter_coding (r : Request) (host : String) :
    (r.fields host).filter (·.1.toLower == "transfer-encoding") = [] :=
  List.filter_eq_nil_iff.mpr fun field hf => by
    simpa using r.fields_transferEncoding host field hf

private theorem filter_read (fields : List (String × String)) (name : String) :
    ((fields.map readField).filter (·.1 == name)).map (·.2)
      = (fields.filter (·.1.toLower == name)).map fun f => String.ofList (trimOws f.2.toList) := by
  rw [List.filter_map, List.map_map]
  rfl

private theorem digits_ne {n : Nat} : ∀ c ∈ (toString n).toList, ows c = false ∧ c ≠ '\t' := by
  intro c hc
  have hd : c.isDigit = true := by
    simp only [Nat.toString_eq_repr, Nat.toList_repr] at hc
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
  have h1 := Char.le_def.mp hd.1
  refine ⟨?_, fun e => by rw [e] at h1; exact absurd h1 (by decide)⟩
  simp only [ows, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  constructor <;> intro e <;> rw [e] at h1 <;> exact absurd h1 (by decide)

private theorem fieldLines_wire {r : Request} {host : String} (hsent : (r.wire host).isSome) :
    (((r.fields host).map fun field => field.1 ++ ": " ++ field.2).map String.toList).mapM
      fieldLine? = .ok ((r.fields host).map readField) := by
  rw [List.map_map, List.mapM_map]
  refine mapM_ok fun field hf => ?_
  simp only [Function.comp_apply, fieldLine?,
    headerLine?_field (r.fields_token host field hf) (value_plain hsent hf)]
  rfl

private theorem host?_wire {r : Request} {host : String} (hvisible : host.toList.all visible = true)
    (hne : host ≠ "") (hchars : host.toList.all hostChar = true) :
    host? .http11 ((r.fields host).map readField) = .ok () := by
  have htrim : String.ofList (trimOws host.toList) = host := by
    rw [trimOws_of_forall fun c hc => ows_of_visible (List.all_eq_true.mp hvisible c hc),
      String.ofList_toList]
  simp only [host?, filter_read, filter_host, List.map_cons, List.map_nil, htrim]
  simp [hne, hchars]

private theorem framing?_wire {limits : Limits} {r : Request} {host : String}
    (hbody : r.body.size ≤ limits.body_max) (hdigits : r.body.size < 10 ^ 18) :
    framing? limits .http11 ((r.fields host).map readField) = .ok (.length r.body.size) := by
  have htrim : String.ofList (trimOws (toString r.body.size).toList) = toString r.body.size := by
    rw [trimOws_of_forall fun c hc => (digits_ne c hc).1, String.ofList_toList]
  simp only [framing?, filter_read, filter_length, filter_coding, List.map_cons, List.map_nil,
    htrim, decimal?_toString hdigits, show ¬ limits.body_max < r.body.size by omega, ↓reduceIte]

theorem tabbedFraming_wire (r : Request) (host : String) :
    tabbedFraming (((r.fields host).map fun field => field.1 ++ ": " ++ field.2).map
      String.toList) = false := by
  simp only [tabbedFraming, List.map_map, List.any_map, List.any_eq_false, Function.comp_apply,
    Bool.and_eq_true, not_and]
  intro field hf hname
  have htoken := r.fields_token host field hf
  have hcolon : ∀ c ∈ field.1.toList, (c != ':') = true := by
    intro c hc
    simp only [token, Bool.and_eq_true, List.all_eq_true] at htoken
    refine bne_iff_ne.mpr fun e => ?_
    subst e
    exact absurd (htoken.2 _ hc) (by decide)
  have hline : (field.1 ++ ": " ++ field.2).toList = field.1.toList ++ ':' :: ' ' :: field.2.toList :=
    by simp
  rw [hline, List.takeWhile_append_of_pos hcolon, List.takeWhile_cons_of_neg (by decide),
    List.append_nil, String.ofList_toList] at hname
  have hlength : field.1.toLower = "content-length" := by
    have hcoding := r.fields_transferEncoding host field hf
    simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at hname
    exact hname.resolve_right hcoding
  have : field ∈ (r.fields host).filter (·.1.toLower == "content-length") :=
    List.mem_filter.mpr ⟨hf, by simp [hlength]⟩
  rw [filter_length, List.mem_singleton] at this
  subst this
  simp only [String.toList_append, List.contains_iff_mem, List.mem_append, not_or]
  refine ⟨⟨by decide, by decide⟩, fun h => (digits_ne _ h).2 rfl⟩

private theorem parseHead_wire {limits : Limits} {r : Request} {host : String} (hsent : (r.wire host).isSome)
    (hvisible : host.toList.all visible = true) (hne : host ≠ "")
    (hfits : r.fits limits host = true) :
    parseHead limits ((r.head host).map String.toList)
      = .ok { method := r.method, headOnly := false, path := r.path, query := r.query,
              version := .http11, fields := (r.fields host).map readField,
              framing := .length r.body.size } := by
  simp only [fits, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hfits
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hcount⟩, hbody⟩, hdigits⟩, hchars⟩, hpath⟩ := hfits
  have htarget : ∀ c ∈ r.target.toList, c ≠ ' ' := by
    intro c hc e
    have := List.all_eq_true.mp r.target_visible c hc
    rw [e] at this
    exact absurd this (by decide)
  have hpieces : pieces ' ' (methodWord r.method ++ " " ++ r.target ++ " HTTP/1.1").toList
      = [(methodWord r.method).toList, r.target.toList, "HTTP/1.1".toList] := by
    have e : (methodWord r.method ++ " " ++ r.target ++ " HTTP/1.1").toList
        = (methodWord r.method).toList ++ ' ' :: (r.target.toList ++ ' ' :: "HTTP/1.1".toList) := by
      simp
    rw [e, pieces_append (word_ne_space _), pieces_append htarget, pieces_of_forall (by decide)]
  rw [head_eq, List.map_cons]
  exact parseHead_of hpieces rfl (method?_word _) (by simpa using hcount) (fieldLines_wire hsent)
    (host?_wire hvisible hne hchars) (tabbedFraming_wire r host) (framing?_wire hbody hdigits)
    (target?_target r hpath)

end Request

namespace Request

private theorem elements_close : elements ["close"] = ["close"] := by
  simp only [elements, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    pieces_of_forall (show ∀ c ∈ "close".toList, c ≠ ',' by decide), List.map_cons, List.map_nil,
    trimOws_of_forall (show ∀ c ∈ "close".toList, ows c = false by decide), String.ofList_toList]
  rw [List.cons.injEq, toLower_eq_iff']
  exact ⟨by decide, rfl⟩

private theorem close_wire (r : Request) (host : String) :
    ((r.fields host).map readField).any (fun (name, value) =>
      name == "connection" && (elements [value]).contains "close") = true := by
  have hread : readField ("Connection", "close") = ("connection", "close") := by
    simp only [readField, trimOws_of_forall (show ∀ c ∈ "close".toList, ows c = false by decide),
      String.ofList_toList, Prod.mk.injEq, and_true]
    rw [toLower_eq_iff']
    decide
  refine List.any_eq_true.mpr ⟨("connection", "close"), List.mem_map.mpr
    ⟨("Connection", "close"), by simp [fields], hread⟩, ?_⟩
  simp [elements_close]

private theorem lines_wire {r : Request} {host : String} (hsent : (r.wire host).isSome) :
    ∀ l ∈ r.head host, l ≠ "" ∧ ∀ c ∈ l.toList, c ≠ '\n' := by
  intro l hl
  have hplain := head_plain r host hsent l hl
  refine ⟨fun e => ?_, fun c hc e => ?_⟩
  · rw [head_eq] at hl
    rcases List.mem_cons.mp hl with rfl | hl
    · have := congrArg String.length e
      simp at this
    · obtain ⟨field, -, rfl⟩ := List.mem_map.mp hl
      have := congrArg String.length e
      simp at this
  · have := List.all_eq_true.mp hplain c hc
    rw [e] at this
    exact absurd this (by decide)

/-- What `Request.wire` writes is read back as written, with its names in lowercase and the
blanks around its values left out, as soon as its last byte is there, wherever it starts in
the bytes and whatever follows it. -/
theorem read_wire {limits : Limits} {r : Request} {host : String} {w : ByteArray}
    (hw : r.wire host = some w) (hfits : r.fits limits host = true) (pre tail : ByteArray) :
    read limits (pre ++ (w ++ tail)) pre.size = .done (r.sent host) (pre.size + w.size) := by
  have hsent : (r.wire host).isSome := by rw [hw]; rfl
  have hhost : host ≠ "" ∧ host.toList.all visible = true := by
    simp only [wire] at hw
    split at hw
    · rename_i h
      simpa using h
    · cases hw
  have hwire : w = headWire (r.head host) ++ r.body := by
    have hb : (host != "") = true := by simpa using hhost.1
    simp only [wire, hb, hhost.2, Bool.and_self, ↓reduceIte, Option.some.injEq] at hw
    exact hw.symm
  have hfits' := hfits
  simp only [fits, Bool.and_eq_true, decide_eq_true_eq] at hfits'
  obtain ⟨⟨⟨⟨⟨⟨hline, hhead⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hfits'
  have hparse := parseHead_wire hsent hhost.2 hhost.1 hfits
  have hne : r.head host ≠ [] := by rw [head_eq]; simp
  have hbytes : pre ++ (w ++ tail) = pre ++ (headWire (r.head host) ++ (r.body ++ tail)) := by
    rw [hwire, ByteArray.append_assoc]
  have hsize : (headWire (r.head host)).size = ("\r\n".intercalate (r.head host)).utf8ByteSize + 4 := by
    rw [headWire, String.toUTF8_eq_toByteArray, String.size_toByteArray, String.utf8ByteSize_append]
    rfl
  unfold read
  rw [hbytes, readHead_headWire limits pre _ hne (fun l hl => (lines_wire hsent l hl).1)
    (.inl fun l hl => (lines_wire hsent l hl).2)]
  simp only [show ¬ limits.line_max < ((r.head host).headD "").utf8ByteSize by omega,
    show ¬ limits.head_max < ("\r\n".intercalate (r.head host)).utf8ByteSize + 4 by omega,
    ↓reduceIte, hparse]
  have hbody : (pre ++ (headWire (r.head host) ++ (r.body ++ tail))).extract
      (pre.size + ("\r\n".intercalate (r.head host)).utf8ByteSize + 4)
      (pre.size + ("\r\n".intercalate (r.head host)).utf8ByteSize + 4 + r.body.size) = r.body := by
    rw [← ByteArray.append_assoc]
    have := extract_append_front (pre ++ headWire (r.head host)) r.body tail
    rwa [ByteArray.size_append, hsize, ← Nat.add_assoc] at this
  simp only [ByteArray.size_append, hsize, show pre.size + ("\r\n".intercalate (r.head host)).utf8ByteSize
    + 4 + r.body.size ≤ pre.size + (("\r\n".intercalate (r.head host)).utf8ByteSize + 4
      + (r.body.size + tail.size)) by omega, ↓reduceIte, hbody, hwire]
  have hclose := close_wire r host
  congr 1
  · simp only [Head.incoming, Head.close, hclose, Bool.or_true, sent]
    rfl
  · omega

/-- Every strict start of what `Request.wire` writes, wherever it starts, needs more. -/
theorem read_wire_extract {limits : Limits} {r : Request} {host : String} {w : ByteArray}
    (hw : r.wire host = some w) (hfits : r.fits limits host = true) (pre : ByteArray) {n : Nat}
    (hn : n < w.size) : read limits (pre ++ w.extract 0 n) pre.size = .more := by
  have hwhole := read_wire hw hfits pre .empty
  rw [ByteArray.append_empty] at hwhole
  have hcut : (pre ++ w).extract 0 (pre.size + n) = pre ++ w.extract 0 n := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    have hpre : pre.data.toList.length = pre.size := by simp
    rw [toList_extract_zero, ByteArray.data_append, ByteArray.data_append, Array.toList_append,
      Array.toList_append, toList_extract_zero, List.take_append, hpre,
      List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
  rcases read_extract limits (pre ++ w) (pre.size + n) pre.size with e | e
  · rw [hcut] at e
    exact e
  · rw [hcut, hwhole] at e
    have := (read_done e).2.1
    simp only [ByteArray.size_append, ByteArray.size_extract] at this
    omega

end Request

/-! What a head the reader takes is made of, and the heads it refuses -/

namespace Request

theorem pieces_ne_nil (sep : Char) : ∀ l, pieces sep l ≠ []
  | [] => by simp [pieces]
  | c :: l => by
    simp only [pieces]
    split <;> simp

theorem intercalate_pieces (sep : Char) : ∀ l, [sep].intercalate (pieces sep l) = l
  | [] => rfl
  | c :: l => by
    have ih := intercalate_pieces sep l
    obtain ⟨p, ps, hps⟩ := List.exists_cons_of_ne_nil (pieces_ne_nil sep l)
    simp only [pieces, hps, List.headD_cons, List.tail_cons]
    rw [hps] at ih
    split
    · rename_i h
      rw [List.intercalate_cons_cons, ih, h]
      rfl
    · cases ps with
      | nil => simpa using ih
      | cons q ps =>
        rw [List.intercalate_cons_cons] at ih ⊢
        rw [← ih]
        rfl

private theorem clean_of_visible {c : Char} (h : visible c = true) : c ≠ '\r' ∧ c ≠ '\n' := by
  constructor <;> (rintro rfl; exact absurd h (by decide))

private theorem clean_of_plain {c : Char} (h : plain c = true) : c ≠ '\r' ∧ c ≠ '\n' := by
  constructor <;> (rintro rfl; exact absurd h (by decide))

/-- The name of a field line the reader takes is a token right up to its colon, and the line
has neither CR nor LF. -/
theorem headerLine?_some {line : List Char} {field : String × String}
    (h : headerLine? line = some field) :
    token (String.ofList (line.takeWhile (· != ':'))) = true
      ∧ field.1 = (String.ofList (line.takeWhile (· != ':'))).toLower
      ∧ ∀ c ∈ line, c ≠ '\r' ∧ c ≠ '\n' := by
  simp only [headerLine?] at h
  split at h
  · rename_i x value hd
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      cases h
      refine ⟨hc.1, rfl, fun c hc' => ?_⟩
      rw [← List.takeWhile_append_dropWhile (p := (· != ':')) (l := line), hd] at hc'
      rcases List.mem_append.mp hc' with hc' | hc'
      · have htok := hc.1
        simp only [token, Bool.and_eq_true, List.all_eq_true, String.toList_ofList] at htok
        exact clean_of_visible (visible_of_tokenChar (htok.2 c hc'))
      · rcases List.mem_cons.mp hc' with rfl | hc'
        · have := dropWhile_head hd
          simp only [bne_eq_false_iff_eq] at this
          rw [this]
          decide
        · exact clean_of_plain (List.all_eq_true.mp hc.2 c hc')
    · cases h
  · cases h

private theorem method?_clean {m : List Char} {mh : Method × Bool} (h : method? m = .ok mh) :
    ∀ c ∈ m, c ≠ '\r' ∧ c ≠ '\n' := by
  have hm : m = (String.ofList m).toList := String.toList_ofList.symm
  simp only [method?] at h
  split at h <;> rename_i heq
  all_goals first
    | (rw [hm, heq]; decide)
    | (split at h <;> cases h)

private theorem version?_clean {v : List Char} {version : Version} (h : version? v = .ok version) :
    ∀ c ∈ v, c ≠ '\r' ∧ c ≠ '\n' := by
  simp only [version?] at h
  split at h
  · decide
  · decide
  · split at h <;> cases h
  · cases h

private theorem target?_clean {t : List Char} {pq : List String × List (String × String)}
    (h : target? t = .ok pq) : ∀ c ∈ t, c ≠ '\r' ∧ c ≠ '\n' := by
  simp only [target?] at h
  split at h
  · rename_i rest
    split at h
    · rename_i hall
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · decide
      · have := List.all_eq_true.mp hall c hc
        constructor <;> (rintro rfl; exact absurd this (by decide))
    · cases h
  · cases h

/-- A head the reader takes has neither CR nor LF in any of its lines: a bare CR or LF is never
read as part of a line or as the end of one. -/
theorem parseHead_clean {limits : Limits} {lines : List (List Char)} {head : Head}
    (h : parseHead limits lines = .ok head) : ∀ l ∈ lines, ∀ c ∈ l, c ≠ '\r' ∧ c ≠ '\n' := by
  cases lines with
  | nil => simp [parseHead] at h
  | cons line fieldLines =>
    obtain ⟨m, t, v, hp, hv, hm, -, hf, -, -, -, hpq⟩ := parseHead_ok h
    intro l hl c hc
    rcases List.mem_cons.mp hl with rfl | hl
    · rw [← intercalate_pieces ' ' l, hp] at hc
      refine forall_mem_intercalate (p := fun c => c ≠ '\r' ∧ c ≠ '\n') (by decide)
        (fun part hpart => ?_) c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpart
      rcases hpart with rfl | rfl | rfl
      · exact method?_clean hm
      · exact target?_clean hpq
      · exact version?_clean hv
    · obtain ⟨field, hfield⟩ := mapM_ok_mem hf l hl
      simp only [fieldLine?] at hfield
      split at hfield
      · rename_i field' hl'
        exact (headerLine?_some hl').2.2 c hc
      · cases hfield

private theorem fieldLines_names {fieldLines : List (List Char)} :
    ∀ {fields : List (String × String)}, fieldLines.mapM fieldLine? = .ok fields →
      fields.map (·.1) = fieldLines.map (fun l => (String.ofList (l.takeWhile (· != ':'))).toLower)
        ∧ ∀ l ∈ fieldLines, token (String.ofList (l.takeWhile (· != ':'))) = true := by
  induction fieldLines with
  | nil => intro fields h; cases h; simp
  | cons l ls ih =>
    intro fields h
    rw [List.mapM_cons] at h
    cases hl : fieldLine? l with
    | error e => simp [hl, bind, Except.bind] at h
    | ok f =>
      cases hls : ls.mapM fieldLine? with
      | error e => simp [hl, hls, bind, Except.bind] at h
      | ok fs =>
        simp only [hl, hls, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [fieldLine?] at hl
        split at hl
        · rename_i f' hf'
          cases hl
          obtain ⟨htok, hname, -⟩ := headerLine?_some hf'
          obtain ⟨ih₁, ih₂⟩ := ih hls
          refine ⟨by simp [hname, ih₁], fun l' hl' => ?_⟩
          rcases List.mem_cons.mp hl' with rfl | hl'
          · exact htok
          · exact ih₂ l' hl'
        · cases hl

private theorem framing?_both {limits : Limits} {version : Version}
    {fields : List (String × String)} (hl : "content-length" ∈ fields.map (·.1))
    (hc : "transfer-encoding" ∈ fields.map (·.1)) {framing : Framing} :
    framing? limits version fields ≠ .ok framing := by
  have hl' : (fields.filter (·.1 == "content-length")).map (·.2) ≠ [] := by
    obtain ⟨f, hf, e⟩ := List.mem_map.mp hl
    intro hnil
    have := List.filter_eq_nil_iff.mp (List.map_eq_nil_iff.mp hnil) f hf
    simp [e] at this
  have hc' : (fields.filter (·.1 == "transfer-encoding")).map (·.2) ≠ [] := by
    obtain ⟨f, hf, e⟩ := List.mem_map.mp hc
    intro hnil
    have := List.filter_eq_nil_iff.mp (List.map_eq_nil_iff.mp hnil) f hf
    simp [e] at this
  simp only [framing?]
  generalize (fields.filter (·.1 == "content-length")).map (·.2) = lengths at hl'
  generalize (fields.filter (·.1 == "transfer-encoding")).map (·.2) = codings at hc'
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hc'
  obtain ⟨l, ls, rfl⟩ := List.exists_cons_of_ne_nil hl'
  simp

private theorem framing?_twoLengths {limits : Limits} {version : Version}
    {fields : List (String × String)}
    (h : 2 ≤ ((fields.map (·.1)).filter (· == "content-length")).length) {framing : Framing} :
    framing? limits version fields ≠ .ok framing := by
  have hlen : 2 ≤ ((fields.filter (·.1 == "content-length")).map (·.2)).length := by
    rw [List.length_map]
    rw [List.filter_map, List.length_map] at h
    exact h
  simp only [framing?]
  generalize (fields.filter (·.1 == "content-length")).map (·.2) = lengths at hlen
  generalize (fields.filter (·.1 == "transfer-encoding")).map (·.2) = codings
  match lengths, hlen with
  | _ :: _ :: _, _ => cases codings <;> simp

/-- The name a reader that splits a field line at its first colon sees, without the blanks
around it and in lowercase. -/
def fieldName (line : String) : String :=
  (String.ofList (trimOws (line.toList.takeWhile (· != ':')))).toLower

/-- A head of lines that the reader cannot take is refused, whatever follows it: never read,
and never waited on. -/
theorem read_headWire_refuse {limits : Limits} (pre rest : ByteArray) {lines : List String}
    (hne : lines ≠ []) (hlines : ∀ l ∈ lines, l ≠ "")
    (hclean : (∀ l ∈ lines, ∀ c ∈ l.toList, c ≠ '\n') ∨ (∀ l ∈ lines, ∀ c ∈ l.toList, c ≠ '\r'))
    (h : ∀ head, parseHead limits (lines.map String.toList) ≠ .ok head) :
    ∃ why, read limits (pre ++ (headWire lines ++ rest)) pre.size = .refuse why := by
  have hr : ∃ why, readHead limits (pre ++ (headWire lines ++ rest)) pre.size = .refuse why := by
    rw [readHead_headWire limits pre rest hne hlines hclean]
    by_cases h₁ : limits.line_max < (lines.headD "").utf8ByteSize
    · exact ⟨.uriTooLong, by simp only [h₁, ↓reduceIte]⟩
    · by_cases h₂ : limits.head_max < ("\r\n".intercalate lines).utf8ByteSize + 4
      · exact ⟨.fieldsTooLarge, by simp only [h₁, h₂, ↓reduceIte]⟩
      · simp only [h₁, h₂, ↓reduceIte]
        cases hp : parseHead limits (lines.map String.toList) with
        | error why => exact ⟨why, rfl⟩
        | ok head => exact absurd hp (h head)
  obtain ⟨why, hw⟩ := hr
  unfold read
  rw [hw]
  exact ⟨why, rfl⟩

private theorem names_of_ok {limits : Limits} {lines : List String} {head : Head}
    (h : parseHead limits (lines.map String.toList) = .ok head) :
    head.fields.map (·.1) = lines.tail.map fieldName
      ∧ framing? limits head.version head.fields = .ok head.framing
      ∧ ∀ l ∈ lines.tail, token (String.ofList (l.toList.takeWhile (· != ':'))) = true := by
  cases lines with
  | nil => simp [parseHead] at h
  | cons line more =>
    obtain ⟨-, -, -, -, -, -, -, hf, -, -, hfr, -⟩ := parseHead_ok h
    obtain ⟨hnames, htokens⟩ := fieldLines_names hf
    have htokens' : ∀ l ∈ more, token (String.ofList (l.toList.takeWhile (· != ':'))) = true :=
      fun l hl => htokens _ (List.mem_map.mpr ⟨l, hl, rfl⟩)
    refine ⟨?_, hfr, htokens'⟩
    rw [hnames, List.map_map, List.tail_cons]
    refine List.map_congr_left fun l hl => ?_
    have htok := htokens' l hl
    simp only [token, Bool.and_eq_true, List.all_eq_true, String.toList_ofList] at htok
    simp only [Function.comp_apply, fieldName]
    rw [trimOws_of_forall fun c hc => ows_of_visible (visible_of_tokenChar (htok.2 c hc))]

/-- A head with a `Content-Length` and a `Transfer-Encoding`, in either order, with any values
and any blanks around the names, is refused, whatever follows it (CL.TE and TE.CL). -/
theorem read_lengthAndCoding {limits : Limits} (pre rest : ByteArray) {lines : List String}
    (hlines : ∀ l ∈ lines, l ≠ "" ∧ ∀ c ∈ l.toList, c ≠ '\n')
    (hlength : ∃ l ∈ lines.tail, fieldName l = "content-length")
    (hcoding : ∃ l ∈ lines.tail, fieldName l = "transfer-encoding") :
    ∃ why, read limits (pre ++ (headWire lines ++ rest)) pre.size = .refuse why := by
  have hne : lines ≠ [] := by rintro rfl; simp at hlength
  refine read_headWire_refuse pre rest hne (fun l hl => (hlines l hl).1)
    (.inl fun l hl => (hlines l hl).2) fun head hp => ?_
  obtain ⟨hnames, hfr, -⟩ := names_of_ok hp
  obtain ⟨l, hl, el⟩ := hlength
  obtain ⟨c, hc, ec⟩ := hcoding
  exact framing?_both (by rw [hnames]; exact List.mem_map.mpr ⟨l, hl, el⟩)
    (by rw [hnames]; exact List.mem_map.mpr ⟨c, hc, ec⟩) hfr

/-- A head with two `Content-Length` fields is refused, whether their values differ or not. -/
theorem read_twoLengths {limits : Limits} (pre rest : ByteArray) {lines : List String}
    (hlines : ∀ l ∈ lines, l ≠ "" ∧ ∀ c ∈ l.toList, c ≠ '\n')
    (htwo : 2 ≤ (lines.tail.filter (fieldName · == "content-length")).length) :
    ∃ why, read limits (pre ++ (headWire lines ++ rest)) pre.size = .refuse why := by
  have hne : lines ≠ [] := by rintro rfl; simp at htwo
  refine read_headWire_refuse pre rest hne (fun l hl => (hlines l hl).1)
    (.inl fun l hl => (hlines l hl).2) fun head hp => ?_
  obtain ⟨hnames, hfr, -⟩ := names_of_ok hp
  refine framing?_twoLengths ?_ hfr
  rw [hnames, List.filter_map, List.length_map]
  exact htwo

/-- A field line with a blank before its first colon is refused: a blank between a name and
its colon (RFC 9112, 5.1), and a line that starts with a blank, which folds it into the one
before it (obs-fold, RFC 9112, 5.2). -/
theorem read_blankInName {limits : Limits} (pre rest : ByteArray) {lines : List String}
    (hlines : ∀ l ∈ lines, l ≠ "" ∧ ∀ c ∈ l.toList, c ≠ '\n')
    (hblank : ∃ l ∈ lines.tail, (l.toList.takeWhile (· != ':')).any ows = true) :
    ∃ why, read limits (pre ++ (headWire lines ++ rest)) pre.size = .refuse why := by
  have hne : lines ≠ [] := by rintro rfl; simp at hblank
  refine read_headWire_refuse pre rest hne (fun l hl => (hlines l hl).1)
    (.inl fun l hl => (hlines l hl).2) fun head hp => ?_
  obtain ⟨-, -, htokens⟩ := names_of_ok hp
  obtain ⟨l, hl, hany⟩ := hblank
  have htok := htokens l hl
  simp only [token, Bool.and_eq_true, List.all_eq_true, String.toList_ofList] at htok
  obtain ⟨c, hc, hows⟩ := List.any_eq_true.mp hany
  have := ows_of_visible (visible_of_tokenChar (htok.2 c hc))
  rw [this] at hows
  cases hows

theorem read_fold {limits : Limits} (pre rest : ByteArray) {lines : List String}
    (hlines : ∀ l ∈ lines, l ≠ "" ∧ ∀ c ∈ l.toList, c ≠ '\n')
    (hfold : ∃ l ∈ lines.tail, l.toList.head? = some ' ' ∨ l.toList.head? = some '\t') :
    ∃ why, read limits (pre ++ (headWire lines ++ rest)) pre.size = .refuse why := by
  obtain ⟨l, hl, hhead⟩ := hfold
  refine read_blankInName pre rest hlines ⟨l, hl, ?_⟩
  cases hcs : l.toList with
  | nil => rw [hcs] at hhead; simp at hhead
  | cons c cs =>
    rw [hcs] at hhead
    simp only [List.head?_cons, Option.some.injEq] at hhead
    rcases hhead with rfl | rfl <;> simp [ows]

/-- A head with a bare CR in it, a CR not followed by LF, is refused (RFC 9112, 2.2). -/
theorem read_bareCR {limits : Limits} (pre rest : ByteArray) {lines : List String}
    (hlines : ∀ l ∈ lines, l ≠ "" ∧ ∀ c ∈ l.toList, c ≠ '\n')
    (hcr : ∃ l ∈ lines, '\r' ∈ l.toList) :
    ∃ why, read limits (pre ++ (headWire lines ++ rest)) pre.size = .refuse why := by
  have hne : lines ≠ [] := by rintro rfl; simp at hcr
  refine read_headWire_refuse pre rest hne (fun l hl => (hlines l hl).1)
    (.inl fun l hl => (hlines l hl).2) fun head hp => ?_
  obtain ⟨l, hl, hc⟩ := hcr
  exact (parseHead_clean hp l.toList (List.mem_map.mpr ⟨l, hl, rfl⟩) '\r' hc).1 rfl

/-- A head with a bare LF in it, which some parsers take for the end of a line, is refused. -/
theorem read_bareLF {limits : Limits} (pre rest : ByteArray) {lines : List String}
    (hlines : ∀ l ∈ lines, l ≠ "" ∧ ∀ c ∈ l.toList, c ≠ '\r')
    (hlf : ∃ l ∈ lines, '\n' ∈ l.toList) :
    ∃ why, read limits (pre ++ (headWire lines ++ rest)) pre.size = .refuse why := by
  have hne : lines ≠ [] := by rintro rfl; simp at hlf
  refine read_headWire_refuse pre rest hne (fun l hl => (hlines l hl).1)
    (.inr fun l hl => (hlines l hl).2) fun head hp => ?_
  obtain ⟨l, hl, hc⟩ := hlf
  exact (parseHead_clean hp l.toList (List.mem_map.mpr ⟨l, hl, rfl⟩) '\n' hc).2 rfl

end Request

/-! A chunk size line that is not one to sixteen hex digits -/

namespace Request

/-- Whether the chunk reader reads a byte as a hex digit. -/
def hexByte (b : UInt8) : Bool :=
  (hexValue? (Char.ofNat b.toNat)).isSome

/-- A chunk whose size line is not one to sixteen hex digits followed by CR is refused: blanks,
a sign, `0x`, an extension, a bare LF, an empty size or seventeen digits. -/
theorem chunkSize_bad {bytes : ByteArray} {pos : Nat} {line : List UInt8}
    (hline : ∀ k (hk : k < line.length), bytes[pos + k]? = some line[k])
    (hcr : bytes[pos + line.length]? = some 13) (hno : ∀ b ∈ line, b ≠ 13)
    (hbad : ¬ (line ≠ [] ∧ line.length ≤ 16 ∧ line.all hexByte = true)) :
    chunkSize bytes pos = .refuse .badRequest := by
  generalize hk : ((line.take 16).takeWhile hexByte).length = k
  have hprefix : k ≤ (line.take 16).length := by
    rw [← hk]
    exact (List.takeWhile_prefix _).length_le
  have hk16 : k ≤ 16 := by simp at hprefix; omega
  have hkline : k ≤ line.length := by simp at hprefix; omega
  have hdigit : ∀ i (hi : i < k), bytes[pos + i]?.bind (fun b => hexValue? (Char.ofNat b.toNat))
      = some ((hexValue? (Char.ofNat (line[i]'(by omega)).toNat)).getD 0) := by
    intro i hi
    have hhex := takeWhile_getElem (p := hexByte) (l := line.take 16) (i := i) (by omega)
      (by simp; omega)
    simp only [List.getElem_take] at hhex
    rw [hline i (by omega), Option.bind_some]
    simp only [hexByte, Option.isSome_iff_exists] at hhex
    obtain ⟨d, hd⟩ := hhex
    rw [hd]
    rfl
  have hstop : k < 16 → bytes[pos + k]?.bind (fun b => hexValue? (Char.ofNat b.toNat)) = none := by
    intro h16
    by_cases hlt : k < line.length
    · have hnot := takeWhile_stop (p := hexByte) (l := line.take 16) (by simp; omega)
      simp only [hk, List.getElem_take] at hnot
      rw [hline k hlt, Option.bind_some]
      simpa [hexByte] using hnot
    · rw [show k = line.length by omega, hcr]
      decide
  have hhex := hex_digits bytes ((List.range k).map fun i =>
      if h : i < line.length then (hexValue? (Char.ofNat line[i].toNat)).getD 0 else 0)
    chunkSizeDigits_max pos 0 (by simp [chunkSizeDigits_max]; omega)
    (fun i hi => by
      simp only [List.length_map, List.length_range] at hi
      simp only [List.getElem_map, List.getElem_range, show i < line.length by omega,
        ↓reduceDIte]
      exact hdigit i hi)
    (fun h => by simpa using hstop (by simpa [chunkSizeDigits_max] using h))
  simp only [List.length_map, List.length_range] at hhex
  unfold chunkSize
  rw [hhex]
  simp only
  by_cases hk0 : k = 0
  · subst hk0
    have : pos < bytes.size := by
      by_cases hz : line.length = 0
      · obtain ⟨h, -⟩ := getElem_of_getElem? (show bytes[pos + line.length]? = some 13 from hcr)
        omega
      · obtain ⟨h, -⟩ := getElem_of_getElem? (hline 0 (by omega))
        omega
    simp only [Nat.add_zero, ↓reduceIte, this]
  · simp only [show ¬ pos + k = pos by omega, ↓reduceIte]
    by_cases hlt : k < line.length
    · have hb := hline k hlt
      obtain ⟨hsize, e⟩ := getElem_of_getElem? hb
      have hne : line[k] ≠ 13 := hno _ (List.getElem_mem _)
      unfold crlf
      by_cases h₁ : pos + k + 1 < bytes.size
      · simp [h₁, e, hne]
      · simp [h₁, hsize, e, hne]
    · exfalso
      apply hbad
      have hall : ((line.take 16).takeWhile hexByte).length = (line.take 16).length := by
        rw [hk]
        simp
        omega
      refine ⟨fun e => by subst e; simp at hkline; omega, by omega, ?_⟩
      have := forall_of_takeWhile_length hall
      rw [List.take_of_length_le (by omega)] at this
      exact List.all_eq_true.mpr this

theorem chunks_badSize {limits : Limits} {bytes : ByteArray} {pos : Nat} {line : List UInt8}
    (hline : ∀ k (hk : k < line.length), bytes[pos + k]? = some line[k])
    (hcr : bytes[pos + line.length]? = some 13) (hno : ∀ b ∈ line, b ≠ 13)
    (hbad : ¬ (line ≠ [] ∧ line.length ≤ 16 ∧ line.all hexByte = true)) (fuel : Nat)
    (body : ByteArray) : chunks limits bytes (fuel + 1) pos body = .refuse .badRequest := by
  simp [chunks, chunkSize_bad hline hcr hno hbad]

/-- A chunked request whose first chunk's size line is not one to sixteen hex digits followed
by CR is refused, whatever its head and whatever follows. -/
theorem read_badChunkSize {limits : Limits} {bytes : ByteArray} {pos : Nat} {head : Head}
    {start : Nat} (hhead : readHead limits bytes pos = .done head start)
    (hchunked : head.framing = .chunked) {line : List UInt8}
    (hline : ∀ k (hk : k < line.length), bytes[start + k]? = some line[k])
    (hcr : bytes[start + line.length]? = some 13) (hno : ∀ b ∈ line, b ≠ 13)
    (hbad : ¬ (line ≠ [] ∧ line.length ≤ 16 ∧ line.all hexByte = true)) :
    read limits bytes pos = .refuse .badRequest := by
  unfold read
  rw [hhead]
  simp only [hchunked, chunks_badSize hline hcr hno hbad]

end Request

end Lanes.Http
