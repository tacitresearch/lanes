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

end Lanes.Http
