/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.Cookie

/-!
A cookie read back as a browser reads it. `readSetCookie` is what RFC 6265 (5.2) has a browser
store from a `Set-Cookie` header; `readSetCookie_header` proves that it stores a valid cookie's
name and value and exactly the attributes the cookie names, so no value can add one, and
`setCookie_read` that every header `Response.setCookie` adds is read so. `cookieHeader` is the
`Cookie` header a browser sends back (5.4), and `parseCookies_cookieHeader` proves that
`parseCookies` reads its names and values.
-/

@[expose] public section

namespace Lanes.Http

/-- What a browser stores from a `Set-Cookie` header: the name and value, split at the first `=`
of the text before the first `;`, and the attributes, the pieces between the later `;`, each
trimmed. `none` if the text has no `=` or the name is empty. -/
def readSetCookie (header : String) : Option (String × String × List String) :=
  match header.toList.splitOn ';' with
  | pair :: attrs =>
    match pair.dropWhile (· != '=') with
    | '=' :: value =>
      let name := trimBlank (pair.takeWhile (· != '='))
      if name.isEmpty then none
      else some (String.ofList name, String.ofList (trimBlank value),
        attrs.map fun attr => String.ofList (trimBlank attr))
    | _ => none
  | [] => none

/-- The `Cookie` header a browser sends for the cookies it holds. -/
def cookieHeader (pairs : List (String × String)) : String :=
  "; ".intercalate (pairs.map fun pair => pair.1 ++ "=" ++ pair.2)

/-- A character that ends no piece of a cookie header and is not trimmed from one. -/
private def bare (c : Char) : Bool :=
  c != ';' && !c.isWhitespace

private theorem ne_of_bare {c : Char} (h : bare c) : c ≠ ';' := by
  simp only [bare, Bool.and_eq_true, bne_iff_ne] at h
  exact h.1

private theorem whitespace_of_bare {c : Char} (h : bare c) : c.isWhitespace = false := by
  simp only [bare, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2

private theorem whitespace_of_visible {c : Char} (h : visible c) : c.isWhitespace = false := by
  cases hw : c.isWhitespace
  · rfl
  · simp only [Char.isWhitespace, Bool.or_eq_true, decide_eq_true_eq] at hw
    rcases hw with ((rfl | rfl) | rfl) | rfl <;> exact absurd h (by decide)

private theorem bare_of_visible {c : Char} (h : visible c) (hc : c ≠ ';') : bare c := by
  simp [bare, hc, whitespace_of_visible h]

private theorem bare_of_token {c : Char} (h : tokenChar c) : bare c ∧ c ≠ '=' :=
  ⟨bare_of_visible (visible_of_tokenChar h) (by rintro rfl; exact absurd h (by decide)),
    by rintro rfl; exact absurd h (by decide)⟩

private theorem bare_of_octet {c : Char} (h : cookieOctet c) : bare c := by
  simp only [cookieOctet, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact bare_of_visible h.1.1.1.1 h.1.2

private theorem bare_of_digit {c : Char} (h : c.isDigit) : bare c := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq, UInt32.le_iff_toNat_le] at h
  cases hw : c.isWhitespace
  · have : c ≠ ';' := by rintro rfl; simp at h
    simp [bare, this, hw]
  · simp only [Char.isWhitespace, Bool.or_eq_true, decide_eq_true_eq] at hw
    rcases hw with ((rfl | rfl) | rfl) | rfl <;> simp at h

private theorem dropWhile_whitespace {l : List Char} (h : ∀ c ∈ l, c.isWhitespace = false) :
    l.dropWhile Char.isWhitespace = l := by
  cases l with
  | nil => rfl
  | cons c cs => simp [h c (by simp)]

private theorem trimBlank_bare {l : List Char} (h : ∀ c ∈ l, bare c) : trimBlank l = l := by
  have hw : ∀ c ∈ l, c.isWhitespace = false := fun c hc => whitespace_of_bare (h c hc)
  rw [trimBlank, dropWhile_whitespace hw,
    dropWhile_whitespace fun c hc => hw c (List.mem_reverse.mp hc), List.reverse_reverse]

private theorem trimBlank_space {l : List Char} (h : ∀ c ∈ l, bare c) : trimBlank (' ' :: l) = l := by
  have hw : ∀ c ∈ l, c.isWhitespace = false := fun c hc => whitespace_of_bare (h c hc)
  rw [trimBlank, List.dropWhile_cons_of_pos (by decide), dropWhile_whitespace hw,
    dropWhile_whitespace fun c hc => hw c (List.mem_reverse.mp hc), List.reverse_reverse]

private theorem intercalate_semicolon : ∀ (x : List Char) (xs : List (List Char)),
    ([';', ' '] : List Char).intercalate (x :: xs) = [';'].intercalate (x :: xs.map (' ' :: ·))
  | x, [] => by simp
  | x, y :: ys => by
    rw [List.intercalate_cons_cons, List.map_cons, List.intercalate_cons_cons,
      List.intercalate_cons_cons_left, intercalate_semicolon y ys]
    simp

private theorem split_header (part : String) (parts : List String)
    (h : ∀ s ∈ part :: parts, ∀ c ∈ s.toList, bare c) :
    ("; ".intercalate (part :: parts)).toList.splitOn ';'
      = part.toList :: parts.map fun s => ' ' :: s.toList := by
  rw [String.toList_intercalate, List.map_cons, show "; ".toList = [';', ' '] from rfl,
    intercalate_semicolon, List.map_map]
  apply List.splitOn_intercalate
  · intro l hl hmem
    simp only [List.mem_cons, List.mem_map, Function.comp_apply] at hl
    rcases hl with rfl | ⟨s, hs, rfl⟩
    · exact ne_of_bare (h part (by simp) ';' hmem) rfl
    · simp only [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · exact absurd heq (by decide)
      · exact ne_of_bare (h s (by simp [hs]) ';' hmem) rfl
  · simp

private theorem attributes_bare (c : Cookie) (hpath : c.path.toList.all cookieOctet) :
    ∀ s ∈ c.attributes, ∀ d ∈ s.toList, bare d := by
  intro s hs d hd
  simp only [Cookie.attributes, List.mem_append, List.mem_singleton, Option.mem_toList,
    Option.map_eq_some_iff] at hs
  rcases hs with (((rfl | ⟨n, -, rfl⟩) | hs) | hs) | rfl
  · simp only [String.toList_append, List.mem_append] at hd
    rcases hd with hd | hd
    · revert d; decide
    · exact bare_of_octet (List.all_eq_true.mp hpath d hd)
  · simp only [String.toList_append, List.mem_append] at hd
    rcases hd with hd | hd
    · revert d; decide
    · rw [show toString n = n.repr from rfl, Nat.toList_repr] at hd
      exact bare_of_digit (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hd)
  · split at hs
    · simp only [List.mem_singleton] at hs; subst hs; revert d; decide
    · simp at hs
  · split at hs
    · simp only [List.mem_singleton] at hs; subst hs; revert d; decide
    · simp at hs
  · simp only [String.toList_append, List.mem_append] at hd
    rcases hd with hd | hd
    · revert d; decide
    · generalize c.sameSite = site at hd
      cases site <;> revert d <;> decide

/-- A browser stores a valid cookie's name and value, and exactly the attributes it names. -/
theorem readSetCookie_header {c : Cookie} (h : c.valid) :
    readSetCookie c.header = some (c.name, c.value, c.attributes) := by
  simp only [Cookie.valid, token, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨hname, hnameChars⟩, hvalue⟩, hpath⟩ := h
  have hn : ∀ d ∈ c.name.toList, bare d ∧ d ≠ '=' :=
    fun d hd => bare_of_token (List.all_eq_true.mp hnameChars d hd)
  have hv : ∀ d ∈ c.value.toList, bare d := fun d hd => bare_of_octet (List.all_eq_true.mp hvalue d hd)
  have hattrs := attributes_bare c hpath
  have hpair : ∀ d ∈ (c.name ++ "=" ++ c.value).toList, bare d := by
    intro d hd
    simp only [String.toList_append, List.mem_append] at hd
    rcases hd with (hd | hd) | hd
    · exact (hn d hd).1
    · revert d; decide
    · exact hv d hd
  have hsplit := split_header _ _ fun s hs => by
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hpair
    · exact hattrs s hs
  have hstop : ∀ d ∈ c.name.toList, (d != '=') = true := fun d hd => by simp [(hn d hd).2]
  have hempty : (trimBlank c.name.toList).isEmpty = false := by
    rw [trimBlank_bare fun d hd => (hn d hd).1]
    cases hc : c.name.toList with
    | nil => exact absurd (String.toList_eq_nil_iff.mp hc) hname
    | cons _ _ => rfl
  rw [readSetCookie, Cookie.header, hsplit]
  simp only [String.toList_append, show "=".toList = ['='] from rfl, List.append_assoc,
    List.singleton_append, List.dropWhile_append_of_pos hstop, List.takeWhile_append_of_pos hstop]
  simp only [List.dropWhile_cons, List.takeWhile_cons, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, List.append_nil, hempty]
  rw [trimBlank_bare fun d hd => (hn d hd).1, trimBlank_bare hv]
  simp only [String.ofList_toList, List.map_map, Function.comp_def, Option.some.injEq,
    Prod.mk.injEq, true_and]
  conv => rhs; rw [← List.map_id c.attributes]
  exact List.map_congr_left fun s hs => by
    rw [trimBlank_space (hattrs s hs), String.ofList_toList]
    rfl

/-- Every `Set-Cookie` header `setCookie` adds is read by a browser as `c`, with exactly the
attributes `c` names. -/
theorem setCookie_read (r : Response) (c : Cookie) {value : String}
    (h : ("set-cookie", value) ∈ (r.setCookie c).headers) :
    ("set-cookie", value) ∈ r.headers ∨ readSetCookie value = some (c.name, c.value, c.attributes) := by
  unfold Response.setCookie at h
  split at h
  · rename_i hvalid
    simp only [Response.withHeader, List.mem_append, List.mem_singleton, Prod.mk.injEq,
      true_and] at h
    rcases h with h | rfl
    · exact .inl h
    · exact .inr (readSetCookie_header hvalid)
  · exact .inl h

private theorem parseCookie_piece {name value : String} (hname : token name) {l : List Char}
    (hl : trimBlank l = (name ++ "=" ++ value).toList) : parseCookie l = some (name, value) := by
  unfold parseCookie
  simp only [token, Bool.and_eq_true, bne_iff_ne, ne_eq] at hname
  have hnot : '=' ∉ name.toList := fun hmem =>
    (bare_of_token (List.all_eq_true.mp hname.2 _ hmem)).2 rfl
  rw [hl, String.toList_append, String.toList_append, show "=".toList = ['='] from rfl,
    List.append_assoc, List.singleton_append, List.splitOn_append_cons_self_of_not_mem hnot]
  obtain ⟨v, vs, hvs⟩ := List.exists_cons_of_ne_nil (List.splitOn_ne_nil '=' value.toList)
  have hne : name.toList.isEmpty = false := by
    cases hc : name.toList with
    | nil => exact absurd (String.toList_eq_nil_iff.mp hc) hname.1
    | cons _ _ => rfl
  simp only [hvs, hne, Bool.false_eq_true, ↓reduceIte, String.ofList_toList]
  rw [← hvs, List.intercalate_splitOn, String.ofList_toList]

private theorem filterMap_parseCookie : ∀ (pairs : List (String × String)),
    (∀ q ∈ pairs, token q.1 ∧ ∀ d ∈ (q.1 ++ "=" ++ q.2).toList, bare d) →
    (pairs.map fun q => ' ' :: (q.1 ++ "=" ++ q.2).toList).filterMap parseCookie = pairs
  | [], _ => rfl
  | q :: qs, h => by
    rw [List.map_cons, List.filterMap_cons,
      parseCookie_piece (h q (by simp)).1 (trimBlank_space (h q (by simp)).2),
      filterMap_parseCookie qs fun q' hq' => h q' (by simp [hq'])]

/-- `parseCookies` reads the names and values of the `Cookie` header a browser sends, for names
that are tokens and values of cookie octets: those `Cookie.valid` lets `setCookie` set. -/
theorem parseCookies_cookieHeader {pairs : List (String × String)}
    (h : ∀ p ∈ pairs, token p.1 ∧ p.2.toList.all cookieOctet) :
    parseCookies (cookieHeader pairs) = pairs := by
  cases pairs with
  | nil => simp [parseCookies, cookieHeader, parseCookie, trimBlank]
  | cons p ps =>
    have hbare : ∀ q ∈ p :: ps, ∀ d ∈ (q.1 ++ "=" ++ q.2).toList, bare d := by
      intro q hq d hd
      obtain ⟨hn, hv⟩ := h q hq
      simp only [token, Bool.and_eq_true] at hn
      simp only [String.toList_append, List.mem_append] at hd
      rcases hd with (hd | hd) | hd
      · exact (bare_of_token (List.all_eq_true.mp hn.2 d hd)).1
      · revert d; decide
      · exact bare_of_octet (List.all_eq_true.mp hv d hd)
    rw [parseCookies, cookieHeader, List.map_cons,
      split_header _ _ fun s hs => by
        simp only [List.mem_cons, List.mem_map] at hs
        rcases hs with rfl | ⟨q, hq, rfl⟩
        · exact hbare p (by simp)
        · exact hbare q (by simp [hq]),
      List.filterMap_cons, parseCookie_piece (h p (by simp)).1
        (trimBlank_bare (hbare p (by simp))), List.map_map]
    simp only [Function.comp_def]
    rw [filterMap_parseCookie ps fun q hq => ⟨(h q (by simp [hq])).1, hbare q (by simp [hq])⟩]

theorem Request.sameOrigin_iff (r : Request) (origin : String) :
    r.sameOrigin origin = true
      ↔ (∀ o, r.header? "origin" = some o → o = origin)
        ∧ ∀ site, r.header? "sec-fetch-site" = some site → site = "same-origin" ∨ site = "none" := by
  simp [Request.sameOrigin, Option.all_eq_true]

theorem Request.bodyWithin_iff (r : Request) (limit : Nat) :
    r.bodyWithin limit = true ↔ r.body.size ≤ limit := by
  simp [Request.bodyWithin]

end Lanes.Http
