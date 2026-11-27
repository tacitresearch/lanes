import Ledger.System

/-!
The book's properties, proved of `Book.serve` and lifted to the ledger actor and every run; and
that a reply to a user shows only that user's records.
-/

namespace Ledger

open Lanes

variable {N C : Type} [DecidableEq N] [DecidableEq C]

namespace Book

/-- The four properties of a book, together. -/
def Sound (b : Book N) : Prop :=
  b.conserved .eur = true ∧ b.conserved .usd = true ∧ b.noOverdraft = true ∧ b.paired = true
    ∧ b.cached = true

omit [DecidableEq N] in
theorem conserved_iff (b : Book N) (c : Currency) :
    b.conserved c = true ↔ (b.accounts.map fun a => if a.currency = c then a.balance else 0).sum = 0 := by
  simp [conserved]

theorem check_ok {owner : N} {src dst : AccountId} {amount : Nat} {s? d? : Option (Account N)}
    {s d : Account N} (h : check owner src dst amount s? d? = .ok (s, d)) :
    s? = some s ∧ d? = some d ∧ src ≠ dst ∧ s.currency = d.currency ∧ s.owner = owner
      ∧ (s.allowsNegative = false → (amount : Int) ≤ s.balance) := by
  unfold check at h
  split at h
  · simp at h
  · rename_i s'
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i d'
        repeat (split at h; · simp at h)
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, rfl, by assumption, by simp_all, by simp_all, fun hneg => ?_⟩
        simp_all

omit [DecidableEq N] in
theorem paired_iff (b : Book N) :
    b.paired = true ↔ ∀ e ∈ b.entries, b.transferSum e.transfer = 0 := by
  simp [paired]

omit [DecidableEq N] in
theorem transferSum_zero {b : Book N} (h : b.paired = true) (t : ReqId) : b.transferSum t = 0 := by
  cases hf : b.entries.filter (·.transfer == t) with
  | nil => simp [transferSum, hf]
  | cons e rest =>
    have he : e ∈ b.entries.filter (·.transfer == t) := by simp [hf]
    obtain ⟨hmem, ht⟩ := List.mem_filter.mp he
    have := (paired_iff b).mp h e hmem
    simpa using (beq_iff_eq.mp ht) ▸ this

omit [DecidableEq N] in
theorem noOverdraft_iff (b : Book N) :
    b.noOverdraft = true ↔ ∀ a ∈ b.accounts, a.allowsNegative = false → 0 ≤ a.balance := by
  simp only [noOverdraft, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  refine forall_congr' fun a => imp_congr_right fun _ => ?_
  cases a.allowsNegative <;> simp

omit [DecidableEq N] in
theorem cached_iff (b : Book N) :
    b.cached = true ↔ (∀ e ∈ b.entries, e.account < b.accounts.length)
      ∧ ∀ k a, b.accounts[k]? = some a → a.balance = b.accountSum k := by
  simp only [cached, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    Option.all_eq_true_iff_get, beq_iff_eq]
  constructor
  · rintro ⟨he, hk⟩
    refine ⟨he, fun k a hka => ?_⟩
    have hlt := (List.getElem?_eq_some_iff.mp hka).1
    have := hk k hlt (by simp [hka])
    simpa [hka] using this
  · rintro ⟨he, hk⟩
    refine ⟨he, fun k _ hsome => ?_⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsome
    simpa [ha] using hk k a ha

section Transfer

variable {b : Book N} {owner : N} {id : ReqId} {src dst : AccountId} {amount : Nat}
  {s d : Account N} {A : List (Account N)}

omit [DecidableEq N] in
theorem getElem?_after (hs : b.accounts[src]? = some s) (hd : b.accounts[dst]? = some d)
    (k : Nat) :
    ((b.accounts.set src (debit s amount)).set dst (credit d amount))[k]?
      = if k = dst then some (credit d amount)
        else if k = src then some (debit s amount) else b.accounts[k]? := by
  have hsl := (List.getElem?_eq_some_iff.mp hs).1
  have hdl := (List.getElem?_eq_some_iff.mp hd).1
  simp only [List.getElem?_set, List.length_set]
  by_cases hkd : k = dst
  · subst hkd; simp [hdl]
  · by_cases hks : k = src
    · subst hks; simp [Ne.symm hkd, hkd, hsl]
    · simp [Ne.symm hkd, Ne.symm hks, hkd, hks]

omit [DecidableEq N] in
theorem accountSum_after (b : Book N) (k : Nat) :
    accountSum { accounts := A, entries := ⟨id, dst, src, amount⟩ :: ⟨id, src, dst, -(amount : Int)⟩
      :: b.entries } k
      = (if dst = k then (amount : Int) else 0) + (if src = k then -(amount : Int) else 0)
        + b.accountSum k := by
  simp only [accountSum, List.filter_cons, beq_iff_eq]
  by_cases hd : dst = k <;> by_cases hs : src = k <;> simp [hd, hs] <;> omega

omit [DecidableEq N] in
theorem transferSum_after (b : Book N) (t : Nat) :
    transferSum { accounts := A, entries := ⟨id, dst, src, amount⟩ :: ⟨id, src, dst, -(amount : Int)⟩
      :: b.entries } t = b.transferSum t := by
  simp only [transferSum, List.filter_cons, beq_iff_eq]
  by_cases h : id = t <;> simp [h] <;> omega

theorem transfer_sound (h : Sound b) : Sound (b.transfer owner id src dst amount).1 := by
  unfold transfer
  split
  · exact h
  · rename_i s d hcheck
    obtain ⟨hs, hd, hne, hcur, -, hfunds⟩ := check_ok hcheck
    obtain ⟨heur, husd, hover, hpair, hcache⟩ := h
    obtain ⟨hknown, hbal⟩ := (cached_iff b).mp hcache
    have hsl := (List.getElem?_eq_some_iff.mp hs).1
    have hdl := (List.getElem?_eq_some_iff.mp hd).1
    have hd1 : (b.accounts.set src (debit s amount))[dst]? = some d := by
      rw [List.getElem?_set_ne hne]; exact hd
    have hsum : ∀ c : Currency,
        (((b.accounts.set src (debit s amount)).set dst (credit d amount)).map
          fun a => if a.currency = c then a.balance else 0).sum
        = (b.accounts.map fun a => if a.currency = c then a.balance else 0).sum := by
      intro c
      have h1 := sum_map_set (fun a : Account N => if a.currency = c then a.balance else 0)
        (credit d amount) hd1
      have h2 := sum_map_set (fun a : Account N => if a.currency = c then a.balance else 0)
        (debit s amount) hs
      have e1 : (if (credit d amount).currency = c then (credit d amount).balance else 0)
          = (if d.currency = c then d.balance else 0) + (if d.currency = c then (amount : Int) else 0) := by
        by_cases hc : d.currency = c <;> simp [credit, hc]
      have e2 : (if (debit s amount).currency = c then (debit s amount).balance else 0)
          = (if s.currency = c then s.balance else 0) - (if d.currency = c then (amount : Int) else 0) := by
        by_cases hc : d.currency = c <;> simp [debit, hc, hcur] <;> omega
      omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [conserved_iff, hsum]; exact (conserved_iff b _).mp heur
    · rw [conserved_iff, hsum]; exact (conserved_iff b _).mp husd
    · rw [noOverdraft_iff]
      intro a ha hneg
      obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
      rw [getElem?_after hs hd] at hk
      have hold := (noOverdraft_iff b).mp hover
      split at hk
      · cases hk
        have := hold d (List.mem_of_getElem? hd) hneg
        simp [credit]; omega
      · split at hk
        · cases hk
          have := hfunds hneg
          simp [debit]; omega
        · exact hold a (List.mem_of_getElem? hk) hneg
    · rw [paired_iff]
      intro e _
      rw [transferSum_after]
      exact transferSum_zero hpair _
    · rw [cached_iff]
      refine ⟨?_, fun k a hk => ?_⟩
      · intro e he
        simp only [List.length_set]
        simp only [List.mem_cons] at he
        rcases he with rfl | rfl | he
        · exact hdl
        · exact hsl
        · exact hknown e he
      · rw [accountSum_after b k]
        rw [getElem?_after hs hd] at hk
        split at hk
        · rename_i hkd
          cases hk; subst hkd
          simp [credit, hbal _ _ hd, hne]; omega
        · rename_i hkd
          split at hk
          · rename_i hks
            cases hk; subst hks
            simp [debit, hbal _ _ hs, Ne.symm hkd]; omega
          · rename_i hks
            simp [Ne.symm hkd, Ne.symm hks, hbal _ _ hk]

end Transfer

omit [DecidableEq N] in
theorem openAccount_sound {b : Book N} (h : Sound b) (owner : N) (c : Currency)
    (allowsNegative : Bool) : Sound (b.openAccount owner c allowsNegative).1 := by
  obtain ⟨heur, husd, hover, hpair, hcache⟩ := h
  obtain ⟨hknown, hbal⟩ := (cached_iff b).mp hcache
  refine ⟨?_, ?_, ?_, hpair, ?_⟩
  · simpa [openAccount, conserved_iff] using (conserved_iff b _).mp heur
  · simpa [openAccount, conserved_iff] using (conserved_iff b _).mp husd
  · rw [noOverdraft_iff]
    intro a ha hneg
    simp only [openAccount, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact (noOverdraft_iff b).mp hover a ha hneg
    · simp
  · rw [cached_iff]
    refine ⟨fun e he => by simpa [openAccount] using Nat.lt_succ_of_lt (hknown e he), ?_⟩
    intro k a hk
    simp only [openAccount] at hk ⊢
    rw [List.getElem?_append] at hk
    split at hk
    · exact hbal k a hk
    · rename_i hge
      simp only [List.getElem?_singleton] at hk
      split at hk
      · rename_i hzero
        cases hk
        have hnone : b.entries.filter (·.account == k) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro e he
          have := hknown e he
          simp only [beq_iff_eq]
          intro heq
          exact hge (heq ▸ this)
        simp [accountSum, hnone]
      · simp at hk

theorem serve_sound {b : Book N} (h : Sound b) (config : Config N) (owner : N) (req : ReqId)
    (op : Op) : Sound (b.serve config owner req op).1 := by
  cases op with
  | openAccount c allowsNegative =>
    simp only [serve]
    split
    · exact h
    · split
      · exact h
      · exact openAccount_sound h owner c allowsNegative
  | transfer src dst amount => exact transfer_sound h
  | logOut | accounts | entries | audit => exact h

omit [DecidableEq N] in
theorem sound_empty : Sound ({} : Book N) := by
  simp [Sound, conserved, noOverdraft, paired, cached]

end Book

/-- The book is sound in every state the ledger actor reaches. -/
theorem ledger_sound (config : Config N) :
    (ledger (C := C) config).Invariant Book.Sound :=
  Actor.Inductive.invariant
    { init := Book.sound_empty
      step := fun b msg h => by
        cases msg with
        | answer => exact h
        | serve req owner op => exact Book.serve_sound h config owner req op
        | unlocked | ended => exact h
      recover := fun _ h => h }

/-- In every reachable state of the system, under every environment model, the book conserves
money in each currency, no account that may not go below zero does, every transfer's entries
sum to zero and every balance is the sum of its entries. -/
theorem book_invariant (config : Config N) (answering : Answering) (env : EnvModel (sig N C)) :
    (system N C config answering).Invariant env fun c => Book.Sound (c.state Id.ledger) :=
  System.invariant_of_actor _ Id.ledger (ledger_sound config) env

end Ledger

namespace Ledger

open Lanes

variable {N C : Type} [DecidableEq N] [DecidableEq C]

/-- What the ledger answers `owner` shows only `owner`'s records, but for the audit. -/
theorem serve_onlyOf (config : Config N) (b : Book N) (owner : N) (req : ReqId) (op : Op)
    (h : op ≠ .audit) :
    (b.serve config owner req op).2.onlyOf (b.serve config owner req op).1 owner = true := by
  cases op with
  | accounts =>
    simp only [Book.serve, Reply.onlyOf, List.all_eq_true, Bool.and_eq_true, beq_iff_eq]
    intro ⟨k, a⟩ hmem
    simp only [Book.accountsOf, List.mem_filterMap, Option.ite_none_right_eq_some,
      Option.some.injEq] at hmem
    obtain ⟨⟨a', k'⟩, hz, howner, heq⟩ := hmem
    cases heq
    have := List.mem_zipIdx_iff_getElem?.mp hz
    exact ⟨howner, by simpa [Book.owns, this] using howner⟩
  | entries =>
    simp only [Book.serve, Reply.onlyOf, Book.entriesOf, List.all_eq_true, List.mem_filter]
    exact fun _ he => he.2
  | audit => exact absurd rfl h
  | logOut => simp [Book.serve, Reply.onlyOf]
  | openAccount c neg =>
    simp only [Book.serve]
    split
    · rfl
    · split <;> rfl
  | transfer src dst amount =>
    simp only [Book.serve, Book.transfer]
    split <;> rfl

end Ledger
