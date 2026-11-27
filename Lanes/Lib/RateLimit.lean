/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
The token bucket of Go's `golang.org/x/time/rate`, as a pure state machine over time as data
(D23): `count` tokens every `period_ms` milliseconds, at most `burst` held, starting full.
Arithmetic is exact: a bucket holds credit in units of `1 / period_ms` of a token, and each
millisecond adds `count` of them.

`allow` is `AllowN`: it takes `n` tokens if they are there and otherwise changes nothing.
`reserve` is `ReserveN` with no limit on the wait: it takes `n ≤ burst` tokens now, possibly
into debt, and says how long to wait before acting. Proved: the bucket never holds more than
`burst` tokens (`credit_allow_le`), in any window of `w` milliseconds at most
`burst + rate · w` tokens are allowed (`allowed_le`), and a request that waits as `reserve`
tells it is allowed (`allow_after_reserve`).
-/

@[expose] public section

namespace Lanes.RateLimit

structure Config where
  burst : Nat
  /-- Tokens added every `period_ms`. -/
  count : Nat
  period_ms : Nat
  deriving DecidableEq, Repr

/-- The most credit a bucket holds: `burst` tokens. -/
def Config.cap (c : Config) : Int := c.burst * c.period_ms

structure Bucket where
  /-- In units of `1 / period_ms` of a token; below zero after a reservation into debt. -/
  credit : Int
  last_ms : Nat
  deriving DecidableEq, Repr

def full (c : Config) : Bucket := ⟨c.cap, 0⟩

/-- The credit at `t_ms`: what time has added since `last_ms`, up to the cap. Time that runs
backwards adds nothing. -/
def refill (c : Config) (b : Bucket) (t_ms : Nat) : Int :=
  min c.cap (b.credit + c.count * ((t_ms - b.last_ms : Nat) : Int))

def allow (c : Config) (b : Bucket) (t_ms n : Nat) : Bool × Bucket :=
  if n * c.period_ms ≤ refill c b t_ms then (true, ⟨refill c b t_ms - n * c.period_ms, t_ms⟩)
  else (false, b)

/-- How long, in whole milliseconds, until a credit of `r` is no longer in debt. -/
def wait (c : Config) (r : Int) : Nat :=
  if 0 ≤ r then 0 else ((-r).toNat + c.count - 1) / c.count

/-- `none` when `n` is more than the burst, or the rate is zero and the tokens are not there. -/
def reserve (c : Config) (b : Bucket) (t_ms n : Nat) : Option (Nat × Bucket) :=
  let r := refill c b t_ms - n * c.period_ms
  if n ≤ c.burst ∧ (0 ≤ r ∨ 0 < c.count) then some (wait c r, ⟨r, t_ms⟩) else none

/-- Requests `(t_ms, n)` in turn through `allow`: how many tokens it gave, and the bucket after. -/
def allowAll (c : Config) : Bucket → List (Nat × Nat) → Nat × Bucket
  | b, [] => (0, b)
  | b, (t, n) :: rest =>
    let (ok, b') := allow c b t n
    let (k, b'') := allowAll c b' rest
    ((if ok then n else 0) + k, b'')

theorem refill_le (c : Config) (b : Bucket) (t : Nat) : refill c b t ≤ c.cap := Int.min_le_left _ _

theorem refill_le_credit (c : Config) (b : Bucket) (t : Nat) :
    refill c b t ≤ b.credit + c.count * ((t - b.last_ms : Nat) : Int) := Int.min_le_right _ _

/-- The bucket never holds more than `burst` tokens. -/
theorem credit_allow_le (c : Config) {b : Bucket} (h : b.credit ≤ c.cap) (t n : Nat) :
    (allow c b t n).2.credit ≤ c.cap := by
  unfold allow
  split
  · have := refill_le c b t
    simp only
    have : (0 : Int) ≤ n * c.period_ms := by exact_mod_cast Nat.zero_le (n * c.period_ms)
    omega
  · exact h

theorem credit_reserve_le (c : Config) (b : Bucket) (t n : Nat) {d : Nat} {b' : Bucket}
    (h : reserve c b t n = some (d, b')) : b'.credit ≤ c.cap := by
  unfold reserve at h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    have := refill_le c b t
    have : (0 : Int) ≤ n * c.period_ms := by exact_mod_cast Nat.zero_le (n * c.period_ms)
    simp only
    omega
  · cases h

theorem credit_allowAll_le (c : Config) {b : Bucket} (h : b.credit ≤ c.cap) (reqs : List (Nat × Nat)) :
    (allowAll c b reqs).2.credit ≤ c.cap := by
  induction reqs generalizing b with
  | nil => exact h
  | cons r rest ih => exact ih (credit_allow_le c h r.1 r.2)

theorem allow_of_le {c : Config} {b : Bucket} {t n : Nat} (h : n * c.period_ms ≤ refill c b t) :
    allow c b t n = (true, ⟨refill c b t - n * c.period_ms, t⟩) := by
  simp [allow, h]

theorem allow_of_lt {c : Config} {b : Bucket} {t n : Nat} (h : ¬(n * c.period_ms : Int) ≤ refill c b t) :
    allow c b t n = (false, b) := by
  simp [allow, h]

theorem allowAll_cons (c : Config) (b : Bucket) (t n : Nat) (rest : List (Nat × Nat)) :
    allowAll c b ((t, n) :: rest)
      = ((if (allow c b t n).1 then n else 0) + (allowAll c (allow c b t n).2 rest).1,
        (allowAll c (allow c b t n).2 rest).2) := rfl

theorem credit_allowAll_nonneg (c : Config) {b : Bucket} (h : 0 ≤ b.credit) (reqs : List (Nat × Nat)) :
    0 ≤ (allowAll c b reqs).2.credit := by
  induction reqs generalizing b with
  | nil => exact h
  | cons r rest ih =>
    obtain ⟨t, n⟩ := r
    rw [allowAll_cons]
    apply ih
    by_cases hr : (n * c.period_ms : Int) ≤ refill c b t
    · rw [allow_of_le hr]; simp only; omega
    · rw [allow_of_lt hr]; exact h

theorem natCast_nonneg_mul (a b : Nat) : (0 : Int) ≤ a * b := by
  exact_mod_cast Nat.zero_le (a * b)

/-- After a request at `t ≥ last_ms`, what is spent and what is left is at most what was there
and what time added until `T`. -/
theorem allowAll_spend (c : Config) (T : Nat) (reqs : List (Nat × Nat)) :
    ∀ b : Bucket, reqs.Pairwise (fun a b => a.1 ≤ b.1) → (∀ r ∈ reqs, b.last_ms ≤ r.1 ∧ r.1 ≤ T) →
      b.last_ms ≤ T → 0 ≤ b.credit →
      ((allowAll c b reqs).1 * c.period_ms : Int) + (allowAll c b reqs).2.credit
        ≤ b.credit + c.count * ((T - b.last_ms : Nat) : Int) := by
  induction reqs with
  | nil =>
    intro b _ _ _ _
    have := natCast_nonneg_mul c.count (T - b.last_ms)
    simp only [allowAll]
    omega
  | cons r rest ih =>
    obtain ⟨t, n⟩ := r
    intro b hs hr hT h0
    have ht := hr (t, n) (by simp)
    simp only at ht
    have hrest : ∀ r ∈ rest, t ≤ r.1 := fun r hm => List.rel_of_pairwise_cons hs hm
    have hs' := hs.of_cons
    rw [allowAll_cons]
    by_cases hok : (n * c.period_ms : Int) ≤ refill c b t
    · rw [allow_of_le hok]
      simp only [ite_true]
      have := ih ⟨refill c b t - n * c.period_ms, t⟩ hs'
        (fun r hm => ⟨hrest r hm, (hr r (by simp [hm])).2⟩) ht.2 (by simp only; omega)
      simp only at this
      have hle := refill_le_credit c b t
      have hsum : (T - b.last_ms : Nat) = (t - b.last_ms) + (T - t) := by omega
      have hsplit : (c.count : Int) * ((T - b.last_ms : Nat) : Int)
          = c.count * ((t - b.last_ms : Nat) : Int) + c.count * ((T - t : Nat) : Int) := by
        rw [hsum, Int.natCast_add, Int.mul_add]
      rw [Int.natCast_add, Int.add_mul]
      omega
    · rw [allow_of_lt hok]
      simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
      exact ih b hs' (fun r hm => hr r (by simp [hm])) hT h0

/-- In any window of `w` milliseconds, `allow` gives at most `burst + rate · w` tokens: in
credit, `burst · period_ms + count · w`. -/
theorem allowed_le (c : Config) (b : Bucket) (reqs : List (Nat × Nat))
    (hs : reqs.Pairwise (fun a b => a.1 ≤ b.1)) (t0 w : Nat)
    (hw : ∀ r ∈ reqs, t0 ≤ r.1 ∧ r.1 ≤ t0 + w) :
    ((allowAll c b reqs).1 * c.period_ms : Int) ≤ c.cap + c.count * w := by
  induction reqs generalizing b with
  | nil =>
    have := natCast_nonneg_mul c.burst c.period_ms
    have := natCast_nonneg_mul c.count w
    simp only [allowAll, Config.cap]
    omega
  | cons r rest ih =>
    obtain ⟨t, n⟩ := r
    have ht := hw (t, n) (by simp)
    simp only at ht
    have hrest : ∀ r ∈ rest, t ≤ r.1 := fun r hm => List.rel_of_pairwise_cons hs hm
    have hs' := hs.of_cons
    rw [allowAll_cons]
    by_cases hok : (n * c.period_ms : Int) ≤ refill c b t
    · rw [allow_of_le hok]
      simp only [ite_true]
      have h0 : (0 : Int) ≤ refill c b t - n * c.period_ms := by omega
      have := allowAll_spend c (t0 + w) rest ⟨refill c b t - n * c.period_ms, t⟩ hs'
        (fun r hm => ⟨hrest r hm, (hw r (by simp [hm])).2⟩) ht.2 h0
      have hf := credit_allowAll_nonneg c (b := ⟨refill c b t - n * c.period_ms, t⟩) h0 rest
      simp only at this hf
      have hcap := refill_le c b t
      have hmono : (c.count : Int) * ((t0 + w - t : Nat) : Int) ≤ c.count * w :=
        Int.mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : t0 + w - t ≤ w)) (by omega)
      rw [Int.natCast_add, Int.add_mul]
      omega
    · rw [allow_of_lt hok]
      simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
      exact ih b hs' (fun r hm => hw r (by simp [hm]))

theorem mul_ceil_ge (x k : Nat) (hk : 0 < k) : x ≤ k * ((x + k - 1) / k) := by
  have := Nat.div_add_mod (x + k - 1) k
  have := Nat.mod_lt (x + k - 1) hk
  omega

/-- A request that waits as `reserve` tells it, with nothing else taken meanwhile, is allowed. -/
theorem allow_after_reserve (c : Config) (b : Bucket) {t n d : Nat} {b' : Bucket}
    (h : reserve c b t n = some (d, b')) (hl : b.last_ms ≤ t) : (allow c b (t + d) n).1 = true := by
  unfold reserve at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hcap : (n * c.period_ms : Int) ≤ c.cap := by
      simp only [Config.cap]
      exact_mod_cast Nat.mul_le_mul_right c.period_ms hc.1
    suffices hge : (n * c.period_ms : Int) ≤ refill c b (t + wait c (refill c b t - n * c.period_ms)) by
      rw [allow_of_le hge]
    unfold wait
    split
    · simp only [Nat.add_zero]; omega
    · rename_i hneg
      have hpos : 0 < c.count := by omega
      have hless : refill c b t = b.credit + c.count * ((t - b.last_ms : Nat) : Int) := by
        unfold refill at hneg ⊢
        omega
      have hx := mul_ceil_ge (-(refill c b t - n * c.period_ms)).toNat c.count hpos
      have htn : (((-(refill c b t - n * c.period_ms)).toNat : Nat) : Int)
          = -(refill c b t - n * c.period_ms) := Int.toNat_of_nonneg (by omega)
      generalize ((-(refill c b t - ↑n * ↑c.period_ms)).toNat + c.count - 1) / c.count = q at hx ⊢
      have hx' : (-(refill c b t - n * c.period_ms) : Int) ≤ c.count * q := by
        rw [← htn]; exact_mod_cast hx
      have hsum : (t + q - b.last_ms : Nat) = (t - b.last_ms) + q := by omega
      unfold refill
      rw [hsum, Int.natCast_add, Int.mul_add]
      refine Int.le_min.mpr ⟨hcap, ?_⟩
      omega
  · cases h

end Lanes.RateLimit
