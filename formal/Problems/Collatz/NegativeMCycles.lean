import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The `3n-1` map: odd runs and the chaining of local minima

Lemmas 1 and 3 of the laboratory note *No m-cycles of the 3n−1 map for m ≤ 58*
(`docs/theory/collatz_3n_minus_1_m_cycles_note.md`), for the map

  `g y = y / 2` (`y` even),   `g y = (3 y - 1) / 2` (`y` odd)

on the positive integers, which is the shortcut `3n+1` map read on the negatives.

**The conjugated variable.** The odd step subtracts, so in `u = y - 1` an odd step is exactly
`u ↦ 3 (u / 2)`: halve, then triple. Writing the start of an odd run as `y = 2 ^ a * m + 1`
with `m` odd puts the whole run in closed form and removes every truncated subtraction:

  `g^[k] (2 ^ a * m + 1) = 3 ^ k * 2 ^ (a - k) * m + 1`   for `k ≤ a`  (`negT_run_iter`).

Everything in Lemma 1 reads off that identity: the iterate is odd exactly while `k < a`
(`negT_run_odd`, `negT_run_even`), the run of `a` odd steps starts at `y ≥ 2 ^ a + 1`
(`negT_start_ge`), and the local maximum is `3 ^ a * m + 1` (`negT_localMax`).

**Lemma 3, the chaining.** With at least one halving after the run, the next local minimum
`y'` has `u' = y' - 1` below `u ^ δ / 2`, `δ = log₂ 3`. The integer half is
`2 * u' < 3 ^ a * m` (`negT_chain_nat`), and the only real input is
`3 ^ a * m ≤ (2 ^ a * m) ^ δ`, which is `2 ^ δ = 3` together with `m ≤ m ^ δ`
(`negT_chain_real`). No `X₀` enters the constant, which is why the note's Lemma 3 is exact
where Simons–de Weger's Lemma 6 carries `b = (1 + X₀⁻¹) / 2 ^ (1/δ)`.

**What is not here.** Lemma 2 (the cycle equation and the bound on `Λ`), Rhin's measure, and
the tables. The floor is a computation, archived with the branch `negative_floor_3x1`.
-/

namespace Problems.Collatz

/-- The `3n-1` shortcut map on the positive integers: `y/2` when `y` is even, `(3y-1)/2` when
`y` is odd. Equal to the shortcut `3n+1` map read on the negative integers under `x = -y`. -/
def negT (y : ℕ) : ℕ :=
  if y % 2 = 0 then y / 2 else (3 * y - 1) / 2

theorem negT_even {y : ℕ} (h : Even y) : negT y = y / 2 := by
  have : y % 2 = 0 := Nat.even_iff.mp h
  simp [negT, this]

theorem negT_odd {y : ℕ} (h : Odd y) : negT y = (3 * y - 1) / 2 := by
  have : y % 2 = 1 := Nat.odd_iff.mp h
  simp [negT, this]

/-- `g` iterated, as `g (g^[k-1] y)`. -/
def negTIter : ℕ → ℕ → ℕ
  | 0, y => y
  | k + 1, y => negT (negTIter k y)

@[simp] theorem negTIter_zero (y : ℕ) : negTIter 0 y = y := rfl

@[simp] theorem negTIter_succ (k y : ℕ) :
    negTIter (k + 1) y = negT (negTIter k y) := rfl

/-! ## Lemma 1: an odd run in closed form -/

/-- **One odd step, in the conjugated variable.** For `u` even, `g (u + 1) = 3 (u / 2) + 1`:
the odd step subtracts, so on `u = y - 1` it is exactly halve-then-triple. -/
theorem negT_step_succ {u : ℕ} (hu : Even u) :
    negT (u + 1) = 3 * (u / 2) + 1 := by
  have hmod : u % 2 = 0 := Nat.even_iff.mp hu
  have hodd : Odd (u + 1) := by
    refine Nat.odd_iff.mpr ?_
    omega
  have hu2 : 2 * (u / 2) = u := Nat.two_mul_div_two_of_even hu
  rw [negT_odd hodd]
  have : 3 * (u + 1) - 1 = 2 * (3 * (u / 2) + 1) := by omega
  rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

/-- **The run of an odd start, in closed form.** With `y = 2 ^ a * m + 1` and `m` odd, the
first `a` iterates are `g^[k] y = 3 ^ k * 2 ^ (a - k) * m + 1`. This is the note's Lemma 1:
the run identity `2 ^ k (g^[k] y - 1) = 3 ^ k (y - 1)` with no subtraction. -/
theorem negT_run_iter (a m : ℕ) :
    ∀ k ≤ a, negTIter k (2 ^ a * m + 1) = 3 ^ k * 2 ^ (a - k) * m + 1 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : k ≤ a := Nat.le_of_succ_le hk
    have hlt : k < a := hk
    rw [negTIter_succ, ih hk']
    -- the state is `u + 1` with `u = 3 ^ k * 2 ^ (a - k) * m` even, since `a - k ≥ 1`
    have hsub : a - k = (a - (k + 1)) + 1 := by omega
    have hu : 3 ^ k * 2 ^ (a - k) * m = 2 * (3 ^ k * 2 ^ (a - (k + 1)) * m) := by
      rw [hsub, pow_succ]; ring
    have heven : Even (3 ^ k * 2 ^ (a - k) * m) := by
      exact ⟨3 ^ k * 2 ^ (a - (k + 1)) * m, by omega⟩
    rw [negT_step_succ heven]
    have hhalf : 3 ^ k * 2 ^ (a - k) * m / 2 = 3 ^ k * 2 ^ (a - (k + 1)) * m := by
      rw [hu, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    rw [hhalf, pow_succ]
    ring

/-- The iterates stay odd for `k < a`. -/
theorem negT_run_odd {a m k : ℕ} (hk : k < a) :
    Odd (negTIter k (2 ^ a * m + 1)) := by
  rw [negT_run_iter a m k (le_of_lt hk)]
  have hsub : a - k = (a - (k + 1)) + 1 := by omega
  refine Nat.odd_iff.mpr ?_
  have : 3 ^ k * 2 ^ (a - k) * m = 2 * (3 ^ k * 2 ^ (a - (k + 1)) * m) := by
    rw [hsub, pow_succ]; ring
  omega

/-- The iterate at `k = a` is even: the run has exactly `a` odd steps. -/
theorem negT_run_even {a m : ℕ} (hm : Odd m) :
    Even (negTIter a (2 ^ a * m + 1)) := by
  rw [negT_run_iter a m a le_rfl]
  simp only [Nat.sub_self, pow_zero, mul_one]
  have h3 : Odd (3 ^ a) := Odd.pow (by decide : Odd (3 : ℕ))
  obtain ⟨t, ht⟩ := h3.mul hm
  exact ⟨t + 1, by omega⟩

/-- **A run of `a` odd steps starts at `y ≥ 2 ^ a + 1`** (the note's Lemma 1, last clause;
Hercher's Lemma 8 with `y ≡ 1` in place of `y ≡ -1`, so the floor is larger by two). -/
theorem negT_start_ge {a m : ℕ} (hm : 0 < m) :
    2 ^ a + 1 ≤ 2 ^ a * m + 1 := by
  have : 1 ≤ m := hm
  have := Nat.mul_le_mul_left (2 ^ a) this
  omega

/-- **The local maximum of the run** is `3 ^ a * m + 1`, so in the conjugated variable it is
exactly `3 ^ a * m`: the run multiplies `u` by `(3/2) ^ a`. -/
theorem negT_localMax (a m : ℕ) :
    negTIter a (2 ^ a * m + 1) = 3 ^ a * m + 1 := by
  rw [negT_run_iter a m a le_rfl]
  simp

/-- **The decomposition Lemma 1 starts from.** An odd `y ≥ 3` is `2 ^ a * m + 1` with `m` odd
and `a = v₂(y - 1) ≥ 1`; the note writes `u = y - 1` and `a = v₂(u)`. -/
theorem negT_run_decomp {y : ℕ} (hy : Odd y) (h3 : 3 ≤ y) :
    ∃ a m : ℕ, 1 ≤ a ∧ Odd m ∧ y = 2 ^ a * m + 1 := by
  have hu : y - 1 ≠ 0 := by omega
  obtain ⟨a, m, hm, huv⟩ := Nat.exists_eq_two_pow_mul_odd hu
  refine ⟨a, m, ?_, hm, by omega⟩
  rcases Nat.eq_zero_or_pos a with ha | ha
  · exfalso
    subst ha
    simp only [pow_zero, one_mul] at huv
    have hev : Even (y - 1) := by
      obtain ⟨j, hj⟩ := hy
      exact ⟨j, by omega⟩
    rw [huv] at hev
    exact (Nat.not_even_iff_odd.mpr hm) hev
  · exact ha

/-- **Lemma 1 of the note, packaged at an odd start.** For odd `y ≥ 3` there are `a ≥ 1` and
`m` odd with `y = 2 ^ a * m + 1` such that the first `a` iterates are odd, the `a`-th is even
(so the run has exactly `a` odd steps), the start satisfies `y ≥ 2 ^ a + 1`, and the local
maximum is `3 ^ a * m + 1`. -/
theorem negT_lemma_one {y : ℕ} (hy : Odd y) (h3 : 3 ≤ y) :
    ∃ a m : ℕ, 1 ≤ a ∧ Odd m ∧ y = 2 ^ a * m + 1 ∧
      (∀ k, k < a → Odd (negTIter k y)) ∧ Even (negTIter a y) ∧
      2 ^ a + 1 ≤ y ∧ negTIter a y = 3 ^ a * m + 1 := by
  obtain ⟨a, m, ha, hm, hy'⟩ := negT_run_decomp hy h3
  refine ⟨a, m, ha, hm, hy', ?_, ?_, ?_, ?_⟩
  · intro k hk; rw [hy']; exact negT_run_odd hk
  · rw [hy']; exact negT_run_even hm
  · rw [hy']; exact negT_start_ge hm.pos
  · rw [hy']; exact negT_localMax a m

/-! ## Lemma 3: the chaining of successive local minima -/

/-- **The chaining, in integers.** After the run's local maximum `3 ^ a * m + 1`, at least one
halving follows; the next local minimum `y'` has `u' = y' - 1` with `2 * u' < 3 ^ a * m`.
This is the exact form of the note's `u' < u ^ δ / 2`: no `X₀` enters the constant. -/
theorem negT_chain_nat {a m r y' : ℕ} (hm : 0 < m) (hr : 1 ≤ r)
    (hy' : 2 ^ r * y' = 3 ^ a * m + 1) :
    2 * (y' - 1) < 3 ^ a * m := by
  have hmpos : 0 < m := hm
  have hpos : 1 ≤ 3 ^ a * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : 2 ≤ 2 ^ r := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  have hle : 2 * y' ≤ 2 ^ r * y' := Nat.mul_le_mul_right _ h2
  omega

/-- **The chaining, with the exponent.** `δ = log₂ 3`; for `u = 2 ^ a * m` the local maximum in
the conjugated variable is `3 ^ a * m ≤ u ^ δ`, because `2 ^ δ = 3` and `m ≤ m ^ δ`. With the
integer half this is the note's Lemma 3, `u' < u ^ δ / 2`. -/
theorem negT_chain_real {a m r y' : ℕ} (hm : 0 < m) (hr : 1 ≤ r)
    (hy' : 2 ^ r * y' = 3 ^ a * m + 1) :
    ((y' - 1 : ℕ) : ℝ) < ((2 ^ a * m : ℕ) : ℝ) ^ (Real.logb 2 3) / 2 := by
  have hmpos : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hd : (1 : ℝ) < Real.logb 2 3 := by
    rw [show (1 : ℝ) = Real.logb 2 2 by simp]
    exact Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  -- `(2 ^ a) ^ δ = 3 ^ a`
  have htwo : ((2 : ℝ) ^ a) ^ (Real.logb 2 3) = (3 : ℝ) ^ a := by
    rw [← Real.rpow_natCast (2 : ℝ) a, ← Real.rpow_mul (by norm_num),
      mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
      Real.rpow_natCast]
  have hmle : (m : ℝ) ≤ (m : ℝ) ^ (Real.logb 2 3) :=
    Real.self_le_rpow_of_one_le hmpos (le_of_lt hd)
  have hsplit : ((2 ^ a * m : ℕ) : ℝ) ^ (Real.logb 2 3)
      = ((2 : ℝ) ^ a) ^ (Real.logb 2 3) * (m : ℝ) ^ (Real.logb 2 3) := by
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]
  have hub : ((3 ^ a * m : ℕ) : ℝ) ≤ ((2 ^ a * m : ℕ) : ℝ) ^ (Real.logb 2 3) := by
    rw [hsplit, htwo]
    push_cast
    exact mul_le_mul_of_nonneg_left hmle (by positivity)
  have hnat := negT_chain_nat hm hr hy'
  have hcast : (2 : ℝ) * ((y' - 1 : ℕ) : ℝ) < ((3 ^ a * m : ℕ) : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- **Lemma 3 of the note, packaged.** From a local minimum `y = 2 ^ a * m + 1`, with at least
one halving after the run carrying the local maximum to the next local minimum `y'`, the
conjugated variables obey `u' < u ^ δ / 2` with `u = y - 1`, `u' = y' - 1`, `δ = log₂ 3`. The
constant is exact: no verification floor enters it. -/
theorem negT_lemma_three {y y' a m r : ℕ} (hm : 0 < m) (hy : y = 2 ^ a * m + 1)
    (hr : 1 ≤ r) (hy' : 2 ^ r * y' = negTIter a y) :
    ((y' - 1 : ℕ) : ℝ) < ((y - 1 : ℕ) : ℝ) ^ (Real.logb 2 3) / 2 := by
  subst hy
  rw [negT_localMax a m] at hy'
  have hu : 2 ^ a * m + 1 - 1 = 2 ^ a * m := by omega
  rw [hu]
  exact negT_chain_real hm hr hy'

/-! ## The cycles that exist, against the lemmas

The note's Section 6 checks the inequalities where they must not exclude. The same three
cycles are the kernel's check that these statements are about the intended map: `1`,
`(5, 7, 10)` and the eleven-element cycle at `17`. -/

/-- **The sign is the content.** `g 17 = 25`, where the shortcut `3n+1` map gives `26`: a sign
flip in `negT` would falsify this, and with it every statement above. -/
theorem negT_sign_is_minus : negT 17 = 25 ∧ (3 * 17 + 1) / 2 = 26 := by decide

/-- The three known cycles of `g`. -/
theorem negT_cycle_one : negTIter 1 1 = 1 := by decide

theorem negT_cycle_five : negTIter 3 5 = 5 := by decide

theorem negT_cycle_seventeen : negTIter 11 17 = 17 := by decide

/-- The `17`-cycle read through Lemma 1: `17 = 2 ^ 4 * 1 + 1`, so the run has four odd steps,
`17, 25, 37, 55`, and the local maximum is `82 = 3 ^ 4 * 1 + 1`. -/
theorem negT_run_at_seventeen :
    negTIter 0 17 = 17 ∧ negTIter 1 17 = 25 ∧ negTIter 2 17 = 37 ∧
      negTIter 3 17 = 55 ∧ negTIter 4 17 = 82 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- Lemma 1 at `17`, from the general statement rather than by computation: `a = 4`, `m = 1`. -/
theorem negT_localMax_seventeen : negTIter 4 (2 ^ 4 * 1 + 1) = 3 ^ 4 * 1 + 1 :=
  negT_localMax 4 1

/-- **The chaining is tight on the `17`-cycle.** One halving carries the local maximum `82` to
the next local minimum `41`, so `u' = 40` against `u = 16`; the integer form of Lemma 3 gives
`2 * 40 < 81`, which is the note's `16 → 40` against `16 ^ δ / 2 = 40.5…` with a single unit
to spare. A weaker constant than `u ^ δ / 2` would not exclude it. -/
theorem negT_chain_tight_at_17 : 2 * (41 - 1) < 3 ^ 4 * 1 :=
  negT_chain_nat (by norm_num) (le_refl 1) (by decide)

end Problems.Collatz
