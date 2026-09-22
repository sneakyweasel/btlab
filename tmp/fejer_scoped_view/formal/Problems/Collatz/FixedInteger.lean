import Problems.Collatz.Center

namespace Problems.Collatz

/-!
Fixed-integer affine identities. Every statement is an algebraic identity of
the accelerated formula `2^K x = 3^m n + C`. None of them assumes the
Collatz conjecture.
-/

/-- Integer affine gap `G = n (2^K - 3^m) - C`. -/
def affineGap (n twoPow threePow C : ℤ) : ℤ :=
  (twoPow - threePow) * n - C

/-- From `3^m n + C = 2^K x`, the gap equals `2^K (n - x)`. -/
theorem affineGap_eq_twoPow_mul_start_minus_x
    (twoPow threePow n C x : ℤ)
    (hEndpoint : threePow * n + C = twoPow * x) :
    affineGap n twoPow threePow C = twoPow * (n - x) := by
  simpa [affineGap] using
    affineCenter_start_numerator twoPow threePow n C x hEndpoint

/-- Exact `C` recurrence of one accelerated step. -/
def nextC (C twoPow : ℤ) : ℤ :=
  3 * C + twoPow

/-- Exact `G` recurrence along a valuation with homogeneous factor `2^k`. -/
theorem affineGap_succ
    (n C twoPow threePow twoPowK : ℤ) :
    affineGap n (twoPow * twoPowK) (3 * threePow) (nextC C twoPow) =
      3 * affineGap n twoPow threePow C +
        twoPow * (n * (twoPowK - 3) - 1) := by
  simp [affineGap, nextC]
  ring

/-- Cross-multiplied normalized recurrence `A' = A + 2^K / 3^{m+1}`.

If `A * 3^m = C` and `C' = 3C + 2^K` with `3^{m+1} = 3 · 3^m`, then
`C' = A * 3^{m+1} + 2^K`. -/
theorem normalizedC_succ
    (A C twoPow threePow C' threePow' : ℤ)
    (hA : A * threePow = C)
    (hC : C' = 3 * C + twoPow)
    (hThree : threePow' = 3 * threePow) :
    C' = A * threePow' + twoPow := by
  calc
    C' = 3 * C + twoPow := hC
    _ = 3 * (A * threePow) + twoPow := by rw [hA]
    _ = A * (3 * threePow) + twoPow := by ring
    _ = A * threePow' + twoPow := by rw [hThree]

/-- A periodic orbit `x = n` forces `n (2^K - 3^p) = C`. -/
theorem periodic_fixed_point
    (twoPow threePow n C x : ℤ)
    (hEndpoint : threePow * n + C = twoPow * x)
    (hx : x = n) :
    n * (twoPow - threePow) = C := by
  have hG := affineGap_eq_twoPow_mul_start_minus_x twoPow threePow n C x hEndpoint
  have hzero : affineGap n twoPow threePow C = 0 := by
    simp [hG, hx]
  simp [affineGap] at hzero
  linear_combination hzero

/-- Expanding prefixes with `C > 0` and `n > 0` have `G < 0`. -/
theorem expanding_gap_neg
    (n twoPow threePow C : ℤ)
    (hn : 0 < n)
    (hC : 0 < C)
    (hExp : twoPow < threePow) :
    affineGap n twoPow threePow C < 0 := by
  have hD : twoPow - threePow < 0 := sub_neg.mpr hExp
  have hterm : (twoPow - threePow) * n < 0 := mul_neg_of_neg_of_pos hD hn
  exact sub_neg_of_lt (lt_trans hterm hC)

/-- On an actual orbit, `G ≥ 0` iff `x ≤ n`, once `2^K > 0`. -/
theorem affineGap_nonneg_iff_x_le_n
    (twoPow threePow n C x : ℤ)
    (hpow : 0 < twoPow)
    (hEndpoint : threePow * n + C = twoPow * x) :
    0 ≤ affineGap n twoPow threePow C ↔ x ≤ n := by
  have hG := affineGap_eq_twoPow_mul_start_minus_x twoPow threePow n C x hEndpoint
  constructor
  · intro h
    have hmul : 0 ≤ twoPow * (n - x) := by simpa [hG] using h
    have hright : 0 ≤ n - x :=
      nonneg_of_mul_nonneg_right (by simpa [mul_comm] using hmul) hpow
    exact sub_nonneg.mp hright
  · intro hx
    have : 0 ≤ n - x := sub_nonneg.mpr hx
    simpa [hG] using mul_nonneg (le_of_lt hpow) this

/-- Expanding + `C > 0` makes the unreduced center numerator and denominator
have opposite signs, so the rational center is negative. -/
theorem expanding_center_opposite_signs
    (C D : ℤ) (hC : 0 < C) (hD : D < 0) : C * D < 0 :=
  mul_neg_of_pos_of_neg hC hD

/-- Equality `2^K = 3^m` is impossible for `m ≥ 1`. -/
theorem two_pow_ne_three_pow {K m : ℕ} (hm : 0 < m) : 2 ^ K ≠ 3 ^ m := by
  intro h
  have hodd : Odd (3 ^ m) := Odd.pow (by decide : Odd (3 : ℕ))
  match K with
  | 0 =>
      have h1 : 3 ^ m = 1 := by simpa using h.symm
      rcases (Nat.pow_eq_one.mp h1) with h3 | hm0
      · cases h3
      · exact hm.ne' hm0
  | K + 1 =>
      have heven : Even (2 ^ (K + 1)) :=
        Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero K⟩
      have hnotodd : ¬ Odd (2 ^ (K + 1)) := Nat.not_odd_iff_even.2 heven
      exact hnotodd (h ▸ hodd)

/-- Positivity `x ≥ 1` is not the same statement as `G ≥ 0`.

Witness: the first accelerated step of `7` is `11`, with `2^K = 2`. -/
theorem positivity_not_eq_gap_nonneg :
    ∃ n x twoPow : ℤ, 0 < twoPow ∧ 1 ≤ x ∧ ¬ 0 ≤ twoPow * (n - x) := by
  refine ⟨7, 11, 2, ?_⟩
  decide

/-- Cylinder stabilization: once the modulus exceeds the fixed start, the
unique residue in `[0, 2^{K+1})` is the start itself. -/
theorem unique_residue_of_small_start
    (n modulus R : ℕ)
    (hmod : n % modulus = R % modulus)
    (hR : R < modulus)
    (hn : n < modulus) :
    n = R := by
  have hnR : n % modulus = n := Nat.mod_eq_of_lt hn
  have hRR : R % modulus = R := Nat.mod_eq_of_lt hR
  exact hnR.symm.trans (hmod.trans hRR)

end Problems.Collatz
