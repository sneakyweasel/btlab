import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Linarith

/-!
Cubic difference and 3-adic valuation of a balanced-Monna endpoint pair.

For `u = ζ + 2·3ⁿ` and `v = ζ - 2·3ⁿ` one has the ring identity

  `u³ − v³ = 4·3ⁿ (3ζ² + 4·3^{2n})`

and therefore `t = v₃(u³ − v³) = n + min(1 + 2 v₃(ζ), 2n)`, or `t = 3n`
when `ζ = 0`. The two arguments of the minimum have opposite parity
whenever `ζ ≠ 0`, so there is never a cancellation tie.

The same factor is never `±3^k`, so `u³ − v³` is never `±4·3^k`. That is
the arithmetic obstruction of `BTM-x3-no-preserve`: an endpoint collision
of `B` requires difference `±4·3^k`, and `B` itself is not defined here.

This is not a Collatz claim and not an `M_k(x³)` count. The spectrum row
stays human.
-/

namespace BTCalculus

instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- First endpoint value `u = ζ + 2·3ⁿ`. -/
def monnaEndpointU (n : ℕ) (ζ : ℚ) : ℚ :=
  ζ + 2 * (3 : ℚ) ^ n

/-- Second endpoint value `v = ζ - 2·3ⁿ`. -/
def monnaEndpointV (n : ℕ) (ζ : ℚ) : ℚ :=
  ζ - 2 * (3 : ℚ) ^ n

/-- Ring identity of `BTM-x3-depth`. -/
theorem monnaEndpoint_cube_diff (n : ℕ) (ζ : ℚ) :
    monnaEndpointU n ζ ^ 3 - monnaEndpointV n ζ ^ 3
      = 4 * (3 : ℚ) ^ n * (3 * ζ ^ 2 + 4 * (3 : ℚ) ^ (2 * n)) := by
  unfold monnaEndpointU monnaEndpointV
  ring

/-- Integer form of the same identity. -/
theorem monnaEndpoint_cube_diff_int (n : ℕ) (ζ : ℤ) :
    (ζ + 2 * (3 : ℤ) ^ n) ^ 3 - (ζ - 2 * (3 : ℤ) ^ n) ^ 3
      = 4 * (3 : ℤ) ^ n * (3 * ζ ^ 2 + 4 * (3 : ℤ) ^ (2 * n)) := by
  ring

lemma padicValRat_three : padicValRat 3 (3 : ℚ) = 1 :=
  padicValRat.self (by decide : 1 < 3)

lemma padicValRat_four : padicValRat 3 (4 : ℚ) = 0 := by
  rw [show (4 : ℚ) = ((4 : ℤ) : ℚ) by norm_cast, padicValRat.of_int]
  exact_mod_cast padicValInt.eq_zero_of_not_dvd (by decide : ¬(3 : ℤ) ∣ 4)

lemma padicValRat_sixteen : padicValRat 3 (16 : ℚ) = 0 := by
  rw [show (16 : ℚ) = ((16 : ℤ) : ℚ) by norm_cast, padicValRat.of_int]
  exact_mod_cast padicValInt.eq_zero_of_not_dvd (by decide : ¬(3 : ℤ) ∣ 16)

lemma three_pow_ne_zero (n : ℕ) : (3 : ℚ) ^ n ≠ 0 :=
  pow_ne_zero n (by decide)

lemma padicValRat_three_pow (n : ℕ) : padicValRat 3 ((3 : ℚ) ^ n) = n := by
  rw [padicValRat.pow, padicValRat_three, mul_one]

lemma padicValRat_three_zeta_sq {ζ : ℚ} (hζ : ζ ≠ 0) :
    padicValRat 3 (3 * ζ ^ 2) = 1 + 2 * padicValRat 3 ζ := by
  have h3 : (3 : ℚ) ≠ 0 := by decide
  have hsq : ζ ^ 2 ≠ 0 := pow_ne_zero 2 hζ
  rw [padicValRat.mul h3 hsq, padicValRat.pow, padicValRat_three]
  ring

lemma padicValRat_four_three_pow (n : ℕ) :
    padicValRat 3 (4 * (3 : ℚ) ^ (2 * n)) = 2 * n := by
  have h4 : (4 : ℚ) ≠ 0 := by decide
  have h3 : (3 : ℚ) ^ (2 * n) ≠ 0 := three_pow_ne_zero _
  rw [padicValRat.mul h4 h3, padicValRat_four, padicValRat_three_pow, zero_add]
  norm_cast

lemma odd_one_add_two_mul (k : ℤ) : Odd (1 + 2 * k) :=
  ⟨k, by ring⟩

lemma even_two_mul_int (k : ℤ) : Even (2 * k) :=
  even_two_mul k

lemma odd_ne_even {a b : ℤ} (ha : Odd a) (hb : Even b) : a ≠ b := by
  rintro rfl
  exact (Int.not_even_iff_odd.mpr ha) hb

/-- The two arguments of the depth minimum have opposite parity when `ζ ≠ 0`. -/
theorem monnaEndpoint_val_parity (n : ℕ) {ζ : ℚ} (_hζ : ζ ≠ 0) :
    Odd (1 + 2 * padicValRat 3 ζ) ∧ Even (2 * (n : ℤ)) :=
  ⟨odd_one_add_two_mul _, even_two_mul_int _⟩

lemma monnaEndpoint_factor_ne {n : ℕ} {ζ : ℚ} (hζ : ζ ≠ 0) :
    3 * ζ ^ 2 + 4 * (3 : ℚ) ^ (2 * n) ≠ 0 := by
  intro h
  have hneg : 3 * ζ ^ 2 = -(4 * (3 : ℚ) ^ (2 * n)) :=
    add_eq_zero_iff_eq_neg.mp h
  have hval :
      padicValRat 3 (3 * ζ ^ 2) = padicValRat 3 (4 * (3 : ℚ) ^ (2 * n)) := by
    rw [hneg, padicValRat.neg]
  have hodd : Odd (padicValRat 3 (3 * ζ ^ 2)) := by
    rw [padicValRat_three_zeta_sq hζ]
    exact odd_one_add_two_mul _
  have heven : Even (padicValRat 3 (4 * (3 : ℚ) ^ (2 * n))) := by
    rw [padicValRat_four_three_pow]
    exact even_two_mul_int _
  exact odd_ne_even hodd heven hval

lemma monnaEndpoint_factor_val {n : ℕ} {ζ : ℚ} (hζ : ζ ≠ 0) :
    padicValRat 3 (3 * ζ ^ 2 + 4 * (3 : ℚ) ^ (2 * n))
      = min (1 + 2 * padicValRat 3 ζ) (2 * (n : ℤ)) := by
  have hL : 3 * ζ ^ 2 ≠ 0 :=
    mul_ne_zero (by decide) (pow_ne_zero 2 hζ)
  have hR : 4 * (3 : ℚ) ^ (2 * n) ≠ 0 :=
    mul_ne_zero (by decide) (three_pow_ne_zero _)
  have hsum := monnaEndpoint_factor_ne (n := n) hζ
  have hneq :
      padicValRat 3 (3 * ζ ^ 2) ≠ padicValRat 3 (4 * (3 : ℚ) ^ (2 * n)) := by
    rw [padicValRat_three_zeta_sq hζ, padicValRat_four_three_pow]
    exact odd_ne_even (odd_one_add_two_mul _) (even_two_mul_int _)
  rw [padicValRat.add_eq_min hsum hL hR hneq, padicValRat_three_zeta_sq hζ,
    padicValRat_four_three_pow]

/-- Valuation law of `BTM-x3-depth` for nonzero midpoint. -/
theorem monnaEndpoint_cube_val_of_ne (n : ℕ) {ζ : ℚ} (hζ : ζ ≠ 0) :
    padicValRat 3 (monnaEndpointU n ζ ^ 3 - monnaEndpointV n ζ ^ 3)
      = n + min (1 + 2 * padicValRat 3 ζ) (2 * (n : ℤ)) := by
  rw [monnaEndpoint_cube_diff]
  have h4 : (4 : ℚ) ≠ 0 := by decide
  have h3 : (3 : ℚ) ^ n ≠ 0 := three_pow_ne_zero n
  have hf := monnaEndpoint_factor_ne (n := n) hζ
  have h43 : 4 * (3 : ℚ) ^ n ≠ 0 := mul_ne_zero h4 h3
  rw [padicValRat.mul h43 hf, padicValRat.mul h4 h3, padicValRat_four,
    padicValRat_three_pow, monnaEndpoint_factor_val hζ, zero_add]

/-- Valuation law of `BTM-x3-depth` at the zero midpoint: `t = 3n`. -/
theorem monnaEndpoint_cube_val_zero (n : ℕ) :
    padicValRat 3 (monnaEndpointU n 0 ^ 3 - monnaEndpointV n 0 ^ 3) = 3 * n := by
  rw [monnaEndpoint_cube_diff]
  simp
  have hform :
      (4 : ℚ) * (3 : ℚ) ^ n * (4 * (3 : ℚ) ^ (2 * n))
        = 16 * (3 : ℚ) ^ (3 * n) := by
    calc
      (4 : ℚ) * (3 : ℚ) ^ n * (4 * (3 : ℚ) ^ (2 * n))
          = (4 * 4) * ((3 : ℚ) ^ n * (3 : ℚ) ^ (2 * n)) := by ring
      _ = 16 * (3 : ℚ) ^ (n + 2 * n) := by
        rw [← pow_add]
        norm_num
      _ = 16 * (3 : ℚ) ^ (3 * n) := by
        rw [show n + 2 * n = 3 * n by omega]
  rw [hform]
  have h16 : (16 : ℚ) ≠ 0 := by decide
  have h3 : (3 : ℚ) ^ (3 * n) ≠ 0 := three_pow_ne_zero _
  rw [padicValRat.mul h16 h3, padicValRat_sixteen, padicValRat_three_pow, zero_add]
  norm_cast

/-- Combined 3-adic valuation law of `BTM-x3-depth`. -/
theorem monnaEndpoint_cube_val (n : ℕ) (ζ : ℚ) :
    padicValRat 3 (monnaEndpointU n ζ ^ 3 - monnaEndpointV n ζ ^ 3)
      = if ζ = 0 then 3 * (n : ℤ)
        else (n : ℤ) + min (1 + 2 * padicValRat 3 ζ) (2 * (n : ℤ)) := by
  by_cases hζ : ζ = 0
  · subst hζ
    simpa using monnaEndpoint_cube_val_zero n
  · rw [if_neg hζ, monnaEndpoint_cube_val_of_ne n hζ]

/-! ## Non-preservation (`BTM-x3-no-preserve`) -/

lemma three_pow_pos (n : ℕ) : (0 : ℚ) < (3 : ℚ) ^ n :=
  pow_pos (by norm_num) n

lemma monnaEndpoint_factor_nonneg_sq (ζ : ℚ) : (0 : ℚ) ≤ 3 * ζ ^ 2 :=
  mul_nonneg (by norm_num) (sq_nonneg ζ)

/-- The cubic factor is strictly positive, hence never `-3^k`. -/
theorem monnaEndpoint_factor_pos (n : ℕ) (ζ : ℚ) :
    0 < 3 * ζ ^ 2 + 4 * (3 : ℚ) ^ (2 * n) := by
  have h4 : (0 : ℚ) < 4 * (3 : ℚ) ^ (2 * n) :=
    mul_pos (by norm_num) (three_pow_pos _)
  linarith [monnaEndpoint_factor_nonneg_sq ζ]

theorem monnaEndpoint_factor_ne_neg_three_pow (n k : ℕ) (ζ : ℚ) :
    3 * ζ ^ 2 + 4 * (3 : ℚ) ^ (2 * n) ≠ -((3 : ℚ) ^ k) := by
  intro h
  have hpos := monnaEndpoint_factor_pos n ζ
  have hneg : -((3 : ℚ) ^ k) < 0 := neg_neg_of_pos (three_pow_pos k)
  linarith

/-- The cubic factor is never a nonnegative power of three. -/
theorem monnaEndpoint_factor_ne_three_pow (n k : ℕ) (ζ : ℚ) :
    3 * ζ ^ 2 + 4 * (3 : ℚ) ^ (2 * n) ≠ (3 : ℚ) ^ k := by
  intro h
  by_cases hζ : ζ = 0
  · subst hζ
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add] at h
    have hval :
        padicValRat 3 (4 * (3 : ℚ) ^ (2 * n)) = padicValRat 3 ((3 : ℚ) ^ k) := by
      rw [h]
    rw [padicValRat_four_three_pow, padicValRat_three_pow] at hval
    have hk : k = 2 * n := by exact_mod_cast hval.symm
    subst hk
    have h3 : (3 : ℚ) ^ (2 * n) ≠ 0 := three_pow_ne_zero _
    have hx :
        (4 : ℚ) * (3 : ℚ) ^ (2 * n) = (1 : ℚ) * (3 : ℚ) ^ (2 * n) := by
      rw [one_mul]
      exact h
    have h4 : (4 : ℚ) = 1 := mul_right_cancel₀ h3 hx
    norm_num at h4
  · have hval :
        padicValRat 3 (3 * ζ ^ 2 + 4 * (3 : ℚ) ^ (2 * n))
          = padicValRat 3 ((3 : ℚ) ^ k) := by
      rw [h]
    rw [monnaEndpoint_factor_val hζ, padicValRat_three_pow] at hval
    set s := padicValRat 3 ζ
    rcases lt_trichotomy (1 + 2 * s) (2 * (n : ℤ)) with hlt | heq | hgt
    · have hmin : min (1 + 2 * s) (2 * (n : ℤ)) = 1 + 2 * s :=
        min_eq_left (le_of_lt hlt)
      have hkn : k < 2 * n := by
        have : (k : ℤ) < 2 * (n : ℤ) := by
          rw [← hval, hmin]
          exact hlt
        exact_mod_cast this
      have hζsq : 3 * ζ ^ 2 = (3 : ℚ) ^ k - 4 * (3 : ℚ) ^ (2 * n) := by
        linarith
      have hpowlt : (3 : ℚ) ^ k < 4 * (3 : ℚ) ^ (2 * n) := by
        have hlt3 : (3 : ℚ) ^ k < (3 : ℚ) ^ (2 * n) :=
          pow_lt_pow_right₀ (by norm_num : (1 : ℚ) < 3) hkn
        have hle4 : (3 : ℚ) ^ (2 * n) ≤ 4 * (3 : ℚ) ^ (2 * n) := by
          nlinarith [three_pow_pos (2 * n)]
        linarith
      have hneg : 3 * ζ ^ 2 < 0 := by linarith
      exact (not_lt.mpr (monnaEndpoint_factor_nonneg_sq ζ)) hneg
    · exact odd_ne_even (odd_one_add_two_mul s) (even_two_mul_int (n : ℤ)) heq
    · have hmin : min (1 + 2 * s) (2 * (n : ℤ)) = 2 * (n : ℤ) :=
        min_eq_right (le_of_lt hgt)
      have hk : k = 2 * n := by
        have : (k : ℤ) = 2 * (n : ℤ) := by
          rw [← hval, hmin]
        exact_mod_cast this
      subst hk
      have hζsq : 3 * ζ ^ 2 = (3 : ℚ) ^ (2 * n) - 4 * (3 : ℚ) ^ (2 * n) := by
        linarith
      have hneg : 3 * ζ ^ 2 = -3 * (3 : ℚ) ^ (2 * n) := by
        linarith
      have hlt0 : 3 * ζ ^ 2 < 0 := by
        nlinarith [three_pow_pos (2 * n)]
      exact (not_lt.mpr (monnaEndpoint_factor_nonneg_sq ζ)) hlt0

/-- Arithmetic core of `BTM-x3-no-preserve`: the factor is never `±3^k`. -/
theorem monnaEndpoint_factor_ne_pm_three_pow (n k : ℕ) (ζ : ℚ) :
    3 * ζ ^ 2 + 4 * (3 : ℚ) ^ (2 * n) ≠ (3 : ℚ) ^ k ∧
      3 * ζ ^ 2 + 4 * (3 : ℚ) ^ (2 * n) ≠ -((3 : ℚ) ^ k) :=
  ⟨monnaEndpoint_factor_ne_three_pow n k ζ,
    monnaEndpoint_factor_ne_neg_three_pow n k ζ⟩

lemma monnaEndpoint_cube_diff_pos (n : ℕ) (ζ : ℚ) :
    0 < monnaEndpointU n ζ ^ 3 - monnaEndpointV n ζ ^ 3 := by
  rw [monnaEndpoint_cube_diff]
  have hf := monnaEndpoint_factor_pos n ζ
  have h3 := three_pow_pos n
  nlinarith

/-- Cubing an endpoint pair never produces difference `-4·3^k`. -/
theorem monnaEndpoint_cube_diff_ne_neg_four_three_pow (n k : ℕ) (ζ : ℚ) :
    monnaEndpointU n ζ ^ 3 - monnaEndpointV n ζ ^ 3 ≠ -(4 * (3 : ℚ) ^ k) := by
  intro h
  have hpos := monnaEndpoint_cube_diff_pos n ζ
  have h4 : (0 : ℚ) < 4 * (3 : ℚ) ^ k := mul_pos (by norm_num) (three_pow_pos k)
  linarith

/-- Cubing an endpoint pair never produces difference `4·3^k`. -/
theorem monnaEndpoint_cube_diff_ne_four_three_pow (n k : ℕ) (ζ : ℚ) :
    monnaEndpointU n ζ ^ 3 - monnaEndpointV n ζ ^ 3 ≠ 4 * (3 : ℚ) ^ k := by
  intro h
  rw [monnaEndpoint_cube_diff] at h
  have h4 : (4 : ℚ) ≠ 0 := by decide
  have hcancel :
      (3 : ℚ) ^ n * (3 * ζ ^ 2 + 4 * (3 : ℚ) ^ (2 * n)) = (3 : ℚ) ^ k :=
    mul_left_cancel₀ h4 (by linarith)
  by_cases hnk : n ≤ k
  · have hpow :
        (3 : ℚ) ^ n * (3 : ℚ) ^ (k - n) = (3 : ℚ) ^ k := by
      rw [← pow_add, Nat.add_sub_cancel' hnk]
    have hf :
        3 * ζ ^ 2 + 4 * (3 : ℚ) ^ (2 * n) = (3 : ℚ) ^ (k - n) :=
      mul_left_cancel₀ (three_pow_ne_zero n) (hcancel.trans hpow.symm)
    exact monnaEndpoint_factor_ne_three_pow n (k - n) ζ hf
  · have hkn : k < n := Nat.lt_of_not_ge hnk
    have hf :
        3 * ζ ^ 2 + 4 * (3 : ℚ) ^ (2 * n) = (3 : ℚ) ^ k / (3 : ℚ) ^ n :=
      (eq_div_iff (three_pow_ne_zero n)).2 (by linarith [hcancel])
    have hsmall : (3 : ℚ) ^ k / (3 : ℚ) ^ n < 1 := by
      rw [div_lt_one (three_pow_pos n)]
      exact pow_lt_pow_right₀ (by norm_num : (1 : ℚ) < 3) hkn
    have hge4 : (4 : ℚ) ≤ 3 * ζ ^ 2 + 4 * (3 : ℚ) ^ (2 * n) := by
      have hpow1 : (1 : ℚ) ≤ (3 : ℚ) ^ (2 * n) :=
        one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 3)
      nlinarith [monnaEndpoint_factor_nonneg_sq ζ]
    linarith

/-- Arithmetic obstruction of `BTM-x3-no-preserve`: `u³−v³` is never `±4·3^k`.

Endpoint collisions of the balanced Monna map are pairs whose difference is
`±4·3^k` (with the named tails). The difference obstruction is therefore
enough for non-preservation; `B` is not defined in this module. -/
theorem monnaEndpoint_cube_diff_ne_pm_four_three_pow (n k : ℕ) (ζ : ℚ) :
    monnaEndpointU n ζ ^ 3 - monnaEndpointV n ζ ^ 3 ≠ 4 * (3 : ℚ) ^ k ∧
      monnaEndpointU n ζ ^ 3 - monnaEndpointV n ζ ^ 3 ≠ -(4 * (3 : ℚ) ^ k) :=
  ⟨monnaEndpoint_cube_diff_ne_four_three_pow n k ζ,
    monnaEndpoint_cube_diff_ne_neg_four_three_pow n k ζ⟩

end BTCalculus
