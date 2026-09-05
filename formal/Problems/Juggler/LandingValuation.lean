import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Problems.Juggler.SequentialMordell
import Problems.Juggler.Residuals

namespace Problems.Juggler

/-!
# 2-adic landing remainder

On an odd-to-odd step, `y³ = T(y)² + ρ` with both `y` and `T(y)`
odd, so `ρ ≡ y - 1 (mod 8)`. That congruence is the entire
2-adic classification:

* `y ≡ 3,7 (mod 8)` forces `v₂(ρ) = 1`
* `y ≡ 5 (mod 8)` forces `v₂(ρ) = 2`
* `y ≡ 1 (mod 8)` and `ρ ≠ 0` forces `v₂(ρ) ≥ 3`

The floor `T(y) = ⌊y^{3/2}⌋` is not used beyond selecting an odd
landing. The same congruences hold for any odd square below `y³`.
They do not become stronger at a persistent-expanding endpoint,
and `y ≡ 1 (mod 16)` does not force `v₂ ≥ 4`.

This file does not claim that every start reaches `1`.
-/

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def landingRemainder (y : ℕ) : ℕ :=
  localDefectOdd y

abbrev oddOddLanding (y : ℕ) : Prop :=
  y % 2 = 1 ∧ floorPower y % 2 = 1

def landingValuation (y : ℕ) : ℕ :=
  padicValNat 2 (landingRemainder y)

theorem odd_cube_mod_eight {y : ℕ} (h : y % 2 = 1) :
    y ^ 3 % 8 = y % 8 := by
  have hsq : y ^ 2 % 8 = 1 := odd_sq_mod_eight h
  have hcube : y ^ 3 = y * y ^ 2 := by ring
  rw [hcube, Nat.mul_mod, hsq, Nat.mul_one, Nat.mod_mod]

theorem odd_cube_minus_odd_square_mod_eight {y z : ℕ}
    (hy : y % 2 = 1) (hz : z % 2 = 1) (hle : z ^ 2 ≤ y ^ 3) :
    (y ^ 3 - z ^ 2) % 8 = (y - 1) % 8 := by
  have hy3 : y ^ 3 % 8 = y % 8 := odd_cube_mod_eight hy
  have hz2 : z ^ 2 % 8 = 1 := odd_sq_mod_eight hz
  have hsum : z ^ 2 + (y ^ 3 - z ^ 2) = y ^ 3 := Nat.add_sub_of_le hle
  have hmod :
      (z ^ 2 + (y ^ 3 - z ^ 2)) % 8 = y ^ 3 % 8 := by rw [hsum]
  rw [Nat.add_mod, hz2, hy3] at hmod
  have : 1 ≤ y := by omega
  omega

theorem odd_odd_remainder_mod_eight {y : ℕ} (h : oddOddLanding y) :
    landingRemainder y % 8 = (y - 1) % 8 := by
  rcases h with ⟨hodd, hT⟩
  have hle := floorPower_odd_sq_le_cube hodd
  simpa [landingRemainder, localDefectOdd] using
    odd_cube_minus_odd_square_mod_eight hodd hT hle

theorem odd_odd_remainder_even {y : ℕ} (h : oddOddLanding y) :
    landingRemainder y % 2 = 0 := by
  have heq : floorPower y ^ 2 + landingRemainder y = y ^ 3 :=
    localDefectOdd_add h.1
  have hy3 : y ^ 3 % 2 = 1 := by simp [Nat.pow_mod, h.1]
  have hz2 : floorPower y ^ 2 % 2 = 1 := by simp [Nat.pow_mod, h.2]
  omega

theorem landing_remainder_mod_eight_cases {y : ℕ}
    (h : oddOddLanding y) :
    y % 8 = 1 ∧ landingRemainder y % 8 = 0 ∨
      y % 8 = 3 ∧ landingRemainder y % 8 = 2 ∨
        y % 8 = 5 ∧ landingRemainder y % 8 = 4 ∨
          y % 8 = 7 ∧ landingRemainder y % 8 = 6 := by
  have hρ := odd_odd_remainder_mod_eight h
  have : y % 8 = 1 ∨ y % 8 = 3 ∨ y % 8 = 5 ∨ y % 8 = 7 := by
    have := h.1
    omega
  omega

theorem le_padicValNat_two_of_pow_dvd {n k : ℕ}
    (hn : n ≠ 0) (h : 2 ^ k ∣ n) :
    k ≤ padicValNat 2 n := by
  by_contra hlt
  have hk : padicValNat 2 n + 1 ≤ k := by omega
  have : 2 ^ (padicValNat 2 n + 1) ∣ n :=
    dvd_trans (pow_dvd_pow (2 : ℕ) hk) h
  exact pow_succ_padicValNat_not_dvd hn this

theorem padicValNat_two_eq_one_of_mod_eight
    {n : ℕ} (h : n % 8 = 2 ∨ n % 8 = 6) :
    padicValNat 2 n = 1 := by
  have hn : n ≠ 0 := by omega
  have h2 : 2 ∣ n := by omega
  have h4 : ¬(4 ∣ n) := by omega
  have hge : 1 ≤ padicValNat 2 n := one_le_padicValNat_of_dvd hn h2
  have hle : padicValNat 2 n ≤ 1 := by
    by_contra hlt
    have htwo : 2 ≤ padicValNat 2 n := by omega
    have : 2 ^ 2 ∣ n :=
      dvd_trans (pow_dvd_pow (2 : ℕ) htwo) pow_padicValNat_dvd
    exact h4 this
  omega

theorem padicValNat_two_eq_two_of_mod_eight_four
    {n : ℕ} (h : n % 8 = 4) :
    padicValNat 2 n = 2 := by
  have hn : n ≠ 0 := by omega
  have h4 : 4 ∣ n := by omega
  have h8 : ¬(8 ∣ n) := by omega
  have hge : 2 ≤ padicValNat 2 n :=
    le_padicValNat_two_of_pow_dvd hn (by simpa using h4)
  have hle : padicValNat 2 n ≤ 2 := by
    by_contra hlt
    have hthree : 3 ≤ padicValNat 2 n := by omega
    have : 2 ^ 3 ∣ n :=
      dvd_trans (pow_dvd_pow (2 : ℕ) hthree) pow_padicValNat_dvd
    exact h8 this
  omega

theorem padicValNat_two_ge_three_of_mod_eight_zero
    {n : ℕ} (hn : n ≠ 0) (h : n % 8 = 0) :
    3 ≤ padicValNat 2 n :=
  le_padicValNat_two_of_pow_dvd hn (by omega)

theorem landing_valuation_three_or_seven {y : ℕ}
    (h : oddOddLanding y) (hy : y % 8 = 3 ∨ y % 8 = 7) :
    landingValuation y = 1 := by
  have hcases := landing_remainder_mod_eight_cases h
  have hρ : landingRemainder y % 8 = 2 ∨ landingRemainder y % 8 = 6 := by
    omega
  simpa [landingValuation] using
    padicValNat_two_eq_one_of_mod_eight hρ

theorem landing_valuation_five {y : ℕ}
    (h : oddOddLanding y) (hy : y % 8 = 5) :
    landingValuation y = 2 := by
  have hcases := landing_remainder_mod_eight_cases h
  have hρ : landingRemainder y % 8 = 4 := by omega
  simpa [landingValuation] using
    padicValNat_two_eq_two_of_mod_eight_four hρ

theorem landing_valuation_one {y : ℕ}
    (h : oddOddLanding y) (hy : y % 8 = 1)
    (hρ : landingRemainder y ≠ 0) :
    3 ≤ landingValuation y := by
  have hcases := landing_remainder_mod_eight_cases h
  have h8 : landingRemainder y % 8 = 0 := by omega
  simpa [landingValuation] using
    padicValNat_two_ge_three_of_mod_eight_zero hρ h8

/-- Exact 2-adic classification of a realized odd-odd remainder. -/
theorem landing_valuation_classification {y : ℕ}
    (h : oddOddLanding y) (hρ : landingRemainder y ≠ 0) :
    (y % 8 = 3 ∨ y % 8 = 7) ∧ landingValuation y = 1 ∨
      y % 8 = 5 ∧ landingValuation y = 2 ∨
        y % 8 = 1 ∧ 3 ≤ landingValuation y := by
  have hcases := landing_remainder_mod_eight_cases h
  rcases hcases with h1 | h3 | h5 | h7
  · exact Or.inr (Or.inr ⟨h1.1, landing_valuation_one h h1.1 hρ⟩)
  · exact Or.inl ⟨Or.inl h3.1, landing_valuation_three_or_seven h (Or.inl h3.1)⟩
  · exact Or.inr (Or.inl ⟨h5.1, landing_valuation_five h h5.1⟩)
  · exact Or.inl ⟨Or.inr h7.1, landing_valuation_three_or_seven h (Or.inr h7.1)⟩

/-- `y ≡ 1 (mod 16)` does not force `v₂ ≥ 4`. -/
theorem landing_valuation_33 :
    oddOddLanding 33 ∧ (33 : ℕ) % 16 = 1 ∧ landingValuation 33 = 3 := by
  decide +kernel

/-- A PE endpoint can have valuation 1. History does not force `v₂ ≥ 2`. -/
theorem pe_endpoint_763_valuation :
    PersistentExpandingResidual 365 763 ∧ landingValuation 763 = 1 := by
  refine ⟨two_block_ooe_365.1, ?_⟩
  have h : oddOddLanding 763 := by decide +kernel
  have h8 : (763 : ℕ) % 8 = 3 := by decide
  exact landing_valuation_three_or_seven h (Or.inl h8)

end Problems.Juggler
