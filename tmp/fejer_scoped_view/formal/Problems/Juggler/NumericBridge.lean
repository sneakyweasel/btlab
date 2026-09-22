import Problems.Juggler.RootCells
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact numeric bridges for root-cell and height arguments

Signed-to-natural conversions retain their nonnegativity hypotheses, and
natural subtraction is cast only after its order condition is established.
-/

namespace Problems.Juggler.NumericBridge

/-- A nonnegative integer power cell transports to natural numbers. -/
theorem int_toNat_pow_cell {a z : ℤ} {p q : ℕ}
    (ha : 0 ≤ a) (hz : 0 ≤ z)
    (hlo : z ^ p ≤ a ^ q) (hhi : a ^ q < (z + 1) ^ p) :
    z.toNat ^ p ≤ a.toNat ^ q ∧ a.toNat ^ q < (z.toNat + 1) ^ p := by
  have haN : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha
  have hzN : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz
  have hloZ : (z.toNat : ℤ) ^ p ≤ (a.toNat : ℤ) ^ q := by
    simpa only [haN, hzN] using hlo
  have hhiZ : (a.toNat : ℤ) ^ q < ((z.toNat : ℤ) + 1) ^ p := by
    simpa only [haN, hzN] using hhi
  exact ⟨by exact_mod_cast hloZ, by exact_mod_cast hhiZ⟩

/-- A strict affine bound contracts any real gap at least two. -/
theorem affine_gap_lt {d g k B : ℝ} (hd : 2 ≤ d)
    (hk : k ≤ 1) (hB : 2 * k + B ≤ 2) (h : g < k * d + B) :
    g < d := by
  have hprod := mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hd)
  nlinarith

/-- Clear a positive natural scale and rational exponent in a height strip. -/
theorem power_strip_of_real_strip {m M a b q : ℕ}
    (hm : 0 < m) (hb : 0 < b) (hq : 0 < q)
    (h : (M : ℝ) < (m : ℝ) ^ 3 - (1 / (q : ℝ)) * (m : ℝ) ^ ((a : ℝ) / b)) :
    m ^ a < (q * (m ^ 3 - M)) ^ b := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hp0 := Real.rpow_pos_of_pos hmR ((a : ℝ) / b)
  have hM : M < m ^ 3 := by
    have hterm : 0 < (1 / (q : ℝ)) * (m : ℝ) ^ ((a : ℝ) / b) := by positivity
    exact_mod_cast (show (M : ℝ) < (m : ℝ) ^ 3 by linarith)
  have hh : (m : ℝ) ^ ((a : ℝ) / b) / q < (m : ℝ) ^ 3 - M := by
    rw [div_eq_mul_inv]
    simpa only [one_div, mul_comm] using (show
      (1 / (q : ℝ)) * (m : ℝ) ^ ((a : ℝ) / b) < (m : ℝ) ^ 3 - M by linarith)
  have hd : (m : ℝ) ^ ((a : ℝ) / b) < (q * (m ^ 3 - M) : ℕ) := by
    rw [Nat.cast_mul, Nat.cast_sub hM.le, Nat.cast_pow]
    simpa only [mul_comm] using (div_lt_iff₀ hqR).mp hh
  have hp := pow_lt_pow_left₀ hd hp0.le (by omega : b ≠ 0)
  have he : ((m : ℝ) ^ ((a : ℝ) / b)) ^ b = (m : ℝ) ^ a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmR.le]
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
    rw [div_mul_cancel₀ _ hbR, Real.rpow_natCast]
  rw [he] at hp
  exact_mod_cast hp

end Problems.Juggler.NumericBridge
