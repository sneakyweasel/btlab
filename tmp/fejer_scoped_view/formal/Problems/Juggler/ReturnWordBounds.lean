import Problems.Juggler.ReturnWordData

namespace Problems.Juggler.ReturnWordBounds

open ReturnWordLoss


def cShifts : List ℕ := [8, 13, 3, 10, 15, 6, 12, 0]

def wShifts : List ℕ := [43, 71, 15, 53, 78, 28, 61, 83, 39, 68, 9, 49, 75, 22, 57, 81, 34, 65, 3, 44, 72, 17, 54, 78, 29, 62, 84, 40, 69, 11, 50, 76, 24, 58, 81, 35, 66, 4, 45, 73, 18, 55, 79, 30, 63, 84, 41, 70, 12, 51, 76, 25, 59, 82, 36, 67, 6, 47, 74, 20, 56, 80, 32, 64, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem c_certificate : DyadicCertificate 24 wordC cShifts := by
  norm_num [cShifts, wordC, wordA, wordB, DyadicCertificate, exponent, alpha, branchExp]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem w_certificate : DyadicCertificate 128 wordW wShifts := by
  norm_num [wShifts, wordW, wordD, wordC, wordA, wordB,
    DyadicCertificate, exponent, alpha, branchExp]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem c_dyadic_sum : dyadicSum wordC cShifts = 1 + (63121 : ℝ) / 524288 := by
  norm_num [dyadicSum, cShifts, wordC, wordA, wordB, exponent, alpha, branchExp]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem w_dyadic_sum : dyadicSum wordW wShifts =
    1 + (277910493483851358096413315698577150111783 : ℝ) / 2 ^ 140 := by
  norm_num [dyadicSum, wShifts, wordW, wordD, wordC, wordA, wordB,
    exponent, alpha, branchExp]

theorem c_budget_lt {m : ℝ} (hm : (2 : ℝ) ^ 24 ≤ m) : budget m wordC < 9 / 8 := by
  have hh := budget_le_dyadic hm wordC cShifts c_tails c_certificate
  rw [c_dyadic_sum] at hh
  linarith

theorem w_budget_lt {m : ℝ} (hm : (2 : ℝ) ^ 128 ≤ m) : budget m wordW < 6 / 5 := by
  have hh := budget_le_dyadic hm wordW wShifts w_tails w_certificate
  rw [w_dyadic_sum] at hh
  norm_num at hh
  linarith

theorem c_loss {x : ℕ} (hx : 2 ^ 24 ≤ x) :
    0 ≤ (x : ℝ) ^ ((243 : ℝ) / 256) - eval wordC x ∧
      (x : ℝ) ^ ((243 : ℝ) / 256) - eval wordC x < 9 / 8 := by
  simpa only [exponent_C] using loss_of_budget
    (m := (x : ℝ)) (by exact_mod_cast (show 0 < x by omega))
    (by decide : wordC ≠ []) (by omega : 0 < x) c_tails
    (c_innerAbove (by omega)) (c_budget_lt (by exact_mod_cast hx)).le

theorem w_loss {x : ℕ} (hx : 2 ^ 128 ≤ x) :
    0 ≤ (x : ℝ) ^ ((3 : ℝ) ^ 41 / 2 ^ 65) - eval wordW x ∧
      (x : ℝ) ^ ((3 : ℝ) ^ 41 / 2 ^ 65) - eval wordW x < 6 / 5 := by
  simpa only [exponent_W] using loss_of_budget
    (m := (x : ℝ)) (by exact_mod_cast (show 0 < x by omega))
    (by decide : wordW ≠ []) (by omega : 0 < x) w_tails
    (w_innerAbove (by omega)) (w_budget_lt (by exact_mod_cast hx)).le

theorem c_slope_lt {m : ℝ} (hm : (2 : ℝ) ^ 24 ≤ m) :
    (243 : ℝ) / 256 * m ^ ((-13 : ℝ) / 256) < 27 / 64 := by
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  have hpow := dyadic_rpow_lower (q := (13 : ℝ) / 256) (c := (9 : ℝ) / 4)
    (a := 6) (b := 5) hm (by norm_num) (by norm_num) (by norm_num)
  have hp0 : 0 < m ^ ((13 : ℝ) / 256) := Real.rpow_pos_of_pos hm0 _
  have he : m ^ ((-13 : ℝ) / 256) = (m ^ ((13 : ℝ) / 256))⁻¹ := by
    rw [show (-13 : ℝ) / 256 = -(13 / 256) by ring, Real.rpow_neg hm0.le]
  rw [he, ← div_eq_mul_inv]
  apply (div_lt_iff₀ hp0).mpr
  nlinarith only [hpow]

theorem c_slope_large_lt {m : ℝ} (hm : (2 : ℝ) ^ 128 ≤ m) :
    (243 : ℝ) / 256 * m ^ ((-13 : ℝ) / 256) < 1 / 64 := by
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  have hpow := dyadic_rpow_lower (q := (13 : ℝ) / 256) (c := (64 : ℝ))
    (a := 13) (b := 2) hm (by norm_num) (by norm_num) (by norm_num)
  have hp0 : 0 < m ^ ((13 : ℝ) / 256) := Real.rpow_pos_of_pos hm0 _
  have he : m ^ ((-13 : ℝ) / 256) = (m ^ ((13 : ℝ) / 256))⁻¹ := by
    rw [show (-13 : ℝ) / 256 = -(13 / 256) by ring, Real.rpow_neg hm0.le]
  rw [he, ← div_eq_mul_inv]
  apply (div_lt_iff₀ hp0).mpr
  nlinarith only [hpow]

theorem w_slope_lt {m : ℝ} (hm : (2 : ℝ) ^ 128 ≤ m) :
    ((3 : ℝ) ^ 41 / 2 ^ 65) * m ^ (((3 : ℝ) ^ 41 / 2 ^ 65) - 1) < 3 / 8 := by
  let p : ℝ := (3 : ℝ) ^ 41 / 2 ^ 65
  have hp : 0 < p ∧ p < 1 := by norm_num [p]
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  have hpow := dyadic_rpow_lower (q := 1 - p) (c := (8 : ℝ) / 3)
    (a := 10) (b := 7) hm (by linarith)
    (by norm_num [p]) (by norm_num)
  have hp0 : 0 < m ^ (1 - p) := Real.rpow_pos_of_pos hm0 _
  have he : m ^ (p - 1) = (m ^ (1 - p))⁻¹ := by
    rw [show p - 1 = -(1 - p) by ring, Real.rpow_neg hm0.le]
  change p * m ^ (p - 1) < _
  rw [he, ← div_eq_mul_inv]
  apply (div_lt_iff₀ hp0).mpr
  nlinarith only [hp.2, hpow]

theorem c_pair_from_floor {m : ℝ} (hm : (2 : ℝ) ^ 24 ≤ m) {x y : ℕ}
    (hmx : m ≤ x) (hxy : x ≤ y) :
    (eval wordC y : ℝ) - eval wordC x <
      ((243 : ℝ) / 256) * m ^ ((-13 : ℝ) / 256) * ((y : ℝ) - x) + 9 / 8 := by
  have hx3 : 3 ≤ x := by
    have : (3 : ℝ) ≤ x := (show (3 : ℝ) ≤ 2 ^ 24 by norm_num).trans (hm.trans hmx)
    exact_mod_cast this
  have hh := paired_bound_of_budget (lt_of_lt_of_le (by positivity) hm)
    (by decide : wordC ≠ []) c_tails (by rw [exponent_C]; norm_num)
    hmx hxy (innerAbove_mono hmx (c_innerAbove hx3))
    (c_budget_lt hm).le
  rw [exponent_C] at hh
  norm_num only [show (243 : ℝ) / 256 - 1 = -13 / 256 by norm_num] at hh
  simpa only [neg_div] using hh

theorem w_pair_from_floor {m : ℝ} (hm : (2 : ℝ) ^ 128 ≤ m) {x y : ℕ}
    (hmx : m ≤ x) (hxy : x ≤ y) :
    (eval wordW y : ℝ) - eval wordW x <
      ((3 : ℝ) ^ 41 / 2 ^ 65) * m ^ (((3 : ℝ) ^ 41 / 2 ^ 65) - 1) *
        ((y : ℝ) - x) + 6 / 5 := by
  have hx24 : 2 ^ 24 ≤ x := by
    have : (2 : ℝ) ^ 24 ≤ x := (show (2 : ℝ) ^ 24 ≤ 2 ^ 128 by norm_num).trans (hm.trans hmx)
    exact_mod_cast this
  have hh := paired_bound_of_budget (lt_of_lt_of_le (by positivity) hm)
    (by decide : wordW ≠ []) w_tails (by rw [exponent_W]; norm_num)
    hmx hxy (innerAbove_mono hmx (w_innerAbove hx24))
    (w_budget_lt hm).le
  rw [exponent_W] at hh
  exact hh

theorem c_contract {x y : ℕ} (hx : 2 ^ 24 ≤ x) (hxy : x + 2 ≤ y) :
    (eval wordC y : ℝ) - eval wordC x < (y : ℝ) - x := by
  have hm : (2 : ℝ) ^ 24 ≤ x := by exact_mod_cast hx
  have hxyR : (x : ℝ) + 2 ≤ y := by exact_mod_cast hxy
  have hg : (2 : ℝ) ≤ (y : ℝ) - x := by linarith
  have hb := c_pair_from_floor hm (le_refl (x : ℝ)) (by omega : x ≤ y)
  have hs := c_slope_lt hm
  have hscaled := mul_le_mul_of_nonneg_right hs.le (by linarith : (0 : ℝ) ≤ (y : ℝ) - x)
  exact NumericBridge.affine_gap_lt (k := (27 / 64 : ℝ)) (B := (9 / 8 : ℝ))
    hg (by norm_num) (by norm_num) (by linarith)

theorem w_contract {x y : ℕ} (hx : 2 ^ 128 ≤ x) (hxy : x + 2 ≤ y) :
    (eval wordW y : ℝ) - eval wordW x < (y : ℝ) - x := by
  have hm : (2 : ℝ) ^ 128 ≤ x := by exact_mod_cast hx
  have hxyR : (x : ℝ) + 2 ≤ y := by exact_mod_cast hxy
  have hg : (2 : ℝ) ≤ (y : ℝ) - x := by linarith
  have hb := w_pair_from_floor hm (le_refl (x : ℝ)) (by omega : x ≤ y)
  have hs := w_slope_lt hm
  have hscaled := mul_le_mul_of_nonneg_right hs.le (by linarith : (0 : ℝ) ≤ (y : ℝ) - x)
  exact NumericBridge.affine_gap_lt (k := (3 / 8 : ℝ)) (B := (6 / 5 : ℝ))
    hg (by norm_num) (by norm_num) (by linarith)

end Problems.Juggler.ReturnWordBounds
