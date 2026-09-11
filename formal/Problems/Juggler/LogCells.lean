import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace Problems.Juggler.LogCells

noncomputable def logEta (v : ℝ) : ℝ :=
  Real.log (Real.log (v + 1) / Real.log v)

theorem logEta_pos {v : ℝ} (hv : 1 < v) : 0 < logEta v := by
  apply Real.log_pos
  apply (one_lt_div (Real.log_pos hv)).mpr
  exact Real.log_lt_log (by linarith) (by linarith)

theorem logEta_antitone {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    logEta v ≤ logEta u := by
  have hv : 1 < v := hu.trans_le huv
  have hup : 0 < u := by linarith
  have hvp : 0 < v := by linarith
  have hlu := Real.log_pos hu
  have hlv := Real.log_pos hv
  have hinc : Real.log (v + 1) - Real.log v ≤
      Real.log (u + 1) - Real.log u := by
    rw [← Real.log_div (by linarith : v + 1 ≠ 0) (ne_of_gt hvp),
      ← Real.log_div (by linarith : u + 1 ≠ 0) (ne_of_gt hup)]
    apply Real.log_le_log (div_pos (by linarith) hvp)
    apply (div_le_div_iff₀ hvp hup).mpr
    nlinarith
  have hmul := mul_le_mul hinc (Real.log_le_log hup huv) (le_of_lt hlu)
    (sub_nonneg.mpr (Real.log_le_log hup (by linarith : u ≤ u + 1)))
  apply Real.log_le_log (div_pos (Real.log_pos (by linarith : 1 < v + 1)) hlv)
  apply (div_le_div_iff₀ hlv hlu).mpr
  nlinarith

theorem logEta_lt_inv {v : ℝ} (hv : 1 < v) :
    logEta v < 1 / (v * Real.log v) := by
  have hvp : 0 < v := by linarith
  have hlv := Real.log_pos hv
  have hq : 1 < Real.log (v + 1) / Real.log v := by
    apply (one_lt_div hlv).mpr
    exact Real.log_lt_log hvp (by linarith)
  have hr : 1 < (v + 1) / v := by
    apply (one_lt_div hvp).mpr
    linarith
  have h₁ := Real.log_lt_sub_one_of_pos (lt_trans zero_lt_one hq) (ne_of_gt hq)
  have h₂ := Real.log_lt_sub_one_of_pos (lt_trans zero_lt_one hr) (ne_of_gt hr)
  rw [Real.log_div (by linarith : v + 1 ≠ 0) (ne_of_gt hvp)] at h₂
  calc
    logEta v < Real.log (v + 1) / Real.log v - 1 := h₁
    _ = (Real.log (v + 1) - Real.log v) / Real.log v := by
      field_simp
    _ < ((v + 1) / v - 1) / Real.log v := div_lt_div_of_pos_right h₂ hlv
    _ = 1 / (v * Real.log v) := by
      field_simp
      ring

end Problems.Juggler.LogCells

namespace Problems.Juggler

/-- Shared scalar bound, retaining the existing public declaration name. -/
theorem one_lt_logb_two_three : 1 < Real.logb 2 3 := by
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
  norm_num

end Problems.Juggler
