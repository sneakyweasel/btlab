import Problems.Juggler.ReturnWordLoss

namespace Problems.Juggler.ReturnTerminal

theorem quarter_power_cube (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (3 / 4 : ℝ)) ^ 4 = x ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- The mixed passage contracts the integer gap across the absolute cut. -/
theorem mixed_gap_of_cells {m h s q t : ℕ}
    (hh1 : 1 ≤ h) (hh : h < m^2) (hs : m^2 < s)
    (hq : q^2 ≤ m^3) (ht : h^3 < (t+1)^4) :
    (q : ℤ) - t < (s : ℤ) - h := by
  let X : ℝ := (m : ℝ)^2
  have hh1r : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hh0 : (0 : ℝ) < h := by linarith
  have hhX : (h : ℝ) < X := by dsimp [X]; exact_mod_cast hh
  have hXs : X+1 ≤ (s : ℝ) := by
    dsimp [X]
    exact_mod_cast Nat.succ_le_of_lt hs
  have hq2 : (q : ℝ)^2 ≤ (m : ℝ)^3 := by exact_mod_cast hq
  have hq4 : (q : ℝ)^4 ≤ X^3 := by
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (q : ℝ)^2) hq2 2
    dsimp [X]
    nlinarith only [hp]
  have hqR : (q : ℝ) ≤ X^(3/4 : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
      (Real.rpow_nonneg (by positivity) _)
    rw [quarter_power_cube X (by positivity)]
    exact hq4
  have ht4 : (h : ℝ)^3 < ((t : ℝ)+1)^4 := by exact_mod_cast ht
  have htR : (h : ℝ)^(3/4 : ℝ) < (t : ℝ)+1 := by
    apply lt_of_pow_lt_pow_left₀ 4 (by positivity)
    rw [quarter_power_cube (h : ℝ) (Nat.cast_nonneg h)]
    exact ht4
  have hconc := ReturnWordLoss.rpow_sub_le hh0 hhX.le
    (by norm_num : (0 : ℝ) ≤ 3/4) (by norm_num : (3/4 : ℝ) ≤ 1)
  have hpow : (h : ℝ)^((3/4 : ℝ)-1) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
      hh1r (by norm_num : (3/4 : ℝ)-1 ≤ 0)
  have hmul := mul_le_mul_of_nonneg_right hpow (sub_nonneg.mpr hhX.le)
  have hreal : (q : ℝ) - t < (s : ℝ) - h := by nlinarith
  exact_mod_cast hreal

theorem mixed_gap {m h s : ℕ}
    (hh1 : 1 ≤ h) (hh : h < m^2) (hs : m^2 < s) :
    ((m^3).sqrt : ℤ) - ReturnCells.oe h < (s : ℤ) - h :=
  mixed_gap_of_cells hh1 hh hs (Nat.sqrt_le' _) (ReturnCells.oe_cell h).2

end Problems.Juggler.ReturnTerminal
