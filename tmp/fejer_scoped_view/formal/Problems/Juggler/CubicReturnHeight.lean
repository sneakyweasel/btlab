import Problems.Juggler.NumericBridge

namespace Problems.Juggler

/-- A return-cell gap implies the uniform eighth-power height gap. -/
theorem cubic_return_height_algebra {m t z M : ℕ}
    (hm : 7 ≤ m) (hz : z ^ 8 ≤ m ^ 9)
    (ht : t ^ 3 < (z - 1) ^ 4) (hM : M + 2 ≤ (t + 1) ^ 2) :
    m ^ 15 < (m ^ 3 - M) ^ 8 := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  let r : ℝ := (m : ℝ) ^ ((3 : ℝ) / 8)
  have hr0 : 0 ≤ r := Real.rpow_nonneg hm0 _
  have hr8 : r ^ 8 = (m : ℝ) ^ 3 := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0]
    norm_num
  have hr24 : (r ^ 3) ^ 8 = (m : ℝ) ^ 9 := by
    calc
      (r ^ 3) ^ 8 = (r ^ 8) ^ 3 := by ring
      _ = (m : ℝ) ^ 9 := by rw [hr8]; ring
  have hr2 : 2 ≤ r := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) hr0
    rw [hr8]
    have hmm : (7 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith only [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7) hmm 3]
  have hzr : (z : ℝ) ≤ r ^ 3 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (pow_nonneg hr0 3)
    rw [hr24]
    exact_mod_cast hz
  have hz1 : 1 ≤ z := by
    by_contra h
    have : z = 0 := by omega
    simp [this] at ht
  have ht' : (t : ℝ) ^ 3 < ((z : ℝ) - 1) ^ 4 := by
    exact_mod_cast ht
  have hr3 : 1 ≤ r ^ 3 := by
    nlinarith only [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hr2 3]
  have hgap0 : 0 ≤ r ^ 4 - r := by nlinarith only [mul_nonneg hr0 (sub_nonneg.mpr hr3)]
  have hcell : ((z : ℝ) - 1) ^ 4 ≤ (r ^ 4 - r) ^ 3 := by
    have hz1' : (1 : ℝ) ≤ z := by exact_mod_cast hz1
    have hpow := pow_le_pow_left₀ (sub_nonneg.mpr hz1') (sub_le_sub_right hzr 1) 4
    have hid : (r ^ 4 - r) ^ 3 - (r ^ 3 - 1) ^ 4 = (r ^ 3 - 1) ^ 3 := by ring
    nlinarith only [hpow, hid, pow_nonneg (sub_nonneg.mpr hr3) 3]
  have htr : (t : ℝ) < r ^ 4 - r := by
    apply lt_of_pow_lt_pow_left₀ 3 hgap0
    exact lt_of_lt_of_le ht' hcell
  have htop : (M : ℝ) + 2 ≤ ((t : ℝ) + 1) ^ 2 := by exact_mod_cast hM
  have hsquare : ((t : ℝ) + 1) ^ 2 < (r ^ 4 - r + 1) ^ 2 := by
    have hbase : (t : ℝ) + 1 < r ^ 4 - r + 1 := by linarith only [htr]
    exact pow_lt_pow_left₀ hbase (by positivity) (by norm_num : (2 : ℕ) ≠ 0)
  have hfactor : r ^ 8 - r ^ 5 - ((r ^ 4 - r + 1) ^ 2 - 2) =
      (r - 2) * (r ^ 4 - r) + 1 := by ring
  have hMr : (M : ℝ) < r ^ 8 - r ^ 5 := by
    nlinarith only [htop, hsquare, hfactor, mul_nonneg (sub_nonneg.mpr hr2) hgap0]
  have hr15 : r ^ 5 = (m : ℝ) ^ ((15 : ℝ) / 8) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0]
    norm_num
  have hstrip : (M : ℝ) < (m : ℝ) ^ 3 - (1 / (1 : ℝ)) * (m : ℝ) ^ ((15 : ℝ) / 8) := by
    simpa only [← hr8, ← hr15, one_div_one, one_mul] using hMr
  simpa only [one_mul] using NumericBridge.power_strip_of_real_strip
    (q := 1) (by omega : 0 < m) (by decide : 0 < 8) (by decide : 0 < 1) (by simpa using hstrip)

end Problems.Juggler
