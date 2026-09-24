import Problems.Juggler.Dynamics

namespace Problems.Juggler.HugFlow

open Problems.Juggler Filter Topology

/-!
# Odd Juggler images are separated by three square roots

The depth-two hug-flow gap: consecutive odd sources `x` and `x + 2` have
images at least `3⌊√x⌋` apart, because `(x+2)^3` exceeds
`(x^{3/2} + 3√x)^2` by `3x + 8`. The integer proof squares the target and
bounds the cross term by `⌊x^{3/2}⌋⌊√x⌋ ≤ x^2`. The gap beats the depth-one
working window `(2/3) Y^{1/3}` at image scale `Y = ⌊x^{3/2}⌋`, with ratio
tending to `9/2`, so the odd image of a window is a separated packing rather
than an interval. This is not a mixing or halting statement.
-/

/-- Integer form of the gap, valid for every `x`:
`⌊x^{3/2}⌋ + 3⌊√x⌋ ≤ ⌊(x+2)^{3/2}⌋`. -/
theorem sqrt_cube_add_two_ge (x : ℕ) :
    (x ^ 3).sqrt + 3 * x.sqrt ≤ ((x + 2) ^ 3).sqrt := by
  set y := (x ^ 3).sqrt
  set s := x.sqrt
  have hy : y ^ 2 ≤ x ^ 3 := Nat.sqrt_le' _
  have hs : s ^ 2 ≤ x := Nat.sqrt_le' _
  have hys : y * s ≤ x ^ 2 := by
    have : (y * s) ^ 2 ≤ (x ^ 2) ^ 2 := by
      calc (y * s) ^ 2 = y ^ 2 * s ^ 2 := by ring
        _ ≤ x ^ 3 * x := Nat.mul_le_mul hy hs
        _ = (x ^ 2) ^ 2 := by ring
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this
  rw [Nat.le_sqrt']
  nlinarith [hy, hs, hys]

/-- For odd `x`, `J(x+2) - J(x) ≥ 3⌊√x⌋`. -/
theorem floorPower_add_two_ge {x : ℕ} (hx : x % 2 = 1) :
    floorPower x + 3 * x.sqrt ≤ floorPower (x + 2) := by
  rw [floorPower_odd_eq hx, floorPower_odd_eq (by omega)]
  exact sqrt_cube_add_two_ge x

/-- `J` is monotone on odd states. -/
theorem floorPower_odd_mono {x z : ℕ} (hx : x % 2 = 1) (hz : z % 2 = 1)
    (hxz : x ≤ z) : floorPower x ≤ floorPower z := by
  rw [floorPower_odd_eq hx, floorPower_odd_eq hz]
  exact Nat.sqrt_le_sqrt (Nat.pow_le_pow_left hxz 3)

/-- Separation: no odd source has its image strictly inside
`(J(x), J(x) + 3⌊√x⌋)`. In particular the odd image of any window of odd
sources is not a run of consecutive integers once `x ≥ 1`. -/
theorem no_odd_image_in_gap {x z : ℕ} (hx : x % 2 = 1) (hz : z % 2 = 1) :
    ¬ (floorPower x < floorPower z ∧ floorPower z < floorPower x + 3 * x.sqrt) := by
  rintro ⟨hlo, hhi⟩
  rcases le_or_gt z x with hzx | hxz
  · have := floorPower_odd_mono hz hx hzx
    omega
  · have hz2 : x + 2 ≤ z := by omega
    have h1 := floorPower_add_two_ge hx
    have h2 := floorPower_odd_mono (by omega : (x + 2) % 2 = 1) hz hz2
    omega

/-- The integer after an odd image is never an odd image, for `x ≥ 1`. -/
theorem floorPower_odd_ne_succ {x z : ℕ} (hx : x % 2 = 1) (hz : z % 2 = 1) :
    floorPower z ≠ floorPower x + 1 := by
  intro h
  have hs : 1 ≤ x.sqrt := Nat.le_sqrt.mpr (by omega)
  exact no_odd_image_in_gap hx hz ⟨by omega, by omega⟩

/-- The depth-one working window at image scale `Y = ⌊x^{3/2}⌋` is at most
the source-scale window: `(2/3) Y^{1/3} ≤ (2/3) √x`. -/
theorem window_le_sqrt (x : ℕ) :
    (2 / 3 : ℝ) * ((x ^ 3).sqrt : ℝ) ^ (1 / 3 : ℝ) ≤ (2 / 3) * Real.sqrt x := by
  have hY : (((x ^ 3).sqrt : ℕ) : ℝ) ^ 2 ≤ (x : ℝ) ^ 3 := by
    exact_mod_cast Nat.sqrt_le' (x ^ 3)
  have hbase : 0 ≤ (((x ^ 3).sqrt : ℕ) : ℝ) := by positivity
  set c := (((x ^ 3).sqrt : ℕ) : ℝ) ^ (1 / 3 : ℝ) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg hbase _
  have hc6 : c ^ 6 = (((x ^ 3).sqrt : ℕ) : ℝ) ^ 2 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hbase]
    norm_num
  have hs6 : Real.sqrt x ^ 6 = (x : ℝ) ^ 3 := by
    have : Real.sqrt x ^ 2 = (x : ℝ) := Real.sq_sqrt (by positivity)
    calc Real.sqrt x ^ 6 = (Real.sqrt x ^ 2) ^ 3 := by ring
      _ = (x : ℝ) ^ 3 := by rw [this]
  have : c ≤ Real.sqrt x := by
    have h6 : c ^ 6 ≤ Real.sqrt x ^ 6 := by rw [hc6, hs6]; exact hY
    exact (pow_le_pow_iff_left₀ hc0 (Real.sqrt_nonneg _) (by norm_num)).mp h6
  linarith

/-- For `x ≥ 1` the gap `3⌊√x⌋` exceeds the whole working window. -/
theorem window_lt_gap {x : ℕ} (hx : 1 ≤ x) :
    (2 / 3 : ℝ) * ((x ^ 3).sqrt : ℝ) ^ (1 / 3 : ℝ) < 3 * (x.sqrt : ℝ) := by
  have hw := window_le_sqrt x
  have hlt : Real.sqrt x < (x.sqrt : ℝ) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hs : (1 : ℝ) ≤ x.sqrt := by exact_mod_cast Nat.le_sqrt.mpr (by omega)
  linarith

/-- The gap-to-window ratio `3⌊√x⌋ / ((2/3)√x)` tends to `9/2`. -/
theorem gap_window_ratio_tendsto :
    Tendsto (fun x : ℕ => 3 * (x.sqrt : ℝ) / ((2 / 3) * Real.sqrt x)) atTop
      (𝓝 (9 / 2)) := by
  have hsqrt : Tendsto (fun x : ℕ => Real.sqrt x) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun x : ℕ => (Real.sqrt x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hlow : Tendsto (fun x : ℕ => 9 / 2 * (1 - (Real.sqrt x)⁻¹)) atTop (𝓝 (9 / 2)) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hinv).const_mul (9 / 2 : ℝ)
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by exact_mod_cast hx)
    have hlt : Real.sqrt x < (x.sqrt : ℝ) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
    rw [le_div_iff₀ (by positivity)]
    have : 9 / 2 * (1 - (Real.sqrt x)⁻¹) * (2 / 3 * Real.sqrt x) = 3 * (Real.sqrt x - 1) := by
      field_simp; ring
    rw [this]; linarith
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by exact_mod_cast hx)
    have hle : (x.sqrt : ℝ) ≤ Real.sqrt x := Real.nat_sqrt_le_real_sqrt
    rw [div_le_iff₀ (by positivity)]
    linarith

end Problems.Juggler.HugFlow
