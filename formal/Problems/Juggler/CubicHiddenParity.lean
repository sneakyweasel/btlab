import Problems.Juggler.CubicBand
import Problems.Juggler.ReturnCells

namespace Problems.Juggler.CubicHiddenParity

open Problems.Juggler Problems.Juggler.ReturnCells

/-!
# Collapsed cube-threshold returns can hide an odd internal state

For odd `s ≥ 3`, threshold `b = s^3` and source `x = s^4`, the threshold map
`S_b` sends `s^4 ↦ s^6 ↦ s^3`, a lower-to-lower first return through the
upper state `s^6 = b^2`. Both endpoints are odd and the collapsed OE endpoint
is `x^{3/4} = s^3`, yet the eliminated state `s^6` is odd, so the actual
Juggler step there is `s^9`. Endpoint cells, endpoint parity and threshold
cuts therefore do not imply the internal parity guard. These are blocks at
unbounded cube thresholds, not cycles.
-/

/-- The source `s^4` lies in the lower part of the cube band of `b = s^3`,
and its two threshold iterates are `s^6 = b^2` (upper) and `s^3 = b` (lower). -/
theorem thresholdMap_cube_block {s : ℕ} (hs : 3 ≤ s) :
    InCubicBand (s ^ 3) (s ^ 4) ∧ s ^ 4 < (s ^ 3) ^ 2 ∧
      thresholdMap (s ^ 3) (s ^ 4) = s ^ 6 ∧ s ^ 6 = (s ^ 3) ^ 2 ∧
      thresholdMap (s ^ 3) (s ^ 6) = s ^ 3 ∧ s ^ 3 < (s ^ 3) ^ 2 := by
  have h1 : 1 < s := by omega
  have h34 : s ^ 3 ≤ s ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h46 : s ^ 4 < s ^ 6 := Nat.pow_lt_pow_right h1 (by norm_num)
  have h36 : s ^ 3 < s ^ 6 := Nat.pow_lt_pow_right h1 (by norm_num)
  have h69 : s ^ 6 < s ^ 9 := Nat.pow_lt_pow_right h1 (by norm_num)
  have hb2 : (s ^ 3) ^ 2 = s ^ 6 := by ring
  have hb3 : (s ^ 3) ^ 3 = s ^ 9 := by ring
  refine ⟨⟨h34, by rw [hb3]; omega⟩, by rw [hb2]; exact h46, ?_, hb2.symm, ?_,
    by rw [hb2]; exact h36⟩
  · rw [thresholdMap, if_pos (by rw [hb2]; exact h46)]
    rw [show (s ^ 4) ^ 3 = (s ^ 6) ^ 2 by ring, Nat.sqrt_eq']
  · rw [thresholdMap, if_neg (by rw [hb2]; omega)]
    rw [show s ^ 6 = (s ^ 3) ^ 2 by ring, Nat.sqrt_eq']

/-- The threshold block collapses to the OE return: `S_b(S_b(s^4)) = oe(s^4) = s^3`. -/
theorem threshold_block_eq_oe {s : ℕ} (hs : 3 ≤ s) :
    thresholdMap (s ^ 3) (thresholdMap (s ^ 3) (s ^ 4)) = oe (s ^ 4) := by
  obtain ⟨-, -, h1, -, h2, -⟩ := thresholdMap_cube_block hs
  rw [h1, h2, (oe_perfect_power s).2]

/-- For odd `s`, the eliminated internal state `s^6` is odd, so the actual
Juggler map sends it to `s^9`: the actual two-step image of `s^4` is `s^9`,
not the collapsed endpoint `s^3`. -/
theorem floorPower_hidden_odd_block {s : ℕ} (hs : 3 ≤ s) (hodd : s % 2 = 1) :
    s ^ 4 % 2 = 1 ∧ s ^ 6 % 2 = 1 ∧ s ^ 3 % 2 = 1 ∧
      floorPower (s ^ 4) = s ^ 6 ∧ floorPower (s ^ 6) = s ^ 9 ∧
      floorPower (floorPower (s ^ 4)) ≠ thresholdMap (s ^ 3) (thresholdMap (s ^ 3) (s ^ 4)) := by
  obtain ⟨h4, h6, h3⟩ := oe_perfect_power_hidden_odd hodd
  rw [(oe_perfect_power s).1] at h6
  rw [(oe_perfect_power s).2] at h3
  have hJ4 : floorPower (s ^ 4) = s ^ 6 := by
    rw [floorPower_odd_eq h4, (oe_perfect_power s).1]
  have hJ6 : floorPower (s ^ 6) = s ^ 9 := by
    rw [floorPower_odd_eq h6, show (s ^ 6) ^ 3 = (s ^ 9) ^ 2 by ring, Nat.sqrt_eq']
  refine ⟨h4, h6, h3, hJ4, hJ6, ?_⟩
  rw [threshold_block_eq_oe hs, (oe_perfect_power s).2, hJ4, hJ6]
  exact (Nat.pow_lt_pow_right (by omega) (by norm_num)).ne'

end Problems.Juggler.CubicHiddenParity
