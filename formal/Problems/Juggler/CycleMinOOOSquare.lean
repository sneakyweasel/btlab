import Problems.Juggler.CycleCore

namespace Problems.Juggler.OOOSquare

open Problems.Juggler

/-!
# A first OOO loses the square-cell ceiling at its second odd letter

For `n ≥ 3`, `⌊n^{3/2}⌋^3 ≥ n^4`, so two odd steps from any odd state
`x ≥ n` land at or above `n^2`. On the other side, the realized prefix
`(OOE)^k` keeps its image below `n^2` exactly while `3^{2k} < 2^{3k+1}`,
which holds for `k ≤ 5` and first fails at `k = 6`. The prefix `OOEOOO` has
already lost the square-cell gap (`3^5 ≥ 2^7`), and the completed `OOEOOOE`
restores it (`3^5 < 2^8`). This is not an OOO-inevitability, census or
halting theorem.
-/

/-- `⌊n^{3/2}⌋^3 ≥ n^4` for every `n ≥ 3`. -/
theorem sqrt_cube_cube_ge {n : ℕ} (hn : 3 ≤ n) : n ^ 4 ≤ (n ^ 3).sqrt ^ 3 := by
  rcases Nat.lt_or_ge n 4 with h3 | h4
  · obtain rfl : n = 3 := by omega
    have h27 : (3 ^ 3 : ℕ).sqrt = 5 := by
      symm; rw [Nat.eq_sqrt']; norm_num
    rw [h27]; norm_num
  set k := (n ^ 3).sqrt with hkdef
  have hlt : n ^ 3 < (k + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hkn : n ≤ k := Nat.le_sqrt'.mpr (Nat.pow_le_pow_right (by omega) (by norm_num))
  by_contra hcon
  have hk3 : k ^ 3 < n ^ 4 := by omega
  -- `(k+1)^6 ≤ 4 k^6`, since `4(k+1) ≤ 5k` and `5^6 ≤ 4 · 4^6`.
  have hstep : (k + 1) ^ 6 ≤ 4 * k ^ 6 := by
    have h45 : 4 * (k + 1) ≤ 5 * k := by omega
    have h6 : (4 * (k + 1)) ^ 6 ≤ (5 * k) ^ 6 := Nat.pow_le_pow_left h45 6
    have : 4096 * (k + 1) ^ 6 ≤ 4096 * (4 * k ^ 6) := by
      calc 4096 * (k + 1) ^ 6 = (4 * (k + 1)) ^ 6 := by ring
        _ ≤ (5 * k) ^ 6 := h6
        _ = 15625 * k ^ 6 := by ring
        _ ≤ 4096 * (4 * k ^ 6) := by nlinarith [Nat.zero_le (k ^ 6)]
    exact Nat.le_of_mul_le_mul_left this (by norm_num)
  have hk6 : k ^ 6 < n ^ 8 := by
    have := Nat.pow_lt_pow_left hk3 (by norm_num : (2 : ℕ) ≠ 0)
    calc k ^ 6 = (k ^ 3) ^ 2 := by ring
      _ < (n ^ 4) ^ 2 := this
      _ = n ^ 8 := by ring
  have hupper : (k + 1) ^ 6 < n ^ 9 := by
    have h1 : 4 * k ^ 6 ≤ n * k ^ 6 := Nat.mul_le_mul_right _ (by omega)
    have h2 : n * k ^ 6 < n * n ^ 8 := Nat.mul_lt_mul_of_pos_left hk6 (by omega)
    calc (k + 1) ^ 6 ≤ 4 * k ^ 6 := hstep
      _ ≤ n * k ^ 6 := h1
      _ < n * n ^ 8 := h2
      _ = n ^ 9 := by ring
  have hlower : n ^ 9 < (k + 1) ^ 6 := by
    have := Nat.pow_lt_pow_left hlt (by norm_num : (3 : ℕ) ≠ 0)
    calc n ^ 9 = (n ^ 3) ^ 3 := by ring
      _ < ((k + 1) ^ 2) ^ 3 := this
      _ = (k + 1) ^ 6 := by ring
  omega

/-- Two odd steps from an odd state `x ≥ n ≥ 3` reach at least `n^2`. -/
theorem floorPower_two_odd_ge_sq {n x : ℕ} (hn : 3 ≤ n) (hx : n ≤ x)
    (hxo : x % 2 = 1) (hTo : floorPower x % 2 = 1) :
    n ^ 2 ≤ floorPower (floorPower x) := by
  have h1 : (n ^ 3).sqrt ≤ floorPower x := by
    rw [floorPower_odd_eq hxo]
    exact Nat.sqrt_le_sqrt (Nat.pow_le_pow_left hx 3)
  rw [floorPower_odd_eq hTo]
  calc n ^ 2 = (n ^ 4).sqrt := by
          rw [show n ^ 4 = (n ^ 2) ^ 2 by ring, Nat.sqrt_eq']
    _ ≤ ((n ^ 3).sqrt ^ 3).sqrt := Nat.sqrt_le_sqrt (sqrt_cube_cube_ge hn)
    _ ≤ (floorPower x ^ 3).sqrt := Nat.sqrt_le_sqrt (Nat.pow_le_pow_left h1 3)

/-- The word `(OOE)^k`. -/
def ooePow : ℕ → List Branch
  | 0 => []
  | k + 1 => [.odd, .odd, .even] ++ ooePow k

/-- `|(OOE)^k| = 3k`. -/
theorem ooePow_length (k : ℕ) : (ooePow k).length = 3 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ooePow, ih]; ring

/-- `#O((OOE)^k) = 2k`. -/
theorem ooePow_oddCount (k : ℕ) : oddCount (ooePow k) = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ooePow, ih]; ring

/-- The square-cell gap `3^{2k} < 2^{3k+1}` holds exactly for `k ≤ 5` among
`k ≤ 6`: it fails at `k = 6`. -/
theorem ooePow_gap {k : ℕ} (hk : k ≤ 5) : 3 ^ (2 * k) < 2 * 2 ^ (3 * k) := by
  interval_cases k <;> norm_num

/-- The square-cell gap fails at `k = 6` (`3^12 ≥ 2^19`). -/
theorem ooePow_gap_fails_six : ¬ 3 ^ (2 * 6) < 2 * 2 ^ (3 * 6) := by norm_num

/-- A realized `(OOE)^k` with `k ≤ 5` from `n ≥ 2` lands below `n^2`. -/
theorem ooePow_image_lt_sq {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ 5)
    (hw : follows n (ooePow k)) : image n (ooePow k) < n ^ 2 := by
  have h := power_bound_word hw
  rw [ooePow_length, ooePow_oddCount] at h
  rw [image_eq_iterate, ooePow_length]
  exact envelope_lt_pow hn (by positivity) h (ooePow_gap hk)

/-- From a cycle minimum, a proper `(OOE)^k` prefix with `k ≤ 5` lands in
`[n, n^2)`. -/
theorem cycleMin_ooePow_mem {n k : ℕ} {v : List Branch} (hn : 2 ≤ n) (hk : k ≤ 5)
    (hv : v ≠ []) (hmin : CycleMin n (ooePow k ++ v)) :
    n ≤ image n (ooePow k) ∧ image n (ooePow k) < n ^ 2 := by
  have hfol : follows n (ooePow k ++ v) := hmin.1.1
  have hw : follows n (ooePow k) := follows_of_append_left hfol
  refine ⟨?_, ooePow_image_lt_sq hn hk hw⟩
  rw [image_eq_iterate]
  apply cycleMin_ge hmin
  have : 0 < v.length := List.length_pos_of_ne_nil hv
  simp only [List.length_append]
  omega

/-- The prefix `OOEOOO` (length 6, five odds) has lost the square-cell gap. -/
theorem ooeooo_gap_lost : ¬ 3 ^ 5 < 2 * 2 ^ 6 := by norm_num

/-- Every prefix `(OOE)^k·OOO` has lost the square-cell gap: it has `2k + 3` odds
in length `3k + 3`, and `27·9^k ≥ 16·8^k`. So `OOEOOO` (`k = 1`) is the first
such prefix after the first `OO`, and the bare `OOO` (`k = 0`) has lost it too. -/
theorem ooePow_ooo_gap_lost (k : ℕ) :
    ¬ 3 ^ oddCount (ooePow k ++ [Branch.odd, .odd, .odd]) <
      2 * 2 ^ (ooePow k ++ [Branch.odd, .odd, .odd]).length := by
  have ho : oddCount (ooePow k ++ [Branch.odd, .odd, .odd]) = 2 * k + 3 := by
    rw [oddCount_append, ooePow_oddCount]; rfl
  have hl : (ooePow k ++ [Branch.odd, .odd, .odd]).length = 3 * k + 3 := by
    simp [ooePow_length]
  rw [ho, hl, Nat.not_lt]
  have h98 : 8 ^ k ≤ 9 ^ k := Nat.pow_le_pow_left (by norm_num) k
  calc 2 * 2 ^ (3 * k + 3) = 16 * 8 ^ k := by
        rw [pow_add, pow_mul]; ring
    _ ≤ 27 * 9 ^ k := by omega
    _ = 3 ^ (2 * k + 3) := by rw [pow_add, pow_mul]; ring

/-- The word `OOEOOOE`. -/
def ooeoooe : List Branch := [.odd, .odd, .even, .odd, .odd, .odd, .even]

/-- The completed `OOEOOOE` restores the gap (`243 < 256`): its image from
`n ≥ 2` is below `n^2`. -/
theorem ooeoooe_image_lt_sq {n : ℕ} (hn : 2 ≤ n) (hw : follows n ooeoooe) :
    image n ooeoooe < n ^ 2 := by
  have h := power_bound_word hw
  rw [image_eq_iterate]
  exact envelope_lt_pow hn (by positivity) h (by decide)

end Problems.Juggler.OOOSquare
