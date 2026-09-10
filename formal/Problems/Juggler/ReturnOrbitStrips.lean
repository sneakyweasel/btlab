import Problems.Juggler.ReturnTransferHeight

namespace Problems.Juggler.ReturnOrbitStrips

/-- The DC strip applies to the repository's actual cycle-minimum predicate. -/
theorem cycleMin_dc_height {m M : ℕ} {w : List Branch}
    (h : CycleMin m w) (hm : 2 ^ 24 ≤ m) (hM : M < m ^ 3)
    (hupper : ∀ j < w.length, floorPower^[j] m ≤ M)
    (hmax : ∃ j < w.length, floorPower^[j] m = M) :
    (M : ℝ) < (m : ℝ) ^ 3 - (1 / 2 : ℝ) * (m : ℝ) ^ (253 / 128 : ℝ) ∧
      m ^ 253 < (2 * (m ^ 3 - M)) ^ 128 :=
  ReturnTransferHeight.dc_cycle_height
    (CubicReturn.periodicExtrema_of_cycleMin h hupper hmax) hm hM

/-- The same actual-cycle interface yields both LR exponents and the integer strip. -/
theorem cycleMin_lr_height {m M : ℕ} {w : List Branch}
    (h : CycleMin m w) (hm : 2 ^ 128 ≤ m) (hM : M < m ^ 3)
    (hupper : ∀ j < w.length, floorPower^[j] m ≤ M)
    (hmax : ∃ j < w.length, floorPower^[j] m = M) :
    (M : ℝ) < (m : ℝ) ^ 3 - (1 / 2 : ℝ) * (m : ℝ) ^ (381 / 128 - (3 : ℝ) ^ 41 / 2 ^ 65) ∧
    (M : ℝ) < (m : ℝ) ^ 3 - (1 / 2 : ℝ) * (m : ℝ) ^ (127 / 64 : ℝ) ∧
      m ^ 127 < (2 * (m ^ 3 - M)) ^ 64 :=
  ReturnTransferHeight.lr_cycle_height
    (CubicReturn.periodicExtrema_of_cycleMin h hupper hmax) hm hM

/-- Every state of a cubic cycle satisfies the DC integer strip. -/
theorem cycleMin_all_states_dc_strip {m : ℕ} {w : List Branch}
    (h : CycleMin m w) (hm : 2 ^ 24 ≤ m)
    (hcubic : ∀ j < w.length, floorPower^[j] m < m ^ 3) :
    ∀ j < w.length, m ^ 253 < (2 * (m ^ 3 - floorPower^[j] m)) ^ 128 := by
  obtain ⟨i, hi, hmax⟩ := exists_iterate_max m w.length h.1.2.2
  have hs := (cycleMin_dc_height h hm (hcubic i hi) hmax ⟨i, hi, rfl⟩).2
  intro j hj
  exact hs.trans_le (Nat.pow_le_pow_left
    (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_left (hmax j hj) _)) 128)

/-- Every state satisfies the clean LR integer strip on its larger minimum domain. -/
theorem cycleMin_all_states_lr_strip {m : ℕ} {w : List Branch}
    (h : CycleMin m w) (hm : 2 ^ 128 ≤ m)
    (hcubic : ∀ j < w.length, floorPower^[j] m < m ^ 3) :
    ∀ j < w.length, m ^ 127 < (2 * (m ^ 3 - floorPower^[j] m)) ^ 64 := by
  obtain ⟨i, hi, hmax⟩ := exists_iterate_max m w.length h.1.2.2
  have hs := (cycleMin_lr_height h hm (hcubic i hi) hmax ⟨i, hi, rfl⟩).2.2
  intro j hj
  exact hs.trans_le (Nat.pow_le_pow_left
    (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_left (hmax j hj) _)) 64)

/-- A threshold cycle inside the excluded DC strip has a wrong source parity. -/
theorem threshold_cycle_dc_wrong_parity {b m M k : ℕ} (hb : 3 ≤ b)
    (hm : 2 ^ 24 ≤ m) (hx : InCubicBand b m) (hk : 0 < k)
    (hp : (thresholdMap b)^[k] m = m) (hM : M < m ^ 3)
    (hbound : ∀ j < k,
      m ≤ (thresholdMap b)^[j] m ∧ (thresholdMap b)^[j] m ≤ M)
    (hmax : ∃ j < k, (thresholdMap b)^[j] m = M)
    (hstrip : (2 * (m ^ 3 - M)) ^ 128 ≤ m ^ 253) :
    ∃ j < k, ¬ (((thresholdMap b)^[j] m) % 2 = 1 ↔
      (thresholdMap b)^[j] m < b ^ 2) := by
  by_contra hn
  push Not at hn
  have hper : Function.IsPeriodicPt (thresholdMap b) k m := hp
  have hcompatible : ∀ j,
      ((thresholdMap b)^[j] m) % 2 = 1 ↔ (thresholdMap b)^[j] m < b ^ 2 := by
    intro j
    rw [← hper.iterate_mod_apply j]
    exact hn _ (Nat.mod_lt _ hk)
  have heq := threshold_iterates_eq_of_compatible hb hx hcompatible
  have hpactual : floorPower^[k] m = m := (heq k).symm.trans hp
  have hbactual : ∀ j < k, m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M := by
    intro j hj
    rw [← heq j]
    exact hbound j hj
  have hmaxactual : ∃ j < k, floorPower^[j] m = M := by
    obtain ⟨j, hj, he⟩ := hmax
    exact ⟨j, hj, (heq j).symm.trans he⟩
  exact (not_lt_of_ge hstrip)
    (ReturnTransferHeight.periodicOrbit_dc_height hk hpactual hbactual hmaxactual hm hM).2

/-- The clean LR exclusion has the same exact wrong-parity consequence. -/
theorem threshold_cycle_lr_wrong_parity {b m M k : ℕ} (hb : 3 ≤ b)
    (hm : 2 ^ 128 ≤ m) (hx : InCubicBand b m) (hk : 0 < k)
    (hp : (thresholdMap b)^[k] m = m) (hM : M < m ^ 3)
    (hbound : ∀ j < k,
      m ≤ (thresholdMap b)^[j] m ∧ (thresholdMap b)^[j] m ≤ M)
    (hmax : ∃ j < k, (thresholdMap b)^[j] m = M)
    (hstrip : (2 * (m ^ 3 - M)) ^ 64 ≤ m ^ 127) :
    ∃ j < k, ¬ (((thresholdMap b)^[j] m) % 2 = 1 ↔
      (thresholdMap b)^[j] m < b ^ 2) := by
  by_contra hn
  push Not at hn
  have hper : Function.IsPeriodicPt (thresholdMap b) k m := hp
  have hcompatible : ∀ j,
      ((thresholdMap b)^[j] m) % 2 = 1 ↔ (thresholdMap b)^[j] m < b ^ 2 := by
    intro j
    rw [← hper.iterate_mod_apply j]
    exact hn _ (Nat.mod_lt _ hk)
  have heq := threshold_iterates_eq_of_compatible hb hx hcompatible
  have hpactual : floorPower^[k] m = m := (heq k).symm.trans hp
  have hbactual : ∀ j < k, m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M := by
    intro j hj
    rw [← heq j]
    exact hbound j hj
  have hmaxactual : ∃ j < k, floorPower^[j] m = M := by
    obtain ⟨j, hj, he⟩ := hmax
    exact ⟨j, hj, (heq j).symm.trans he⟩
  exact (not_lt_of_ge hstrip)
    (ReturnTransferHeight.periodicOrbit_lr_height hk hpactual hbactual hmaxactual hm hM).2.2

end Problems.Juggler.ReturnOrbitStrips
