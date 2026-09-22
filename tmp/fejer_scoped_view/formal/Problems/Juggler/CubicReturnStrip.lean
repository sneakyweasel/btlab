import Problems.Juggler.CubicReturn
import Problems.Juggler.CubicReturnHeight

namespace Problems.Juggler.CubicReturn

/-- Exact first-return ordering excludes the terminal strip of a cubic band.
The integer conclusion is equivalent to `M < m³ - m^(15/8)`. -/
theorem height_strip {C : Set ℕ} {m M : ℕ}
    (D : PeriodicExtrema C m M) (hm : 7 ≤ m) (hM : M < m ^ 3) :
    m ^ 15 < (m ^ 3 - M) ^ 8 := by
  obtain ⟨_, hmax, hseam⟩ := exact_return_seam D (by omega) hM
  exact cubic_return_height_algebra hm (ReturnCells.ooe_upper_pow m) hseam hmax

/-- The height-strip restriction applies to every ordinary actual periodic orbit. -/
theorem periodicOrbit_height_strip {m M k : ℕ} (hm : 7 ≤ m) (hk : 0 < k)
    (hp : floorPower^[k] m = m) (hM : M < m ^ 3)
    (hbound : ∀ j < k, m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M)
    (hmax : ∃ j < k, floorPower^[j] m = M) :
    m ^ 15 < (m ^ 3 - M) ^ 8 :=
  height_strip (periodicExtrema_of_orbit hk hp hbound hmax) hm hM

/-- A cycle spelled by the repository's exact `CycleMin` predicate has the
same height restriction, without an additional parity or return hypothesis. -/
theorem cycleMin_height_strip {m M : ℕ} {w : List Branch}
    (h : CycleMin m w) (hm : 7 ≤ m) (hM : M < m ^ 3)
    (hupper : ∀ j < w.length, floorPower^[j] m ≤ M)
    (hmax : ∃ j < w.length, floorPower^[j] m = M) :
    m ^ 15 < (m ^ 3 - M) ^ 8 :=
  height_strip (periodicExtrema_of_cycleMin h hupper hmax) hm hM

/-- No choice of a maximum is needed in the all-states formulation. -/
theorem cycleMin_all_states_height_strip {m : ℕ} {w : List Branch}
    (h : CycleMin m w) (hm : 7 ≤ m)
    (hcubic : ∀ j < w.length, floorPower^[j] m < m ^ 3) :
    ∀ j < w.length, m ^ 15 < (m ^ 3 - floorPower^[j] m) ^ 8 := by
  obtain ⟨i, hi, hmax⟩ := exists_iterate_max m w.length h.1.2.2
  have hstrip := cycleMin_height_strip h hm (hcubic i hi) hmax ⟨i, hi, rfl⟩
  intro j hj
  exact hstrip.trans_le (Nat.pow_le_pow_left (Nat.sub_le_sub_left (hmax j hj) _) 8)

/-- An exact threshold cycle in the excluded strip must fail actual source parity
at some state of its period. This statement concerns only the specified strip. -/
theorem threshold_cycle_wrong_parity {b m M k : ℕ} (hb : 3 ≤ b) (hm : 7 ≤ m)
    (hx : InCubicBand b m) (hk : 0 < k)
    (hp : (thresholdMap b)^[k] m = m) (hM : M < m ^ 3)
    (hbound : ∀ j < k,
      m ≤ (thresholdMap b)^[j] m ∧ (thresholdMap b)^[j] m ≤ M)
    (hmax : ∃ j < k, (thresholdMap b)^[j] m = M)
    (hstrip : (m ^ 3 - M) ^ 8 ≤ m ^ 15) :
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
    (periodicOrbit_height_strip hm hk hpactual hM hbactual hmaxactual)

end Problems.Juggler.CubicReturn
