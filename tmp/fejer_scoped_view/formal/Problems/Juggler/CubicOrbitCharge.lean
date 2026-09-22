import Problems.Juggler.CubicUpperCells
import Problems.Juggler.CubicConsequences
import Problems.Juggler.ReturnRankedCycle

namespace Problems.Juggler.CubicGrid

/-- The same complete ordinary-orbit model, retaining its rotation and all charge bounds. -/
structure OrbitUpperChargeCertificate (m M k : ℕ)
    extends ReturnSeams.PeriodicOrbitModel m M k where
  oddCount : ℕ
  oddCount_le : oddCount ≤ length
  oddCount_card : (Finset.univ.filter (fun i => state i % 2 = 1)).card = oddCount
  odd_cut : ∀ i, state i % 2 = 1 ↔ i.val < oddCount
  threshold_cut : ∀ i, state i < m ^ 2 ↔ i.val < oddCount
  rotation : ∀ i, (next i).val = (i.val + (length - oddCount)) % length
  coprime : Nat.Coprime length oddCount
  period_eq : length = Function.minimalPeriod floorPower m
  band : ∀ i, InCubicBand m (state i)
  grid :
    let : NeZero length := ⟨length_pos.ne'⟩
    RealizedGridBounds (fun i => (state i : ℝ)) oddCount
  charge :
    let : NeZero length := ⟨length_pos.ne'⟩
    FullUpperCellChargeBounds (L := length) m oddCount

namespace OrbitUpperChargeCertificate

/-- Connectedness belongs to the retained actual model, not to a new selected orbit. -/
theorem connected {m M k : ℕ} (Q : OrbitUpperChargeCertificate m M k) :
    ∀ i j, ∃ n : ℕ, floorPower^[n] (Q.state i) = Q.state j := by
  intro i j
  exact Q.toPeriodicOrbitModel.connected _ (Q.toPeriodicOrbitModel.member i)
    _ (Q.toPeriodicOrbitModel.member j)

end OrbitUpperChargeCertificate

/-- Strengthen an existing model without choosing a second sorted state set or permutation. -/
theorem orbitModel_upper_charge {m M k : ℕ}
    (S : ReturnSeams.PeriodicOrbitModel m M k) (hm : 1 < m) (hM : M < m ^ 3) :
    ∃ Q : OrbitUpperChargeCertificate m M k, Q.toPeriodicOrbitModel = S := by
  let : NeZero S.length := ⟨S.length_pos.ne'⟩
  have hzero : S.state 0 = m := by
    rw [show (0 : Fin S.length) = ⟨0, S.length_pos⟩ by apply Fin.ext; simp]
    exact S.min_eq
  have hband : ∀ i, InCubicBand m (S.state i) :=
    fun i => S.periodicExtrema.band hM (S.member i)
  obtain ⟨o, ho, hcut, hcard, hrank⟩ :=
    cubicBand_sorted_rotation S.state S.ordered S.next hband S.step
  have hthcut : ∀ i, S.state i < m ^ 2 ↔ i.val < o := by
    intro i
    have hp := cubicBand_parity_iff (hband i)
      (by rw [← S.step]; exact hband (S.next i))
    exact hp.symm.trans (hcut i)
  have hthreshold : ∀ i, S.state (S.next i) = thresholdMap m (S.state i) := by
    intro i
    rw [S.step]
    apply cubicBand_floorPower_eq_threshold (hband i)
    rw [← S.step]
    exact hband (S.next i)
  have hpos : ∀ i, (1 : ℝ) < S.state i := by
    intro i
    exact_mod_cast hm.trans_le (hband i).1
  have hcycle : S.next.IsCycleOn (↑(Finset.univ : Finset (Fin S.length))) := by
    simpa using S.cycleOn
  have hlen : S.length = o + (S.length - o) := by omega
  have hlower := threshold_real_power_cells S.state S.next hthcut hthreshold
  have hupper := threshold_real_upper_power_cells S.state S.next hthcut hthreshold
  have hgrid : RealizedGridBounds (fun i => (S.state i : ℝ)) o := by
    apply realized_grid_bounds_of_power_cells (fun i => (S.state i : ℝ)) S.next
      o (S.length - o) hpos ?_ ?_ hlen hrank hcycle hlower
    · intro i j hij
      change (S.state i : ℝ) < (S.state j : ℝ)
      exact_mod_cast S.ordered hij
    · intro i
      have hh : S.state i < S.state 0 ^ 3 := by
        simpa only [hzero] using (hband i).2
      exact_mod_cast hh
  have hcharge := power_cells_full_charge (fun i => (S.state i : ℝ)) S.next
    o (S.length - o) hpos hlen hrank hcycle hlower hupper
  have hcop := (Nat.coprime_self_sub_right ho).mp
    (rankRotation_coprime S.length_pos S.next hrank hcycle)
  refine ⟨{
    toPeriodicOrbitModel := S
    oddCount := o
    oddCount_le := ho
    oddCount_card := hcard
    odd_cut := hcut
    threshold_cut := hthcut
    rotation := hrank
    coprime := hcop
    period_eq := S.least_period hM
    band := hband
    grid := hgrid
    charge := ?_
  }, rfl⟩
  simpa only [hzero] using hcharge

/-- One ordinary periodic orbit produces one complete rotation-and-charge certificate. -/
theorem periodicOrbit_upper_charge_certificate {m M k : ℕ} (hk : 0 < k)
    (hp : floorPower^[k] m = m) (hm : 1 < m) (hM : M < m ^ 3)
    (hbound : ∀ j < k, m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M)
    (hmax : ∃ j < k, floorPower^[j] m = M) :
    Nonempty (OrbitUpperChargeCertificate m M k) := by
  obtain ⟨S⟩ := ReturnSeams.periodicOrbit_model hk hp hbound hmax
  obtain ⟨Q, _⟩ := orbitModel_upper_charge S hm hM
  exact ⟨Q⟩

/-- An ordinary finite actual orbit yields the complete grid and charge at its true least period. -/
theorem periodicOrbit_upper_charge {m M k : ℕ} (hk : 0 < k)
    (hp : floorPower^[k] m = m) (hm : 1 < m) (hM : M < m ^ 3)
    (hbound : ∀ j < k, m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M)
    (hmax : ∃ j < k, floorPower^[j] m = M) :
    ∃ (L : ℕ) (hL : 0 < L) (c : Fin L → ℕ),
      let : NeZero L := ⟨hL.ne'⟩
      StrictMono c ∧ (∀ j, ∃ i, c i = floorPower^[j] m) ∧
      (∀ i, ∃ j < k, c i = floorPower^[j] m) ∧
      c 0 = m ∧ c ⟨L - 1, by omega⟩ = M ∧
      L = Function.minimalPeriod floorPower m ∧
      ∃ o ≤ L, (Finset.univ.filter (fun i => c i % 2 = 1)).card = o ∧
        RealizedGridBounds (fun i => (c i : ℝ)) o ∧ UpperCellChargeBounds (L := L) m o := by
  obtain ⟨Q⟩ := periodicOrbit_upper_charge_certificate hk hp hm hM hbound hmax
  let : NeZero Q.length := ⟨Q.length_pos.ne'⟩
  exact ⟨Q.length, Q.length_pos, Q.state, Q.ordered, Q.covers, Q.mem,
    Q.min_eq, Q.max_eq, Q.period_eq, Q.oddCount, Q.oddCount_le,
    Q.oddCount_card, Q.grid, Q.charge.geometric⟩

/-- A minimum-based itinerary retains the same full certificate at its true least period. -/
theorem cycleMin_upper_charge_certificate {m M : ℕ} {w : List Branch}
    (hcycle : CycleMin m w) (hm : 1 < m) (hM : M < m ^ 3)
    (hbound : ∀ j < w.length, floorPower^[j] m ≤ M)
    (hmax : ∃ j < w.length, floorPower^[j] m = M) :
    Nonempty (OrbitUpperChargeCertificate m M w.length) := by
  obtain ⟨a, ha, hamax⟩ := hmax
  have hk : 0 < w.length := Nat.zero_lt_of_lt ha
  exact periodicOrbit_upper_charge_certificate hk (cycle_iterate_period hcycle.1) hm hM
    (fun j hj => ⟨cycleMin_ge hcycle hj, hbound j hj⟩) ⟨a, ha, hamax⟩

/-- A minimum-based closed itinerary is normalized to its least period before applying the charge. -/
theorem cycleMin_upper_charge {m M : ℕ} {w : List Branch}
    (hcycle : CycleMin m w) (hm : 1 < m) (hM : M < m ^ 3)
    (hbound : ∀ j < w.length, floorPower^[j] m ≤ M)
    (hmax : ∃ j < w.length, floorPower^[j] m = M) :
    ∃ (L : ℕ) (hL : 0 < L) (c : Fin L → ℕ),
      let : NeZero L := ⟨hL.ne'⟩
      StrictMono c ∧ (∀ j, ∃ i, c i = floorPower^[j] m) ∧
      (∀ i, ∃ j < w.length, c i = floorPower^[j] m) ∧
      c 0 = m ∧ c ⟨L - 1, by omega⟩ = M ∧
      L = Function.minimalPeriod floorPower m ∧
      ∃ o ≤ L, (Finset.univ.filter (fun i => c i % 2 = 1)).card = o ∧
        RealizedGridBounds (fun i => (c i : ℝ)) o ∧ UpperCellChargeBounds (L := L) m o := by
  obtain ⟨a, ha, hamax⟩ := hmax
  have hk : 0 < w.length := Nat.zero_lt_of_lt ha
  exact periodicOrbit_upper_charge hk (cycle_iterate_period hcycle.1) hm hM
    (fun j hj => ⟨cycleMin_ge hcycle hj, hbound j hj⟩) ⟨a, ha, hamax⟩

end Problems.Juggler.CubicGrid
