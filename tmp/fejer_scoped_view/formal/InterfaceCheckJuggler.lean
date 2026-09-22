import Problems.Juggler.CubicOrbitCharge
import Problems.Juggler.CubicChargeMonotonicity
import Problems.Juggler.ReturnTerminal
import Problems.Juggler.CubicRemainderAssembly

/-!
# Consumer checks for the cubic orbit interfaces

These checks are outside the production module inventory. The entry points
start from ordinary finite-period evidence. Certificate consumers then retain
one sorted model for terminal totals, rank rotation, and analytic bounds.
-/

namespace Problems.Juggler.InterfaceChecks

/-- The legacy terminal entry point remains callable with its original inputs. -/
theorem legacy_terminal_entry {m M k : ℕ} (hk : 0 < k)
    (hp : floorPower^[k] m = m)
    (hbound : ∀ j < k, m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M)
    (hmax : ∃ j < k, floorPower^[j] m = M) (hm : 3 ≤ m) (hM : M < m ^ 3) :
    Nonempty (ReturnTerminal.TerminalCut
      (Set.range (fun j : ℕ => floorPower^[j] m)) m M) :=
  ReturnTerminal.periodicOrbit_terminal_cut hk hp hbound hmax hm hM

/-- The older grid/charge entry point keeps its original least-period result. -/
theorem legacy_charge_entry {m M k : ℕ} (hk : 0 < k)
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
        CubicGrid.RealizedGridBounds (fun i => (c i : ℝ)) o ∧
        CubicGrid.UpperCellChargeBounds (L := L) m o :=
  CubicGrid.periodicOrbit_upper_charge hk hp hm hM hbound hmax

/-- The explicitly nonlinear sum and the legacy bound use this exact model. -/
theorem certificate_nonlinear_charge {m M k : ℕ}
    (Q : CubicGrid.OrbitUpperChargeCertificate m M k) :
    let : NeZero Q.length := ⟨Q.length_pos.ne'⟩
    let A := CubicGrid.logGridScale (L := Q.length) (m : ℝ) Q.oddCount
    CubicGrid.logGridSurplus Q.length Q.oddCount <
      (∑ i : Fin Q.length,
        Real.exp (-(A * Real.exp ((i.val : ℝ) * Real.log 3 / (Q.length : ℝ))) -
          (i.val : ℝ) * Real.log 3 / (Q.length : ℝ)) / A) ∧
      CubicGrid.UpperCellChargeBounds (L := Q.length) m Q.oddCount := by
  let : NeZero Q.length := ⟨Q.length_pos.ne'⟩
  exact ⟨Q.charge.nonlinear, Q.charge.geometric⟩

/-- The certificate alone retains the supplied period and supports exact
terminal counts, coprimality, and rank rotation on that same sorted model. -/
theorem certificate_terminal_totals {m M k : ℕ}
    (Q : CubicGrid.OrbitUpperChargeCertificate m M k)
    (hm : 3 ≤ m) (hM : M < m ^ 3) :
    ∃ T : ReturnTerminal.TerminalOrbitCut Q.toPeriodicOrbitModel,
      let w := T.lowerWord ++ T.upperWord
      follows m w ∧ image m w = m ∧
      w.length = Function.minimalPeriod floorPower m ∧ w.length ∣ k ∧
      oddCount w = Q.oddCount ∧ evenCount w = Q.length - Q.oddCount ∧
      evenCount w = (Finset.univ.filter (fun i => Q.state i % 2 = 0)).card ∧
      Nat.Coprime w.length (oddCount w) ∧
      (∀ i, (Q.next i).val = (i.val + evenCount w) % w.length) := by
  obtain ⟨T⟩ := Q.toPeriodicOrbitModel.terminal_cut hm hM
  have hlen : (T.lowerWord ++ T.upperWord).length = Q.length := by
    simpa only [List.length_append] using T.length_total
  have hodd : oddCount (T.lowerWord ++ T.upperWord) = Q.oddCount := by
    simpa only [oddCount_append] using T.odd_total.trans Q.oddCount_card
  have heven : evenCount (T.lowerWord ++ T.upperWord) = Q.length - Q.oddCount := by
    have hsum := evenCount_add_oddCount (T.lowerWord ++ T.upperWord)
    omega
  have heven_card : evenCount (T.lowerWord ++ T.upperWord) =
      (Finset.univ.filter (fun i => Q.state i % 2 = 0)).card := by
    simpa only [evenCount_append] using T.even_total
  have hleast : (T.lowerWord ++ T.upperWord).length =
      Function.minimalPeriod floorPower m := hlen.trans T.least_period
  have hperiod : Function.IsPeriodicPt floorPower k m := Q.periodic
  refine ⟨T, ?_, ?_, hleast, ?_, hodd, heven, heven_card, ?_, ?_⟩
  · exact follows_append T.lower_guard (by simpa only [T.lower_return] using T.upper_guard)
  · rw [image_append, T.lower_return, T.upper_return]
  · rw [hleast]
    exact hperiod.minimalPeriod_dvd
  · rw [hlen, hodd]
    exact Q.coprime
  · intro i
    rw [heven, hlen]
    exact Q.rotation i

/-- One ordinary orbit supplies one shared charge/terminal model. The supplied
period may repeat the primitive cycle; only divisibility by that period follows. -/
theorem shared_terminal_totals {m M k : ℕ} (hk : 0 < k)
    (hp : floorPower^[k] m = m) (hm : 3 ≤ m) (hM : M < m ^ 3)
    (hbound : ∀ j < k, m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M)
    (hmax : ∃ j < k, floorPower^[j] m = M) :
    ∃ (Q : CubicGrid.OrbitUpperChargeCertificate m M k)
      (T : ReturnTerminal.TerminalOrbitCut Q.toPeriodicOrbitModel),
      let w := T.lowerWord ++ T.upperWord
      follows m w ∧ image m w = m ∧
      w.length = Function.minimalPeriod floorPower m ∧ w.length ∣ k ∧
      oddCount w = Q.oddCount ∧ evenCount w = Q.length - Q.oddCount ∧
      evenCount w = (Finset.univ.filter (fun i => Q.state i % 2 = 0)).card ∧
      Nat.Coprime w.length (oddCount w) ∧
      (∀ i, (Q.next i).val = (i.val + evenCount w) % w.length) := by
  obtain ⟨Q⟩ := CubicGrid.periodicOrbit_upper_charge_certificate hk hp
    (show 1 < m by omega) hM hbound hmax
  obtain ⟨T, hT⟩ := certificate_terminal_totals Q hm hM
  exact ⟨Q, T, hT⟩

/-- A cutoff expressed using the terminal word totals excludes the same orbit.
The weaker closed comparison can feed the stronger nonlinear interface. -/
theorem terminal_word_cutoff {m M k : ℕ}
    (Q : CubicGrid.OrbitUpperChargeCertificate m M k)
    (T : ReturnTerminal.TerminalOrbitCut Q.toPeriodicOrbitModel)
    {m0 : ℝ} (hm0 : 1 < m0)
    (hcut :
      let L := T.lowerWord.length + T.upperWord.length
      let : NeZero L := ⟨by
        dsimp only [L]
        rw [T.length_total]
        exact Q.length_pos.ne'⟩
      CubicGrid.closedGeometricChargeBound L
        (CubicGrid.logGridScale (L := L) m0 (oddCount T.lowerWord + oddCount T.upperWord)) ≤
        CubicGrid.logGridSurplus L (oddCount T.lowerWord + oddCount T.upperWord)) :
    (m : ℝ) < m0 := by
  let : NeZero Q.length := ⟨Q.length_pos.ne'⟩
  have hodd : oddCount T.lowerWord + oddCount T.upperWord = Q.oddCount :=
    T.odd_total.trans Q.oddCount_card
  have hclosed : CubicGrid.closedGeometricChargeBound Q.length
      (CubicGrid.logGridScale (L := Q.length) m0 Q.oddCount) ≤
      CubicGrid.logGridSurplus Q.length Q.oddCount := by
    simpa only [T.length_total, hodd] using hcut
  have hA := CubicGrid.logGridScale_pos (L := Q.length) hm0 Q.oddCount
  apply Q.minimum_lt_of_nonlinear_cutoff hm0
  exact (CubicGrid.nonlinearChargeBound_le_finiteGeometric Q.length hA).trans
    ((CubicGrid.finiteGeometricChargeBound_lt_closed Q.length hA).le.trans hclosed)

/-- Leftover height from an actual charge certificate and m < 520000000. -/
theorem leftover_gap_height {m M k : ℕ}
    (Q : CubicGrid.OrbitUpperChargeCertificate m M k)
    (hM : M < m ^ 3) (hmin : m < 520000000) (i : Fin Q.length) :
    padicValNat 2 (CubicRemainderAssembly.gap Q i) ≤ 86 :=
  CubicRemainderAssembly.leftover_gap_val_le Q hM hmin i

/-- Fixed leftover counts and an assembled cover imply S >= 4483. -/
theorem leftover_deviation_from_certificate {m M k : ℕ}
    (Q : CubicGrid.OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (hM : M < m ^ 3) (hmin : m < 520000000)
    (hL : Q.length = 780239)
    (βOO βOE βEO : ℕ)
    (heven : ∀ i, i ∉ CubicRemainderAssembly.resets Q →
      CubicRemainderAssembly.denom Q i % 2 = 0)
    (hcover : CubicRemainderAssembly.resets Q ⊆
      CubicRemainderAssembly.boundary Q hm hM ∪
        CubicRemainderAssembly.deviations Q βOO βOE βEO ∪
        (CubicRemainderAssembly.deviations Q βOO βOE βEO).image
          (CubicRemainderAssembly.predIdx Q)) :
    4483 ≤ (CubicRemainderAssembly.deviations Q βOO βOE βEO).card :=
  CubicRemainderAssembly.leftover_deviation_lower_of_cover
    Q hm hM hmin hL βOO βOE βEO heven hcover

end Problems.Juggler.InterfaceChecks

#print axioms Problems.Juggler.InterfaceChecks.legacy_terminal_entry
#print axioms Problems.Juggler.InterfaceChecks.legacy_charge_entry
#print axioms Problems.Juggler.InterfaceChecks.certificate_nonlinear_charge
#print axioms Problems.Juggler.InterfaceChecks.certificate_terminal_totals
#print axioms Problems.Juggler.InterfaceChecks.shared_terminal_totals
#print axioms Problems.Juggler.InterfaceChecks.terminal_word_cutoff
#print axioms Problems.Juggler.InterfaceChecks.leftover_gap_height
#print axioms Problems.Juggler.InterfaceChecks.leftover_deviation_from_certificate
