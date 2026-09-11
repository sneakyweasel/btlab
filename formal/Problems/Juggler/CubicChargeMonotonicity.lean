import Problems.Juggler.CubicOrbitCharge

namespace Problems.Juggler.CubicGrid

open scoped BigOperators

/-- The finite nonlinear upper-cell majorant at a positive grid scale. -/
noncomputable def nonlinearChargeBound (L : ℕ) (A : ℝ) : ℝ :=
  ∑ i : Fin L,
    Real.exp (-(A * Real.exp ((i.val : ℝ) * Real.log 3 / (L : ℝ))) -
      (i.val : ℝ) * Real.log 3 / (L : ℝ)) / A

/-- The finite geometric upper-cell majorant. -/
noncomputable def finiteGeometricChargeBound (L : ℕ) (A : ℝ) : ℝ :=
  Real.exp (-A) / A *
    ∑ i : Fin L, Real.exp (-(A + 1) * ((i.val : ℝ) * Real.log 3 / (L : ℝ)))

/-- The closed geometric upper-cell majorant used by the symbolic cutoff. -/
noncomputable def closedGeometricChargeBound (L : ℕ) (A : ℝ) : ℝ :=
  Real.exp (-A) / A * (1 + (L : ℝ) / (Real.log 3 * (A + 1)))

private theorem charge_prefactor_lt {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    Real.exp (-B) / B < Real.exp (-A) / A := by
  have hB : 0 < B := hA.trans hAB
  calc
    Real.exp (-B) / B < Real.exp (-A) / B :=
      div_lt_div_of_pos_right (Real.exp_lt_exp.mpr (neg_lt_neg hAB)) hB
    _ ≤ Real.exp (-A) / A :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hA hAB.le

/-- Every nonlinear summand decreases strictly with the positive grid scale. -/
theorem nonlinearChargeBound_strictAntiOn (L : ℕ) [NeZero L] :
    StrictAntiOn (nonlinearChargeBound L) (Set.Ioi 0) := by
  intro A hA B hB hAB
  change 0 < A at hA
  change 0 < B at hB
  have hterm (i : Fin L) :
      Real.exp (-(B * Real.exp ((i.val : ℝ) * Real.log 3 / (L : ℝ))) -
        (i.val : ℝ) * Real.log 3 / (L : ℝ)) / B <
      Real.exp (-(A * Real.exp ((i.val : ℝ) * Real.log 3 / (L : ℝ))) -
        (i.val : ℝ) * Real.log 3 / (L : ℝ)) / A := by
    have hp := mul_lt_mul_of_pos_right hAB
      (Real.exp_pos ((i.val : ℝ) * Real.log 3 / (L : ℝ)))
    have hn : -(B * Real.exp ((i.val : ℝ) * Real.log 3 / (L : ℝ))) -
        (i.val : ℝ) * Real.log 3 / (L : ℝ) <
        -(A * Real.exp ((i.val : ℝ) * Real.log 3 / (L : ℝ))) -
          (i.val : ℝ) * Real.log 3 / (L : ℝ) := by linarith
    exact (div_lt_div_of_pos_right (Real.exp_lt_exp.mpr hn) hB).trans_le
      (div_le_div_of_nonneg_left (Real.exp_pos _).le hA hAB.le)
  unfold nonlinearChargeBound
  exact Finset.sum_lt_sum (fun i _ => (hterm i).le) ⟨0, Finset.mem_univ _, hterm 0⟩

/-- The finite geometric majorant decreases strictly; no derivative estimate is used. -/
theorem finiteGeometricChargeBound_strictAntiOn (L : ℕ) [NeZero L] :
    StrictAntiOn (finiteGeometricChargeBound L) (Set.Ioi 0) := by
  intro A hA B hB hAB
  change 0 < A at hA
  change 0 < B at hB
  have hT : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (Nat.pos_of_neZero L)
  have hsum : (∑ i : Fin L,
      Real.exp (-(B + 1) * ((i.val : ℝ) * Real.log 3 / (L : ℝ)))) ≤
      ∑ i : Fin L, Real.exp (-(A + 1) * ((i.val : ℝ) * Real.log 3 / (L : ℝ))) := by
    apply Finset.sum_le_sum
    intro i _
    have ht : 0 ≤ (i.val : ℝ) * Real.log 3 / (L : ℝ) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) hT.le) hL.le
    have hp := mul_le_mul_of_nonneg_right (show -(B + 1) ≤ -(A + 1) by linarith) ht
    exact Real.exp_le_exp.mpr hp
  have hpos : 0 < ∑ i : Fin L,
      Real.exp (-(A + 1) * ((i.val : ℝ) * Real.log 3 / (L : ℝ))) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨0, Finset.mem_univ _⟩
  unfold finiteGeometricChargeBound
  exact (mul_le_mul_of_nonneg_left hsum (div_pos (Real.exp_pos _) hB).le).trans_lt
    (mul_lt_mul_of_pos_right (charge_prefactor_lt hA hAB) hpos)

/-- Both positive factors of the closed majorant decrease with the grid scale. -/
theorem closedGeometricChargeBound_strictAntiOn (L : ℕ) :
    StrictAntiOn (closedGeometricChargeBound L) (Set.Ioi 0) := by
  intro A hA B hB hAB
  change 0 < A at hA
  change 0 < B at hB
  have hT : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hden : 0 < Real.log 3 * (A + 1) := mul_pos hT (by linarith)
  have hdens : Real.log 3 * (A + 1) ≤ Real.log 3 * (B + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hT.le
  have hfactor : 1 + (L : ℝ) / (Real.log 3 * (B + 1)) ≤
      1 + (L : ℝ) / (Real.log 3 * (A + 1)) := by
    have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg L) hden hdens
    linarith
  have hpos : 0 < 1 + (L : ℝ) / (Real.log 3 * (A + 1)) := by
    have hh := div_nonneg (Nat.cast_nonneg L : (0 : ℝ) ≤ L) hden.le
    linarith
  unfold closedGeometricChargeBound
  exact (mul_le_mul_of_nonneg_left hfactor (div_pos (Real.exp_pos _) hB).le).trans_lt
    (mul_lt_mul_of_pos_right (charge_prefactor_lt hA hAB) hpos)

/-- The named finite majorants retain the original nonlinear-to-geometric comparison. -/
theorem nonlinearChargeBound_le_finiteGeometric (L : ℕ) [NeZero L]
    {A : ℝ} (hA : 0 < A) :
    nonlinearChargeBound L A ≤ finiteGeometricChargeBound L A :=
  grid_charge_le_geometric hA

/-- The finite majorant is strictly sharper than the closed geometric bound. -/
theorem finiteGeometricChargeBound_lt_closed (L : ℕ) [NeZero L]
    {A : ℝ} (hA : 0 < A) :
    finiteGeometricChargeBound L A < closedGeometricChargeBound L A :=
  geometric_grid_charge_lt hA

/-- With the period and odd count fixed, the anchored scale increases with the minimum. -/
theorem logGridScale_strictMonoOn (L : ℕ) [NeZero L] (o : ℕ) :
    StrictMonoOn (fun m => logGridScale (L := L) m o) (Set.Ioi 1) := by
  intro x hx y _ hxy
  change 1 < x at hx
  exact mul_lt_mul_of_pos_right
    (Real.log_lt_log (zero_lt_one.trans hx) hxy) (Real.exp_pos _)

theorem logGridScale_monotoneOn (L : ℕ) [NeZero L] (o : ℕ) :
    MonotoneOn (fun m => logGridScale (L := L) m o) (Set.Ioi 1) :=
  (logGridScale_strictMonoOn L o).monotoneOn

/-- The nonlinear bound decreases with the minimum when both counts are held fixed. -/
theorem nonlinearChargeBound_strictAntiOn_minimum (L : ℕ) [NeZero L] (o : ℕ) :
    StrictAntiOn (fun m => nonlinearChargeBound L (logGridScale (L := L) m o))
      (Set.Ioi 1) := by
  intro x hx y hy hxy
  exact nonlinearChargeBound_strictAntiOn L (logGridScale_pos hx o)
    (logGridScale_pos hy o) (logGridScale_strictMonoOn L o hx hy hxy)

theorem finiteGeometricChargeBound_strictAntiOn_minimum (L : ℕ) [NeZero L] (o : ℕ) :
    StrictAntiOn (fun m => finiteGeometricChargeBound L (logGridScale (L := L) m o))
      (Set.Ioi 1) := by
  intro x hx y hy hxy
  exact finiteGeometricChargeBound_strictAntiOn L (logGridScale_pos hx o)
    (logGridScale_pos hy o) (logGridScale_strictMonoOn L o hx hy hxy)

theorem closedGeometricChargeBound_strictAntiOn_minimum (L : ℕ) [NeZero L] (o : ℕ) :
    StrictAntiOn (fun m => closedGeometricChargeBound L (logGridScale (L := L) m o))
      (Set.Ioi 1) := by
  intro x hx y hy hxy
  exact closedGeometricChargeBound_strictAntiOn L (logGridScale_pos hx o)
    (logGridScale_pos hy o) (logGridScale_strictMonoOn L o hx hy hxy)

private theorem minimum_lt_of_antitone_bound {B : ℝ → ℝ} {m m0 surplus : ℝ}
    (hanti : AntitoneOn B (Set.Ioi 1)) (hm0 : 1 < m0)
    (hactual : surplus < B m) (hcut : B m0 ≤ surplus) : m < m0 := by
  by_contra hn
  have hmin : m0 ≤ m := le_of_not_gt hn
  have hm : 1 < m := hm0.trans_le hmin
  have hb := hanti hm0 hm hmin
  exact (lt_irrefl surplus) (hactual.trans_le (hb.trans hcut))

namespace FullUpperCellChargeBounds

variable {L : ℕ} [NeZero L] {m m0 : ℝ} {o : ℕ}

/-- A nonlinear cutoff excludes every larger minimum at these same fixed counts. -/
theorem minimum_lt_of_nonlinear_cutoff (h : FullUpperCellChargeBounds (L := L) m o)
    (hm0 : 1 < m0)
    (hcut : nonlinearChargeBound L (logGridScale (L := L) m0 o) ≤ logGridSurplus L o) :
    m < m0 :=
  minimum_lt_of_antitone_bound (nonlinearChargeBound_strictAntiOn_minimum L o).antitoneOn
    hm0 h.nonlinear hcut

theorem minimum_lt_of_finiteGeometric_cutoff (h : FullUpperCellChargeBounds (L := L) m o)
    (hm0 : 1 < m0)
    (hcut : finiteGeometricChargeBound L (logGridScale (L := L) m0 o) ≤ logGridSurplus L o) :
    m < m0 :=
  minimum_lt_of_antitone_bound (finiteGeometricChargeBound_strictAntiOn_minimum L o).antitoneOn
    hm0 h.finite_geometric hcut

theorem minimum_lt_of_closedGeometric_cutoff (h : FullUpperCellChargeBounds (L := L) m o)
    (hm0 : 1 < m0)
    (hcut : closedGeometricChargeBound L (logGridScale (L := L) m0 o) ≤ logGridSurplus L o) :
    m < m0 :=
  minimum_lt_of_antitone_bound (closedGeometricChargeBound_strictAntiOn_minimum L o).antitoneOn
    hm0 h.closed_geometric hcut

theorem nonlinear_cutoff_excludes (h : FullUpperCellChargeBounds (L := L) m o)
    (hm0 : 1 < m0) (hmin : m0 ≤ m)
    (hcut : nonlinearChargeBound L (logGridScale (L := L) m0 o) ≤ logGridSurplus L o) :
    False :=
  (not_lt_of_ge hmin) (h.minimum_lt_of_nonlinear_cutoff hm0 hcut)

theorem closedGeometric_cutoff_excludes (h : FullUpperCellChargeBounds (L := L) m o)
    (hm0 : 1 < m0) (hmin : m0 ≤ m)
    (hcut : closedGeometricChargeBound L (logGridScale (L := L) m0 o) ≤ logGridSurplus L o) :
    False :=
  (not_lt_of_ge hmin) (h.minimum_lt_of_closedGeometric_cutoff hm0 hcut)

end FullUpperCellChargeBounds

namespace OrbitUpperChargeCertificate

/-- A symbolic nonlinear cutoff uses the counts of this same ordinary-orbit certificate. -/
theorem minimum_lt_of_nonlinear_cutoff {m M k : ℕ}
    (Q : OrbitUpperChargeCertificate m M k) {m0 : ℝ} (hm0 : 1 < m0)
    (hcut : let : NeZero Q.length := ⟨Q.length_pos.ne'⟩
      nonlinearChargeBound Q.length (logGridScale (L := Q.length) m0 Q.oddCount) ≤
        logGridSurplus Q.length Q.oddCount) : (m : ℝ) < m0 := by
  let : NeZero Q.length := ⟨Q.length_pos.ne'⟩
  exact Q.charge.minimum_lt_of_nonlinear_cutoff hm0 hcut

theorem minimum_lt_of_finiteGeometric_cutoff {m M k : ℕ}
    (Q : OrbitUpperChargeCertificate m M k) {m0 : ℝ} (hm0 : 1 < m0)
    (hcut : let : NeZero Q.length := ⟨Q.length_pos.ne'⟩
      finiteGeometricChargeBound Q.length (logGridScale (L := Q.length) m0 Q.oddCount) ≤
        logGridSurplus Q.length Q.oddCount) : (m : ℝ) < m0 := by
  let : NeZero Q.length := ⟨Q.length_pos.ne'⟩
  exact Q.charge.minimum_lt_of_finiteGeometric_cutoff hm0 hcut

theorem minimum_lt_of_closedGeometric_cutoff {m M k : ℕ}
    (Q : OrbitUpperChargeCertificate m M k) {m0 : ℝ} (hm0 : 1 < m0)
    (hcut : let : NeZero Q.length := ⟨Q.length_pos.ne'⟩
      closedGeometricChargeBound Q.length (logGridScale (L := Q.length) m0 Q.oddCount) ≤
        logGridSurplus Q.length Q.oddCount) : (m : ℝ) < m0 := by
  let : NeZero Q.length := ⟨Q.length_pos.ne'⟩
  exact Q.charge.minimum_lt_of_closedGeometric_cutoff hm0 hcut

end OrbitUpperChargeCertificate

end Problems.Juggler.CubicGrid
