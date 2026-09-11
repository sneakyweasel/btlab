import Problems.Juggler.CubicLogGrid
import Problems.Juggler.LogCells

namespace Problems.Juggler.CubicGrid

open scoped BigOperators

variable {L : ℕ}

/-- The strict upper square cell bounds the logarithmic defect by its target capacity. -/
theorem logCellDefect_lt_logEta
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o : ℕ)
    (hc : ∀ i, 1 < c i)
    (hupper : ∀ i, c i ^ (if i.val < o then 3 else 1) < (c (σ i) + 1) ^ 2)
    (i : Fin L) : logCellDefect c σ o i < LogCells.logEta (c (σ i)) := by
  have hlog := Real.log_lt_log
    (pow_pos (lt_trans zero_lt_one (hc i)) _) (hupper i)
  rw [Real.log_pow, Real.log_pow] at hlog
  have hbound : cellMultiplier o i * Real.log (c i) < Real.log (c (σ i) + 1) := by
    unfold cellMultiplier
    split_ifs with hi
    · norm_num [hi] at hlog
      linarith
    · norm_num [hi] at hlog
      linarith
  exact Real.log_lt_log
    (div_pos (mul_pos (cellMultiplier_pos o i) (Real.log_pos (hc i)))
      (Real.log_pos (hc (σ i))))
    (div_lt_div_of_pos_right hbound (Real.log_pos (hc (σ i))))

/-- Upper cells are an additional exact integer input, distinct from lower real cells. -/
theorem threshold_real_upper_power_cells
    {b o : ℕ} (c : Fin L → ℕ) (σ : Equiv.Perm (Fin L))
    (hcut : ∀ i, c i < b ^ 2 ↔ i.val < o)
    (hstep : ∀ i, c (σ i) = thresholdMap b (c i)) (j : Fin L) :
    (c j : ℝ) ^ (if j.val < o then 3 else 1) < ((c (σ j) : ℝ) + 1) ^ 2 := by
  have hcell : c j ^ (if j.val < o then 3 else 1) < (c (σ j) + 1) ^ 2 := by
    rw [hstep, thresholdMap]
    by_cases hj : j.val < o
    · rw [if_pos hj, if_pos ((hcut j).mpr hj)]
      exact Nat.lt_succ_sqrt' (c j ^ 3)
    · have hj' : ¬c j < b ^ 2 := fun h => hj ((hcut j).mp h)
      rw [if_neg hj, if_neg hj', pow_one]
      exact Nat.lt_succ_sqrt' (c j)
  exact_mod_cast hcell

/-- The unused upper capacity is the exact logarithmic distance from the upper face. -/
theorem upper_slack_identity
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o : ℕ)
    (hc : ∀ i, 1 < c i) (i : Fin L) :
    LogCells.logEta (c (σ i)) - logCellDefect c σ o i =
      Real.log (Real.log ((c (σ i) + 1) ^ 2)) -
        Real.log (Real.log (c i ^ (if i.val < o then 3 else 1))) := by
  have hx := Real.log_pos (hc i)
  have hy := Real.log_pos (hc (σ i))
  have hy1 := Real.log_pos (show 1 < c (σ i) + 1 by linarith [hc (σ i)])
  unfold LogCells.logEta logCellDefect cellMultiplier
  rw [Real.log_div (ne_of_gt hy1) (ne_of_gt hy)]
  split_ifs with hi
  · rw [Real.log_div (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) hx))
      (ne_of_gt hy), Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hy1),
      Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hx),
      Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0) (ne_of_gt hx),
      Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  · rw [Real.log_div (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hx))
      (ne_of_gt hy), Real.log_pow, pow_one]
    norm_num only [Nat.cast_ofNat]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hy1),
      Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) (ne_of_gt hx),
      Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_one]
    ring

/-- An exact upper face leaves strictly positive unused capacity. -/
theorem upper_slack_pos
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o : ℕ)
    (hc : ∀ i, 1 < c i)
    (hupper : ∀ i, c i ^ (if i.val < o then 3 else 1) < (c (σ i) + 1) ^ 2)
    (i : Fin L) :
    0 < Real.log (Real.log ((c (σ i) + 1) ^ 2)) -
      Real.log (Real.log (c i ^ (if i.val < o then 3 else 1))) := by
  rw [← upper_slack_identity c σ o hc i]
  exact sub_pos.mpr (logCellDefect_lt_logEta c σ o hc hupper i)

/-- Exact arc slack telescoping reuses the coordinate coboundary. -/
theorem upper_slack_sum_along_arc [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L) (i : Fin L) (k : ℕ) :
    (∑ j ∈ Finset.range k,
      (LogCells.logEta (c (σ ((σ ^ j) i))) - logCellDefect c σ o ((σ ^ j) i))) =
      (∑ j ∈ Finset.range k, LogCells.logEta (c (σ ((σ ^ j) i)))) -
        ((k : ℝ) * (logGridSurplus L o / (L : ℝ)) +
          logGridError c (c 0) i - logGridError c (c 0) ((σ ^ k) i)) := by
  rw [Finset.sum_sub_distrib, defect_sum_along_arc σ _ _ _
    (logGrid_coboundary c σ o e (c 0) hc (hc 0) hlen hrank)]

/-- A state above the logarithmic envelope has the corresponding reciprocal charge bound. -/
theorem inv_log_charge_le {x A t : ℝ} (hx : 1 < x) (hA : 0 < A)
    (hlog : A * Real.exp t ≤ Real.log x) :
    1 / (x * Real.log x) ≤ Real.exp (-(A * Real.exp t) - t) / A := by
  have hu := mul_pos hA (Real.exp_pos t)
  have hexp : Real.exp (A * Real.exp t) ≤ x := by
    simpa only [Real.exp_log (lt_trans zero_lt_one hx)] using Real.exp_le_exp.mpr hlog
  have hp : (A * Real.exp t) * Real.exp (A * Real.exp t) ≤ x * Real.log x := by
    have hh := mul_le_mul hlog hexp (Real.exp_pos _).le (Real.log_pos hx).le
    simpa only [mul_comm] using hh
  calc
    1 / (x * Real.log x) ≤ 1 / ((A * Real.exp t) * Real.exp (A * Real.exp t)) :=
      one_div_le_one_div_of_le (mul_pos hu (Real.exp_pos _)) hp
    _ = Real.exp (-(A * Real.exp t) - t) / A := by
      rw [Real.exp_sub, Real.exp_neg]
      field_simp

/-- Linearizing only the inner exponential produces a finite geometric majorant. -/
theorem nonlinear_charge_le_geometric {A t : ℝ} (hA : 0 < A) :
    Real.exp (-(A * Real.exp t) - t) / A ≤
      Real.exp (-A) / A * Real.exp (-(A + 1) * t) := by
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp t) hA.le
  calc
    Real.exp (-(A * Real.exp t) - t) / A ≤
        Real.exp (-A - (A + 1) * t) / A := by
      apply div_le_div_of_nonneg_right _ hA.le
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = Real.exp (-A) / A * Real.exp (-(A + 1) * t) := by
      rw [show -A - (A + 1) * t = -A + (-(A + 1) * t) by ring, Real.exp_add]
      ring

/-- A finite exponential sum is strictly below the elementary geometric envelope. -/
theorem finite_exp_sum_lt (n : ℕ) {z : ℝ} (hz : 0 < z) :
    (∑ i ∈ Finset.range n, Real.exp (-(i : ℝ) * z)) < 1 + 1 / z := by
  let r := Real.exp (-z)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by simpa [r] using Real.exp_lt_one_iff.mpr (neg_neg_of_pos hz)
  have hgeom : (1 - r) * (∑ i ∈ Finset.range n, r ^ i) = 1 - r ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith
  have hs : (∑ i ∈ Finset.range n, r ^ i) < 1 / (1 - r) := by
    apply (lt_div_iff₀ (sub_pos.mpr hr1)).mpr
    have hp := pow_pos hr n
    nlinarith
  have he : z < Real.exp z - 1 := by
    have hh := Real.add_one_lt_exp (ne_of_gt hz)
    linarith
  have hepos : 0 < Real.exp z - 1 := hz.trans he
  have hid : 1 / (1 - r) = 1 + 1 / (Real.exp z - 1) := by
    dsimp [r]
    rw [Real.exp_neg]
    field_simp
    ring
  have hlast : 1 / (1 - r) < 1 + 1 / z := by
    rw [hid]
    linarith [one_div_lt_one_div_of_lt hz he]
  have hconvert : ∀ i : ℕ, Real.exp (-(i : ℝ) * z) = r ^ i := by
    intro i
    rw [show -(i : ℝ) * z = (i : ℝ) * (-z) by ring, Real.exp_nat_mul]
  simpa only [hconvert] using hs.trans hlast

/-- Exact upper cells give a strict total charge bound on the same state permutation. -/
theorem logCellDefect_sum_lt_inv_log [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L)
    (hupper : ∀ i, c i ^ (if i.val < o then 3 else 1) < (c (σ i) + 1) ^ 2) :
    logGridSurplus L o < ∑ i, 1 / (c i * Real.log (c i)) := by
  have hpoint : ∀ i, logCellDefect c σ o i < 1 / (c (σ i) * Real.log (c (σ i))) :=
    fun i => (logCellDefect_lt_logEta c σ o hc hupper i).trans
      (LogCells.logEta_lt_inv (hc (σ i)))
  have hs : (∑ i, logCellDefect c σ o i) <
      ∑ i, 1 / (c (σ i) * Real.log (c (σ i))) :=
    Finset.sum_lt_sum (fun i _ => (hpoint i).le) ⟨0, Finset.mem_univ _, hpoint 0⟩
  rw [logCellDefect_sum c σ o e hc hlen hrank] at hs
  have hperm := Equiv.sum_comp σ (fun i => 1 / (c i * Real.log (c i)))
  rw [hperm] at hs
  exact hs

/-- The grid supplies a finite, unlinearized upper-cell charge majorant. -/
theorem inv_log_sum_le_grid [NeZero L]
    (c : Fin L → ℝ) (o : ℕ) (hc : ∀ i, 1 < c i)
    (hgrid : ∀ i, |logGridError c (c 0) i| ≤
      (1 - 1 / (L : ℝ)) * logGridSurplus L o) :
    (∑ i, 1 / (c i * Real.log (c i))) ≤
      ∑ i : Fin L,
        Real.exp (-(logGridScale (L := L) (c 0) o *
          Real.exp ((i.val : ℝ) * Real.log 3 / (L : ℝ))) -
          (i.val : ℝ) * Real.log 3 / (L : ℝ)) / logGridScale (L := L) (c 0) o := by
  apply Finset.sum_le_sum
  intro i _
  exact inv_log_charge_le (hc i) (logGridScale_pos (hc 0) o)
    (log_lower_of_loglog_bound (hc i) (hc 0) (hgrid i))

/-- The finite unlinearized charge is bounded by the finite geometric charge. -/
theorem grid_charge_le_geometric [NeZero L] {A : ℝ} (hA : 0 < A) :
    (∑ i : Fin L,
      Real.exp (-(A * Real.exp ((i.val : ℝ) * Real.log 3 / (L : ℝ))) -
        (i.val : ℝ) * Real.log 3 / (L : ℝ)) / A) ≤
      Real.exp (-A) / A *
        ∑ i : Fin L, Real.exp (-(A + 1) * ((i.val : ℝ) * Real.log 3 / (L : ℝ))) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => nonlinear_charge_le_geometric hA)

/-- Strict finite-to-closed geometric charge comparison. -/
theorem geometric_grid_charge_lt [NeZero L] {A : ℝ} (hA : 0 < A) :
    Real.exp (-A) / A *
        (∑ i : Fin L, Real.exp (-(A + 1) * ((i.val : ℝ) * Real.log 3 / (L : ℝ)))) <
      Real.exp (-A) / A * (1 + (L : ℝ) / (Real.log 3 * (A + 1))) := by
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (Nat.pos_of_neZero L)
  have hT : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  let z := Real.log 3 * (A + 1) / (L : ℝ)
  have hz : 0 < z := div_pos (mul_pos hT (by linarith)) hL
  have hs := finite_exp_sum_lt L hz
  rw [← Fin.sum_univ_eq_sum_range] at hs
  apply mul_lt_mul_of_pos_left _ (div_pos (Real.exp_pos _) hA)
  have hsum : (∑ i : Fin L,
      Real.exp (-(A + 1) * ((i.val : ℝ) * Real.log 3 / (L : ℝ)))) =
      ∑ i : Fin L, Real.exp (-(i.val : ℝ) * z) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    dsimp [z]
    ring
  have hright : 1 + (L : ℝ) / (Real.log 3 * (A + 1)) = 1 + 1 / z := by
    dsimp [z]
    field_simp
  rw [hsum, hright]
  exact hs

/-- The exact finite nonlinear charge, before linearizing the inner exponential. -/
theorem power_cells_nonlinear_charge [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L)
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hlower : ∀ i, c (σ i) ^ 2 ≤ c i ^ (if i.val < o then 3 else 1))
    (hupper : ∀ i, c i ^ (if i.val < o then 3 else 1) < (c (σ i) + 1) ^ 2) :
    let A := logGridScale (L := L) (c 0) o
    logGridSurplus L o < ∑ i : Fin L,
      Real.exp (-(A * Real.exp ((i.val : ℝ) * Real.log 3 / (L : ℝ))) -
        (i.val : ℝ) * Real.log 3 / (L : ℝ)) / A := by
  have hgrid := log_grid_of_power_cells c σ o e hc hlen hrank hcycle hlower
  exact (logCellDefect_sum_lt_inv_log c σ o e hc hlen hrank hupper).trans_le
    (inv_log_sum_le_grid c o hc hgrid)

/-- The exact finite and closed upper-cell charges from primitive power-cell data. -/
theorem power_cells_grid_charge [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L)
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hlower : ∀ i, c (σ i) ^ 2 ≤ c i ^ (if i.val < o then 3 else 1))
    (hupper : ∀ i, c i ^ (if i.val < o then 3 else 1) < (c (σ i) + 1) ^ 2) :
    let A := logGridScale (L := L) (c 0) o
    0 < A ∧ 0 < logGridSurplus L o ∧
      logGridSurplus L o < Real.exp (-A) / A *
        (∑ i : Fin L, Real.exp (-(A + 1) * ((i.val : ℝ) * Real.log 3 / (L : ℝ)))) ∧
      logGridSurplus L o < Real.exp (-A) / A *
        (1 + (L : ℝ) / (Real.log 3 * (A + 1))) := by
  dsimp only
  have hA := logGridScale_pos (L := L) (hc 0) o
  have hfinite := (power_cells_nonlinear_charge c σ o e hc hlen hrank hcycle
    hlower hupper).trans_le (grid_charge_le_geometric hA)
  exact ⟨hA, logGridSurplus_pos_of_power_cells c σ o e hc hlen hrank hlower,
    hfinite, hfinite.trans (geometric_grid_charge_lt hA)⟩

/-- A denominator-free exact corollary of the closed charge. -/
theorem power_cells_scaled_charge [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L)
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hlower : ∀ i, c (σ i) ^ 2 ≤ c i ^ (if i.val < o then 3 else 1))
    (hupper : ∀ i, c i ^ (if i.val < o then 3 else 1) < (c (σ i) + 1) ^ 2) :
    let A := logGridScale (L := L) (c 0) o
    Real.exp A * A * (A + 1) * logGridSurplus L o < A + 1 + (L : ℝ) / Real.log 3 := by
  let A := logGridScale (L := L) (c 0) o
  have hA : 0 < A := logGridScale_pos (hc 0) o
  have hb := (power_cells_grid_charge c σ o e hc hlen hrank hcycle hlower hupper).2.2.2
  change logGridSurplus L o < Real.exp (-A) / A *
    (1 + (L : ℝ) / (Real.log 3 * (A + 1))) at hb
  have hp : 0 < Real.exp A * A * (A + 1) :=
    mul_pos (mul_pos (Real.exp_pos _) hA) (by linarith)
  have hh := mul_lt_mul_of_pos_left hb hp
  change Real.exp A * A * (A + 1) * logGridSurplus L o < _
  have hid : Real.exp A * A * (A + 1) *
      (Real.exp (-A) / A * (1 + (L : ℝ) / (Real.log 3 * (A + 1)))) =
      A + 1 + (L : ℝ) / Real.log 3 := by
    rw [Real.exp_neg]
    field_simp
  rw [hid] at hh
  exact hh

/-- Exact finite and closed geometric charge conclusions at the anchored minimum. -/
def UpperCellChargeBounds [NeZero L] (m : ℝ) (o : ℕ) : Prop :=
  let A := logGridScale (L := L) m o
  0 < A ∧ 0 < logGridSurplus L o ∧
    logGridSurplus L o < Real.exp (-A) / A *
      (∑ i : Fin L, Real.exp (-(A + 1) * ((i.val : ℝ) * Real.log 3 / (L : ℝ)))) ∧
    logGridSurplus L o < Real.exp (-A) / A *
      (1 + (L : ℝ) / (Real.log 3 * (A + 1)))

/-- The nonlinear charge together with the existing geometric charge interface. -/
structure FullUpperCellChargeBounds [NeZero L] (m : ℝ) (o : ℕ) : Prop where
  geometric : UpperCellChargeBounds (L := L) m o
  nonlinear :
    let A := logGridScale (L := L) m o
    logGridSurplus L o < ∑ i : Fin L,
      Real.exp (-(A * Real.exp ((i.val : ℝ) * Real.log 3 / (L : ℝ))) -
        (i.val : ℝ) * Real.log 3 / (L : ℝ)) / A

namespace FullUpperCellChargeBounds

variable [NeZero L] {m : ℝ} {o : ℕ} (h : FullUpperCellChargeBounds (L := L) m o)

include h

theorem scale_pos : 0 < logGridScale (L := L) m o := h.geometric.1

theorem surplus_pos : 0 < logGridSurplus L o := h.geometric.2.1

theorem finite_geometric :
    let A := logGridScale (L := L) m o
    logGridSurplus L o < Real.exp (-A) / A *
      (∑ i : Fin L, Real.exp (-(A + 1) * ((i.val : ℝ) * Real.log 3 / (L : ℝ)))) :=
  h.geometric.2.2.1

theorem closed_geometric :
    let A := logGridScale (L := L) m o
    logGridSurplus L o < Real.exp (-A) / A *
      (1 + (L : ℝ) / (Real.log 3 * (A + 1))) :=
  h.geometric.2.2.2

end FullUpperCellChargeBounds

/-- One power-cell certificate retains the nonlinear and both geometric charges. -/
theorem power_cells_full_charge [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L)
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hlower : ∀ i, c (σ i) ^ 2 ≤ c i ^ (if i.val < o then 3 else 1))
    (hupper : ∀ i, c i ^ (if i.val < o then 3 else 1) < (c (σ i) + 1) ^ 2) :
    FullUpperCellChargeBounds (L := L) (c 0) o :=
  ⟨power_cells_grid_charge c σ o e hc hlen hrank hcycle hlower hupper,
    power_cells_nonlinear_charge c σ o e hc hlen hrank hcycle hlower hupper⟩

/-- Full exact threshold cells retain the grid and all three upper-charge inequalities. -/
theorem threshold_cycle_full_upper_charge [NeZero L]
    {b : ℕ} (hb : 1 < b) (c : Fin L → ℕ) (hc : StrictMono c)
    (σ : Equiv.Perm (Fin L)) (hband : ∀ i, InCubicBand b (c i))
    (hstep : ∀ i, c (σ i) = thresholdMap b (c i))
    (hconnected : ∀ i j, ∃ k : ℕ, (thresholdMap b)^[k] (c i) = c j) :
    ∃ o ≤ L, (Finset.univ.filter (fun i => c i < b ^ 2)).card = o ∧
      RealizedGridBounds (fun i => (c i : ℝ)) o ∧
      FullUpperCellChargeBounds (L := L) (c 0) o := by
  obtain ⟨o, ho, hcut, hcard, hrank⟩ := threshold_sorted_rotation c hc σ hband hstep
  have hpos : ∀ i, (1 : ℝ) < c i := by
    intro i
    exact_mod_cast hb.trans_le (hband i).1
  have hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))) := by
    simpa using rank_isCycleOn_of_connected c hc.injective σ (thresholdMap b) hstep hconnected
  have hlen : L = o + (L - o) := by omega
  have hlower := threshold_real_power_cells c σ hcut hstep
  refine ⟨o, ho, hcard, ?_, ?_⟩
  · apply realized_grid_bounds_of_power_cells (fun i => (c i : ℝ)) σ o (L - o)
      hpos ?_ ?_ hlen hrank hcycle hlower
    · intro i j hij
      change (c i : ℝ) < (c j : ℝ)
      exact_mod_cast hc hij
    · intro i
      have h : c i < c 0 ^ 3 :=
        (hband i).2.trans_le (Nat.pow_le_pow_left (hband 0).1 3)
      exact_mod_cast h
  · exact power_cells_full_charge (fun i => (c i : ℝ)) σ o (L - o)
      hpos hlen hrank hcycle hlower (threshold_real_upper_power_cells c σ hcut hstep)

/-- Compatibility projection to the original threshold charge conclusion. -/
theorem threshold_cycle_upper_charge [NeZero L]
    {b : ℕ} (hb : 1 < b) (c : Fin L → ℕ) (hc : StrictMono c)
    (σ : Equiv.Perm (Fin L)) (hband : ∀ i, InCubicBand b (c i))
    (hstep : ∀ i, c (σ i) = thresholdMap b (c i))
    (hconnected : ∀ i j, ∃ k : ℕ, (thresholdMap b)^[k] (c i) = c j) :
    ∃ o ≤ L, (Finset.univ.filter (fun i => c i < b ^ 2)).card = o ∧
      RealizedGridBounds (fun i => (c i : ℝ)) o ∧
      UpperCellChargeBounds (L := L) (c 0) o := by
  obtain ⟨o, ho, hcard, hgrid, hcharge⟩ :=
    threshold_cycle_full_upper_charge hb c hc σ hband hstep hconnected
  exact ⟨o, ho, hcard, hgrid, hcharge.geometric⟩

/-- Actual closure supplies the full charge certificate with the true odd count. -/
theorem cubicBand_cycle_full_upper_charge [NeZero L]
    {m : ℕ} (hm : 1 < m) (c : Fin L → ℕ) (hc : StrictMono c)
    (σ : Equiv.Perm (Fin L)) (hband : ∀ i, InCubicBand m (c i))
    (hstep : ∀ i, c (σ i) = floorPower (c i))
    (hconnected : ∀ i j, ∃ k : ℕ, floorPower^[k] (c i) = c j) :
    ∃ o ≤ L, (Finset.univ.filter (fun i => c i % 2 = 1)).card = o ∧
      RealizedGridBounds (fun i => (c i : ℝ)) o ∧
      FullUpperCellChargeBounds (L := L) (c 0) o := by
  have hthreshold : ∀ i, c (σ i) = thresholdMap m (c i) := by
    intro i
    rw [hstep]
    apply cubicBand_floorPower_eq_threshold (hband i)
    rw [← hstep]
    exact hband (σ i)
  have hconj (k : ℕ) (i : Fin L) :
      (thresholdMap m)^[k] (c i) = c (σ^[k] i) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih, ← hthreshold]
  have hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))) := by
    simpa using rank_isCycleOn_of_connected c hc.injective σ floorPower hstep hconnected
  have hthreshold_connected : ∀ i j, ∃ k : ℕ, (thresholdMap m)^[k] (c i) = c j := by
    intro i j
    obtain ⟨k, _, hk⟩ := hcycle.exists_pow_eq (a := i) (b := j)
      (Finset.mem_univ _) (Finset.mem_univ _)
    exact ⟨k, by rw [hconj, σ.iterate_eq_pow, hk]⟩
  obtain ⟨o, ho, hcard, hgrid, hcharge⟩ :=
    threshold_cycle_full_upper_charge hm c hc σ hband hthreshold hthreshold_connected
  refine ⟨o, ho, ?_, hgrid, hcharge⟩
  have hpar : ∀ i, c i % 2 = 1 ↔ c i < m ^ 2 := by
    intro i
    apply cubicBand_parity_iff (hband i)
    rw [← hstep]
    exact hband (σ i)
  simpa only [hpar] using hcard

/-- Compatibility projection to the original actual-cycle charge conclusion. -/
theorem cubicBand_cycle_upper_charge [NeZero L]
    {m : ℕ} (hm : 1 < m) (c : Fin L → ℕ) (hc : StrictMono c)
    (σ : Equiv.Perm (Fin L)) (hband : ∀ i, InCubicBand m (c i))
    (hstep : ∀ i, c (σ i) = floorPower (c i))
    (hconnected : ∀ i j, ∃ k : ℕ, floorPower^[k] (c i) = c j) :
    ∃ o ≤ L, (Finset.univ.filter (fun i => c i % 2 = 1)).card = o ∧
      RealizedGridBounds (fun i => (c i : ℝ)) o ∧
      UpperCellChargeBounds (L := L) (c 0) o := by
  obtain ⟨o, ho, hcard, hgrid, hcharge⟩ :=
    cubicBand_cycle_full_upper_charge hm c hc σ hband hstep hconnected
  exact ⟨o, ho, hcard, hgrid, hcharge.geometric⟩

end Problems.Juggler.CubicGrid
