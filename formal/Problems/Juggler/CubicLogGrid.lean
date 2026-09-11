import Problems.Juggler.CubicGrid
import Problems.Juggler.CubicBand
import Problems.Juggler.CubicRotation
import Mathlib.Logic.Equiv.Fin.Rotate

/-!+# Power-cell realization of the uniform log-log grid

The finite-permutation estimates are instantiated with the actual logarithms
of positive states. Square-cell inequalities supply nonnegative defects;
rank rotation supplies the lifted coordinate equation. No grid bound is
assumed. This does not settle the parity of a complete threshold cycle.
-/

namespace Problems.Juggler

open scoped BigOperators

namespace CubicGrid

variable {L : ℕ}

noncomputable def logCoordinate (c : Fin L → ℝ) (m : ℝ) (i : Fin L) : ℝ :=
  Real.log (Real.log (c i) / Real.log m)

noncomputable def logGridError (c : Fin L → ℝ) (m : ℝ) (i : Fin L) : ℝ :=
  logCoordinate c m i - (i.val : ℝ) * Real.log 3 / (L : ℝ)

noncomputable def logGridSurplus (L o : ℕ) : ℝ :=
  (o : ℝ) * Real.log 3 - (L : ℝ) * Real.log 2

noncomputable def cellMultiplier (o : ℕ) (i : Fin L) : ℝ :=
  if i.val < o then 3 / 2 else 1 / 2

noncomputable def logCellDefect (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L))
    (o : ℕ) (i : Fin L) : ℝ :=
  Real.log (cellMultiplier o i * Real.log (c i) / Real.log (c (σ i)))

/-- The adjacent gap includes the log 3 seam of the periodic lift. -/
noncomputable def liftedLogGap [NeZero L] (c : Fin L → ℝ) (i : Fin L) : ℝ :=
  logCoordinate c (c 0) (finRotate L i) - logCoordinate c (c 0) i +
    if i.val + 1 < L then 0 else Real.log 3

theorem cellMultiplier_pos (o : ℕ) (i : Fin L) : 0 < cellMultiplier o i := by
  unfold cellMultiplier
  split_ifs <;> norm_num

/-- This exact identity is where the genuine log-log coordinates enter. -/
theorem log_defect_identity {p x y m : ℝ}
    (hp : 0 < p) (hx : 1 < x) (hy : 1 < y) (hm : 1 < m) :
    Real.log (Real.log y / Real.log m) - Real.log (Real.log x / Real.log m) =
      Real.log p - Real.log (p * Real.log x / Real.log y) := by
  have hlx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hly : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have hlm : Real.log m ≠ 0 := ne_of_gt (Real.log_pos hm)
  rw [Real.log_div hly hlm, Real.log_div hlx hlm,
    Real.log_div (mul_ne_zero (ne_of_gt hp) hlx) hly,
    Real.log_mul (ne_of_gt hp) hlx]
  ring

/-- The lower square-cell inequality is enough for the one-step logarithmic loss sign. -/
theorem logCellDefect_nonneg
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o : ℕ)
    (hc : ∀ i, 1 < c i)
    (hcell : ∀ i, c (σ i) ^ 2 ≤ c i ^ (if i.val < o then 3 else 1))
    (i : Fin L) : 0 ≤ logCellDefect c σ o i := by
  have hlog := Real.log_le_log (sq_pos_of_pos (lt_trans zero_lt_one (hc (σ i)))) (hcell i)
  rw [Real.log_pow, Real.log_pow] at hlog
  have hbound : Real.log (c (σ i)) ≤ cellMultiplier o i * Real.log (c i) := by
    unfold cellMultiplier
    split_ifs with hi
    · norm_num [hi] at hlog
      linarith
    · norm_num [hi] at hlog
      linarith
  apply Real.log_nonneg
  exact (one_le_div (Real.log_pos (hc (σ i)))).mpr hbound

/-- The modular rank equation has the expected single-wrap form in real coordinates. -/
theorem rank_rotation_real
    (σ : Equiv.Perm (Fin L)) (o e : ℕ) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L) (i : Fin L) :
    ((σ i).val : ℝ) - (i.val : ℝ) =
      (e : ℝ) - if i.val < o then 0 else (L : ℝ) := by
  by_cases hi : i.val < o
  · have hh : (σ i).val = i.val + e := by
      rw [hrank, Nat.mod_eq_of_lt (by omega)]
    rw [if_pos hi]
    have hh' : ((σ i).val : ℝ) = (i.val : ℝ) + (e : ℝ) := by exact_mod_cast hh
    linarith
  · have hh : (σ i).val = i.val + e - L := by
      rw [hrank, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [if_neg hi]
    have hle : L ≤ i.val + e := by omega
    have hh' : ((σ i).val : ℝ) = (i.val : ℝ) + (e : ℝ) - (L : ℝ) := by
      exact_mod_cast hh
    linarith

/-- Exact power cells and rank rotation yield the coordinate coboundary. -/
theorem logGrid_coboundary
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ) (m : ℝ)
    (hc : ∀ i, 1 < c i) (hm : 1 < m) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L) (i : Fin L) :
    logGridError c m (σ i) - logGridError c m i =
      logGridSurplus L o / (L : ℝ) - logCellDefect c σ o i := by
  have hL : (L : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt))
  have hlen' : (L : ℝ) = (o : ℝ) + (e : ℝ) := by exact_mod_cast hlen
  have hid := log_defect_identity (cellMultiplier_pos o i) (hc i) (hc (σ i)) hm
  have hr := rank_rotation_real σ o e hlen hrank i
  have hmul : Real.log (cellMultiplier o i) =
      Real.log 3 - Real.log 2 - if i.val < o then 0 else Real.log 3 := by
    unfold cellMultiplier
    split_ifs <;> rw [Real.log_div (by norm_num) (by norm_num)] <;> simp
  unfold logGridError logCoordinate logGridSurplus logCellDefect
  change Real.log (Real.log (c (σ i)) / Real.log m) -
      (↑(σ i).val * Real.log 3 / ↑L) -
      (Real.log (Real.log (c i) / Real.log m) - ↑i.val * Real.log 3 / ↑L) = _
  rw [show Real.log (Real.log (c (σ i)) / Real.log m) =
      Real.log (Real.log (c i) / Real.log m) + Real.log (cellMultiplier o i) -
        Real.log (cellMultiplier o i * Real.log (c i) / Real.log (c (σ i))) by linarith [hid]]
  rw [hmul]
  have hrr := congrArg (fun r : ℝ => r * Real.log 3) hr
  have hll := congrArg (fun r : ℝ => r * Real.log 3) hlen'
  split_ifs at hr hrr ⊢ with hi <;> field_simp <;> nlinarith

/-- The total loss is obtained by permutation summation of the exact coordinates. -/
theorem logCellDefect_sum [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L) :
    ∑ i, logCellDefect c σ o i = logGridSurplus L o :=
  defect_sum_of_coboundary σ _ _ _ (Nat.pos_of_neZero L)
    (logGrid_coboundary c σ o e (c 0) hc (hc 0) hlen hrank)

/-- A realized power-cell cycle satisfies the claimed sharp log-log grid at every rank. -/
theorem log_grid_of_power_cells [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L)
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hcell : ∀ i, c (σ i) ^ 2 ≤ c i ^ (if i.val < o then 3 else 1))
    (i : Fin L) :
    |Real.log (Real.log (c i) / Real.log (c 0)) -
      (i.val : ℝ) * Real.log 3 / (L : ℝ)| ≤
        (1 - 1 / (L : ℝ)) * logGridSurplus L o := by
  let w := logGridError c (c 0)
  let δ := logCellDefect c σ o
  have hδ : ∀ i, 0 ≤ δ i := logCellDefect_nonneg c σ o hc hcell
  have hw : ∀ i, w (σ i) - w i = logGridSurplus L o / (L : ℝ) - δ i :=
    logGrid_coboundary c σ o e (c 0) hc (hc 0) hlen hrank
  have hsum : ∑ i, δ i = logGridSurplus L o :=
    logCellDefect_sum c σ o e hc hlen hrank
  have hanchor : w 0 = 0 := by
    simp [w, logGridError, logCoordinate, ne_of_gt (Real.log_pos (hc 0))]
  exact defect_grid_at_anchor σ hcycle w δ _ hδ hsum hw 0 hanchor i

/-- Positive powers of two and powers of three have different parity. -/
theorem logGridSurplus_ne_zero (o : ℕ) (hL : 0 < L) : logGridSurplus L o ≠ 0 := by
  intro hz
  have hlogs : Real.log ((3 : ℝ) ^ o) = Real.log ((2 : ℝ) ^ L) := by
    rw [Real.log_pow, Real.log_pow]
    unfold logGridSurplus at hz
    linarith
  have heq : (3 : ℝ) ^ o = (2 : ℝ) ^ L :=
    Real.log_injOn_pos (pow_pos (by norm_num : (0 : ℝ) < 3) o)
      (pow_pos (by norm_num : (0 : ℝ) < 2) L) hlogs
  have hnat : (3 : ℕ) ^ o = (2 : ℕ) ^ L := by exact_mod_cast heq
  have hmod := congrArg (fun n : ℕ => n % 2) hnat
  norm_num [Nat.pow_mod, Nat.ne_of_gt hL] at hmod

/-- A realized cycle has strictly positive logarithmic surplus. -/
theorem logGridSurplus_pos_of_power_cells [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L)
    (hcell : ∀ i, c (σ i) ^ 2 ≤ c i ^ (if i.val < o then 3 else 1)) :
    0 < logGridSurplus L o := by
  have hsum := logCellDefect_sum c σ o e hc hlen hrank
  have hnonneg : 0 ≤ logGridSurplus L o := by
    rw [← hsum]
    exact Finset.sum_nonneg (fun i _ => logCellDefect_nonneg c σ o hc hcell i)
  exact lt_of_le_of_ne hnonneg (Ne.symm (logGridSurplus_ne_zero o (Nat.pos_of_neZero L)))

theorem finRotate_val [NeZero L] (i : Fin L) :
    (finRotate L i).val = (i.val + 1) % L := by
  rw [finRotate_apply]
  simp [Fin.val_add, Nat.add_mod]

/-- Any rank translation commutes with the adjacent-rank shift. -/
theorem rank_commute_finRotate [NeZero L]
    (σ : Equiv.Perm (Fin L)) (e : ℕ)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L) :
    Function.Commute σ (finRotate L) :=
  rankRotation_commute_adjacent σ hrank

/-- The seam definition agrees with the centered-error representation of a gap. -/
theorem liftedLogGap_eq_error [NeZero L] (c : Fin L → ℝ) (i : Fin L) :
    liftedLogGap c i =
      logGridError c (c 0) (finRotate L i) - logGridError c (c 0) i +
        Real.log 3 / (L : ℝ) := by
  have hL : (L : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (Nat.pos_of_neZero L))
  have hr := rank_rotation_real (finRotate L) (L - 1) 1 (by have := Nat.pos_of_neZero L; omega)
    (finRotate_val (L := L)) i
  have hrr := congrArg (fun r : ℝ => r * Real.log 3) hr
  unfold liftedLogGap logGridError
  by_cases hi : i.val + 1 < L
  · have hi' : i.val < L - 1 := by omega
    rw [if_pos hi'] at hrr
    rw [if_pos hi]
    norm_num only [Nat.cast_one] at hrr
    field_simp
    nlinarith
  · have hi' : ¬i.val < L - 1 := by omega
    rw [if_neg hi'] at hrr
    rw [if_neg hi]
    norm_num only [Nat.cast_one] at hrr
    field_simp
    nlinarith

/-- Sorted states below the cubic height make even the seam gap strictly positive. -/
theorem liftedLogGap_pos [NeZero L]
    (c : Fin L → ℝ) (hc : ∀ i, 1 < c i) (hsorted : StrictMono c)
    (hheight : ∀ i, c i < c 0 ^ 3) (i : Fin L) : 0 < liftedLogGap c i := by
  have hlm := Real.log_pos (hc 0)
  have hlx := Real.log_pos (hc i)
  have hzero : logCoordinate c (c 0) 0 = 0 := by
    simp [logCoordinate, ne_of_gt hlm]
  by_cases hi : i.val + 1 < L
  · have hnext : i < finRotate L i := by
      rw [Fin.lt_def, finRotate_val, Nat.mod_eq_of_lt hi]
      omega
    have hlog := Real.log_lt_log (lt_trans zero_lt_one (hc i)) (hsorted hnext)
    have hdiv := div_lt_div_of_pos_right hlog hlm
    have hcoord := Real.log_lt_log (div_pos hlx hlm) hdiv
    unfold liftedLogGap logCoordinate
    rw [if_pos hi]
    linarith
  · have hlast : i.val + 1 = L := by omega
    have hnext : finRotate L i = 0 := by
      apply Fin.ext
      rw [finRotate_val, hlast, Nat.mod_self, Fin.val_zero]
    have hlog := Real.log_lt_log (lt_trans zero_lt_one (hc i)) (hheight i)
    rw [Real.log_pow] at hlog
    have hdiv : Real.log (c i) / Real.log (c 0) < 3 := (div_lt_iff₀ hlm).mpr (by simpa [mul_comm] using hlog)
    have hcoord := Real.log_lt_log (div_pos hlx hlm) hdiv
    unfold liftedLogGap
    rw [if_neg hi, hnext, hzero]
    unfold logCoordinate
    linarith
/-- Both claimed adjacent-gap estimates hold for realized power-cell cycles. -/
theorem log_gap_bounds_of_power_cells [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L)
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hcell : ∀ i, c (σ i) ^ 2 ≤ c i ^ (if i.val < o then 3 else 1))
    (i j : Fin L) :
    |liftedLogGap c j - liftedLogGap c i| ≤ logGridSurplus L o ∧
      |liftedLogGap c i - Real.log 3 / (L : ℝ)| ≤
        (1 - 1 / (L : ℝ)) * logGridSurplus L o := by
  let w := logGridError c (c 0)
  let δ := logCellDefect c σ o
  have hδ : ∀ i, 0 ≤ δ i := logCellDefect_nonneg c σ o hc hcell
  have hw : ∀ i, w (σ i) - w i = logGridSurplus L o / (L : ℝ) - δ i :=
    logGrid_coboundary c σ o e (c 0) hc (hc 0) hlen hrank
  have hsum : ∑ i, δ i = logGridSurplus L o :=
    logCellDefect_sum c σ o e hc hlen hrank
  simpa only [liftedLogGap_eq_error] using
    adjacent_gap_bounds σ hcycle (finRotate L) (rank_commute_finRotate σ e hrank)
      w δ _ (Real.log 3 / (L : ℝ)) hδ hsum hw i j

/-- Exact integer successors supply the real square-cell inequalities without a numerical oracle. -/
theorem threshold_real_power_cells
    {b o : ℕ} (c : Fin L → ℕ) (σ : Equiv.Perm (Fin L))
    (hcut : ∀ i, c i < b ^ 2 ↔ i.val < o)
    (hstep : ∀ i, c (σ i) = thresholdMap b (c i)) (j : Fin L) :
    (c (σ j) : ℝ) ^ 2 ≤ (c j : ℝ) ^ (if j.val < o then 3 else 1) := by
  have hcell : c (σ j) ^ 2 ≤ c j ^ (if j.val < o then 3 else 1) := by
    rw [hstep, thresholdMap]
    by_cases hj : j.val < o
    · rw [if_pos hj, if_pos ((hcut j).mpr hj)]
      simpa [pow_two] using Nat.sqrt_le (c j ^ 3)
    · have hj' : ¬c j < b ^ 2 := fun h => hj ((hcut j).mp h)
      rw [if_neg hj, if_neg hj', pow_one]
      simpa [pow_two] using Nat.sqrt_le (c j)
  exact_mod_cast hcell

/-- The universal grid bound specialized to an exact threshold cycle. -/
theorem threshold_log_grid [NeZero L]
    {b o : ℕ} (hb : 3 ≤ b) (ho : o ≤ L)
    (c : Fin L → ℕ) (hc : StrictMono c) (σ : Equiv.Perm (Fin L))
    (hband : ∀ i, InCubicBand b (c i))
    (hcut : ∀ i, c i < b ^ 2 ↔ i.val < o)
    (hstep : ∀ i, c (σ i) = thresholdMap b (c i))
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (i : Fin L) :
    |Real.log (Real.log (c i) / Real.log (c 0)) -
      (i.val : ℝ) * Real.log 3 / (L : ℝ)| ≤
        (1 - 1 / (L : ℝ)) * logGridSurplus L o := by
  apply log_grid_of_power_cells (fun i => (c i : ℝ)) σ o (L - o)
  · intro j
    have h : 1 < c j := by have := (hband j).1; omega
    exact_mod_cast h
  · omega
  · exact threshold_rank_rotation ho c hc σ hband hcut hstep
  · exact hcycle
  · exact threshold_real_power_cells c σ hcut hstep

/-- The same bound holds for the actual map under cubic-band closure. -/
theorem cubicBand_log_grid [NeZero L]
    {m o : ℕ} (hm : 3 ≤ m) (ho : o ≤ L)
    (c : Fin L → ℕ) (hc : StrictMono c) (σ : Equiv.Perm (Fin L))
    (hband : ∀ i, InCubicBand m (c i))
    (hcut : ∀ i, c i < m ^ 2 ↔ i.val < o)
    (hstep : ∀ i, c (σ i) = floorPower (c i))
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (i : Fin L) :
    |Real.log (Real.log (c i) / Real.log (c 0)) -
      (i.val : ℝ) * Real.log 3 / (L : ℝ)| ≤
        (1 - 1 / (L : ℝ)) * logGridSurplus L o := by
  apply threshold_log_grid hm ho c hc σ hband hcut ?_ hcycle i
  intro j
  rw [hstep]
  apply cubicBand_floorPower_eq_threshold (hband j)
  rw [← hstep]
  exact hband (σ j)

/-- The complete quantitative conclusion, including positivity and the lifted seam. -/
def RealizedGridBounds [NeZero L] (c : Fin L → ℝ) (o : ℕ) : Prop :=
  0 < logGridSurplus L o ∧
  (∀ i, |logGridError c (c 0) i| ≤ (1 - 1 / (L : ℝ)) * logGridSurplus L o) ∧
  (∀ i j, |logGridError c (c 0) j - logGridError c (c 0) i| ≤
    (1 - 1 / (L : ℝ)) * logGridSurplus L o) ∧
  (∀ i, 0 < liftedLogGap c i) ∧
  (∀ i j, |liftedLogGap c j - liftedLogGap c i| ≤ logGridSurplus L o ∧
    |liftedLogGap c i - Real.log 3 / (L : ℝ)| ≤
      (1 - 1 / (L : ℝ)) * logGridSurplus L o)

/-- A logarithmic grid error gives a lower bound for the ordinary logarithm. -/
theorem log_lower_of_loglog_bound {x m t ω : ℝ}
    (hx : 1 < x) (hm : 1 < m)
    (h : |Real.log (Real.log x / Real.log m) - t| ≤ ω) :
    Real.log m * Real.exp (-ω) * Real.exp t ≤ Real.log x := by
  have hlm := Real.log_pos hm
  have hratio := div_pos (Real.log_pos hx) hlm
  have hlow : t - ω ≤ Real.log (Real.log x / Real.log m) := by
    have := (abs_le.mp h).1
    linarith
  have hexp := Real.exp_le_exp.mpr hlow
  rw [Real.exp_log hratio] at hexp
  calc
    Real.log m * Real.exp (-ω) * Real.exp t =
        Real.log m * Real.exp (t - ω) := by
      rw [show t - ω = -ω + t by ring, Real.exp_add]
      ring
    _ ≤ Real.log m * (Real.log x / Real.log m) := mul_le_mul_of_nonneg_left hexp hlm.le
    _ = Real.log x := by field_simp

/-- The anchored grid scale used by the absolute upper-cell estimate. -/
noncomputable def logGridScale [NeZero L] (m : ℝ) (o : ℕ) : ℝ :=
  Real.log m * Real.exp (-((1 - 1 / (L : ℝ)) * logGridSurplus L o))

theorem logGridScale_pos [NeZero L] {m : ℝ} (hm : 1 < m) (o : ℕ) :
    0 < logGridScale (L := L) m o :=
  mul_pos (Real.log_pos hm) (Real.exp_pos _)

namespace RealizedGridBounds

variable [NeZero L] {c : Fin L → ℝ} {o : ℕ} (h : RealizedGridBounds c o)

include h

theorem surplus_pos : 0 < logGridSurplus L o := h.1

theorem grid_bound (i : Fin L) :
    |logGridError c (c 0) i| ≤ (1 - 1 / (L : ℝ)) * logGridSurplus L o := h.2.1 i

theorem error_oscillation (i j : Fin L) :
    |logGridError c (c 0) j - logGridError c (c 0) i| ≤
      (1 - 1 / (L : ℝ)) * logGridSurplus L o := h.2.2.1 i j

theorem gap_pos (i : Fin L) : 0 < liftedLogGap c i := h.2.2.2.1 i

theorem gap_range (i j : Fin L) :
    |liftedLogGap c j - liftedLogGap c i| ≤ logGridSurplus L o :=
  (h.2.2.2.2 i j).1

theorem gap_mean_bound (i : Fin L) :
    |liftedLogGap c i - Real.log 3 / (L : ℝ)| ≤
      (1 - 1 / (L : ℝ)) * logGridSurplus L o :=
  (h.2.2.2.2 i i).2

theorem log_state_lower (hc : ∀ i, 1 < c i) (i : Fin L) :
    logGridScale (L := L) (c 0) o *
      Real.exp ((i.val : ℝ) * Real.log 3 / (L : ℝ)) ≤ Real.log (c i) :=
  log_lower_of_loglog_bound (hc i) (hc 0) (h.grid_bound i)

end RealizedGridBounds

/-- Full realization of both grid and gap bounds from power cells and sorted rank rotation. -/
theorem realized_grid_bounds_of_power_cells [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hsorted : StrictMono c)
    (hheight : ∀ i, c i < c 0 ^ 3) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L)
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hcell : ∀ i, c (σ i) ^ 2 ≤ c i ^ (if i.val < o then 3 else 1)) :
    RealizedGridBounds c o := by
  refine ⟨logGridSurplus_pos_of_power_cells c σ o e hc hlen hrank hcell,
    log_grid_of_power_cells c σ o e hc hlen hrank hcycle hcell, ?_,
    liftedLogGap_pos c hc hsorted hheight,
    log_gap_bounds_of_power_cells c σ o e hc hlen hrank hcycle hcell⟩
  have hw := logGrid_coboundary c σ o e (c 0) hc (hc 0) hlen hrank
  have hsum := logCellDefect_sum c σ o e hc hlen hrank
  exact defect_oscillation σ hcycle _ _ _ (logCellDefect_nonneg c σ o hc hcell) hsum hw

/-- The cutoff and all quantitative bounds follow for an exact threshold invariant cycle. -/
theorem threshold_invariant_grid [NeZero L]
    {b : ℕ} (hb : 3 ≤ b) (c : Fin L → ℕ) (hc : StrictMono c)
    (σ : Equiv.Perm (Fin L)) (hband : ∀ i, InCubicBand b (c i))
    (hstep : ∀ i, c (σ i) = thresholdMap b (c i))
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L)))) :
    ∃ o ≤ L, (Finset.univ.filter (fun i => c i < b ^ 2)).card = o ∧
      RealizedGridBounds (fun i => (c i : ℝ)) o := by
  obtain ⟨o, ho, hcut, hcard, hrank⟩ := threshold_sorted_rotation c hc σ hband hstep
  refine ⟨o, ho, hcard, ?_⟩
  apply realized_grid_bounds_of_power_cells (fun i => (c i : ℝ)) σ o (L - o)
  · intro i
    have h : 1 < c i := by have := (hband i).1; omega
    exact_mod_cast h
  · intro i j hij
    change (c i : ℝ) < (c j : ℝ)
    exact_mod_cast hc hij
  · intro i
    have h : c i < c 0 ^ 3 :=
      (hband i).2.trans_le (Nat.pow_le_pow_left (hband 0).1 3)
    exact_mod_cast h
  · omega
  · exact hrank
  · exact hcycle
  · exact threshold_real_power_cells c σ hcut hstep

/-- Standard connectedness of the exact threshold orbit supplies transitivity automatically. -/
theorem threshold_cycle_grid [NeZero L]
    {b : ℕ} (hb : 3 ≤ b) (c : Fin L → ℕ) (hc : StrictMono c)
    (σ : Equiv.Perm (Fin L)) (hband : ∀ i, InCubicBand b (c i))
    (hstep : ∀ i, c (σ i) = thresholdMap b (c i))
    (hconnected : ∀ i j, ∃ k : ℕ, (thresholdMap b)^[k] (c i) = c j) :
    ∃ o ≤ L, (Finset.univ.filter (fun i => c i < b ^ 2)).card = o ∧
      RealizedGridBounds (fun i => (c i : ℝ)) o := by
  apply threshold_invariant_grid hb c hc σ hband hstep
  simpa using rank_isCycleOn_of_connected c hc.injective σ (thresholdMap b) hstep hconnected

/-- Full quantitative bounds for an actual connected Juggler cycle in a cubic band. -/
theorem cubicBand_cycle_grid [NeZero L]
    {m : ℕ} (hm : 3 ≤ m) (c : Fin L → ℕ) (hc : StrictMono c)
    (σ : Equiv.Perm (Fin L)) (hband : ∀ i, InCubicBand m (c i))
    (hstep : ∀ i, c (σ i) = floorPower (c i))
    (hconnected : ∀ i j, ∃ k : ℕ, floorPower^[k] (c i) = c j) :
    ∃ o ≤ L, (Finset.univ.filter (fun i => c i % 2 = 1)).card = o ∧
      RealizedGridBounds (fun i => (c i : ℝ)) o := by
  have hthreshold : ∀ i, c (σ i) = thresholdMap m (c i) := by
    intro i
    rw [hstep]
    apply cubicBand_floorPower_eq_threshold (hband i)
    rw [← hstep]
    exact hband (σ i)
  have hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))) := by
    simpa using rank_isCycleOn_of_connected c hc.injective σ floorPower hstep hconnected
  obtain ⟨o, ho, hcard, hgrid⟩ := threshold_invariant_grid hm c hc σ hband hthreshold hcycle
  refine ⟨o, ho, ?_, hgrid⟩
  have hpar : ∀ i, c i % 2 = 1 ↔ c i < m ^ 2 := by
    intro i
    apply cubicBand_parity_iff (hband i)
    rw [← hstep]
    exact hband (σ i)
  simpa only [hpar] using hcard

end CubicGrid

end Problems.Juggler
