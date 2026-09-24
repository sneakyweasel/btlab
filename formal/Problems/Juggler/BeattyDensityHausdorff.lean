import Problems.Juggler.BeattyPassageDensityBlowup
import Problems.Juggler.BeattyPassageConcentration
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Hausdorff size of the infinite-density set

Infinite density is equivalent to membership in arbitrarily late jump
intervals. Their three-halves length bound gives zero Hausdorff measure
at every exponent above two-thirds. This does not supply a lower bound.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory Metric PaperBThreshold
open scoped ENNReal

private theorem infinite_density_mem_tail {y : ℝ} (hy : certificatePassageDensity y = ∞)
    (N : ℕ) : y ∈ certificateJumpTail N := by
  classical
  by_contra hn
  have hz (r : ℕ) (hr : r ∉ Finset.range N) :
      (Ioo (certificateAmplitudeJumpLeft (r+1)) (certificateAmplitudeJumpRight (r+1))).indicator
        (fun y => ENNReal.ofReal (1/((-Real.log (1-beta))*y))) y = 0 := by
    apply indicator_of_notMem
    intro hyr
    apply hn
    exact mem_iUnion₂.mpr ⟨r, by simpa using hr, hyr⟩
  have hfin : certificatePassageDensity y ≠ ∞ := by
    rw [certificatePassageDensity, tsum_eq_sum hz]
    apply ENNReal.sum_ne_top.mpr
    intro r _
    by_cases hr : y ∈ Ioo (certificateAmplitudeJumpLeft (r+1)) (certificateAmplitudeJumpRight (r+1))
    · rw [indicator_of_mem hr]; exact ENNReal.ofReal_ne_top
    · rw [indicator_of_notMem hr]; exact ENNReal.zero_ne_top
  exact hfin hy

/-- The previously constructed dense G-delta is the entire infinite-density
set of the canonical interval-series representative, not just a subset. -/
theorem certificateDensityBlowupSet_eq_infinite :
    certificateDensityBlowupSet = {y | certificatePassageDensity y = ∞} := by
  apply Subset.antisymm certificateDensityBlowupSet_subset_infinite
  intro y hy
  have ht := infinite_density_mem_tail hy
  obtain ⟨r,_,hyr⟩ := mem_iUnion₂.mp (ht 0)
  have hl := (certificateAmplitudeJump_endpoints_mem_support r).1
  have hu := (certificateAmplitudeJump_endpoints_mem_support r).2
  rw [certificatePassageLaw_support_eq_Icc] at hl hu
  exact ⟨⟨hl.1.trans_lt hyr.1, hyr.2.trans_le hu.2⟩, mem_iInter.mpr ht⟩

/-- The entire infinite-density set has zero `s`-dimensional Hausdorff
measure for every `s > 2/3`. This uses only the chronological jump-length
upper bound, not quantitative recurrence of their locations. -/
theorem certificatePassageDensity_infinite_hausdorffMeasure_zero {s : ℝ} (hs : 2/3 < s) :
    Measure.hausdorffMeasure s {y | certificatePassageDensity y = ∞} = 0 := by
  have hs0 : 0 < s := by linarith
  obtain ⟨a,b,ha,hb,hw⟩ := certificateWeight_three_halves_bounds
  let v : ℕ → ℝ := fun n => b*((n : ℝ)+1)^(-3/2 : ℝ)
  let J : ℕ → Set ℝ := fun r =>
    Ioo (certificateAmplitudeJumpLeft (r+1)) (certificateAmplitudeJumpRight (r+1))
  have hv (n : ℕ) : 0 < v n := mul_pos hb (Real.rpow_pos_of_pos (by positivity) _)
  have hdiam (n : ℕ) : ediam (J n) ≤ ENNReal.ofReal (v n) := by
    dsimp only [J]
    rw [Real.ediam_Ioo]
    apply ENNReal.ofReal_le_ofReal
    apply (certificateAmplitudeJump_length_le n).trans
    have he : v n = b/((n : ℝ)+1)^(3/2 : ℝ) := by
      dsimp [v]
      rw [show (-3/2 : ℝ) = -(3/2) by norm_num, Real.rpow_neg (by positivity)]
      simp only [div_eq_mul_inv]
    rw [he]
    exact (hw n).2
  have hvmono (n k : ℕ) : v (k+n) ≤ v n := by
    apply mul_le_mul_of_nonneg_left _ hb.le
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hvzero : Tendsto (fun n => ENNReal.ofReal (v n)) atTop (𝓝 0) := by
    have hr := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3/2)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have hh : Tendsto v atTop (𝓝 0) := by
      simpa only [v, Function.comp_def, neg_div, mul_zero] using hr.const_mul b
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hh
  have hsum : Summable (fun n => (v n)^s) := by
    have h := (Real.summable_nat_rpow.mpr (by linarith : (-3/2 : ℝ)*s < -1)).comp_injective
      (add_left_injective (1 : ℕ))
    apply (h.mul_left (b^s)).congr
    intro n
    symm
    dsimp [v]
    rw [Real.mul_rpow hb.le (by positivity), ← Real.rpow_mul (by positivity)]
    simp only [Nat.cast_add, Nat.cast_one]
  have hsfinite : (∑' n, (ENNReal.ofReal (v n))^s) ≠ ∞ := by
    simp_rw [ENNReal.ofReal_rpow_of_pos (hv _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => Real.rpow_nonneg (hv _).le _) hsum]
    exact ENNReal.ofReal_ne_top
  have hsumzero : Tendsto (fun n => ∑' k, ediam (J (k+n))^s) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_sum_nat_add _ hsfinite) (fun _ => bot_le)
    intro n
    exact ENNReal.tsum_le_tsum fun k => ENNReal.rpow_le_rpow (hdiam (k+n)) hs0.le
  have hcover (n : ℕ) : {y | certificatePassageDensity y = ∞} ⊆ ⋃ k, J (k+n) := by
    intro y hy
    obtain ⟨r,hr,hyr⟩ := mem_iUnion₂.mp (infinite_density_mem_tail hy n)
    exact mem_iUnion.mpr ⟨r-n, by simpa only [Nat.sub_add_cancel hr] using hyr⟩
  have h := Measure.hausdorffMeasure_le_liminf_tsum s
    {y | certificatePassageDensity y = ∞} _ hvzero (fun n k => J (k+n))
    (Eventually.of_forall fun n k => (hdiam (k+n)).trans (ENNReal.ofReal_le_ofReal (hvmono n k)))
    (Eventually.of_forall hcover)
  rw [hsumzero.liminf_eq] at h
  exact le_antisymm h bot_le

/-- The canonical density's infinite-value set has Hausdorff dimension
at most two-thirds despite being residual in its support interval. -/
theorem certificatePassageDensity_infinite_dimH_le :
    dimH {y | certificatePassageDensity y = ∞} ≤ (2/3 : ℝ≥0∞) := by
  apply dimH_le
  intro d hd
  by_contra hn
  have hreal : (2/3 : ℝ) < (d : ℝ) := by
    have h := (ENNReal.toReal_lt_toReal (by finiteness : (2/3 : ℝ≥0∞) ≠ ∞)
      ENNReal.coe_ne_top).mpr (lt_of_not_ge hn)
    simpa using h
  have hz := certificatePassageDensity_infinite_hausdorffMeasure_zero hreal
  rw [hz] at hd
  exact ENNReal.zero_ne_top hd

end Problems.Juggler.BeattyPhase
