import Problems.Juggler.BeattyCertificateWeights
import Problems.Juggler.BeattyCertificateDistribution
import Problems.Juggler.BeattyHausdorffUpper
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Quantitative phase coverage and Hausdorff lower bounds

A polynomial bound for the first phase hitting any interval forces Hölder
regularity of the certificate distribution function. The arithmetic hitting
bound is an explicit premise; it is not inferred from qualitative density.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory
open scoped NNReal ENNReal

/-- A quantitative hitting bound: every interval of width `b-a` in the unit
phase interval contains an orbit point with index at most `H/(b-a)^τ`.
The sequence is indexed from zero and its cost is `n+1`. -/
def PhaseHittingBound (θ : ℕ → ℝ) (H τ : ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
    ∃ n : ℕ, θ n ∈ Ioo a b ∧ ((n : ℝ)+1)*(b-a)^τ ≤ H

/-- The continuous cumulative distribution function of the certificate law. -/
noncomputable def certificateCdf (y : ℝ) : ℝ :=
  (certificateLaw : Measure ℝ).real (Iic y)

/-- The certificate distribution function is monotone. -/
theorem certificateCdf_monotone : Monotone certificateCdf :=
  fun _ _ h => measureReal_mono (Iic_subset_Iic.2 h)

/-- The certificate distribution function takes values in the unit interval. -/
theorem certificateCdf_bounds (y : ℝ) : certificateCdf y ∈ Icc (0 : ℝ) 1 := by
  refine ⟨measureReal_nonneg, ?_⟩
  simp [certificateCdf]

/-- The cumulative distribution function recovers every phase, including endpoints. -/
theorem certificateCdf_profile {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    certificateCdf (certificateProfile t) = t := by
  simp only [certificateCdf, Measure.real, certificateLaw_Iic_profile ht,
    ENNReal.toReal_ofReal ht.1]

/-- Both endpoints and the interior of a certificate gap have the same CDF value. -/
theorem certificateCdf_gap (n : ℕ) {y : ℝ}
    (hy : y ∈ Icc (certificateProfile (certificatePhase (n+1)))
      (certificateProfile (certificatePhase (n+1))+certificateWeight (n+1))) :
    certificateCdf y = certificatePhase (n+1) := by
  simp only [certificateCdf, Measure.real, certificateLaw_Iic_gap n hy,
    ENNReal.toReal_ofReal (certificatePhase_mem_Ico _).1]

/-- The CDF maps the actual certificate cluster set onto the whole unit interval. -/
theorem certificateCdf_image_clusterSet :
    certificateCdf '' certificateClusterSet = Icc (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨y,_,rfl⟩
    exact certificateCdf_bounds y
  · intro t ht
    refine ⟨certificateProfile t, ?_, certificateCdf_profile ht⟩
    rw [certificateClusterSet_eq_closure_range]
    exact subset_closure (mem_range_self t)

private theorem gap_between_cdf_values {x y : ℝ} {n : ℕ}
    (hn : certificatePhase (n+1) ∈ Ioo (certificateCdf x) (certificateCdf y)) :
    certificateWeight (n+1) ≤ y-x := by
  have hl : x < certificateProfile (certificatePhase (n+1)) := by
    by_contra h
    have hm := certificateCdf_monotone (le_of_not_gt h)
    rw [certificateCdf_profile
      ⟨(certificatePhase_mem_Ico _).1,(certificatePhase_mem_Ico _).2.le⟩] at hm
    exact (not_lt_of_ge hm) hn.1
  have hu : certificateProfile (certificatePhase (n+1))+certificateWeight (n+1) < y := by
    by_contra h
    have hm := certificateCdf_monotone (le_of_not_gt h)
    rw [certificateCdf_gap n ⟨by linarith [certificateWeight_nonneg (n+1)],le_rfl⟩] at hm
    exact (not_lt_of_ge hm) hn.2
  linarith

private theorem weight_power_lower :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ,
      A ≤ ((n : ℝ)+1)*certificateWeight (n+1)^(2/3 : ℝ) := by
  obtain ⟨a,b,ha,_,hw⟩ := certificateWeight_three_halves_bounds
  refine ⟨a^(2/3 : ℝ), Real.rpow_pos_of_pos ha _, fun n => ?_⟩
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ a/((n : ℝ)+1)^(3/2 : ℝ))
    (hw n).1 (by norm_num : (0 : ℝ) ≤ 2/3)
  rw [Real.div_rpow ha.le (Real.rpow_nonneg (by positivity) _),
    ← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ)+1)] at h
  norm_num at h
  exact (div_le_iff₀ (by positivity : 0 < (n : ℝ)+1)).1 h |>.trans_eq (mul_comm _ _)

/-- Polynomial phase coverage with exponent `τ` forces a global Hölder
bound of exponent `2/(3*τ)` for the actual certificate CDF. The premise is
quantitative and is not supplied by equidistribution alone. -/
theorem certificateCdf_holder_of_phaseHitting {H τ : ℝ} (hH : 0 < H) (hτ : 0 < τ)
    (hh : PhaseHittingBound (fun n => certificatePhase (n+1)) H τ) :
    ∃ C : ℝ≥0, HolderWith C ⟨(2/3 : ℝ)/τ, by positivity⟩ certificateCdf := by
  obtain ⟨A,hA,hw⟩ := weight_power_lower
  let C : ℝ≥0 := ⟨(H/A)^(1/τ), Real.rpow_nonneg (div_nonneg hH.le hA.le) _⟩
  have hc (x y : ℝ) (hxy : x ≤ y) :
      certificateCdf y-certificateCdf x ≤ (C : ℝ)*(y-x)^((2/3 : ℝ)/τ) := by
    by_cases he : certificateCdf x = certificateCdf y
    · rw [he, sub_self]
      positivity
    have hp : 0 < certificateCdf y-certificateCdf x :=
      sub_pos.2 (lt_of_le_of_ne (certificateCdf_monotone hxy) he)
    obtain ⟨n,hn,hindex⟩ := hh _ _ (certificateCdf_bounds x).1
      (sub_pos.1 hp) (certificateCdf_bounds y).2
    have hgap := gap_between_cdf_values hn
    have hpτ : 0 ≤ (certificateCdf y-certificateCdf x)^τ :=
      Real.rpow_nonneg hp.le _
    have hpow := Real.rpow_le_rpow (certificateWeight_nonneg _) hgap
      (by norm_num : (0 : ℝ) ≤ 2/3)
    have hprod : A*(certificateCdf y-certificateCdf x)^τ ≤ H*(y-x)^(2/3 : ℝ) := by
      calc
        _ ≤ (((n : ℝ)+1)*certificateWeight (n+1)^(2/3 : ℝ))*
            (certificateCdf y-certificateCdf x)^τ := mul_le_mul_of_nonneg_right (hw n) hpτ
        _ = (((n : ℝ)+1)*(certificateCdf y-certificateCdf x)^τ)*
            certificateWeight (n+1)^(2/3 : ℝ) := by ring
        _ ≤ H*certificateWeight (n+1)^(2/3 : ℝ) :=
          mul_le_mul_of_nonneg_right hindex (Real.rpow_nonneg (certificateWeight_nonneg _) _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow hH.le
    have hdiv : (certificateCdf y-certificateCdf x)^τ ≤ (H/A)*(y-x)^(2/3 : ℝ) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hA).2
      simpa only [mul_comm] using hprod
    have hr := Real.rpow_le_rpow hpτ hdiv (by positivity : 0 ≤ 1/τ)
    rw [← Real.rpow_mul hp.le, Real.mul_rpow (div_nonneg hH.le hA.le)
      (Real.rpow_nonneg (sub_nonneg.2 hxy) _),
      ← Real.rpow_mul (sub_nonneg.2 hxy)] at hr
    change _ ≤ (H/A)^(1/τ)*(y-x)^((2/3 : ℝ)/τ)
    simpa [hτ.ne', div_eq_mul_inv] using hr
  refine ⟨C, ?_⟩
  intro x y
  have hd : dist (certificateCdf x) (certificateCdf y) ≤
      (C : ℝ)*dist x y^((2/3 : ℝ)/τ) := by
    rcases le_total x y with hxy | hyx
    · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hxy),
        abs_of_nonpos (sub_nonpos.2 (certificateCdf_monotone hxy)), neg_sub] using hc x y hxy
    · simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hyx),
        abs_of_nonneg (sub_nonneg.2 (certificateCdf_monotone hyx))] using hc y x hyx
  change edist (certificateCdf x) (certificateCdf y) ≤
    (C : ℝ≥0∞)*edist x y^((2/3 : ℝ)/τ)
  simpa only [ENNReal.ofReal_mul C.coe_nonneg,
    ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg : 0 ≤ dist x y)
      (by positivity : 0 ≤ (2/3 : ℝ)/τ), ← edist_dist] using ENNReal.ofReal_le_ofReal hd

/-- The phase-hitting exponent gives a quantitative Hausdorff lower bound
for the actual cluster set. The number-theoretic premise remains explicit. -/
theorem certificateClusterSet_dimH_lower_of_phaseHitting {H τ : ℝ}
    (hH : 0 < H) (hτ : 0 < τ)
    (hh : PhaseHittingBound (fun n => certificatePhase (n+1)) H τ) :
    ENNReal.ofReal ((2/3 : ℝ)/τ) ≤ dimH certificateClusterSet := by
  obtain ⟨C,hC⟩ := certificateCdf_holder_of_phaseHitting hH hτ hh
  let r : ℝ≥0 := ⟨(2/3 : ℝ)/τ, by positivity⟩
  have hr : 0 < r := by change (0 : ℝ) < (2/3 : ℝ)/τ; positivity
  change HolderWith C r certificateCdf at hC
  have h := hC.dimH_image_le hr certificateClusterSet
  rw [certificateCdf_image_clusterSet] at h
  have hI : dimH (Icc (0 : ℝ) 1) = 1 := by
    simpa only [segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)] using
      (Real.dimH_segment (by norm_num : (0 : ℝ) ≠ 1))
  rw [hI] at h
  have hh' := (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.2 hr.ne'))
    (Or.inl ENNReal.coe_ne_top)).1 h
  rw [one_mul, ← ENNReal.ofReal_coe_nnreal] at hh'
  change ENNReal.ofReal ((2/3 : ℝ)/τ) ≤ dimH certificateClusterSet at hh'
  exact hh'

/-- Polynomial phase coverage gives positive Hausdorff measure at the
lower-bound exponent, not merely a dimension inequality. -/
theorem certificateClusterSet_hausdorffMeasure_ne_zero_of_phaseHitting {H τ : ℝ}
    (hH : 0 < H) (hτ : 0 < τ)
    (hh : PhaseHittingBound (fun n => certificatePhase (n+1)) H τ) :
    Measure.hausdorffMeasure ((2/3 : ℝ)/τ) certificateClusterSet ≠ 0 := by
  obtain ⟨C,hC⟩ := certificateCdf_holder_of_phaseHitting hH hτ hh
  let r : ℝ≥0 := ⟨(2/3 : ℝ)/τ, by positivity⟩
  have hr : 0 < r := by change (0 : ℝ) < (2/3 : ℝ)/τ; positivity
  change HolderWith C r certificateCdf at hC
  have h := (hC.holderOnWith certificateClusterSet).hausdorffMeasure_image_le hr
    (d := 1) (by norm_num)
  rw [certificateCdf_image_clusterSet, hausdorffMeasure_real, Real.volume_Icc] at h
  norm_num only [sub_zero, ENNReal.ofReal_one, ENNReal.rpow_one, mul_one] at h
  change (1 : ℝ≥0∞) ≤ (C : ℝ≥0∞)*
    Measure.hausdorffMeasure ((2/3 : ℝ)/τ) certificateClusterSet at h
  intro hz
  rw [hz,mul_zero] at h
  exact (not_le_of_gt zero_lt_one) h

/-- Inverse-linear phase hitting implies positive finite two-thirds
Hausdorff measure of the actual certificate cluster set. This condition
on the concrete logarithmic phase orbit is not discharged here. -/
theorem certificateClusterSet_hausdorffMeasure_pos_finite_of_phaseHitting {H : ℝ}
    (hH : 0 < H)
    (hh : PhaseHittingBound (fun n => certificatePhase (n+1)) H 1) :
    0 < Measure.hausdorffMeasure (2/3 : ℝ) certificateClusterSet ∧
    Measure.hausdorffMeasure (2/3 : ℝ) certificateClusterSet < ⊤ := by
  refine ⟨?_, lt_top_iff_ne_top.2 certificateClusterSet_hausdorffMeasure_ne_top⟩
  exact pos_iff_ne_zero.2 (by simpa only [div_one] using
    certificateClusterSet_hausdorffMeasure_ne_zero_of_phaseHitting hH zero_lt_one hh)

/-- Inverse-linear phase coverage gives the matching Hausdorff dimension
two-thirds, with no other added hypothesis. The coverage premise is explicit. -/
theorem certificateClusterSet_dimH_eq_of_phaseHitting {H : ℝ} (hH : 0 < H)
    (hh : PhaseHittingBound (fun n => certificatePhase (n+1)) H 1) :
    dimH certificateClusterSet = (2/3 : ℝ≥0∞) := by
  apply le_antisymm certificateClusterSet_dimH_upper
  have h := certificateClusterSet_dimH_lower_of_phaseHitting hH zero_lt_one hh
  simpa only [div_one, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3),
    ENNReal.ofReal_ofNat] using h

end Problems.Juggler.BeattyPhase
