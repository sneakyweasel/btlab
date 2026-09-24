import Problems.Juggler.BeattyAmplitudeSupport
import Problems.Juggler.BeattyOccupationSupport
import Problems.Juggler.BeattyPassageMoments

/-!
# The exact interval support of the Gamma-normalized counts

The amplitude has upward jumps and equal endpoint values. Its range
closure, empirical-law support and complete cluster set are one compact
interval. The endpoints are specified by the rescaled certificate jumps.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory PaperBThreshold
open scoped ENNReal

private theorem beta_pos : 0 < beta := by linarith [beta_gt_five_eighths]
private theorem q_pos : 0 < 1-beta := sub_pos.2 beta_lt_one
private theorem q_lt_one : 1-beta < 1 := by linarith [beta_pos]
private theorem scale_pos : 0 < -Real.log (1-beta) := neg_pos.mpr (Real.log_neg q_pos q_lt_one)

/-- The Gamma amplitude is continuous from the left at every real phase,
including all its jump phases. -/
theorem certificatePhaseAmplitude_tendsto_left (t : ℝ) :
    Tendsto certificatePhaseAmplitude (𝓝[<] t) (𝓝 (certificatePhaseAmplitude t)) :=
  ((Real.continuous_const_rpow q_pos.ne').continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).mul (certificateProfile_tendsto_left t)

/-- The tilted profile is lower semicontinuous; its only jumps are upward. -/
theorem certificatePhaseAmplitude_lowerSemicontinuous :
    LowerSemicontinuous certificatePhaseAmplitude :=
  lowerSemicontinuous_mul_monotone_of_tendsto_left certificateProfile_monotone
    certificateProfile_tendsto_left (Real.continuous_const_rpow q_pos.ne')
    (Real.rpow_pos_of_pos q_pos)

/-- The critical total mass closes the amplitude path: both endpoint values equal one. -/
theorem certificatePhaseAmplitude_endpoints :
    certificatePhaseAmplitude 0 = 1 ∧ certificatePhaseAmplitude 1 = 1 := by
  constructor
  · simp [certificatePhaseAmplitude, certificateProfile, jumpProfile,
      fun r => not_lt_of_ge (certificatePhase_pos (r := r+1) (by omega)).le]
  · simp only [certificatePhaseAmplitude, Real.rpow_one, certificateProfile, jumpProfile,
      if_pos (certificatePhase_mem_Ico _).2]
    rw [certificate_jump_weights_hasSum.tsum_eq, terminalRatio]
    field_simp [q_pos.ne', beta_pos.ne']
    ring

/-- Every value between two attained phase amplitudes is attained too.
The function may still have dense upward jumps. -/
theorem certificatePhaseAmplitude_image_ordConnected :
    OrdConnected (certificatePhaseAmplitude '' Icc 0 1) :=
  ordConnected_image_Icc_of_equal_endpoints certificatePhaseAmplitude_lowerSemicontinuous
    certificatePhaseAmplitude_tendsto_left
    (certificatePhaseAmplitude_endpoints.1.trans certificatePhaseAmplitude_endpoints.2.symm)

/-- The probability support is the closure of the actual amplitude range. -/
theorem certificatePassageLaw_support_eq_closure_image :
    (certificatePassageLaw : Measure ℝ).support =
      closure (certificatePhaseAmplitude '' Icc 0 1) := by
  rw [image_Icc_eq_image_Ioc_of_equal_endpoints zero_lt_one
    (certificatePhaseAmplitude_endpoints.1.trans certificatePhaseAmplitude_endpoints.2.symm)]
  exact support_map_restrict_Ioc_eq_closure_image certificatePhaseAmplitude_measurable
    certificatePhaseAmplitude_tendsto_left 0 1

/-- The support is also the closure of the union of all rescaled jump
intervals; these intervals can overlap. -/
theorem certificatePassageLaw_support_eq_closure_jumps :
    (certificatePassageLaw : Measure ℝ).support = closure (⋃ r,
      Ioo (certificateAmplitudeJumpLeft (r+1)) (certificateAmplitudeJumpRight (r+1))) := by
  rw [certificatePassageLaw_eq_sum_logIntervalMeasure]
  exact support_sum_logIntervalMeasure scale_pos (fun r => certificateAmplitudeJumpLeft_pos (r+1))

/-- Unlike the binomial-normalized law's Cantor support, the Gamma-law
support is order connected. This gives a genuine no-gap assertion. -/
theorem certificatePassageLaw_support_ordConnected :
    OrdConnected (certificatePassageLaw : Measure ℝ).support := by
  rw [certificatePassageLaw_support_eq_closure_image]
  exact certificatePhaseAmplitude_image_ordConnected.isPreconnected.closure.ordConnected

/-- The support is compact and contained in the positive amplitude envelope. -/
theorem isCompact_certificatePassageLaw_support :
    IsCompact (certificatePassageLaw : Measure ℝ).support :=
  isCompact_Icc.of_isClosed_subset Measure.isClosed_support
    (Measure.support_subset_of_isClosed isClosed_Icc certificatePassageLaw_ae_mem_envelope)

/-- The original integer counts in the exact Gamma normalization have
precisely the probability support as their full real cluster set. -/
theorem certificateGammaRatio_cluster_iff (y : ℝ) :
    MapClusterPt y atTop certificateGammaRatio ↔ y ∈ (certificatePassageLaw : Measure ℝ).support := by
  rw [certificatePassageLaw_support_eq_closure_image,
    mapClusterPt_iff_of_sub_tendsto_zero certificateGammaRatio_phase_asymptotic]
  exact mapClusterPt_amplitude_iff certificatePhaseAmplitude_tendsto_left
    (certificatePhaseAmplitude_endpoints.1.trans certificatePhaseAmplitude_endpoints.2.symm)
    (fun n => ⟨(certificatePhase_mem_Ico n).1, (certificatePhase_mem_Ico n).2.le⟩)
    certificatePhase_recurrent y

/-- The lower endpoint of the Gamma-law support, specified entirely by
the exact left traces of the rescaled certificate jumps. -/
noncomputable def certificatePassageLower : ℝ :=
  sInf (range (fun r : ℕ => certificateAmplitudeJumpLeft (r+1)))

/-- The upper endpoint of the Gamma-law support, specified entirely by
the exact right traces of the rescaled certificate jumps. -/
noncomputable def certificatePassageUpper : ℝ :=
  sSup (range (fun r : ℕ => certificateAmplitudeJumpRight (r+1)))

private theorem left_bddBelow : BddBelow (range (fun r : ℕ => certificateAmplitudeJumpLeft (r+1))) :=
  ⟨1-beta, by rintro _ ⟨r, rfl⟩; exact (certificateAmplitudeJump_bounds r).1⟩

private theorem right_bddAbove : BddAbove (range (fun r : ℕ => certificateAmplitudeJumpRight (r+1))) :=
  ⟨1+1/terminalRatio, by rintro _ ⟨r, rfl⟩; exact (certificateAmplitudeJump_bounds r).2⟩

/-- Every rescaled certificate jump has strictly positive width. -/
theorem certificateAmplitudeJumpLeft_lt_right (r : ℕ) :
    certificateAmplitudeJumpLeft r < certificateAmplitudeJumpRight r :=
  mul_lt_mul_of_pos_left (lt_add_of_pos_right _ (certificateWeight_pos r))
    (Real.rpow_pos_of_pos q_pos _)

/-- The two traces of each positive-index jump belong to the probability
support, even when a right trace is only a one-sided limit. -/
theorem certificateAmplitudeJump_endpoints_mem_support (r : ℕ) :
    certificateAmplitudeJumpLeft (r+1) ∈ (certificatePassageLaw : Measure ℝ).support ∧
      certificateAmplitudeJumpRight (r+1) ∈ (certificatePassageLaw : Measure ℝ).support := by
  have hsub : closure (Ioo (certificateAmplitudeJumpLeft (r+1))
      (certificateAmplitudeJumpRight (r+1))) ⊆ (certificatePassageLaw : Measure ℝ).support := by
    rw [certificatePassageLaw_support_eq_closure_jumps]
    exact closure_mono (fun y hy => mem_iUnion.mpr ⟨r, hy⟩)
  rw [closure_Ioo (certificateAmplitudeJumpLeft_lt_right (r+1)).ne] at hsub
  exact ⟨hsub ⟨le_rfl, (certificateAmplitudeJumpLeft_lt_right (r+1)).le⟩,
    hsub ⟨(certificateAmplitudeJumpLeft_lt_right (r+1)).le, le_rfl⟩⟩

/-- Both exact extremal endpoints belong to the support. -/
theorem certificatePassage_endpoints_mem_support :
    certificatePassageLower ∈ (certificatePassageLaw : Measure ℝ).support ∧
      certificatePassageUpper ∈ (certificatePassageLaw : Measure ℝ).support := by
  constructor
  · apply closure_minimal ?_ Measure.isClosed_support
      (csInf_mem_closure (range_nonempty _) left_bddBelow)
    rintro _ ⟨r, rfl⟩
    exact (certificateAmplitudeJump_endpoints_mem_support r).1
  · apply closure_minimal ?_ Measure.isClosed_support
      (csSup_mem_closure (range_nonempty _) right_bddAbove)
    rintro _ ⟨r, rfl⟩
    exact (certificateAmplitudeJump_endpoints_mem_support r).2

/-- Exact support identification: every value between the extremal
rescaled jumps is in the support, and there are no values outside it. -/
theorem certificatePassageLaw_support_eq_Icc :
    (certificatePassageLaw : Measure ℝ).support =
      Icc certificatePassageLower certificatePassageUpper := by
  apply Subset.antisymm
  · rw [certificatePassageLaw_support_eq_closure_jumps]
    apply closure_minimal ?_ isClosed_Icc
    intro y hy
    obtain ⟨r, hr⟩ := mem_iUnion.mp hy
    exact ⟨(csInf_le left_bddBelow (mem_range_self r)).trans hr.1.le,
      hr.2.le.trans (le_csSup right_bddAbove (mem_range_self r))⟩
  · exact certificatePassageLaw_support_ordConnected.out
      certificatePassage_endpoints_mem_support.1 certificatePassage_endpoints_mem_support.2

/-- The exact support is a nondegenerate positive interval inside the
previous coarse envelope. No numerical endpoint conjecture is used. -/
theorem certificatePassage_endpoints_bounds :
    1-beta ≤ certificatePassageLower ∧ certificatePassageLower < certificatePassageUpper ∧
      certificatePassageUpper ≤ 1+1/terminalRatio := by
  refine ⟨?_, ?_, ?_⟩
  · exact le_csInf (range_nonempty _) (by rintro _ ⟨r, rfl⟩; exact (certificateAmplitudeJump_bounds r).1)
  · exact (csInf_le left_bddBelow (mem_range_self 0)).trans_lt
      ((certificateAmplitudeJumpLeft_lt_right 1).trans_le (le_csSup right_bddAbove (mem_range_self 0)))
  · exact csSup_le (range_nonempty _) (by rintro _ ⟨r, rfl⟩; exact (certificateAmplitudeJump_bounds r).2)

/-- The complete real accumulation set of the original Gamma-normalized
integer counts is this single nondegenerate interval. -/
theorem certificateGammaRatio_cluster_iff_mem_Icc (y : ℝ) :
    MapClusterPt y atTop certificateGammaRatio ↔
      y ∈ Icc certificatePassageLower certificatePassageUpper := by
  rw [certificateGammaRatio_cluster_iff, certificatePassageLaw_support_eq_Icc]

/-- Every nonempty open interval with endpoints in the support has
strictly positive limiting probability. -/
theorem certificatePassageLaw_Ioo_pos {x y : ℝ}
    (hx : x ∈ Icc certificatePassageLower certificatePassageUpper)
    (hy : y ∈ Icc certificatePassageLower certificatePassageUpper) (hxy : x < y) :
    0 < (certificatePassageLaw : Measure ℝ) (Ioo x y) := by
  obtain ⟨z, hxz, hzy⟩ := exists_between hxy
  have hz : z ∈ (certificatePassageLaw : Measure ℝ).support := by
    rw [certificatePassageLaw_support_eq_Icc]
    exact ⟨hx.1.trans hxz.le, hzy.le.trans hy.2⟩
  exact (Measure.mem_support_iff_forall z).mp hz (Ioo x y) (Ioo_mem_nhds hxz hzy)

/-- The continuous Gamma-law CDF is strictly increasing throughout its
support; there are no internal probability plateaus. -/
theorem certificatePassageLaw_cdf_strictMonoOn :
    StrictMonoOn (fun y => (certificatePassageLaw : Measure ℝ).real (Iic y))
      (Icc certificatePassageLower certificatePassageUpper) := by
  intro x hx y hy hxy
  have hp : 0 < (certificatePassageLaw : Measure ℝ) (Ioc x y) :=
    (certificatePassageLaw_Ioo_pos hx hy hxy).trans_le (measure_mono Ioo_subset_Ioc_self)
  have hr := ENNReal.toReal_pos hp.ne' (measure_ne_top (certificatePassageLaw : Measure ℝ) (Ioc x y))
  have hd : Disjoint (Iic x) (Ioc x y) := disjoint_left.mpr fun z hz hz' =>
    (not_lt_of_ge hz) hz'.1
  have he := measureReal_union (μ := (certificatePassageLaw : Measure ℝ)) hd measurableSet_Ioc
  rw [Iic_union_Ioc_eq_Iic hxy.le] at he
  change 0 < (certificatePassageLaw : Measure ℝ).real (Ioc x y) at hr
  linarith

end Problems.Juggler.BeattyPhase
