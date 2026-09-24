import Problems.Juggler.BeattyAmplitudeSupport
import Problems.Juggler.BeattyOccupationSupport
import Problems.Juggler.BeattySlopeGammaMoments

/-!
# The exact interval support of the Gamma first-passage law for every slope

The tilted amplitude has only upward jumps and equal endpoint values. Its
range closure, the Gamma-law support and the complete cluster set of the
Gamma-normalized counts are one compact interval `[ℓ,u]`, whose endpoints are
the extremal rescaled jump traces. The explicit density is lower
semicontinuous, and infinite wherever arbitrarily late jumps overlap.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped ENNReal

/-- The lower endpoint `ℓ` of the Gamma-law support: the infimum of the
left traces of the positive-index rescaled jumps. -/
noncomputable def passageGammaLower (β : ℝ) : ℝ :=
  sInf (range (fun r : ℕ => passageGammaJumpLeft β (r+1)))

/-- The upper endpoint `u` of the Gamma-law support: the supremum of the
right traces of the positive-index rescaled jumps. -/
noncomputable def passageGammaUpper (β : ℝ) : ℝ :=
  sSup (range (fun r : ℕ => passageGammaJumpRight β (r+1)))

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

omit hβ in
private theorem scale_pos : 0 < -Real.log (1-β) :=
  neg_pos.mpr (Real.log_neg (sub_pos.2 hβ1) (by linarith))

private theorem profile_tendsto_left (t : ℝ) :
    Tendsto (passageProfile β) (𝓝[<] t) (𝓝 (passageProfile β t)) :=
  jumpProfile_tendsto_left (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable
    (fun r => passageJumpWeight_nonneg hβ0 hβ1 (r+1)) t

/-- The tilted amplitude is continuous from the left at every real phase,
including all its jump phases. -/
theorem passageGammaAmp_tendsto_left (t : ℝ) :
    Tendsto (passageGammaAmp β) (𝓝[<] t) (𝓝 (passageGammaAmp β t)) :=
  ((Real.continuous_const_rpow (sub_pos.2 hβ1).ne').continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).mul (profile_tendsto_left hβ0 hβ1 hβ t)

/-- The tilted amplitude is lower semicontinuous; its only jumps are upward. -/
theorem passageGammaAmp_lowerSemicont : LowerSemicontinuous (passageGammaAmp β) :=
  lowerSemicontinuous_mul_monotone_of_tendsto_left (passageProfile_monotone hβ0 hβ1 hβ)
    (profile_tendsto_left hβ0 hβ1 hβ) (Real.continuous_const_rpow (sub_pos.2 hβ1).ne')
    (Real.rpow_pos_of_pos (sub_pos.2 hβ1))

/-- The critical total mass closes the amplitude path: both endpoint values equal one. -/
theorem passageGammaAmp_endpoints : passageGammaAmp β 0 = 1 ∧ passageGammaAmp β 1 = 1 := by
  obtain ⟨h0, h1⟩ := passageProfile_endpoints hβ0 hβ1 hβ
  have hq : (1-β) ≠ 0 := (sub_pos.2 hβ1).ne'
  constructor
  · simp [passageGammaAmp, h0]
  · simp only [passageGammaAmp, Real.rpow_one, h1]
    field_simp

private theorem amp_ends : passageGammaAmp β 0 = passageGammaAmp β 1 :=
  (passageGammaAmp_endpoints hβ0 hβ1 hβ).1.trans (passageGammaAmp_endpoints hβ0 hβ1 hβ).2.symm

/-- Every value between two attained phase amplitudes is attained, although
the amplitude has dense upward jumps. -/
theorem passageGammaAmp_image_ordConn : OrdConnected (passageGammaAmp β '' Icc 0 1) :=
  ordConnected_image_Icc_of_equal_endpoints (passageGammaAmp_lowerSemicont hβ0 hβ1 hβ)
    (passageGammaAmp_tendsto_left hβ0 hβ1 hβ) (amp_ends hβ0 hβ1 hβ)

/-- The Gamma-law support is the closure of the amplitude range on `[0,1]`. -/
theorem passageGammaLaw_support_image :
    ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ).support =
      closure (passageGammaAmp β '' Icc 0 1) := by
  rw [image_Icc_eq_image_Ioc_of_equal_endpoints zero_lt_one (amp_ends hβ0 hβ1 hβ)]
  exact support_map_restrict_Ioc_eq_closure_image (passageGammaAmp_measurable hβ0 hβ1 hβ)
    (passageGammaAmp_tendsto_left hβ0 hβ1 hβ) 0 1

/-- The support is the closure of the union of all rescaled jump
intervals; these intervals can overlap. -/
theorem passageGammaLaw_support_jumps :
    ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ).support = closure (⋃ r,
      Ioo (passageGammaJumpLeft β (r+1)) (passageGammaJumpRight β (r+1))) := by
  rw [passageGammaLaw_eq_sum_log]
  exact support_sum_logIntervalMeasure (scale_pos hβ0 hβ1)
    (fun r => passageGammaJumpLeft_pos hβ0 hβ1 hβ (r+1))

/-- Unlike the Cantor support of the binomial law, the Gamma-law support
is order connected. -/
theorem passageGammaLaw_support_ordConn :
    OrdConnected ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ).support := by
  rw [passageGammaLaw_support_image]
  exact (passageGammaAmp_image_ordConn hβ0 hβ1 hβ).isPreconnected.closure.ordConnected

/-- The Gamma-law support is compact. -/
theorem passageGammaSupport_isCompact :
    IsCompact ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ).support :=
  isCompact_Icc.of_isClosed_subset Measure.isClosed_support
    (Measure.support_subset_of_isClosed isClosed_Icc (passageGammaLaw_ae_envelope hβ0 hβ1 hβ))

/-- The Gamma-normalized integer counts have exactly the Gamma-law support
as their set of real cluster points. -/
theorem passageGamma_cluster_iff_support (y : ℝ) :
    MapClusterPt y atTop (passageGammaRatio β) ↔
      y ∈ ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ).support := by
  rw [passageGammaLaw_support_image,
    mapClusterPt_iff_of_sub_tendsto_zero (passageGamma_phase_asymptotic hβ0 hβ1 hβ)]
  exact mapClusterPt_amplitude_iff (passageGammaAmp_tendsto_left hβ0 hβ1 hβ)
    (amp_ends hβ0 hβ1 hβ)
    (fun n => ⟨(passagePhase_mem_Ico hβ0 n).1, (passagePhase_mem_Ico hβ0 n).2.le⟩)
    (passagePhase_recurrent hβ0 hβ) y

private theorem left_bddBelow :
    BddBelow (range (fun r : ℕ => passageGammaJumpLeft β (r+1))) :=
  ⟨1-β, by rintro _ ⟨r, rfl⟩; exact (passageGammaJump_bounds hβ0 hβ1 hβ r).1⟩

private theorem right_bddAbove :
    BddAbove (range (fun r : ℕ => passageGammaJumpRight β (r+1))) :=
  ⟨1/(1-β), by rintro _ ⟨r, rfl⟩; exact (passageGammaJump_bounds hβ0 hβ1 hβ r).2⟩

omit hβ in
/-- Every rescaled jump has strictly positive width. -/
theorem passageGammaJump_left_lt_right (r : ℕ) :
    passageGammaJumpLeft β r < passageGammaJumpRight β r :=
  mul_lt_mul_of_pos_left (lt_add_of_pos_right _ (passageJumpWeight_pos hβ0 hβ1 r))
    (Real.rpow_pos_of_pos (sub_pos.2 hβ1) _)

/-- Both traces of each positive-index rescaled jump lie in the support. -/
theorem passageGammaJump_mem_support (r : ℕ) :
    passageGammaJumpLeft β (r+1) ∈ ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ).support ∧
      passageGammaJumpRight β (r+1) ∈ ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ).support := by
  have hlt := passageGammaJump_left_lt_right hβ0 hβ1 (r+1)
  have hsub : closure (Ioo (passageGammaJumpLeft β (r+1)) (passageGammaJumpRight β (r+1))) ⊆
      ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ).support := by
    rw [passageGammaLaw_support_jumps]
    exact closure_mono (fun y hy => mem_iUnion.mpr ⟨r, hy⟩)
  rw [closure_Ioo hlt.ne] at hsub
  exact ⟨hsub ⟨le_rfl, hlt.le⟩, hsub ⟨hlt.le, le_rfl⟩⟩

/-- Both extremal endpoints `ℓ` and `u` belong to the support. -/
theorem passageGamma_endpoints_mem :
    passageGammaLower β ∈ ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ).support ∧
      passageGammaUpper β ∈ ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ).support := by
  constructor
  · apply closure_minimal ?_ Measure.isClosed_support
      (csInf_mem_closure (range_nonempty _) (left_bddBelow hβ0 hβ1 hβ))
    rintro _ ⟨r, rfl⟩
    exact (passageGammaJump_mem_support hβ0 hβ1 hβ r).1
  · apply closure_minimal ?_ Measure.isClosed_support
      (csSup_mem_closure (range_nonempty _) (right_bddAbove hβ0 hβ1 hβ))
    rintro _ ⟨r, rfl⟩
    exact (passageGammaJump_mem_support hβ0 hβ1 hβ r).2

/-- Exact support identification: the Gamma-law support is `[ℓ,u]`. -/
theorem passageGammaLaw_support_eq_Icc :
    ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ).support =
      Icc (passageGammaLower β) (passageGammaUpper β) := by
  apply Subset.antisymm
  · rw [passageGammaLaw_support_jumps]
    apply closure_minimal ?_ isClosed_Icc
    intro y hy
    obtain ⟨r, hr⟩ := mem_iUnion.mp hy
    exact ⟨(csInf_le (left_bddBelow hβ0 hβ1 hβ) (mem_range_self r)).trans hr.1.le,
      hr.2.le.trans (le_csSup (right_bddAbove hβ0 hβ1 hβ) (mem_range_self r))⟩
  · exact (passageGammaLaw_support_ordConn hβ0 hβ1 hβ).out
      (passageGamma_endpoints_mem hβ0 hβ1 hβ).1 (passageGamma_endpoints_mem hβ0 hβ1 hβ).2

/-- The support is a nondegenerate interval with `1-β ≤ ℓ < u ≤ 1/(1-β)`. -/
theorem passageGamma_endpoints_bounds :
    1-β ≤ passageGammaLower β ∧ passageGammaLower β < passageGammaUpper β ∧
      passageGammaUpper β ≤ 1/(1-β) := by
  refine ⟨?_, ?_, ?_⟩
  · exact le_csInf (range_nonempty _)
      (by rintro _ ⟨r, rfl⟩; exact (passageGammaJump_bounds hβ0 hβ1 hβ r).1)
  · exact (csInf_le (left_bddBelow hβ0 hβ1 hβ) (mem_range_self 0)).trans_lt
      ((passageGammaJump_left_lt_right hβ0 hβ1 1).trans_le
        (le_csSup (right_bddAbove hβ0 hβ1 hβ) (mem_range_self 0)))
  · exact csSup_le (range_nonempty _)
      (by rintro _ ⟨r, rfl⟩; exact (passageGammaJump_bounds hβ0 hβ1 hβ r).2)

/-- The complete real cluster set of the Gamma-normalized integer counts is
the single nondegenerate interval `[ℓ,u]`, for every irrational `0<β<1`. -/
theorem passageGamma_cluster_iff (y : ℝ) :
    MapClusterPt y atTop (passageGammaRatio β) ↔
      y ∈ Icc (passageGammaLower β) (passageGammaUpper β) := by
  rw [passageGamma_cluster_iff_support hβ0 hβ1 hβ, passageGammaLaw_support_eq_Icc]

/-- Every nonempty open interval with endpoints in `[ℓ,u]` has positive
Gamma-law probability. -/
theorem passageGammaLaw_Ioo_pos {x y : ℝ}
    (hx : x ∈ Icc (passageGammaLower β) (passageGammaUpper β))
    (hy : y ∈ Icc (passageGammaLower β) (passageGammaUpper β)) (hxy : x < y) :
    0 < ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) (Ioo x y) := by
  obtain ⟨z, hxz, hzy⟩ := exists_between hxy
  have hz : z ∈ ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ).support := by
    rw [passageGammaLaw_support_eq_Icc]
    exact ⟨hx.1.trans hxz.le, hzy.le.trans hy.2⟩
  exact (Measure.mem_support_iff_forall z).mp hz (Ioo x y) (Ioo_mem_nhds hxz hzy)

/-- The Gamma-law CDF is strictly increasing on `[ℓ,u]`. -/
theorem passageGammaLaw_cdf_strictMono :
    StrictMonoOn (fun y => ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ).real (Iic y))
      (Icc (passageGammaLower β) (passageGammaUpper β)) := by
  intro x hx y hy hxy
  have hp : 0 < ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) (Ioc x y) :=
    (passageGammaLaw_Ioo_pos hβ0 hβ1 hβ hx hy hxy).trans_le (measure_mono Ioo_subset_Ioc_self)
  have hr := ENNReal.toReal_pos hp.ne'
    (measure_ne_top ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) (Ioc x y))
  have hd : Disjoint (Iic x) (Ioc x y) := disjoint_left.mpr fun z hz hz' =>
    (not_lt_of_ge hz) hz'.1
  have he := measureReal_union (μ := ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ))
    hd measurableSet_Ioc
  rw [Iic_union_Ioc_eq_Iic hxy.le] at he
  change 0 < ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ).real (Ioc x y) at hr
  linarith

/-- The explicit extended density is lower semicontinuous, including its
infinite values. Continuity or boundedness is not asserted. -/
theorem passageGammaDensity_lsc : LowerSemicontinuous (passageGammaDensity β) := by
  apply lowerSemicontinuous_tsum
  intro r y c hc
  by_cases hy : y ∈ Ioo (passageGammaJumpLeft β (r+1)) (passageGammaJumpRight β (r+1))
  · rw [indicator_of_mem hy] at hc
    have hypos := (passageGammaJumpLeft_pos hβ0 hβ1 hβ (r+1)).trans hy.1
    have hcont : ContinuousAt (fun x : ℝ => ENNReal.ofReal (1/((-Real.log (1-β))*x))) y :=
      ENNReal.continuous_ofReal.continuousAt.comp
        (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
          (mul_ne_zero (scale_pos hβ0 hβ1).ne' hypos.ne'))
    filter_upwards [isOpen_Ioo.mem_nhds hy, hcont.eventually (Ioi_mem_nhds hc)] with z hz hcz
    simpa only [indicator_of_mem hz] using hcz
  · rw [indicator_of_notMem hy] at hc
    exact (not_lt_of_ge bot_le hc).elim

omit hβ in
/-- If rescaled jump intervals of arbitrarily large indices contain a
positive value, the explicit density at that value is infinite. -/
theorem passageGammaDensity_top_of_tails {y : ℝ} (hy : 0 < y)
    (htail : ∀ N : ℕ, ∃ r, N ≤ r ∧
      y ∈ Ioo (passageGammaJumpLeft β (r+1)) (passageGammaJumpRight β (r+1))) :
    passageGammaDensity β y = ∞ := by
  by_contra h
  have ht := ENNReal.tendsto_atTop_zero_of_tsum_ne_top h
  have hk : 0 < ENNReal.ofReal (1/((-Real.log (1-β))*y)) :=
    ENNReal.ofReal_pos.mpr (one_div_pos.mpr (mul_pos (scale_pos hβ0 hβ1) hy))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds hk))
  obtain ⟨r, hr, hyr⟩ := htail N
  have hh := hN r hr
  rw [indicator_of_mem hyr] at hh
  exact lt_irrefl _ hh

/-- The infinite-density points form a Lebesgue-null set. -/
theorem volume_passageGammaDensity_top :
    volume {y | passageGammaDensity β y = ∞} = 0 := by
  have h : ∀ᵐ y ∂volume, passageGammaDensity β y ≠ ∞ :=
    (passageGammaDensity_ae_lt_top hβ0 hβ1 hβ).mono fun _ hy => hy.ne
  simpa only [ae_iff, not_not] using h

end Problems.Juggler.BeattySlope
