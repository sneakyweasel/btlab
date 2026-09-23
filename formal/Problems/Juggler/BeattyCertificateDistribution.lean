import Problems.Juggler.BeattyPhaseEquidistribution
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The singular continuous empirical certificate law

The actual normalized integer certificate counts converge in distribution to
the image of uniform phase measure under the explicit certificate profile.
Strict increase makes this law atomless. Its concentration on the previously
identified null accumulation set makes it singular with respect to Lebesgue
measure. No equidistribution or analytic approximation premise remains.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory Finset
open scoped ENNReal BoundedContinuousFunction

/-- The certificate limiting law is the image of uniform phase measure
under the explicit cumulative jump profile. -/
noncomputable def certificateLaw : ProbabilityMeasure ℝ :=
  unitPhaseLaw.map certificateProfile_monotone.measurable.aemeasurable

/-- Monotonicity makes the profile continuous at almost every uniform phase,
despite the density of its jump locations. -/
theorem certificateProfile_ae_continuous :
    ∀ᵐ x ∂(unitPhaseLaw : Measure ℝ), ContinuousAt certificateProfile x := by
  have h := certificateProfile_monotone.countable_not_continuousAt.ae_notMem
    (volume : Measure ℝ)
  exact ae_restrict_of_ae (by simpa using h)

/-- The empirical law of the original binomial-normalized integer counts
converges weakly to the explicitly defined certificate probability law. -/
theorem certificateRatio_empiricalLaw_tendsto :
    Tendsto (empiricalLaw certificateRatio) atTop (𝓝 certificateLaw) := by
  have hm := tendsto_probability_map_of_ae_continuous certificatePhase_equidistributed
    certificateProfile_monotone.measurable certificateProfile_ae_continuous
  simp only [empiricalLaw_map _ certificateProfile_monotone.measurable] at hm
  exact empiricalLaw_tendsto_of_sub_tendsto_zero hm certificate_phase_asymptotic

/-- Every singleton has zero certificate limiting mass. Strict increase on
the phase interval prevents a positive-measure set of phases sharing a value. -/
theorem certificateLaw_singleton (y : ℝ) : (certificateLaw : Measure ℝ) {y} = 0 := by
  rw [certificateLaw, ProbabilityMeasure.map_apply' _ _ (measurableSet_singleton y)]
  change (volume.restrict (Ioc 0 1)) (certificateProfile ⁻¹' {y}) = 0
  rw [Measure.restrict_apply (certificateProfile_monotone.measurable
    (measurableSet_singleton y))]
  apply Set.Subsingleton.measure_zero
  intro a ha b hb
  apply certificateProfile_strictMonoOn.injOn
    ⟨ha.2.1.le, ha.2.2⟩ ⟨hb.2.1.le, hb.2.2⟩
  exact ha.1.trans hb.1.symm

/-- The certificate limiting law is atomless. -/
instance certificateLaw_nullSingletonClass : NullSingletonClass (certificateLaw : Measure ℝ) :=
  ⟨certificateLaw_singleton⟩

/-- The certificate cumulative distribution function is continuous everywhere. -/
theorem certificateLaw_cdf_continuous :
    Continuous (fun y => (certificateLaw : Measure ℝ).real (Iic y)) := by
  apply continuous_iff_continuousAt.2
  intro y
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic (y+1))
      (certificateLaw : Measure ℝ) := (integrable_const 1).integrableOn
  have hc := hi.continuousOn_Iic_primitive_Iic.continuousAt
    (Iic_mem_nhds (lt_add_one y))
  simpa using hc

/-- The limiting law gives zero mass outside the explicit accumulation set. -/
theorem certificateLaw_compl_clusterSet :
    (certificateLaw : Measure ℝ) certificateClusterSetᶜ = 0 := by
  rw [certificateLaw, ProbabilityMeasure.map_apply' _ _
    isCompact_certificateClusterSet.isClosed.measurableSet.compl]
  have he : certificateProfile ⁻¹' certificateClusterSetᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    apply hx
    rw [certificateClusterSet_eq_closure_range]
    exact subset_closure (mem_range_self x)
  rw [he, measure_empty]

/-- The complete accumulation set has full certificate limiting probability. -/
theorem certificateLaw_clusterSet :
    (certificateLaw : Measure ℝ) certificateClusterSet = 1 := by
  have h := measure_add_measure_compl isCompact_certificateClusterSet.isClosed.measurableSet
    (μ := (certificateLaw : Measure ℝ))
  simpa only [certificateLaw_compl_clusterSet, add_zero, measure_univ] using h

/-- The certificate law is singular with respect to real Lebesgue measure. -/
theorem certificateLaw_mutuallySingular_volume :
    (certificateLaw : Measure ℝ).MutuallySingular volume := by
  exact ⟨certificateClusterSetᶜ,
    isCompact_certificateClusterSet.isClosed.measurableSet.compl,
    certificateLaw_compl_clusterSet, by simpa using volume_certificateClusterSet⟩

/-- The continuous distribution function inverts the strictly increasing
phase profile: the mass below `F(t)` is exactly `t` on the unit interval. -/
theorem certificateLaw_Iic_profile {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (certificateLaw : Measure ℝ) (Iic (certificateProfile t)) = ENNReal.ofReal t := by
  rw [certificateLaw, ProbabilityMeasure.map_apply' _ _ measurableSet_Iic]
  change (volume.restrict (Ioc 0 1)) (certificateProfile ⁻¹' Iic (certificateProfile t)) = _
  rw [Measure.restrict_apply (certificateProfile_monotone.measurable measurableSet_Iic)]
  have he : certificateProfile ⁻¹' Iic (certificateProfile t) ∩ Ioc 0 1 = Ioc 0 t := by
    ext x
    constructor
    · rintro ⟨hx, hxI⟩
      refine ⟨hxI.1, ?_⟩
      by_contra hxt
      exact (not_lt_of_ge hx) (certificateProfile_strictMonoOn ht
        ⟨hxI.1.le, hxI.2⟩ (lt_of_not_ge hxt))
    · intro hx
      exact ⟨certificateProfile_monotone hx.2, hx.1, hx.2.trans ht.2⟩
  rw [he, Real.volume_Ioc, sub_zero]

/-- Every closed certificate jump interval has zero limiting mass, including
both endpoints even though they are subsequential limits of the counts. -/
theorem certificateLaw_closed_gap (r : ℕ) :
    (certificateLaw : Measure ℝ)
      (Icc (certificateProfile (certificatePhase (r+1)))
        (certificateProfile (certificatePhase (r+1)) + certificateWeight (r+1))) = 0 := by
  rw [← measure_congr (Ioo_ae_eq_Icc (μ := (certificateLaw : Measure ℝ)))]
  apply measure_mono_null _ certificateLaw_compl_clusterSet
  intro y hy hK
  exact hK.2 (Set.mem_iUnion.2 ⟨r, hy⟩)

/-- Each jump interval of the phase profile becomes a flat interval of the
continuous limiting distribution function, at exactly the corresponding phase. -/
theorem certificateLaw_Iic_gap (r : ℕ) {y : ℝ}
    (hy : y ∈ Icc (certificateProfile (certificatePhase (r+1)))
      (certificateProfile (certificatePhase (r+1)) + certificateWeight (r+1))) :
    (certificateLaw : Measure ℝ) (Iic y) = ENNReal.ofReal (certificatePhase (r+1)) := by
  have hz : (certificateLaw : Measure ℝ)
      (Ioc (certificateProfile (certificatePhase (r+1))) y) = 0 := by
    apply measure_mono_null _ (certificateLaw_closed_gap r)
    intro x hx
    exact ⟨hx.1.le, hx.2.trans hy.2⟩
  rw [← Set.Iic_union_Ioc_eq_Iic hy.1, measure_union (by
    exact Set.disjoint_left.2 (fun _ hx hx' => not_lt_of_ge hx hx'.1)) measurableSet_Ioc,
    hz, add_zero]
  exact certificateLaw_Iic_profile
    ⟨(certificatePhase_mem_Ico _).1, (certificatePhase_mem_Ico _).2.le⟩

/-- At every real threshold the sampling frequency has the limiting
distribution value; atomlessness removes all threshold exceptions. -/
theorem certificateRatio_threshold_frequency (y : ℝ) :
    Tendsto (fun N =>
      (BTCalculus.FourierBoxCounting.count (fun r => certificateRatio r ≤ y) N : ℝ) / N)
      atTop (𝓝 ((certificateLaw : Measure ℝ).real (Iic y))) := by
  apply empiricalLaw_tendsto_count certificateRatio_empiricalLaw_tendsto measurableSet_Iic
  simpa only [frontier_Iic] using certificateLaw_singleton y

/-- The limiting fraction of counts at or below `F(t)` is the phase `t`
itself, including at every jump threshold. -/
theorem certificateRatio_profile_threshold_frequency {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun N =>
      (BTCalculus.FourierBoxCounting.count
        (fun r => certificateRatio r ≤ certificateProfile t) N : ℝ) / N)
      atTop (𝓝 t) := by
  simpa only [Measure.real, certificateLaw_Iic_profile ht,
    ENNReal.toReal_ofReal ht.1] using certificateRatio_threshold_frequency (certificateProfile t)

/-- Test-function form of the empirical limit, with the first `N` actual
counts and the phase integral written explicitly. -/
theorem certificateRatio_average_tendsto (g : ℝ →ᵇ ℝ) :
    Tendsto (fun N => (∑ r ∈ Finset.range N, g (certificateRatio r)) / (N : ℝ))
      atTop (𝓝 (∫ x in Ioc (0 : ℝ) 1, g (certificateProfile x))) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    certificateRatio_empiricalLaw_tendsto g
  have hi : (∫ y, g y ∂(certificateLaw : Measure ℝ)) =
      ∫ x in Ioc (0 : ℝ) 1, g (certificateProfile x) :=
    integral_map_of_stronglyMeasurable certificateProfile_monotone.measurable
      g.continuous.stronglyMeasurable
  simp only [integral_empiricalLaw, hi] at h
  exact (tendsto_add_atTop_iff_nat 1).mp h

end Problems.Juggler.BeattyPhase
