import Problems.Juggler.BeattySlopeCluster
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The singular continuous first-passage law for every irrational slope

The actual normalized integer passage counts converge in distribution to
the image of uniform phase measure under the explicit passage profile.
Strict increase makes this law atomless. Its concentration on the previously
identified null accumulation set makes it singular with respect to Lebesgue
measure. No equidistribution or analytic approximation premise remains.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory Finset BeattyPhase
open scoped ENNReal BoundedContinuousFunction

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

omit hβ1 in
/-- The actual crossing phases have the uniform empirical limiting law for
any irrational boundary in `(0,1)`, without a convergence rate. -/
theorem passagePhase_equidistributed :
    Tendsto (empiricalLaw (passagePhase β)) atTop (𝓝 unitPhaseLaw) := by
  have he : passagePhase β = fun n : ℕ => Int.fract ((n : ℝ)*(1/β)) := by
    funext n
    simp only [passagePhase_eq_fract hβ0, div_eq_mul_inv, one_mul]
  rw [he]
  exact irrational_rotation_equidistributed (by simpa using hβ.inv : Irrational (1/β))

/-- The passage limiting law is the image of uniform phase measure
under the explicit cumulative jump profile. -/
noncomputable def passageLaw : ProbabilityMeasure ℝ :=
  unitPhaseLaw.map (passageProfile_monotone hβ0 hβ1 hβ).measurable.aemeasurable

/-- Monotonicity makes the profile continuous at almost every uniform phase,
despite the density of its jump locations. -/
theorem passageProfile_ae_continuous :
    ∀ᵐ x ∂(unitPhaseLaw : Measure ℝ), ContinuousAt (passageProfile β) x := by
  have h := (passageProfile_monotone hβ0 hβ1 hβ).countable_not_continuousAt.ae_notMem
    (volume : Measure ℝ)
  exact ae_restrict_of_ae (by simpa using h)

/-- The empirical law of the original binomial-normalized integer counts
converges weakly to the explicitly defined passage probability law. -/
theorem passageRatio_empiricalLaw_tendsto :
    Tendsto (empiricalLaw (passageRatio β)) atTop (𝓝 (passageLaw hβ0 hβ1 hβ)) := by
  have hm := tendsto_probability_map_of_ae_continuous (passagePhase_equidistributed hβ0 hβ)
    (passageProfile_monotone hβ0 hβ1 hβ).measurable (passageProfile_ae_continuous hβ0 hβ1 hβ)
  simp only [empiricalLaw_map _ (passageProfile_monotone hβ0 hβ1 hβ).measurable] at hm
  exact empiricalLaw_tendsto_of_sub_tendsto_zero hm (passage_phase_asymptotic_odd_count hβ0 hβ1 hβ)

/-- Every singleton has zero passage limiting mass. Strict increase on
the phase interval prevents a positive-measure set of phases sharing a value. -/
theorem passageLaw_singleton (y : ℝ) : ((passageLaw hβ0 hβ1 hβ) : Measure ℝ) {y} = 0 := by
  rw [passageLaw, ProbabilityMeasure.map_apply' _ _ (measurableSet_singleton y)]
  change (volume.restrict (Ioc 0 1)) ((passageProfile β) ⁻¹' {y}) = 0
  rw [Measure.restrict_apply ((passageProfile_monotone hβ0 hβ1 hβ).measurable
    (measurableSet_singleton y))]
  apply Set.Subsingleton.measure_zero
  intro a ha b hb
  apply (passageProfile_strictMonoOn hβ0 hβ1 hβ).injOn
    ⟨ha.2.1.le, ha.2.2⟩ ⟨hb.2.1.le, hb.2.2⟩
  exact ha.1.trans hb.1.symm

/-- The passage limiting law is atomless. -/
instance passageLaw_nullSingletonClass : NullSingletonClass ((passageLaw hβ0 hβ1 hβ) : Measure ℝ) :=
  ⟨(passageLaw_singleton hβ0 hβ1 hβ)⟩

/-- The passage cumulative distribution function is continuous everywhere. -/
theorem passageLaw_cdf_continuous :
    Continuous (fun y => ((passageLaw hβ0 hβ1 hβ) : Measure ℝ).real (Iic y)) := by
  apply continuous_iff_continuousAt.2
  intro y
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic (y+1))
      ((passageLaw hβ0 hβ1 hβ) : Measure ℝ) := (integrable_const 1).integrableOn
  have hc := hi.continuousOn_Iic_primitive_Iic.continuousAt
    (Iic_mem_nhds (lt_add_one y))
  simpa using hc

/-- The limiting law gives zero mass outside the explicit accumulation set. -/
theorem passageLaw_compl_clusterSet :
    ((passageLaw hβ0 hβ1 hβ) : Measure ℝ) (passageClusterSet β)ᶜ = 0 := by
  rw [passageLaw, ProbabilityMeasure.map_apply' _ _
    (isCompact_passageClusterSet hβ0 hβ1 hβ).isClosed.measurableSet.compl]
  have he : (passageProfile β) ⁻¹' (passageClusterSet β)ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    apply hx
    rw [(passageClusterSet_eq_closure_range hβ0 hβ1 hβ)]
    exact subset_closure (mem_range_self x)
  rw [he, measure_empty]

/-- The complete accumulation set has full passage limiting probability. -/
theorem passageLaw_clusterSet :
    ((passageLaw hβ0 hβ1 hβ) : Measure ℝ) (passageClusterSet β) = 1 := by
  have h := measure_add_measure_compl (isCompact_passageClusterSet hβ0 hβ1 hβ).isClosed.measurableSet
    (μ := ((passageLaw hβ0 hβ1 hβ) : Measure ℝ))
  simpa only [(passageLaw_compl_clusterSet hβ0 hβ1 hβ), add_zero, measure_univ] using h

/-- The passage law is singular with respect to real Lebesgue measure. -/
theorem passageLaw_mutuallySingular_volume :
    ((passageLaw hβ0 hβ1 hβ) : Measure ℝ).MutuallySingular volume := by
  exact ⟨(passageClusterSet β)ᶜ,
    (isCompact_passageClusterSet hβ0 hβ1 hβ).isClosed.measurableSet.compl,
    (passageLaw_compl_clusterSet hβ0 hβ1 hβ), by simpa using (volume_passageClusterSet hβ0 hβ1 hβ)⟩

/-- The continuous distribution function inverts the strictly increasing
phase profile: the mass below `F(t)` is exactly `t` on the unit interval. -/
theorem passageLaw_Iic_profile {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ((passageLaw hβ0 hβ1 hβ) : Measure ℝ) (Iic ((passageProfile β) t)) = ENNReal.ofReal t := by
  rw [passageLaw, ProbabilityMeasure.map_apply' _ _ measurableSet_Iic]
  change (volume.restrict (Ioc 0 1)) ((passageProfile β) ⁻¹' Iic ((passageProfile β) t)) = _
  rw [Measure.restrict_apply ((passageProfile_monotone hβ0 hβ1 hβ).measurable measurableSet_Iic)]
  have he : (passageProfile β) ⁻¹' Iic ((passageProfile β) t) ∩ Ioc 0 1 = Ioc 0 t := by
    ext x
    constructor
    · rintro ⟨hx, hxI⟩
      refine ⟨hxI.1, ?_⟩
      by_contra hxt
      exact (not_lt_of_ge hx) ((passageProfile_strictMonoOn hβ0 hβ1 hβ) ht
        ⟨hxI.1.le, hxI.2⟩ (lt_of_not_ge hxt))
    · intro hx
      exact ⟨(passageProfile_monotone hβ0 hβ1 hβ) hx.2, hx.1, hx.2.trans ht.2⟩
  rw [he, Real.volume_Ioc, sub_zero]

/-- Every closed passage jump interval has zero limiting mass, including
both endpoints even though they are subsequential limits of the counts. -/
theorem passageLaw_closed_gap (r : ℕ) :
    ((passageLaw hβ0 hβ1 hβ) : Measure ℝ)
      (Icc ((passageProfile β) ((passagePhase β) (r+1)))
        ((passageProfile β) ((passagePhase β) (r+1)) + (passageJumpWeight β) (r+1))) = 0 := by
  rw [← measure_congr (Ioo_ae_eq_Icc (μ := ((passageLaw hβ0 hβ1 hβ) : Measure ℝ)))]
  apply measure_mono_null _ (passageLaw_compl_clusterSet hβ0 hβ1 hβ)
  intro y hy hK
  exact hK.2 (Set.mem_iUnion.2 ⟨r, hy⟩)

/-- Each jump interval of the phase profile becomes a flat interval of the
continuous limiting distribution function, at exactly the corresponding phase. -/
theorem passageLaw_Iic_gap (r : ℕ) {y : ℝ}
    (hy : y ∈ Icc ((passageProfile β) ((passagePhase β) (r+1)))
      ((passageProfile β) ((passagePhase β) (r+1)) + (passageJumpWeight β) (r+1))) :
    ((passageLaw hβ0 hβ1 hβ) : Measure ℝ) (Iic y) = ENNReal.ofReal ((passagePhase β) (r+1)) := by
  have hz : ((passageLaw hβ0 hβ1 hβ) : Measure ℝ)
      (Ioc ((passageProfile β) ((passagePhase β) (r+1))) y) = 0 := by
    apply measure_mono_null _ ((passageLaw_closed_gap hβ0 hβ1 hβ) r)
    intro x hx
    exact ⟨hx.1.le, hx.2.trans hy.2⟩
  rw [← Set.Iic_union_Ioc_eq_Iic hy.1, measure_union (by
    exact Set.disjoint_left.2 (fun _ hx hx' => not_lt_of_ge hx hx'.1)) measurableSet_Ioc,
    hz, add_zero]
  exact (passageLaw_Iic_profile hβ0 hβ1 hβ)
    ⟨((passagePhase_mem_Ico hβ0) _).1, ((passagePhase_mem_Ico hβ0) _).2.le⟩

/-- At every real threshold the sampling frequency has the limiting
distribution value; atomlessness removes all threshold exceptions. -/
theorem passageRatio_threshold_frequency (y : ℝ) :
    Tendsto (fun N =>
      (BTCalculus.FourierBoxCounting.count (fun r => (passageRatio β) r ≤ y) N : ℝ) / N)
      atTop (𝓝 (((passageLaw hβ0 hβ1 hβ) : Measure ℝ).real (Iic y))) := by
  apply empiricalLaw_tendsto_count (passageRatio_empiricalLaw_tendsto hβ0 hβ1 hβ) measurableSet_Iic
  simpa only [frontier_Iic] using (passageLaw_singleton hβ0 hβ1 hβ) y

/-- The limiting fraction of counts at or below `F(t)` is the phase `t`
itself, including at every jump threshold. -/
theorem passageRatio_profile_threshold_frequency {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun N =>
      (BTCalculus.FourierBoxCounting.count
        (fun r => (passageRatio β) r ≤ (passageProfile β) t) N : ℝ) / N)
      atTop (𝓝 t) := by
  simpa only [Measure.real, (passageLaw_Iic_profile hβ0 hβ1 hβ) ht,
    ENNReal.toReal_ofReal ht.1] using (passageRatio_threshold_frequency hβ0 hβ1 hβ) ((passageProfile β) t)

/-- Test-function form of the empirical limit, with the first `N` actual
counts and the phase integral written explicitly. -/
theorem passageRatio_average_tendsto (g : ℝ →ᵇ ℝ) :
    Tendsto (fun N => (∑ r ∈ Finset.range N, g ((passageRatio β) r)) / (N : ℝ))
      atTop (𝓝 (∫ x in Ioc (0 : ℝ) 1, g ((passageProfile β) x))) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (passageRatio_empiricalLaw_tendsto hβ0 hβ1 hβ) g
  have hi : (∫ y, g y ∂((passageLaw hβ0 hβ1 hβ) : Measure ℝ)) =
      ∫ x in Ioc (0 : ℝ) 1, g ((passageProfile β) x) :=
    integral_map_of_stronglyMeasurable (passageProfile_monotone hβ0 hβ1 hβ).measurable
      g.continuous.stronglyMeasurable
  simp only [integral_empiricalLaw, hi] at h
  exact (tendsto_add_atTop_iff_nat 1).mp h

end Problems.Juggler.BeattySlope
