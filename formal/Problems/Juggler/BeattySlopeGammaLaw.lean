import Problems.Juggler.BeattySlopeGammaAmplitude
import Problems.Juggler.BeattySlopeDistribution
import Problems.Juggler.BeattyAmplitudeRegularity

/-!
# The absolutely continuous Gamma first-passage law for every slope

For every irrational `0<β<1`, the exact Gamma-normalized integer counts
converge in distribution to `q^U F(U)`, `q=1-β`, for uniform phase `U`.
The pure-jump factor has derivative zero almost everywhere and the
exponential tilt has a nonzero derivative, so this law is absolutely
continuous, whereas the binomial-normalized law is singular.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory Finset BeattyPhase
open scoped ENNReal BoundedContinuousFunction

/-- The tilted amplitude `q^t F(t)` on the phase line, before periodic extension. -/
noncomputable def passageGammaAmp (β : ℝ) (t : ℝ) : ℝ :=
  (1-β)^t*passageProfile β t

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

/-- The amplitude is Borel measurable even at its dense jumps. -/
theorem passageGammaAmp_measurable : Measurable (passageGammaAmp β) :=
  (Real.continuous_const_rpow (sub_pos.2 hβ1).ne').measurable.mul
    (passageProfile_monotone hβ0 hβ1 hβ).measurable

/-- The amplitude is strictly positive at every real argument. -/
theorem passageGammaAmp_pos (t : ℝ) : 0 < passageGammaAmp β t :=
  mul_pos (Real.rpow_pos_of_pos (sub_pos.2 hβ1) t)
    (lt_of_lt_of_le zero_lt_one (passageProfile_bounds hβ0 hβ1 hβ t).1)

/-- The compact positive envelope `[1-β, 1/(1-β)]` of the amplitude on
the phase interval. -/
theorem passageGammaAmp_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1-β ≤ passageGammaAmp β t ∧ passageGammaAmp β t ≤ 1/(1-β) := by
  have hq : 0 < 1-β := sub_pos.2 hβ1
  have hq1 : 1-β < 1 := by linarith
  have hp := Real.rpow_pos_of_pos hq t
  have hl : 1-β ≤ (1-β)^t := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hq hq1.le ht.2
  have hu : (1-β)^t ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hq hq1.le ht.1
  constructor
  · exact hl.trans (le_mul_of_one_le_right hp.le (passageProfile_bounds hβ0 hβ1 hβ t).1)
  · exact (mul_le_of_le_one_left
      (le_trans zero_le_one (passageProfile_bounds hβ0 hβ1 hβ t).1) hu).trans
        (passageProfile_bounds hβ0 hβ1 hβ t).2

/-- The Gamma first-passage law: the image of uniform phase measure on
`(0,1]` under the exponentially tilted jump profile. -/
noncomputable def passageGammaLaw : ProbabilityMeasure ℝ :=
  unitPhaseLaw.map (passageGammaAmp_measurable hβ0 hβ1 hβ).aemeasurable

/-- The family jump profile has derivative zero almost everywhere; its
range is Lebesgue-null. -/
theorem passageProfile_ae_deriv_zero :
    ∀ᵐ t ∂volume, HasDerivAt (passageProfile β) 0 t := by
  apply ae_hasDerivAt_zero_of_monotone_null_range (passageProfile_monotone hβ0 hβ1 hβ)
  exact measure_mono_null subset_closure
    (passageClusterSet_eq_closure_range hβ0 hβ1 hβ ▸ volume_passageClusterSet hβ0 hβ1 hβ)

/-- The amplitude has derivative `log(q) A(t)` almost everywhere, and that
derivative never vanishes on this full-measure set. -/
theorem passageGammaAmp_ae_deriv :
    ∀ᵐ t ∂volume, HasDerivAt (passageGammaAmp β)
      (Real.log (1-β)*passageGammaAmp β t) t ∧
      Real.log (1-β)*passageGammaAmp β t ≠ 0 := by
  have hq : 0 < 1-β := sub_pos.2 hβ1
  filter_upwards [passageProfile_ae_deriv_zero hβ0 hβ1 hβ] with t ht
  constructor
  · change HasDerivAt (fun x : ℝ => (1-β)^x*passageProfile β x)
      (Real.log (1-β)*((1-β)^t*passageProfile β t)) t
    convert ((hasDerivAt_id t).const_rpow hq).mul ht using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  · exact mul_ne_zero (Real.log_neg hq (by linarith)).ne
      (passageGammaAmp_pos hβ0 hβ1 hβ t).ne'

/-- The Gamma first-passage law is absolutely continuous with respect to
Lebesgue measure, for every irrational `0<β<1`. -/
theorem passageGammaLaw_absCont : ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) ≪ volume :=
  map_restrict_absolutelyContinuous_of_ae_nonzero_deriv
    (passageGammaAmp_measurable hβ0 hβ1 hβ) measurableSet_Ioc
    (ae_restrict_of_ae (passageGammaAmp_ae_deriv hβ0 hβ1 hβ))

/-- In particular the Gamma first-passage law has no atoms. -/
instance passageGammaLaw_nullSingleton :
    NullSingletonClass ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) :=
  ⟨fun _ => passageGammaLaw_absCont hβ0 hβ1 hβ (measure_singleton _)⟩

/-- The binomial-normalized and Gamma-normalized limiting laws of the same
integer counts are mutually singular. -/
theorem passageLaw_mutSingular_gamma :
    ((passageLaw hβ0 hβ1 hβ) : Measure ℝ).MutuallySingular
      ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) :=
  (passageLaw_mutuallySingular_volume hβ0 hβ1 hβ).mono_ac Measure.AbsolutelyContinuous.rfl
    (passageGammaLaw_absCont hβ0 hβ1 hβ)

/-- The binomial accumulation set has zero Gamma-law probability. -/
theorem passageGammaLaw_clusterSet :
    ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) (passageClusterSet β) = 0 :=
  passageGammaLaw_absCont hβ0 hβ1 hβ (volume_passageClusterSet hβ0 hβ1 hβ)

/-- The Gamma-law distribution function is continuous at every threshold. -/
theorem passageGammaLaw_cdf_continuous :
    Continuous (fun y => ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ).real (Iic y)) := by
  apply continuous_iff_continuousAt.2
  intro y
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic (y+1))
      ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) := (integrable_const 1).integrableOn
  have hc := hi.continuousOn_Iic_primitive_Iic.continuousAt
    (Iic_mem_nhds (lt_add_one y))
  simpa using hc

/-- The actual integer counts in the exact Gamma normalization converge
weakly to the absolutely continuous first-passage law, for every irrational
`0<β<1`. -/
theorem passageGamma_empiricalLaw :
    Tendsto (empiricalLaw (passageGammaRatio β)) atTop (𝓝 (passageGammaLaw hβ0 hβ1 hβ)) := by
  have hc : ∀ᵐ t ∂(unitPhaseLaw : Measure ℝ), ContinuousAt (passageGammaAmp β) t := by
    filter_upwards [ae_restrict_of_ae (passageGammaAmp_ae_deriv hβ0 hβ1 hβ)] with t ht
    exact ht.1.continuousAt
  have hm := tendsto_probability_map_of_ae_continuous (passagePhase_equidistributed hβ0 hβ)
    (passageGammaAmp_measurable hβ0 hβ1 hβ) hc
  simp only [empiricalLaw_map _ (passageGammaAmp_measurable hβ0 hβ1 hβ)] at hm
  exact empiricalLaw_tendsto_of_sub_tendsto_zero hm (passageGamma_phase_asymptotic hβ0 hβ1 hβ)

/-- The fraction of the first `N` Gamma-normalized counts at or below any
real threshold tends to the Gamma-law distribution function. -/
theorem passageGamma_threshold_freq (y : ℝ) :
    Tendsto (fun N =>
      (BTCalculus.FourierBoxCounting.count (fun r => passageGammaRatio β r ≤ y) N : ℝ)/N)
      atTop (𝓝 (((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ).real (Iic y))) := by
  apply empiricalLaw_tendsto_count (passageGamma_empiricalLaw hβ0 hβ1 hβ) measurableSet_Iic
  simpa only [frontier_Iic] using
    (measure_singleton y : ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) {y} = 0)

/-- Every bounded continuous observable of the Gamma-normalized counts has
Cesaro averages converging to its integral over the tilted phase profile. -/
theorem passageGamma_average_tendsto (g : ℝ →ᵇ ℝ) :
    Tendsto (fun N => (∑ r ∈ Finset.range N, g (passageGammaRatio β r))/(N : ℝ))
      atTop (𝓝 (∫ t in Ioc (0 : ℝ) 1, g (passageGammaAmp β t))) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (passageGamma_empiricalLaw hβ0 hβ1 hβ) g
  have hi : (∫ y, g y ∂((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ)) =
      ∫ t in Ioc (0 : ℝ) 1, g (passageGammaAmp β t) :=
    integral_map_of_stronglyMeasurable (passageGammaAmp_measurable hβ0 hβ1 hβ)
      g.continuous.stronglyMeasurable
  simp only [integral_empiricalLaw, hi] at h
  exact (tendsto_add_atTop_iff_nat 1).mp h

end Problems.Juggler.BeattySlope
