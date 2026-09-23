import Problems.Juggler.BeattyFirstPassageAmplitude
import Problems.Juggler.BeattyCertificateDistribution
import Problems.Juggler.BeattyAmplitudeRegularity

/-!
# The absolutely continuous first-passage amplitude law

The exact Gamma-normalized integer counts converge in distribution to
`q^U F(U)` for uniform phase `U`. Unlike the law of `F(U)`, this law is
absolutely continuous: the pure-jump factor has derivative zero almost
everywhere and the exponential tilt has a nonzero derivative.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory Finset PaperBThreshold
open scoped ENNReal BoundedContinuousFunction

private theorem beta_pos : 0 < beta := by linarith [beta_gt_five_eighths]
private theorem q_pos : 0 < 1-beta := sub_pos.2 beta_lt_one
private theorem q_lt_one : 1-beta < 1 := by linarith [beta_pos]

/-- The first-passage amplitude on the phase interval, before periodic extension. -/
noncomputable def certificatePhaseAmplitude (t : ℝ) : ℝ :=
  (1-beta)^t*certificateProfile t

/-- The amplitude is Borel measurable even at its dense jumps. -/
theorem certificatePhaseAmplitude_measurable : Measurable certificatePhaseAmplitude :=
  (Real.continuous_const_rpow q_pos.ne').measurable.mul certificateProfile_monotone.measurable

/-- The amplitude is strictly positive at every real argument. -/
theorem certificatePhaseAmplitude_pos (t : ℝ) : 0 < certificatePhaseAmplitude t :=
  mul_pos (Real.rpow_pos_of_pos q_pos t)
    (lt_of_lt_of_le zero_lt_one (certificateProfile_bounds t).1)

/-- A compact positive envelope for all amplitudes on the phase interval. -/
theorem certificatePhaseAmplitude_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1-beta ≤ certificatePhaseAmplitude t ∧
      certificatePhaseAmplitude t ≤ 1+1/terminalRatio := by
  have hp := Real.rpow_pos_of_pos q_pos t
  have hl : 1-beta ≤ (1-beta)^t := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge q_pos q_lt_one.le ht.2
  have hu : (1-beta)^t ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge q_pos q_lt_one.le ht.1
  constructor
  · exact hl.trans (le_mul_of_one_le_right hp.le (certificateProfile_bounds t).1)
  · exact (mul_le_of_le_one_left
      (le_trans zero_le_one (certificateProfile_bounds t).1) hu).trans
        (certificateProfile_bounds t).2

/-- The normalized first-passage law is the image of uniform phase measure
under the exponentially tilted jump profile. -/
noncomputable def certificatePassageLaw : ProbabilityMeasure ℝ :=
  unitPhaseLaw.map certificatePhaseAmplitude_measurable.aemeasurable

/-- The original profile has derivative zero almost everywhere. Its null
range is used directly, without a termwise derivative of an infinite series. -/
theorem certificateProfile_ae_hasDerivAt_zero :
    ∀ᵐ t ∂volume, HasDerivAt certificateProfile 0 t := by
  apply ae_hasDerivAt_zero_of_monotone_null_range certificateProfile_monotone
  exact measure_mono_null subset_closure
    (certificateClusterSet_eq_closure_range ▸ volume_certificateClusterSet)

/-- The amplitude has derivative `log(q) B(t)` almost everywhere, and
that derivative never vanishes on this full-measure set. -/
theorem certificatePhaseAmplitude_ae_nonzero_deriv :
    ∀ᵐ t ∂volume, HasDerivAt certificatePhaseAmplitude
      (Real.log (1-beta)*certificatePhaseAmplitude t) t ∧
      Real.log (1-beta)*certificatePhaseAmplitude t ≠ 0 := by
  filter_upwards [certificateProfile_ae_hasDerivAt_zero] with t ht
  constructor
  · change HasDerivAt (fun x : ℝ => (1-beta)^x*certificateProfile x)
      (Real.log (1-beta)*((1-beta)^t*certificateProfile t)) t
    convert ((hasDerivAt_id t).const_rpow q_pos).mul ht using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  · exact mul_ne_zero (Real.log_neg q_pos q_lt_one).ne
      (certificatePhaseAmplitude_pos t).ne'

/-- Exponential phase tilting changes the singular profile law into an
absolutely continuous probability law. No arithmetic premise is added. -/
theorem certificatePassageLaw_absolutelyContinuous_volume :
    (certificatePassageLaw : Measure ℝ) ≪ volume := by
  exact map_restrict_absolutelyContinuous_of_ae_nonzero_deriv
    certificatePhaseAmplitude_measurable measurableSet_Ioc
    (ae_restrict_of_ae certificatePhaseAmplitude_ae_nonzero_deriv)

/-- In particular the first-passage law has no atoms. -/
instance certificatePassageLaw_nullSingletonClass :
    NullSingletonClass (certificatePassageLaw : Measure ℝ) :=
  ⟨fun _ => certificatePassageLaw_absolutelyContinuous_volume (measure_singleton _)⟩

/-- The two normalizations of the same integer counts have mutually singular
limiting laws: the original profile law is concentrated on a null set. -/
theorem certificateLaw_mutuallySingular_passageLaw :
    (certificateLaw : Measure ℝ).MutuallySingular (certificatePassageLaw : Measure ℝ) :=
  certificateLaw_mutuallySingular_volume.mono_ac Measure.AbsolutelyContinuous.rfl
    certificatePassageLaw_absolutelyContinuous_volume

/-- The original accumulation set has zero probability in the Gamma-normalized law. -/
theorem certificatePassageLaw_clusterSet :
    (certificatePassageLaw : Measure ℝ) certificateClusterSet = 0 :=
  certificatePassageLaw_absolutelyContinuous_volume volume_certificateClusterSet

/-- The first-passage distribution function is continuous at every threshold. -/
theorem certificatePassageLaw_cdf_continuous :
    Continuous (fun y => (certificatePassageLaw : Measure ℝ).real (Iic y)) := by
  apply continuous_iff_continuousAt.2
  intro y
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic (y+1))
      (certificatePassageLaw : Measure ℝ) := (integrable_const 1).integrableOn
  have hc := hi.continuousOn_Iic_primitive_Iic.continuousAt
    (Iic_mem_nhds (lt_add_one y))
  simpa using hc

/-- The actual integer counts in the exact BGL Gamma normalization
converge weakly to the absolutely continuous first-passage law. -/
theorem certificateGammaRatio_empiricalLaw_tendsto :
    Tendsto (empiricalLaw certificateGammaRatio) atTop (𝓝 certificatePassageLaw) := by
  have hc : ∀ᵐ t ∂(unitPhaseLaw : Measure ℝ), ContinuousAt certificatePhaseAmplitude t := by
    filter_upwards [ae_restrict_of_ae certificatePhaseAmplitude_ae_nonzero_deriv] with t ht
    exact ht.1.continuousAt
  have hm := tendsto_probability_map_of_ae_continuous certificatePhase_equidistributed
    certificatePhaseAmplitude_measurable hc
  simp only [empiricalLaw_map _ certificatePhaseAmplitude_measurable] at hm
  exact empiricalLaw_tendsto_of_sub_tendsto_zero hm certificateGammaRatio_phase_asymptotic

/-- The fraction of the actual Gamma-normalized counts below any real
threshold tends to the first-passage distribution function, at every threshold. -/
theorem certificateGammaRatio_threshold_frequency (y : ℝ) :
    Tendsto (fun N =>
      (BTCalculus.FourierBoxCounting.count (fun r => certificateGammaRatio r ≤ y) N : ℝ)/N)
      atTop (𝓝 ((certificatePassageLaw : Measure ℝ).real (Iic y))) := by
  apply empiricalLaw_tendsto_count certificateGammaRatio_empiricalLaw_tendsto measurableSet_Iic
  simpa only [frontier_Iic] using
    (measure_singleton y : (certificatePassageLaw : Measure ℝ) {y} = 0)

/-- Every bounded continuous observable of the Gamma-normalized counts
has the corresponding integral over the explicit tilted phase profile. -/
theorem certificateGammaRatio_average_tendsto (g : ℝ →ᵇ ℝ) :
    Tendsto (fun N => (∑ r ∈ Finset.range N, g (certificateGammaRatio r))/(N : ℝ))
      atTop (𝓝 (∫ t in Ioc (0 : ℝ) 1, g (certificatePhaseAmplitude t))) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    certificateGammaRatio_empiricalLaw_tendsto g
  have hi : (∫ y, g y ∂(certificatePassageLaw : Measure ℝ)) =
      ∫ t in Ioc (0 : ℝ) 1, g (certificatePhaseAmplitude t) :=
    integral_map_of_stronglyMeasurable certificatePhaseAmplitude_measurable
      g.continuous.stronglyMeasurable
  simp only [integral_empiricalLaw, hi] at h
  exact (tendsto_add_atTop_iff_nat 1).mp h

end Problems.Juggler.BeattyPhase
