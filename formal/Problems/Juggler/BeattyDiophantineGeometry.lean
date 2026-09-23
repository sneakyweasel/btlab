import Problems.Juggler.BeattyDiophantineHitting

/-!
# Arithmetic hypotheses for certificate Hausdorff geometry

The actual logarithmic phase orbit inherits quantitative hitting and
Hausdorff bounds from an explicit Diophantine premise. Bounds for every
exponent greater than one already suffice for exact Hausdorff dimension;
the stronger exponent-one bound also gives positive critical measure.
Neither arithmetic premise is supplied for the logarithmic slope here.
-/

namespace Problems.Juggler.BeattyPhase

open Set Filter Topology MeasureTheory PaperBThreshold
open scoped ENNReal

/-- A Diophantine bound for the actual slope supplies its phase-hitting
estimate with an explicit constant and no loss in the exponent. -/
theorem certificatePhase_hitting_of_diophantineLowerBound {c τ : ℝ}
    (hc : 0 < c) (hτ : 0 < τ) (hdio : DiophantineLowerBound (1/beta) c τ) :
    PhaseHittingBound (fun n => certificatePhase (n+1)) (4^τ/c+1) τ := by
  simpa only [PhaseHittingBound, certificatePhase_eq_fract, mul_one_div] using
    phaseHittingBound_of_diophantineLowerBound hc hτ hdio

/-- A uniform Diophantine bound gives a lower Hausdorff dimension for
the actual certificate cluster set. The premise remains an argument. -/
theorem certificateClusterSet_dimH_lower_of_diophantineLowerBound {c τ : ℝ}
    (hc : 0 < c) (hτ : 0 < τ) (hdio : DiophantineLowerBound (1/beta) c τ) :
    ENNReal.ofReal ((2/3 : ℝ)/τ) ≤ dimH certificateClusterSet :=
  certificateClusterSet_dimH_lower_of_phaseHitting (by positivity) hτ
    (certificatePhase_hitting_of_diophantineLowerBound hc hτ hdio)

/-- The arithmetic lower bound also gives positive Hausdorff measure
at the lower-bound exponent, not only a dimension inequality. -/
theorem certificateClusterSet_hausdorffMeasure_ne_zero_of_diophantineLowerBound {c τ : ℝ}
    (hc : 0 < c) (hτ : 0 < τ) (hdio : DiophantineLowerBound (1/beta) c τ) :
    Measure.hausdorffMeasure ((2/3 : ℝ)/τ) certificateClusterSet ≠ 0 :=
  certificateClusterSet_hausdorffMeasure_ne_zero_of_phaseHitting (by positivity) hτ
    (certificatePhase_hitting_of_diophantineLowerBound hc hτ hdio)

/-- Bad approximability of the actual logarithmic slope would give
positive finite critical Hausdorff measure. Bad approximability is not
established here. -/
theorem certificateClusterSet_hausdorffMeasure_pos_finite_of_badApprox {c : ℝ}
    (hc : 0 < c) (hdio : DiophantineLowerBound (1/beta) c 1) :
    0 < Measure.hausdorffMeasure (2/3 : ℝ) certificateClusterSet ∧
    Measure.hausdorffMeasure (2/3 : ℝ) certificateClusterSet < ⊤ :=
  certificateClusterSet_hausdorffMeasure_pos_finite_of_phaseHitting (by positivity)
    (certificatePhase_hitting_of_diophantineLowerBound hc zero_lt_one hdio)

/-- A family of Diophantine bounds at every exponent strictly above one
already gives Hausdorff dimension two-thirds. Its constants may depend on
the exponent; this does not assert positive critical Hausdorff measure. -/
theorem certificateClusterSet_dimH_eq_of_diophantine_family
    (hdio : ∀ τ : ℝ, 1 < τ → ∃ c : ℝ, 0 < c ∧ DiophantineLowerBound (1/beta) c τ) :
    dimH certificateClusterSet = (2/3 : ℝ≥0∞) := by
  apply le_antisymm certificateClusterSet_dimH_upper
  have hcont : ContinuousAt (fun τ : ℝ => ENNReal.ofReal ((2/3 : ℝ)/τ)) 1 :=
    ENNReal.continuous_ofReal.continuousAt.comp
      (continuousAt_const.div continuousAt_id (by norm_num))
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 1)
  have hle : ENNReal.ofReal ((2/3 : ℝ)/1) ≤ dimH certificateClusterSet := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    obtain ⟨c,hc,hbound⟩ := hdio τ hτ
    exact certificateClusterSet_dimH_lower_of_diophantineLowerBound hc
      (zero_lt_one.trans hτ) hbound
  simpa only [div_one, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3),
    ENNReal.ofReal_ofNat] using hle

end Problems.Juggler.BeattyPhase
