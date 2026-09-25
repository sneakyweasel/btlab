import Problems.Juggler.BeattySlopeGlobalLaw
import Problems.Juggler.BeattySlopeLawContinuity
import Problems.Juggler.BeattySlopeMeasureDim

/-! Expanded consumers of the global empirical-law theorem. The ratio is
written through the original integer first-passage counts, the crossing
floor and the binomial normalization; no analytic, equidistribution or
arithmetic premise is accepted. -/

namespace Problems.Juggler.BeattySlopeGlobalChecks

open BeattySlope BeattyPhase Filter Topology MeasureTheory Set
open scoped BoundedContinuousFunction

/-- For every real slope above one, rational or irrational, the empirical
law of the original integer ratios converges weakly to a probability law. -/
theorem actual_global_law (α : ℝ) (hα : 1 < α) :
    ∃ μ : ProbabilityMeasure ℝ, Tendsto (empiricalLaw (fun r : ℕ =>
      (r : ℝ)*(passageCount (1/α) (⌊(r : ℝ)/(1/α)⌋₊+1) : ℝ) /
        ((⌊(r : ℝ)/(1/α)⌋₊-1).choose (r-1) : ℝ))) atTop (𝓝 μ) :=
  exists_passageRatio_law hα

/-- The limit is explicit for every slope: bounded continuous averages of the
limit law are phase averages of the actual cumulative profile. -/
theorem actual_global_law_explicit (α : ℝ) (hα : 1 < α) (g : ℝ →ᵇ ℝ) :
    Tendsto (fun N : ℕ => ∫ y, g y ∂(empiricalLaw (passageRatio (1/α)) N : Measure ℝ)) atTop
      (𝓝 (∫ t in Ioc (0 : ℝ) 1, g (passageProfile (1/α) t))) := by
  have hα0 : 0 < α := by linarith
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (passageRatio_law_slope hα) g
  rwa [integral_passageProfileLaw (one_div_pos.2 hα0) ((div_lt_one hα0).2 hα)] at h

/-- At a rational slope `a/b` the limit is the uniform law on the `b` values
of the step profile at `(j+1)/b`. -/
theorem actual_rational_law (a b : ℕ) (hb : 0 < b) (hba : b < a) (g : ℝ →ᵇ ℝ) :
    Tendsto (fun N : ℕ => ∫ y, g y ∂(empiricalLaw (passageRatio ((b : ℝ)/a)) N : Measure ℝ))
      atTop (𝓝 ((1/(b : ℝ))*∑ j ∈ Finset.range b,
        g (passageProfile ((b : ℝ)/a) ((j+1 : ℝ)/b)))) := by
  have ha : (0 : ℝ) < a := by exact_mod_cast hb.trans hba
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hba' : (b : ℝ) < a := by exact_mod_cast hba
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (passageRatio_law_tendsto (div_pos hb' ha) ((div_lt_one ha).2 hba')) g
  rwa [passageProfileLaw_rational hb hba] at h

/-- At every boundary the actual ratios follow the right trace of the
cumulative profile at their Beatty phase. -/
theorem actual_right_phase (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun r : ℕ => (r : ℝ)*(passageCount β (⌊(r : ℝ)/β⌋₊+1) : ℝ) /
        ((⌊(r : ℝ)/β⌋₊-1).choose (r-1) : ℝ) -
      passageProfileRight β ((r : ℝ)/β-⌊(r : ℝ)/β⌋₊)) atTop (𝓝 0) := by
  simpa only [passageRatio, passageIndex, passagePhase] using
    passageRatio_sub_right_tendsto hβ0 hβ1

/-- The limit law of the actual ratios depends on the slope right-continuously
everywhere and continuously exactly at irrational slopes; at `a/b` the limit
from below differs from the value. -/
theorem actual_law_slope_map (α₀ : ℝ) (h : 1 < α₀) :
    Tendsto (empiricalLaw (passageRatio (1/α₀))) atTop (𝓝 (passageProfileLaw (1/α₀))) ∧
    ContinuousWithinAt (fun α => passageProfileLaw (1/α)) (Set.Ici α₀) α₀ ∧
    (ContinuousAt (fun α => passageProfileLaw (1/α)) α₀ ↔ Irrational α₀) :=
  ⟨passageRatio_law_slope h, passageLaw_slope_rightCont h, passageLaw_slope_contAt_iff h⟩

/-- At every irrational slope above one of Diophantine class `ν`, the
empirical law of the original integer ratios converges to a law whose lower
Hausdorff dimension is exactly `2/(2+ν)`. -/
theorem actual_law_dimension (α ν : ℝ) (hα : 1 < α) (hirr : Irrational α) (hν : 1 ≤ ν)
    (hcls : DiophClass α ν) :
    ∃ μ : ProbabilityMeasure ℝ, Tendsto (empiricalLaw (fun r : ℕ =>
      (r : ℝ)*(passageCount (1/α) (⌊(r : ℝ)/(1/α)⌋₊+1) : ℝ) /
        ((⌊(r : ℝ)/(1/α)⌋₊-1).choose (r-1) : ℝ))) atTop (𝓝 μ) ∧
      lawDimH (μ : Measure ℝ) = ENNReal.ofReal (2/(2+ν)) := by
  have hα0 : 0 < α := by linarith
  refine ⟨passageProfileLaw (1/α), passageRatio_law_slope hα, ?_⟩
  rw [passageProfileLaw_irrational (one_div_pos.2 hα0) ((div_lt_one hα0).2 hα)
    (by simpa using hirr.inv)]
  exact passageLaw_lawDimH_eq hα hirr hν hcls

/-- At every Liouville slope the limit law of the original integer ratios has
lower Hausdorff dimension zero. -/
theorem actual_law_dimension_liouville (α : ℝ) (hα : 1 < α) (hL : Liouville α) :
    ∃ μ : ProbabilityMeasure ℝ, Tendsto (empiricalLaw (fun r : ℕ =>
      (r : ℝ)*(passageCount (1/α) (⌊(r : ℝ)/(1/α)⌋₊+1) : ℝ) /
        ((⌊(r : ℝ)/(1/α)⌋₊-1).choose (r-1) : ℝ))) atTop (𝓝 μ) ∧
      lawDimH (μ : Measure ℝ) = 0 := by
  have hα0 : 0 < α := by linarith
  refine ⟨passageProfileLaw (1/α), passageRatio_law_slope hα, ?_⟩
  rw [passageProfileLaw_irrational (one_div_pos.2 hα0) ((div_lt_one hα0).2 hα)
    (by simpa using hL.irrational.inv)]
  exact passageLaw_lawDimH_liouville hα hL

#print axioms actual_global_law
#print axioms actual_global_law_explicit
#print axioms actual_rational_law
#print axioms actual_right_phase
#print axioms actual_law_slope_map
#print axioms actual_law_dimension
#print axioms actual_law_dimension_liouville

end Problems.Juggler.BeattySlopeGlobalChecks
