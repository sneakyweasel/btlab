import Problems.Juggler.BeattySlopeGammaHausdorff
import Problems.Juggler.BeattySlopeGammaCDF
import Problems.Juggler.BeattySlopeGammaLp

/-! Expanded consumers of the Gamma-normalized first-passage law for every
irrational boundary in `(0,1)`. The original integer counts and the exact
Gamma quotient are written out; no analytic premise is accepted. -/

namespace Problems.Juggler.BeattySlopeGammaChecks

open BeattySlope Filter Topology MeasureTheory Set

/-- The actual counts in the exact Gamma normalization follow the periodic
amplitude `q^δ F(δ)`, for every irrational boundary. -/
theorem actual_gamma_phase (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β) :
    Tendsto (fun r : ℕ => (passageCount β (⌊(r : ℝ)/β⌋₊+1) : ℝ) /
        (Real.Gamma ((r : ℝ)/β)/((r.factorial : ℝ)*Real.Gamma ((r : ℝ)*(1-β)/β+1))) -
      (1-β)^((r : ℝ)/β-⌊(r : ℝ)/β⌋₊)*passageProfile β ((r : ℝ)/β-⌊(r : ℝ)/β⌋₊))
      atTop (𝓝 0) := by
  simpa only [passageGammaRatio, passageGammaScale, passageIndex, passagePhase] using
    passageGamma_phase_asymptotic hβ0 hβ1 hβ

/-- The complete set of subsequential limits of the Gamma-normalized counts
is the nondegenerate interval `[ℓ,u]`. -/
theorem actual_gamma_cluster (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β) :
    {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
      (passageCount β (⌊(r : ℝ)/β⌋₊+1) : ℝ) /
        (Real.Gamma ((r : ℝ)/β)/((r.factorial : ℝ)*Real.Gamma ((r : ℝ)*(1-β)/β+1))))} =
      Icc (passageGammaLower β) (passageGammaUpper β) ∧
    passageGammaLower β < passageGammaUpper β := by
  refine ⟨?_, (passageGamma_endpoints_bounds hβ0 hβ1 hβ).2.1⟩
  ext y
  change MapClusterPt y atTop (passageGammaRatio β) ↔ _
  exact passageGamma_cluster_iff hβ0 hβ1 hβ y

/-- The Gamma law is absolutely continuous, mutually singular with the
binomial-normalized law, and has the explicit density series. -/
theorem actual_gamma_law_type (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β) :
    ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) ≪ volume ∧
    ((passageLaw hβ0 hβ1 hβ) : Measure ℝ).MutuallySingular
      ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) ∧
    ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) = volume.withDensity (passageGammaDensity β) :=
  ⟨passageGammaLaw_absCont hβ0 hβ1 hβ, passageLaw_mutSingular_gamma hβ0 hβ1 hβ,
    passageGammaLaw_eq_withDensity hβ0 hβ1 hβ⟩

/-- The explicit density lies in every `L^p` with `1 ≤ p < 3/2`, and its
infinite-value set has Hausdorff dimension at most two-thirds. -/
theorem actual_gamma_regularity (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β) :
    (∀ p : ℝ, 1 ≤ p → p < 3/2 →
      MemLp (fun y => (passageGammaDensity β y).toReal) (ENNReal.ofReal p) volume) ∧
    dimH {y | passageGammaDensity β y = ⊤} ≤ 2/3 :=
  ⟨fun _ hp hp' => passageGammaDensity_memLp hβ0 hβ1 hβ hp hp',
    passageGammaDensity_top_dimH_le hβ0 hβ1 hβ⟩

#print axioms actual_gamma_phase
#print axioms actual_gamma_cluster
#print axioms actual_gamma_law_type
#print axioms actual_gamma_regularity

end Problems.Juggler.BeattySlopeGammaChecks
