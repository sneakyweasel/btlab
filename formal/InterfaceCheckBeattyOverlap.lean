import Problems.Juggler.BeattyOverlapEnergy

/-! Expanded consumer of the actual Gamma-density overlap criterion. -/

namespace Problems.Juggler.BeattyOverlapChecks

open BeattyPhase PaperBThreshold Set MeasureTheory
open scoped ENNReal

/-- L2 membership of the actual density, with the complete interval
overlap sum expanded. This equivalence has no finiteness hypothesis;
it does not assert either side independently. -/
theorem actual_density_overlap_criterion :
    MemLp (fun y => (certificatePassageDensity y).toReal) 2 volume ↔
      (∑' r : ℕ, ∑' s : ℕ, ENNReal.ofReal
        (min ((1-beta)^certificatePhase (r+1)*
                (certificateProfile (certificatePhase (r+1))+certificateWeight (r+1)))
             ((1-beta)^certificatePhase (s+1)*
                (certificateProfile (certificatePhase (s+1))+certificateWeight (s+1))) -
         max ((1-beta)^certificatePhase (r+1)*certificateProfile (certificatePhase (r+1)))
             ((1-beta)^certificatePhase (s+1)*certificateProfile (certificatePhase (s+1))))) < ∞ :=
  certificatePassageDensity_memLp_two_iff

#print axioms actual_density_overlap_criterion
#print axioms lintegral_tsum_indicator_sq
#print axioms certificateJumpMultiplicity_measurable
#print axioms certificateJumpMultiplicity_lintegral_sq
#print axioms certificatePassageDensity_eq_kernel_mul_multiplicity
#print axioms certificatePassageDensity_lintegral_sq_lt_top_iff
#print axioms certificatePassageDensity_memLp_two_iff

end Problems.Juggler.BeattyOverlapChecks
