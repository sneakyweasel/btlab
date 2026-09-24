import Problems.Juggler.BeattySlopeAsymptotic
import Problems.Juggler.BeattySlopeSpecialization
import Problems.Juggler.BeattyCertificateSeries

/-!
# Exact specialization of the family jump profile

The actual crossing indices, phases, weights and strict cumulative profile
agree with the original logarithmic definitions at every finite index.
This bridge lets the original phase theorem use the general proof, without
identifying the distinct tilted and fair-walk survivor profiles.
-/

namespace Problems.Juggler.BeattySlope

open PaperBThreshold

/-- The general pre-crossing index is the original certificate index at
the logarithmic boundary. -/
theorem passageIndex_logarithmic (r : ℕ) :
    passageIndex beta r = BeattyPhase.certificateIndex r := rfl

/-- The general phase agrees exactly with the original certificate phase. -/
theorem passagePhase_logarithmic (r : ℕ) :
    passagePhase beta r = BeattyPhase.certificatePhase r := rfl

/-- The critical Bernoulli weight specializes to the original word mass. -/
theorem criticalWordMass_logarithmic (n k : ℕ) :
    criticalWordMass beta n k = BeattyPhase.criticalWordMass n k := rfl

/-- Equality of actual finite counts identifies every jump weight, including
the auxiliary zero index, with its original logarithmic definition. -/
theorem passageJumpWeight_logarithmic (r : ℕ) :
    passageJumpWeight beta r = BeattyPhase.certificateWeight r := by
  simp only [passageJumpWeight, crossingDepth, passageCount_logarithmic,
    passageIndex_logarithmic, criticalWordMass_logarithmic,
    BeattyPhase.certificateWeight, BeattyPhase.certificateIndex]

/-- The strict atom convention is unchanged under logarithmic specialization;
the profiles agree as functions, including at every jump. -/
theorem passageProfile_logarithmic : passageProfile beta = BeattyPhase.certificateProfile := by
  simp only [passageProfile, passagePhase_logarithmic, passageJumpWeight_logarithmic,
    BeattyPhase.certificateProfile]

end Problems.Juggler.BeattySlope
