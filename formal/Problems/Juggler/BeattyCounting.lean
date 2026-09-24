import Problems.Juggler.BeattySlopeCounting
import Problems.Juggler.BeattySlopeSpecialization

/-!
# The exact logarithmic survivor counting identity

The positive-partial-sum recurrence for the original binary-word counts is
now a specialization of the real-boundary theorem. The logarithmic bridge
identifies the finite word sets exactly and proves boundary irrationality
independently of the counting theorem.
-/

namespace Problems.Juggler.BeattyPhase

open Finset PaperBThreshold

/-- The exact integer positive-partial-sum recurrence for the original
survivor counts, specialized from the arbitrary irrational boundary theorem. -/
theorem survivor_count_recurrence (n : ℕ) :
    n * neverNegCount n = ∑ j ∈ range n, endpointCount (n-j)*neverNegCount j := by
  simpa only [BeattySlope.survivorCount_logarithmic, BeattySlope.endpointCount_logarithmic]
    using BeattySlope.survivorCount_recurrence beta BeattySlope.logarithmic_irrational n

/-- The formal exponential identity holds for the actual logarithmic survivor
counts, by the exact integer recurrence. -/
theorem survivor_exponential_identity : SurvivorExponentialIdentity :=
  survivorExponentialIdentity_iff_count_recurrence.2 survivor_count_recurrence

end Problems.Juggler.BeattyPhase
