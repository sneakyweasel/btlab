import Problems.Juggler.BeattyCounting
import Problems.Juggler.BeattySlopeEndpointAsymptotic

/-! Recorded dependencies of the public arbitrary-boundary counting results.
The expanded actual-count consumers are in `InterfaceCheckBeattySlope.lean`.
-/

namespace Problems.Juggler

#print axioms BeattySlope.survives_iff_strict
#print axioms BeattySlope.survivorCount_add_passageCount
#print axioms BeattySlope.survivorCount_zero
#print axioms BeattySlope.passageCount_zero
#print axioms BeattySlope.FirstPassage.exists_even_prefix
#print axioms BeattySlope.FirstPassage.length_eq_crossingDepth
#print axioms BeattySlope.survivorCount_recurrence
#print axioms BeattySlope.survivorWeight_add_passageWeight
#print axioms BeattySlope.survivorWeight_recurrence
#print axioms BeattySlope.crossingDepth_strictMono
#print axioms BeattySlope.FirstPassage.oddCount_eq_of_length_eq_crossingDepth
#print axioms BeattySlope.passageWeight_crossingDepth
#print axioms BeattySlope.passageCount_eq_weight_div
#print axioms BeattySlope.normalizedSurvivor_recurrence
#print axioms BeattySlope.normalizedSurvivor_eq_renewalCoeff
#print axioms BeattySlope.normalizedSurvivor_three_halves_bound
#print axioms BeattySlope.normalizedSurvivor_phase_limit
#print axioms BeattySlope.tiltedOddWeight_pos
#print axioms BeattySlope.tiltedBernoulliBias_eq
#print axioms BeattySlope.tiltedBernoulliBias_bounds
#print axioms BeattySlope.tiltedOddWeight_terminal_ratio
#print axioms BeattySlope.tilted_choose_step_bound
#print axioms BeattySlope.tilted_choose_shift_bound
#print axioms BeattySlope.tilted_endpoint_first_term_bounds
#print axioms BeattySlope.tiltedBase_eq
#print axioms BeattySlope.tiltedTerminalPhase_eq
#print axioms BeattySlope.tilted_first_term_phase_limit
#print axioms BeattySlope.tilted_binomial_tail_ratio_limit
#print axioms BeattySlope.tilted_endpoint_phase_limit
#print axioms BeattySlope.tiltedTerminalPhase_bound
#print axioms BeattySlope.summable_tilted_survivor
#print axioms BeattySlope.summable_tiltedSurvivorPhase_terms
#print axioms BeattySlope.tiltedSurvivorPhase_bounds
#print axioms BeattySlope.tiltedSurvivorPhase_periodic
#print axioms BeattySlope.tilted_survivor_phase_limit
#print axioms BeattySlope.tilted_survivor_phase_limit_reciprocal
#print axioms BeattySlope.survivorWords_logarithmic
#print axioms BeattySlope.passageWords_logarithmic
#print axioms BeattySlope.survivorCount_logarithmic
#print axioms BeattySlope.passageCount_logarithmic
#print axioms BeattySlope.endpointCount_logarithmic
#print axioms BeattySlope.logarithmic_irrational
#print axioms BeattyPhase.survivor_count_recurrence
#print axioms BeattyPhase.survivor_exponential_identity

end Problems.Juggler
