import Problems.Juggler.FateScaleAverage

/- The new conditional implication, including the imported contagion dependency.
Run: lake env lean AxiomCheckScaleAverage.lean
Only Mathlib's standard logical principles should appear in the output. -/

open Problems.Juggler.ScaleAverage

#print axioms weighted_prefix_le
#print axioms rpow_step_le
#print axioms rpow_le_sum
#print axioms weighted_rpow_sum_le
#print axioms rho_nonneg
#print axioms odd_block_le
#print axioms block_le_rho
#print axioms odd_mass_le
#print axioms conjecture_of_odd_mass
#print axioms conjecture_of_bound
#print axioms pressure_average_conjecture

#check pressure_average_conjecture
