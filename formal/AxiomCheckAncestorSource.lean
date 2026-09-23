import BTCalculus.PreimageGenerations
import Problems.Collatz.BackwardMass

#print axioms BTCalculus.PreimageGenerations.ancestorIndicator_eq
#print axioms BTCalculus.PreimageGenerations.ancestorIndicator_not_fixed
#print axioms BTCalculus.PreimageGenerations.ancestorIndicator_le_of_source_eq
#print axioms BTCalculus.PreimageGenerations.exists_summable_source_iff

-- Unit monomials already defeat Bergman expansiveness for both signs.
-- The analytic monomial norm formula is derived in the dossier.
example (n : ℕ) : Problems.Collatz.shortcutC n = 7 ↔ n = 14 := by
  unfold Problems.Collatz.shortcutC
  split <;> omega

example (n : ℕ) : Problems.Collatz.negT n = 47 ↔ n = 94 := by
  unfold Problems.Collatz.negT
  split <;> omega

example : (1:ℝ)/15 < 1/8 ∧ (1:ℝ)/95 < 1/48 := by norm_num
