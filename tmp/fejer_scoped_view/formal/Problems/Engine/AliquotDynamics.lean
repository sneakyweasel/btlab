import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Problems.Engine

/-!
Exact identities for the divisor-sum iteration campaign.
These statements are the problem definition and its immediate
consequences. They are KNOWN. They are not a Catalan–Dickson theorem
and not a claim about the orbit of 276.
-/

/-- Sum of proper divisors: ``(∑_{d∣n} d) - n``. -/
def properDivisorSum (n : ℕ) : ℕ :=
  (∑ d ∈ n.divisors, d) - n

theorem properDivisorSum_one : properDivisorSum 1 = 0 := by
  native_decide

theorem properDivisorSum_prime {p : ℕ} (hp : p.Prime) : properDivisorSum p = 1 := by
  have hdiv : p.divisors = {1, p} := hp.divisors
  have hne : (1 : ℕ) ≠ p := hp.ne_one.symm
  simp [properDivisorSum, hdiv, Finset.sum_pair hne]

theorem properDivisorSum_six : properDivisorSum 6 = 6 := by
  native_decide

/-- Exact counterexample to global descent: ``12`` increases. -/
theorem properDivisorSum_twelve : properDivisorSum 12 = 16 := by
  native_decide

theorem properDivisorSum_220_284 :
    properDivisorSum 220 = 284 ∧ properDivisorSum 284 = 220 := by
  native_decide

end Problems.Engine
