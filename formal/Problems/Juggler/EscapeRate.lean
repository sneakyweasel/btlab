import Problems.Juggler.FateTaoReduction
import Problems.Juggler.FateOOEEWeighted

namespace Problems.Juggler

/-!
# An escape rate excludes divergent orbits

The escaping starts form a forward-closed class that does not contain `1`, and a
backward-closed one, so the OOEE contagion `FateOOEEWeighted.logMass_growth` makes
them grow at `λ = 5/8` as soon as one exists. The generic Tao reduction
`tao_rate_implies_empty` then turns any count bound on the odd escaping starts of
`(y, 2y]` with exponent `e > 3/8` into the absence of divergent orbits.

The premise is weaker than the failure rate of `FateOOEEWeighted.conjecture_of_tao_rate`,
because every escaping start is a failure; the conclusion is weaker too, since it
excludes escape only and says nothing about cycles other than `{1}`. With
`cycles_or_escapes` it makes every orbit eventually periodic. The escape rate itself is
not proved.
-/

/-- `1` does not escape: it is a fixed point. -/
theorem one_not_escapes : ¬EscapesToInfinity 1 := fun h => by
  have hfix : ∀ k, floorPower^[k] 1 = 1 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih]; decide
  obtain ⟨k, hk⟩ := h 1
  rw [hfix k] at hk
  omega

/-- **An escape rate above `3/8` excludes divergent orbits.** If for some `e > 3/8` the
odd escaping starts in `(y, 2y]` number at most `y (log y)^(-e)` for all large `y`, then
no positive start escapes to infinity. -/
theorem no_escape_of_escape_rate {e : ℝ} (he : 3 / 8 < e)
    (hrate : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((oddMembers EscapesToInfinity y).card : ℝ) ≤ y * Real.log y ^ (-e)) :
    ∀ n, 1 ≤ n → ¬EscapesToInfinity n :=
  tao_rate_implies_empty escapes_forwardClosed one_not_escapes
    (lam := 5 / 8) (by norm_num) (by norm_num) (by linarith)
    (fun ⟨_a, ha, hesc⟩ => FateOOEEWeighted.logMass_growth escapes_backwardClosed ha hesc)
    hrate

/-- **Under an escape rate above `3/8`, every orbit is eventually periodic.** -/
theorem eventuallyCycles_of_escape_rate {e : ℝ} (he : 3 / 8 < e)
    (hrate : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((oddMembers EscapesToInfinity y).card : ℝ) ≤ y * Real.log y ^ (-e))
    {n : ℕ} (hn : 1 ≤ n) : EventuallyCycles n :=
  (cycles_or_escapes n).resolve_right (no_escape_of_escape_rate he hrate n hn)

end Problems.Juggler
