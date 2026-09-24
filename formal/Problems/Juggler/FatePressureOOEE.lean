import Problems.Juggler.FatePressureCorollary
import Problems.Juggler.FateOOEEWeighted

namespace Problems.Juggler

namespace Pressure

/-!
# The pressure and no-momentum corollaries at the OOEE threshold 3/8

The unconditional OOEE contagion `FateOOEEWeighted.logMass_growth` holds at
`λ = 5/8` for every nonempty positive backward-closed class. Fed into
`pressure_conj_of_contagion` and `noMomentum_conj_of_contagion`, whose threshold is
`1 - λ`, it gives Paper C's Section 9.2 corollaries for every failure exponent
`e > 3/8`. This supersedes the averaged forms at `103/203` in
`FatePressureAveraged.lean` and matches the Tao-rate and scale-average thresholds of
`FateOOEEWeighted`. Neither the pressure nor the no-momentum hypothesis is proved.
-/

/-- The failure class grows at `5/8` whenever it is nonempty. -/
private theorem failures_growth_ooee :
    (∃ n, 1 ≤ n ∧ ¬ReachesOne n) →
      ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        K * Real.log x ^ ((5 : ℝ) / 8) ≤ logMass (fun n => ¬ReachesOne n) x :=
  fun ⟨_a, ha, hfail⟩ =>
    FateOOEEWeighted.logMass_growth not_reachesOne_backwardClosed ha hfail

/-- **Theorem 9.2's corollary at `3/8`.** The pressure hypothesis `P_θ(C)` at all
large scales above a certified floor, with `C ≥ 5` and a loss `ε` such that
`3/8 < e < e(C) - ε` for some `e`, gives that every positive integer reaches `1`. -/
theorem pressure_conjecture_ooee {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C ε e : ℝ) (hC : 5 ≤ C)
    (he : e < chernoffExponent C - ε) (he38 : 3 / 8 < e)
    (hP : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → PressureBound N₀ C ε y) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  pressure_conj_of_contagion hN hfloor C ε e hC he hP
    (lam := 5 / 8) (by norm_num) (by norm_num) (by linarith) failures_growth_ooee

/-- **Proposition 9.3's corollary at `3/8`.** The no-momentum hypothesis
`M_{θ,q}(C)` at all large scales above a certified floor, with `C ≥ 5`,
`0 < q < p_C` and a momentum `δ` such that
`3/8 < e < C (D(p_C ‖ q) - c_x δ) / log 2` for some `e`, gives that every positive
integer reaches `1`. -/
theorem noMomentum_conjecture_ooee {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q δ e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C) (he : e < momentumExponent C q δ)
    (he38 : 3 / 8 < e) (hM : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → NoMomentumBound N₀ C q δ y) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  noMomentum_conj_of_contagion hN hfloor C q δ e hC hq0 hqp he hM
    (lam := 5 / 8) (by norm_num) (by norm_num) (by linarith) failures_growth_ooee

end Pressure

end Problems.Juggler
