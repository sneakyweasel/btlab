import Problems.Juggler.FatePressureCorollary
import Problems.Juggler.FatePoorProduction

namespace Problems.Juggler

namespace Pressure

/-!
# The no-momentum corollary at the averaged exponent

`noMomentum_implies_conjecture` (Paper C, Proposition 9.3's corollary) closes the
contagion step through `Production.conjecture_of_tao_rate`, which needs a failure
exponent `e > 27/40`. The unconditional averaged contagion bound
`Production.failures_logMass_averaged` holds at every `λ ≤ 100/203`, and the
threshold is `1 - λ`, so the same corollary holds for every `e > 103/203 = 0.50739…`.
This is the margin `e* = 1 - 100/203` that `J-failure-margin` uses. It is the
pattern of `Production.conjecture_of_tao_rate_averaged`, applied to the no-momentum
hypothesis; the hypothesis itself is not proved.
-/

/-- **Proposition 9.3's corollary at the averaged exponent.** The no-momentum
hypothesis `M_{θ,q}(C)` at all large scales above a certified floor, with `C ≥ 5`,
`0 < q < p_C` and a momentum `δ` such that
`103/203 < e < C (D(p_C ‖ q) - c_x δ) / log 2` for some `e`, gives that every
positive integer reaches `1`. -/
theorem noMomentum_conjecture_averaged {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q δ e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C) (he : e < momentumExponent C q δ)
    (he103 : 103 / 203 < e) (hM : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → NoMomentumBound N₀ C q δ y) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  noMomentum_conj_of_contagion hN hfloor C q δ e hC hq0 hqp he hM
    (lam := 100 / 203) (by norm_num) (by norm_num) (by linarith)
    (fun ⟨_a, ha, hfail⟩ => Production.failures_logMass_averaged ha hfail (by norm_num) le_rfl)

end Pressure

end Problems.Juggler
