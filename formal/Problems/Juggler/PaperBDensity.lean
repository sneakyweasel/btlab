/-
# From Hypothesis FD to density one, conditionally

Theorem 6.1 is stated in the manuscript as the *conditional* density-one certificate theorem:
"Under `FD`, `C_infinity` has natural density one."  `FD` is a hypothesis, not a result --

  for every fixed `d >= 1` and every odd-rooted word `w` of length `d`,
  `#{n <= N : word_d(n) = w} = 2^(-d) N + o_w(N)`,

with no common error rate in `d` assumed.  So the honest formalisation is the one the
laboratory uses for conditional results: state the hypothesis, derive the conclusion, and let
the Lean statement carry the hypothesis where a reader cannot miss it.

`PaperBMarkov` and `PaperBChernoff` already supply the counting half — the bad words number at
most `2^n theta q ^ n`, and `theta q < 1`.  This module supplies the two steps that turn that
into a density statement:

* `density_of_finite_union` — if each of finitely many classes has density `r`, their union has
  density `card * r`.  This is the whole content of "`FD` and a finite sum over surviving words
  show that the natural density is their number divided by `2^d`": FD gives `r = 2^(-d)` for one
  class, and finite additivity does the rest.  It is finite additivity and nothing more, which
  is exactly why the hypothesis is needed for each fixed `d` separately and why no uniformity
  in `d` is asserted.
* `tendsto_zero_of_eventually_le` — if a nonnegative quantity is eventually below `c d` for
  every `d`, and `c d -> 0`, it tends to zero.  This is the `d -> infinity` at the end of the
  proof, where the manuscript writes "letting `d -> infinity` proves the assertion".
* `exceptional_density_zero` — the two combined, in the shape Theorem 6.1 uses: a nonnegative
  density function dominated at each depth by a bound that vanishes has limit zero.

What this does NOT do.  It does not prove `FD`, which is open, and it does not establish that
the bad set at depth `d` IS a finite union of word classes — that is the combinatorial reading
of `word_d`, which stays written mathematics.  It formalises the inference from those to the
conclusion.  Theorem 6.1 remains conditional exactly as the manuscript states it.
-/

import Mathlib.Tactic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace Problems.Juggler

namespace PaperBDensity

open Filter Topology

/-- Finite additivity of density: finitely many classes of density `r` have density `card * r`. -/
theorem density_of_finite_union {ι : Type*} (S : Finset ι) (count : ι → ℕ → ℕ) (r : ℝ)
    (h : ∀ w ∈ S, Tendsto (fun N : ℕ => (count w N : ℝ) / N) atTop (𝓝 r)) :
    Tendsto (fun N : ℕ => (∑ w ∈ S, (count w N : ℝ)) / N) atTop (𝓝 (S.card * r)) := by
  have hrw : ∀ N : ℕ, (∑ w ∈ S, (count w N : ℝ)) / N = ∑ w ∈ S, (count w N : ℝ) / N := by
    intro N
    rw [Finset.sum_div]
  simp_rw [hrw]
  have hsum := tendsto_finsetSum S h
  simpa [Finset.sum_const, nsmul_eq_mul] using hsum

/-- The `d -> infinity` step: eventually below every member of a null sequence means null. -/
theorem tendsto_zero_of_eventually_le {f : ℕ → ℝ} (hf : ∀ N, 0 ≤ f N) {c : ℕ → ℝ}
    (hc : Tendsto c atTop (𝓝 0)) (h : ∀ d, ∀ᶠ N in atTop, f N ≤ c d) :
    Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨d, hd⟩ : ∃ d, c d < ε := by
    obtain ⟨D, hD⟩ := (Metric.tendsto_atTop.mp hc) ε hε
    have hDD := hD D le_rfl
    rw [Real.dist_eq, sub_zero] at hDD
    exact ⟨D, lt_of_abs_lt hDD⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (h d)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : f N ≤ c d := hN₀ N hN
  have h2 : 0 ≤ f N := hf N
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h2]
  linarith

/-- Theorem 6.1's shape: a density dominated at every depth by a vanishing bound is zero. -/
theorem exceptional_density_zero {dens : ℕ → ℝ} (hd : ∀ N, 0 ≤ dens N) {bound : ℕ → ℝ}
    (hb : Tendsto bound atTop (𝓝 0)) (hdom : ∀ d, ∀ᶠ N in atTop, dens N ≤ bound d) :
    Tendsto dens atTop (𝓝 0) :=
  tendsto_zero_of_eventually_le hd hb hdom

end PaperBDensity

end Problems.Juggler
