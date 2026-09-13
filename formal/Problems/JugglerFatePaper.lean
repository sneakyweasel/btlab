import Problems.Juggler.TerminationFloor257
import Problems.Juggler.FateContagion
import Problems.Juggler.CubeFiber
import Problems.Juggler.TiltedShare
import Problems.Juggler.FateRecursion
import Problems.Juggler.FateFirstLetter
import Problems.Juggler.FateSweep
import Problems.Juggler.FateSweepMonotone
import Problems.Juggler.FateChernoff
import Problems.Juggler.FatePressure
import Problems.Juggler.FateTaoReduction
import Problems.Juggler.FateSeed
import Problems.Juggler.FateCylinderCorollary
import Problems.Juggler.FateFiberParity
import Problems.Juggler.FateThinFibers
import Problems.Juggler.FateContagionBound

/-!
# Paper C barrel — everything the repository checks for the fate-contagion note

`docs/theory/juggler_fate_almost_all_note.md`. This file imports exactly the sixteen modules
that paper cites and nothing else, so that a reader can build the formal side of Paper C on
its own rather than selecting modules by hand out of the umbrella `Problems.Juggler`. It is a
laboratory target, not a claim: building it does **not** corroborate the paper's counting.

## What is here, by module

* `TerminationFloor257` — the Lean floor `N₀ = 260`
  (`reachesOne_of_lt_two_hundred_sixty_one`), the seed of every recursion in the paper.
* `FateContagion` — Lemma 2.1 (fate classes are backward-closed, the trichotomy, the
  exclusions), Lemma 3.1 (the even block), Lemma 3.2 (the `OE` fiber and the fourth-power
  cell `sqrt_sqrt_eq_iff`), Theorem 6.1 (odd generation) and Lemma 8.1 (envelope descent,
  on Paper A's `power_bound_word`).
* `CubeFiber` — Lemma 4.7: the `OE` fiber of an even cube is full, of an odd cube alternates.
* `TiltedShare` — Proposition 9.3 (`weightGen_le_pressure`, `count_le_pressure`) on the
  word-weight framework, the no-momentum and mean-share hypotheses as propositions, and the
  two consequences of Section 9.3 (`initial_depths_are_free`, `tower_ratio_lt_one`).
* `FateRecursion` — Lemma 5.1, the recursion lemma, as a statement about an abstract
  function on `(0, ∞)`.
* `FateFirstLetter` — Proposition 6.3(i): the least failure is odd with an odd image
  (`minimal_failure_odd_odd`), and the first-letter trichotomy of Section 6.2.
* `FateSweep` — Lemma 4.1, the sweep lemma, in both half-cell conventions
  (`sweep_fract_lt_half`, `sweep_fract_ge_half`, `sweep_rep_le_half`, `sweep_rep_gt_half`).
* `FateSweepMonotone` — Lemma 4.1′, monotone pairing: each colour of `⌊2 x_j⌋` has at
  least `H/3 - 2` terms (`sweep_monotone_cell`, `sweep_monotone_fract_lt_half`,
  `sweep_monotone_fract_ge_half`), and the left-open convention by reflection
  (`sweep_monotone_ceil`, `sweep_monotone_rep_le_half`, `sweep_monotone_rep_gt_half`).
* `FateChernoff` — Lemma 8.2, the Chernoff count of `L`-bad words (`LBad_count_le`, on the
  Markov tilt of `RateFreeDensity` and Gibbs' inequality `klHalf_nonneg`), and the exact
  skeleton of Theorem 8.3: the odd failures in `(y, 2y]` are covered by the cylinders of the
  envelope-bad words (`oddFailures_subset_bad_cylinders`) and a bound on every bad cylinder
  bounds them by `2^d · 2^{-e(C) L}` times it (`oddFailures_card_le_chernoff`).
* `FatePressure` — Theorem 9.2 in exact form: the live pressure is the generating function
  of the live weight of `LiveCountWeight`, a live start at depth `d ≥ C L(N)` has at least
  `p_C d` odd letters (`live_oddCount_ge`, Lemma 8.1 on live starts), and a pressure bound
  `N a_θ^d E` at the tilt `x = p_C/(1-p_C)` gives at most `N exp(-d D(p_C ‖ 1/2)) E` live
  starts (`live_count_le_of_pressure`).
* `FateTaoReduction` — Theorem 7.2 (Theorem A of the Tao-reduction note) with the contagion
  bound of Theorem 5.3 as a hypothesis: the `E`-tree bound `logMass_le_oddLogMass` (a
  forward-closed class excluding `1` has log-mass at most `(3/2)(1 + log₂ log₂ x)` times its
  odd log-mass), the dyadic sum `oddLogMass_le_of_dyadic` from the rate `y (log y)^{-e}`, and
  `tao_rate_implies_empty` / `tao_rate_implies_conjecture`: a rate with `e > 1 - λ` against
  a contagion bound `K (log x)^λ` forces the class empty.
* `FateSeed` — Lemma 5.2, the seed: a nonempty backward-closed class contains some `m ≥ 3`
  (`exists_ge_three_of_backwardClosed`), and its log-mass on `(√y, y]` is at least the paper's
  `c_A = (1 - 2/m⁴)(3/8 · 1/(m+1) - 1/((m+1)² - 1))` for every `y ≥ (m+1)⁴` (`seed_lemma`,
  `seed_constant_pos`), on the even-block tree `blockTree`.

* `FateCylinderCorollary` — Corollary 8.4: the cylinder hypothesis `H(C, A)` at all large
  scales (`CylinderBound`) with `A > C + e(C)`, together with the contagion bound of
  Theorem 5.3 for the failure set at an exponent `λ` with `1 - λ < e(C)`, gives that every
  positive integer reaches `1` (`cylinder_bound_implies_conjecture`); the absorption of the
  explicit bound of Theorem 8.3 into the rate `y (log y)^{-e}` is `oddFailures_eventually_le`.

* `FateFiberParity` — Lemma 4.2: on a good fiber (`FiberParity.Good`, the paper's
  `‖α_m‖ ≥ 22 m^{-1/3}` and `‖α_m - 1/2‖ ≥ 2 m^{-1/3}` unpacked) with `m ≥ 10^6`, at least
  `H_m/3 - 2` images are even and at least `H_m/3 - 2` are odd
  (`FiberParity.fiber_parity_good`), by Lemma 4.1' on `x(n) = n √n / 2` whose steps along the
  fiber are `(u² + uv + v²)/(u + v)` with `u = √(n+2)`, `v = √n`.

* `FateThinFibers` — Lemma 4.3: for `u ≥ 10^6` at most `63 u^{2/3}` of the `m ∈ (u, 2u]`
  are bad (`FiberParity.bad_count_le`), by an arc count on `{A_m}` with the wrap-around arc
  unwrapped by a shift, and the bad `m ∈ (U, N]` carry log-mass at most `306 U^{-1/3}` for
  every `N` (`FiberParity.bad_logMass_le`), by the dyadic sum.
* `FateContagionBound` — Theorem 5.3 given the production inequality (5.2): the production
  data `productionRate` / `productionCoeff`, `zeta` antitone in `λ` with `zeta_pos_49`
  (`ζ(0.49) > 0` by eight exact rational bounds `r_i^100 ≤ e_i^49`), the paper's `gA` with
  the seed of Lemma 5.2 (`gA_seed`), and `contagion_of_production_inequality` /
  `logMass_contagion_of_production`, for every `0 < λ ≤ 0.49`; Theorem 7.3 with the
  contagion bound as a hypothesis (`tao_rate_iff_conjecture`); and Corollary 8.4 with
  Theorem 5.3 discharged through (5.2) (`conjecture_of_cylinder_bound_of_production`).

## What is not here, and cannot be

Proposition 4.4 (the block average), the
share law 4.5–4.6, the production inequality (5.2) itself (Theorem 5.3 is here given (5.2),
for every `λ ≤ 0.49`; the root `λ** = 0.4926…` and the range `0.49 < λ < λ**` are not),
Corollaries 5.4–5.5, the asymptotic form of Theorem 8.3, Theorem 9.1, the asymptotic form of
Theorem 9.2, Section 10 and Appendix C have no machine check of any kind. Theorems 7.2, 7.3
and Corollary 8.4 are here with the contagion bound as a hypothesis, and Corollary 8.4 also
with (5.2) in its place. Nothing here is a
density estimate, and nothing here is a halt theorem.

This barrel is not imported by `Problems.lean`; build it with
`lake build Problems.JugglerFatePaper`. Paper A's barrel is `Problems.JugglerPaper`, Paper B's
is `Problems.JugglerParityPaper`; this one shares `TerminationFloor257` and, through `FateChernoff`,
`FatePressure` and `FateTaoReduction`, `RateFreeDensity` and `LiveCountWeight` with Paper A, and no module
with Paper B.
-/
