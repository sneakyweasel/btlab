import Problems.Juggler.TerminationFloor257
import Problems.Juggler.FateContagion
import Problems.Juggler.CubeFiber
import Problems.Juggler.TiltedShare
import Problems.Juggler.FateRecursion
import Problems.Juggler.FateFirstLetter
import Problems.Juggler.FateBlockAverage
import Problems.Juggler.FateShareLaw
import Problems.Juggler.FateProduction
import Problems.Juggler.FateOneSided
import Problems.Juggler.FateOneSidedCorollary
import Problems.Juggler.FatePressureCorollary
import Problems.Juggler.FateOneSidedAtoms
import Problems.Juggler.FateEnergyAtoms
import Problems.Juggler.FateCollapse
import Problems.Juggler.FateCylinderEnergy
import Problems.Juggler.FateLandingWindow
import Problems.Juggler.FateWindowCount
import Problems.Juggler.FateSweep
import Problems.Juggler.FateSweepMonotone
import Problems.Juggler.FateChernoff
import Problems.Juggler.FatePressure
import Problems.Juggler.FateTaoReduction
import Problems.Juggler.FateSeed
import Problems.Juggler.FateCylinderCorollary
import Problems.Juggler.FateNumerics
import Problems.Juggler.FateFiberParity
import Problems.Juggler.FateThinFibers
import Problems.Juggler.FateContagionBound

/-!
# Paper C barrel — everything the repository checks for the fate-contagion note

`docs/theory/juggler_fate_almost_all_note.md`. This file imports exactly the twenty-nine modules
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
* `FateBlockAverage` — Proposition 4.4 **given its exponential-sum bounds**, and its exact
  layer: the paper's `I(m')` written with the landing window (`BlockAverage.mem_oddBlock`),
  `U(m')` as the disjoint union of the even-image parts of the fibers over the even `m` of
  the block (`BlockAverage.U_card_eq`, on Lemma 4.2's `evenImageCount`), and the expansion
  `4|U(m')| = M + S₁ + S₂ + S₁₂` the proof starts from (`BlockAverage.four_card_U`).
  Equation (4.1) follows once the three parity sums are bounded
  (`BlockAverage.block_average_bound`) — and those bounds, which are the content of the
  proposition, are hypotheses here, not theorems: Vaaler's approximation and the van der
  Corput estimates are not formalized anywhere in this repository.
* `FateShareLaw` — the exact layer of Section 4.3: the fiber phase expanded about its first
  term with the cubic remainder as polynomial algebra (`ShareLaw.xval_expansion`, on
  `ShareLaw.taylor_three_halves`; at most `(2/27)(m+1)/m²` on a fiber,
  `ShareLaw.xval_expansion_fiber`), the range of the quadratic phase `β s + s²/3` on `[0, 1]`
  and its threshold `β ∈ [-5/6, 1/6]` (`ShareLaw.phiRange_le_half_iff`, Corollary 4.6(2)'s
  arithmetic), and `∫ max(0, 1/2 - range) dβ = 25/108` (`ShareLaw.integral_extremeMeasure`,
  Corollary 4.6(3)'s arithmetic). Lemma 4.5 itself, an equidistribution statement, and the
  measure-theoretic parts of Corollary 4.6 are not here.
* `FateProduction` — the production inequality without its exponential sums, and what it
  yields on its own. Of the three families of Section 5.1, the `E`-images through Lemma 3.1
  (`Production.family_E`) and the `OE`-fibers through Lemmas 4.2 and 4.3
  (`Production.family_OE`) need no analysis; together they give
  `g_A(t) ≥ (1 - 4e^{-t/4}) g_A(t/2) + (2/9 - (50/9)e^{-t/8}) g_A(3t/4) - errAdd t` for
  `t ≥ 40` (`Production.production_two`), with every error explicit. The recursion lemma on
  these two productions, with `ζ(3/10) > 0` certified by two rational bounds
  (`Production.zeta2_pos`), gives **an unconditional theorem**: every nonempty backward-closed
  set has log-mass at least `K (log x)^λ` up to `x` for every `0 < λ ≤ 3/10`
  (`Production.logMass_contagion_elementary`), and so do the failures if any exist
  (`Production.failures_logMass_ge`). The block-average family, whose two exponential-sum
  bounds are hypotheses in `FateBlockAverage`, and the five ladder productions of Section 5.7,
  whose Appendix D estimates are human, are what lift `3/10` to the paper's `0.49`.
* `FateOneSided` — Theorem 9.1 in exact form, by exponential moments and without the
  martingale, carrying out the paper's remark after Proposition 9.3. The tilted mass of the
  `L`-bad cylinders, `badMass t = Σ_{|w|=t, w bad} #[w] x^{o(w)}`, obeys the affine recursion
  `badMass (t+1) ≤ (1 + (x-1) q) badMass t + (x-1) err (2x)^t` under the one-sided hypothesis
  `OneSided.OneSidedShare` (`OneSided.badMass_succ_le`), because bad words are prefix-closed
  and a cylinder splits into its two children; it unrolls to `x a_q^t N + (x-1) err t (2x)^t`
  (`OneSided.badMass_le`), and Lemma 8.1 with the Markov tilt bounds the odd failures of
  `(y, 2y]` by `badMass d / x^{p_C d}` (`OneSided.oddFailures_card_le_badMass`), so at every
  scale `#{odd failures} ≤ (x a_q^{d-1} N + (x-1) err (d-1) (2x)^{d-1}) / x^{p_C d}`
  (`OneSided.one_sided_bound`); at the re-centring tilt the main term is
  `(x/a_q) N e^{-d D(p_C ‖ q)}` (`OneSided.one_sided_bound_kl`). The absorption of the error
  into the rate, which here costs `C (1 - p_C) log₂ x` more of `A` than the paper's Markov
  step, and the displayed asymptotic form are not here.
* `FateOneSidedCorollary` — Theorem 9.1's consequence, the conjecture from the one-sided
  hypothesis, in the pattern of Corollary 8.4. `OneSided.OneSidedBound` is `H_q(C, A)` at a
  scale, `OneSided.oneSidedExponent` the Chernoff exponent `C D(p_C ‖ q)/log 2`; the
  absorption of the exact bound into the rate `y (log y)^{-e}` for every `e < e_{C,q}` and
  `A > C(1 + log₂ x) + 1 + e` (`OneSided.oddFailures_le_of_one_sided`, on Gibbs' inequality
  `OneSided.klDiv_nonneg` and the two scale comparisons `OneSided.exp_le_rpow_scale`,
  `OneSided.pow_le_rpow_scale`), then Theorem 7.2: with the contagion bound as a hypothesis
  at an exponent `λ` with `1 - λ < e` (`OneSided.implies_conjecture_of_contagion`), or with
  nothing else assumed when `e > 7/10` (`OneSided.one_sided_implies_conjecture`), and the
  paper's remark after Theorem 9.1, a share bound with no error term
  (`OneSided.exact_share_implies_conjecture`). The paper's condition `A > C + e_q(C)` and
  its numerical forms are not here.
* `FatePressureCorollary` — Section 9.2's consequences, the conjecture from the pressure
  hypothesis `P_θ(C)` and from the no-momentum hypothesis `M_{θ,q}(C)`, in the same pattern.
  A failure never enters the floor, so the odd failures of `(y, 2y]` are live starts of
  `{1, …, 2y}` at every depth (`Pressure.oddFailures_subset_live`); Theorem 9.2 in exact form
  and Proposition 9.3 under no momentum then bound them by `2y e^{-d D} (log y)^ε`, and the
  shared absorption `Pressure.absorb` turns that into the rate `y (log y)^{-e}` for every
  `e < C D / log 2 - ε`. `Pressure.PressureBound` is `P_θ(C)` at a scale with the paper's
  `e^{o(d)}` quantified as `(log y)^ε`, `Pressure.NoMomentumBound` is `M_{θ,q}(C)` on the
  live weight with the paper's `o(d)` as `δ d`, and `Pressure.momentumExponent` the
  exponent `C (D(p_C ‖ q) - c_x δ)/log 2`. Each composes with Theorem 7.2 with the contagion
  bound as a hypothesis (`Pressure.pressure_conj_of_contagion`,
  `Pressure.noMomentum_conj_of_contagion`) and with nothing else assumed
  (`Pressure.pressure_implies_conjecture`, `Pressure.noMomentum_implies_conjecture`).
* `FateOneSidedAtoms` — Section 10(d), first paragraph: Theorem 9.1 survives if the share
  bound fails on bad atoms of total mass `y (log y)^{-B}` at each depth. The hypothesis
  `OneSided.OneSidedShareExc` allows an exceptional set of words of mass at most `exc` at
  each depth; an exceptional bad atom sends at most its whole mass to its odd child, so the
  affine recursion gains the term `(x - 1)(1 - q) exc x^t` (`OneSided.badMass_succ_le_exc`),
  unrolls (`OneSided.badMass_le_exc`) and gives the exact bound
  (`OneSided.one_sided_bound_exc`, `OneSided.one_sided_bound_kl_exc` at the re-centring
  tilt). The absorption (`OneSided.oddFailures_le_of_exc`, on the one-tail lemma
  `OneSided.tail_le`) needs `B > C log₂ x + 1 + e`, `C` less than the error's condition
  because the exceptional atoms are not doubled at each depth; then Theorem 7.2 with the
  contagion bound as a hypothesis (`OneSided.exc_conj_of_contagion`) or with nothing else
  assumed (`OneSided.exc_implies_conjecture`), the weakest one-sided hypothesis the paper
  states. The paper's `B > e_q(C)` is not restated.
* `FateEnergyAtoms` — Section 10(d)'s "additional quantitative bound on these sums can
  supply an exceptional-atom estimate", exactly. The bias energy `Σ_{|w|=t} D(w)²` over the
  odd starts of `(y, 2y]` (`Energy.biasEnergy`, equal to the paper's `C_{t+1}/2 - C_t/4` by
  `Energy.biasEnergy_eq`) bounds the squared masses of the atoms violating `#[wO] ≤ q #[w]`
  by `biasEnergy/(q - 1/2)²`, and Cauchy–Schwarz over at most `2^t` atoms bounds their total
  mass (`Energy.mass_violators_le`); so an energy bound `(q - 1/2)² exc²/2^t` at every depth
  gives the one-sided hypothesis with exceptional atoms of mass `exc` and no error term
  (`Energy.oneSidedShareExc_of_energy`), and `FateOneSidedAtoms` runs it to the conjecture:
  `Energy.energy_implies_conjecture` with nothing else assumed, `Energy.energy_conj_of_contagion`
  with the contagion bound as a hypothesis. The pincer's rate-side question is thereby a single
  second-moment statement about how cylinders split (`Energy.EnergyBound`). Nothing here
  proves it.
* `FateCollapse` — the collapsed component is nearly fair, exact layer. For a finite set of
  starts, `Collapse.fiber S t v` counts the starts whose `t`-th iterate is `v`, and the
  next-letter bias of the starts whose iterate lands in a window `[a, b]`
  (`Collapse.windowBias`) is the alternating sum `-Σ_{v ∈ [a,b]} (-1)^v fiber(v)`
  (`Collapse.windowBias_eq_sum`), hence at most the total variation of the fiber profile
  plus one fiber (`Collapse.abs_windowBias_le`, by summation by parts,
  `Collapse.abs_alt_sum_le`). One step of the map sums fibers over preimages, the even
  numbers of `[v², (v+1)²)` plus at most one odd preimage (`Collapse.fiber_succ`,
  `Collapse.fiber_succ_eq`, `Collapse.pre_filter_even`), and the even branch smooths: with
  the depth-`t` profile between `m` and `M` on the double block `[v², (v+2)²)`, consecutive
  block sums differ by at most `(v+1)(M-m) + 2M` (`Collapse.blockSum_sub_le`, on the counts
  `v ≤ evenCount v ≤ v+1`). Hence `Collapse.collapse_bias_le`: the bias of the collapsed
  window is at most `Σ_v ((v+1)(M_v - m_v) + 2M_v)`, plus twice the odd-preimage mass, plus
  one fiber. The variation bound on a fiber profile and the parity of the odd-preimage mass
  are not here.
* `FateCylinderEnergy` — the counting identity of Section 10(d): a cylinder splits into
  its two children (`CylinderEnergy.wordCount_split`), so the first-letter biases
  `D(w) = #[wO] - #[w]/2` satisfy `Σ_{|w|=t} D(w)² = C_{t+1}/2 - C_t/4` exactly
  (`CylinderEnergy.sum_bias_sq`), for an arbitrary finite set of starts. The Parseval form
  in Walsh sums is not here, and neither is any discrepancy bound.
* `FateLandingWindow` — Appendix D.1: along a nested production the two-step map is
  `F(u) = ⌊u^{3/4}⌋` (`LandingWindow.cell34`, equal to `J²` on an `OE` step), and the
  integers whose `F`-image lands in `[a, b)` are exactly those of `[Φ(a), Φ(b))` with
  `Φ(a) = ⌈a^{4/3}⌉` the least `n` with `a⁴ ≤ n³` (`LandingWindow.exact_endpoints`,
  equation (D.1)), iterated to the nested window (D.2)
  (`LandingWindow.exact_endpoints_iterate`). The smooth comparison (D.3) and the
  multiplicities are not here.
* `FateWindowCount` — the counting move Lemmas 4.1, 4.1′ and 4.3 share, for an arbitrary
  `f : ℕ → ℝ`: steps bounded below telescope (`WindowCount.span_ge`, `WindowCount.span_le`,
  `WindowCount.mono_of_stepGe`), and a `d`-separated sequence puts at most `w/d + 1` of its
  terms into a window of width `w` (`WindowCount.window_card_le`, and
  `WindowCount.window_card_le_nat` for the `⌊1/(2a)⌋ + 1` terms of a half-cell). Nothing here
  is about the map.
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

* `FateNumerics` — the two numerical moves Lemmas 4.2, 4.3 and 8.2 share: a real power
  compared through an integer power, `x^p ≤ c ↔ x^{pn} ≤ c^n` (`Numerics.rpow_le_iff_pow` and
  its three siblings, which certify `2^{1/3} ≤ 1.26`, `u^{2/3} ≥ 10^4`, `log₂ 3 ≤ 8/5` and
  `m^{4/3} ≤ n` on the fiber), and Bernoulli's inequality at a point,
  `(a + h)^p ⋚ a^p + p a^{p-1} h` (`Numerics.bernoulli_ge`, `Numerics.bernoulli_le`, the
  fiber steps of Lemmas 4.2 and 4.3). Nothing here is about the map.
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
Corollaries 5.4–5.5, the asymptotic forms of Theorems 8.3, 9.1 and 9.2, Section 10 except
the counting identity of 10(d), its exceptional-atom form of Theorem 9.1 and the energy
bound's supply of those atoms, and Appendix C have no machine check of any kind. Theorems 7.2, 7.3, Corollary 8.4 and the corollaries of
Theorem 9.1 (with and without exceptional atoms), Theorem 9.2 and Proposition 9.3 are here
with the contagion bound as a hypothesis, Corollary 8.4 also with (5.2) in its place, and
Theorem 7.2, Corollary 8.4 and the four Section 9 corollaries also with the contagion bound
discharged at exponent `3/10`. Nothing here is a
density estimate, and nothing here is a halt theorem.

This barrel is not imported by `Problems.lean`; build it with
`lake build Problems.JugglerFatePaper`. Paper A's barrel is `Problems.JugglerPaper`, Paper B's
is `Problems.JugglerParityPaper`; this one shares `TerminationFloor257` and, through `FateChernoff`,
`FatePressure` and `FateTaoReduction`, `RateFreeDensity` and `LiveCountWeight` with Paper A, and no module
with Paper B.
-/
