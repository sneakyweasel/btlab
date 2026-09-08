import Problems.Juggler.TerminationFloor257
import Problems.Juggler.FateContagion
import Problems.Juggler.CubeFiber
import Problems.Juggler.TiltedShare
import Problems.Juggler.FateRecursion
import Problems.Juggler.FateFirstLetter
import Problems.Juggler.FateSweep
import Problems.Juggler.FateChernoff

/-!
# Paper C barrel — everything the repository checks for the fate-contagion note

`docs/theory/juggler_fate_almost_all_note.md`. This file imports exactly the eight modules
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
* `FateChernoff` — Lemma 8.2, the Chernoff count of `L`-bad words (`LBad_count_le`, on the
  Markov tilt of `RateFreeDensity` and Gibbs' inequality `klHalf_nonneg`), and the exact
  skeleton of Theorem 8.3: the odd failures in `(y, 2y]` are covered by the cylinders of the
  envelope-bad words (`oddFailures_subset_bad_cylinders`) and a bound on every bad cylinder
  bounds them by `2^d · 2^{-e(C) L}` times it (`oddFailures_card_le_chernoff`).

## What is not here, and cannot be

Lemma 4.1' (monotone pairing), Lemmas 4.2–4.3, Proposition 4.4 (the block average), the
share law 4.5–4.6, the seed 5.2, Theorem 5.3 and its corollaries, Theorems 7.2–7.3, the
asymptotic form of Theorem 8.3 and Corollary 8.4, Theorems 9.1–9.2, Section 10 and
Appendix C have no machine check of any kind. Nothing here is a
density estimate, and nothing here is a halt theorem.

This barrel is not imported by `Problems.lean`; build it with
`lake build Problems.JugglerFatePaper`. Paper A's barrel is `Problems.JugglerPaper`, Paper B's
is `Problems.JugglerParityPaper`; this one shares `TerminationFloor257` and, through `FateChernoff`,
`RateFreeDensity` with Paper A, and no module with Paper B.
-/
