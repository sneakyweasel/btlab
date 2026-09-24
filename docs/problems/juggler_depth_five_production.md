# Juggler `depth_five_production`

Status: **PARK** (24 September 2026). Phase-0 priced the depth-five productions
and located the missing estimate; no production is proved.

## Problem

Can actual productions along the depth-five first-descent words `OOOEE` and
`OOEOE` lift unconditional fate contagion above the kernel-checked `5/8`?

## Exact statement

The [OOEE weighted production](../theory/juggler_ooee_weighted_production_note.md)
proves, for every nonempty positive backward-closed class `A`,
`logMass A X >= K (log X)^(5/8)` (`J-ooee-contagion-five-eighths`), from the
three productions `E`, `OE`, `OOEE` with coefficients `1`, `33/100`, `11/100`.
The question is whether, for `w` in `{OOOEE, OOEOE}`, the actual source mass of
the `w`-fibres satisfies a production inequality
`(1 - eta) c_w fullMass A (rho_w t - O(1)) <= sourceMass A w (cutoff t) + C`
with `c_w = 1/27` and `rho_w = 27/32`, uniformly in `A`. Together with the
depth-four productions this would certify contagion near `0.75` and lower the
Tao and pressure thresholds from `3/8` to about `1/4`.

## Current literature

`extended`. Paper C (5.7) gives the ideal coefficient `2^{-|w|}/rho_w` and
Proposition 5.12 the ideal ceiling `lambda = 1`; this dossier prices the finite
first-descent families. The depth-four production is internal
([poor fibres](juggler_ooee_poor_fibres.md),
[count-poor tail](../theory/juggler_ooee_count_poor_tail_note.md)).
Paper B's written depth-five counts are `J-paper-b-oooee-count` and
`J-paper-b-ooeoe-split`, pending independent review.

## Branch budget

- **Target:** actual `OOOEE` and `OOEOE` productions, uniform over backward-closed classes.
- **Novelty hypothesis:** a depth-five count-poor tail, so that no backward-closed
  class can concentrate on unfair depth-five fibres.
- **Falsifier:** the poor tail needs single-fibre parity control on windows of
  length `P^(5/32)`, and no averaged substitute exists on present estimates.
- **Already killed by?:** not by
  [the elementary ladder](../negative_knowledge/the-elementary-production-ladder-is-finished.md),
  which is a different family with ceiling `0.4927` and exports nested-floor
  rungs to Paper B; this branch tests whether that export can return. Not by the
  Tao dossier's depth-five `K_3` wall, which concerns uniform `H(C,A)`.
- **Existing machinery:** `FateOOEEWeighted`, `FateOOEEAssembly`, the depth-four
  fibre geometry, joint parity and resonance tail; `FejerBox3`; Paper B's depth-five
  global mixed sums (written).
- **Maximum Phase-0 scope:** a pricing probe and a desk analysis of whether the
  depth-four argument survives at depth five. No new Lean, no census.
- **Promotion criterion:** a written reduction of the depth-five poor tail to
  named existing estimates, certifying `lambda > 0.74`.
- **Stop criterion:** the reduction needs single-fibre equidistribution at length
  `P^(5/32)` with no averaging substitute.

## Balanced-ternary formulation

None used. The objects are parity words and floor powers.

## Why BT may be relevant

Not relevant to this question.

## Candidate operations / invariants

- The ideal coefficient `c_w = 2^{-|w|}/rho_w = 3^{-a}` (Paper C (5.7)); **KNOWN**.
- The fibre window `P^(1 - rho_w)` for sources near `P = m^(1/rho_w)`;
  **EXACT — HUMAN PROOF** (inverse-power calculus, as in the depth-four geometry).

## Experiments

Probe `research.juggler_sequence.depth_five_production`, output
`data/research/juggler/depth_five_production/pricing.json` with its manifest,
test `tests/research/juggler_sequence/test_depth_five_production.py`. Scope:
first-descent words of length at most 12, exact rational multipliers, roots by
bisection.

| Depth | New words | Ideal root | Required rate `e >` |
|---|---|---|---|
| 4 | `OOEE` | 0.6328 | 0.3672 |
| 5 | `OOOEE`, `OOEOE` | 0.7512 | 0.2488 |
| 7 | three words | 0.7993 | 0.2007 |
| 8 | seven words | 0.8514 | 0.1486 |
| 12 | 57 words in all | 0.8901 | 0.1099 |

The certified depth-four assembly has root `0.6266 >= 5/8`.

## Conjectures

None.

## Counterexamples

None.

## Formalization

None new. The depth-four chain is `FateOOEEWeighted.lean` and its imports.

## Results

**1. Depth five is the largest single step (COMPUTATIONALLY VERIFIED).** The
first-descent words through length four are exactly `E`, `OE`, `OOEE`, the three
the `5/8` assembly uses, so `5/8` sits just below the depth-four ideal `0.6328`.
Depth five adds `OOOEE` and `OOEOE`, each with `c_w = 1/27` and `rho_w = 27/32`,
and lifts the ideal root to `0.7512`.

**2. The depth-five fibres are windows of length `P^(5/32)`.** A word with
multiplier `rho` has target `m` fibre near `P = m^(1/rho)` spanning about
`P^(1-rho)` sources: `P^(7/16)` for `OOEE`, `P^(5/32)` for both depth-five words.

**3. The depth-four argument does not transfer.** At depth four the fibre count
is controlled by the three-coordinate Fejér bound with one slow coordinate
`W ~ x^(9/8)`, whose resonance family has small reciprocal mass, and by mixed-mode
bounds `O(P^(13/32))` for the nested pair `X = x^(3/2)`, `Y = floor(X)^(3/2)` on
windows of length `P^(7/16)`: a saving of `P^(1/32)`. At depth five:

- the window `P^(5/32)` is shorter than the existing mixed-mode bound `P^(13/32)`,
  so that bound is weaker than trivial there;
- `OOOEE` needs the doubly nested coordinate `Z = floor(Y)^(3/2)` and has no slow
  coordinate; `OOEOE` nests a further `3/2` power on the depth-four slow mode;
- an averaged poor tail, bounding the fibre-count variance over targets, needs the
  differenced depth-five mixed sums with shifts up to `P^(5/32)`. Paper B's
  frozen-gap collision reaches shifts `P^(1/8)`, and its depth-five mixed sums
  (`J-paper-b-oooee-mixed-127`, written) are unshifted.

**4. The frozen-gap desk study locates the binding inequality (desk reading,
24 September 2026; not a proof).** By Chebyshev over windows of length
`L = P^(5/32)`, the fraction of unfair windows is at most
`(1/(eta^2 L)) (1 + P^(-1) sum_{0<|d|<L} |T_d|)` with
`T_d = sum_{P<n<=2P} e(phi(n+2d) - phi(n))`. The diagonal gives `P^(-5/32)`, so
the poor tail needs only some power saving in the once-differenced depth-five
sums for shifts `d <= P^(5/32)` and **bounded** frequencies.

In [Paper B](../theory/juggler_parity_discrepancy_note.md), Appendix C, (C.4)
collapses the doubly nested floor to a kernel term `c(n){Y}` with
`c ~ k n^(9/8)`, (C.10) differences twice with `h_1 < P^(1/48)` and
`h_2 < P^(1/24)`, and (C.17) splits the growing kernel coefficient into
`(27/32) k b x^(3/8)` plus a remainder `O(Pi P^(-1/8) + ...)`, `Pi = k h_1 h_2`,
which the argument uses as a bounded coefficient. That needs
`k h_1 h_2 <= P^(1/8)`, the same exponent as the range `h <= P^(1/8)` of
Proposition 7.6: in both places it is the Taylor remainder of a frozen
coefficient. With the fibre shift as `h_1 = d`, bounded `k` and `h_2 = 1`,
`d = P^(5/32)` exceeds `P^(1/8)` by `P^(1/32)`; the remainder then reaches
`P^(1/32)`, against Paper B's uniform saving `P^(1/128)`. Proposition 7.6's own
bound (7.5) keeps a power saving up to `h < P^(1/4)` when `u` is bounded, so the
basic model is not what binds.

## Open questions

The missing input is a power saving for the once-differenced depth-five sums
`T_d` with shifts `d <= P^(5/32)` and bounded frequencies. The binding step in
Paper B's route is the bounded remainder of (C.17), which needs
`k h_1 h_2 <= P^(1/8)`. Paper B's `P^(1/128)` saving is paid for uniformity over
frequencies up to `P^(1/24)`; for bounded frequencies the margin of Appendix C
may be larger, and C.5--C.9 have not been re-audited for other binding terms.

## Decision

**PARK.** The stop criterion fired: the production reduces to depth-five
parity control on windows of length `P^(5/32)`, which neither the depth-four
fibre machinery nor Paper B's global depth-five sums supply, and no averaged
substitute is available on present estimates. The pricing stands: depth five
would move contagion from `5/8` toward `0.75` and the required rate from `3/8`
toward `1/4`. Best next question: rerun Appendix C's exponent bookkeeping
with bounded frequencies and an outer shift `P^delta`; is the largest `delta`
with a positive saving at least `5/32`?

## Publication assessment

Status: `EXPLORATORY`.
