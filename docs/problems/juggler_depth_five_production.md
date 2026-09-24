# Juggler `depth_five_production`

Status: **PARK** (24 September 2026), pending audit. Phase-0 priced the
depth-five productions; a first-pass exponent bookkeeping (Result 5) suggests the
`OOOEE` estimate is within reach of Paper B's machinery. No production is proved.

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

**5. First-pass exponent bookkeeping: `OOOEE` shifts up to `P^(5/32)` look
reachable (desk reading, 24 September 2026; not a proof, audit required).**
Put the fibre shift `d = P^delta` into Paper B's chain for `T_d` with bounded
frequencies, one internal Weyl shift `h_2 = P^gamma`, `Pi = k d h_2`.

- *Theorem B.1 endpoint term.* (B.14) becomes `D_h << (h + P^delta) P^(1/2)`, so
  (B.16) gains `P^(delta+7/8) h^(-1/2)`; after the Weyl average (B.8) it costs
  `P^(15/8+delta) H^(-1/2)`, below `P^2` iff `delta < 1/8 + eta/2` for
  `H = P^eta`. With Paper B's `H = P^(1/12)` this is `delta < 1/6`. The only
  printed reason for `h <= P^(1/12)` in the Weyl step that this pass found is the
  theta cost (B.11), `|t| h P^(3/4) <= P^(7/8)`, which allows `H = P^(1/8)` at
  bounded `t`, hence `delta < 3/16`. At `delta = 5/32`: `|U| << P^(1-0.0052)` or
  `P^(1-0.0156)` respectively.
- *D2 error.* Lemma A.1 charges `D/(Qa) << ((h_1+h_2)/(h_1 h_2)) P^(15/16)`: the
  derivative scale grows with `h_1 h_2` as fast as the run count, so a larger
  shift does not raise it.
- *Other B.1 budgets.* `|a| r <= P^(1/2)` holds at `P^(0.28+gamma)`; boundary
  crossings `h P^(21/32) <= P^(0.78)`; (B.13), (B.17) and the D1 curvature ratio
  are unaffected.
- *Appendix C.* The (C.17) remainder `Pi P^(-1/8)` is no longer bounded, but
  centering at the floor of the whole coefficient instead of its main term keeps
  the residual in `[0,1)` with few extra windows, since the remainder's
  derivative is `O(Pi P^(-9/8))`. The (C.26) frequency gap fails once
  `Pi >= P^(1/8)`: the `l_F` and `Pi x^(-5/8)` curvatures can collide. The
  reference function factors monotonically as in Proposition 7.6, and Lemma 7.5
  then bounds the collision band by about `P^(0.78)`. (C.22), (C.23) and the
  `l_F = 0` term stay within budget.

With `OOOEE` alone the ideal contagion root is `0.6915` (about `0.685` at 99% of
the ideal coefficient); `OOEOE` uses Theorem 4.9's different phase family and has
not been bookkept. The pass rests on a first reading of Appendices A.1, B and C;
the lemma statements' fixed-shift clauses (`O(P^(1/24))` translations) were
checked only for their relative derivative comparisons.

**6. Adversarial audit of Result 5 (24 September 2026).** An independent
reviewer, instructed to break the chain, confirmed (a) the Theorem B.1 endpoint
limit `delta < 1/6`, (c) the non-growth of Lemma A.1's D2 error, (d) the other
B.1 budgets and (g) the C.7 curvature terms. It found three defects, checked here
at source:

- *C.8 at `b = 0` fails as written.* C.5 prints "For b=0 use N_*=0" and C.8 uses
  `|B| << 1`; at `Pi >= P^(1/8)`, `B` is about `P^(1/32+gamma)`. Result 5's repair,
  centering at the floor of the whole coefficient, is wrong: Lemma 7.5 needs one
  continuous reference `Lambda`, and a frozen integer frequency jumps `f''` by
  `(3/4) x^(-1/2)` at every window, forcing `rho >= P^(1/8)/Pi` and no saving near
  `Pi = P^(1/8)`. The collision estimate also omitted the endpoint term
  `P^(31/32) Pi^(-1/2) = P^(57/64)`, still below `P`.
- *Repair (desk).* From `a_r(beta) = int_0^1 e(-(beta+r)t) dt`,
  `|a_r(beta)| + |a_r'(beta)| << 1/(1+|r+beta|)` for every real `beta`, so on
  stretches where `beta` varies by `O(1)` the coefficient masses are `O(log T)`
  uniformly in the size of `beta`. The uncentered expansion then gives every mode a
  fixed integer frequency and a continuous curvature, and Lemma 7.5 applies mode by
  mode. This is sharper than the printed bounded-residual extension, whose constants
  are stated only as depending on `B_0`.
- *Claim (b)'s premise is false*: at bounded `(i,j,k,l)` the frequency `t` is still
  `O(J)` by (C.12). The conclusion `delta < 3/16` survives; `5/32` never needed it.

Unwritten pieces remain: Lemma 4.4 (printed for `h <= P^(1/12)`) is needed at
`h = P^(5/32)` for (A.13), with a margin of only `P^(1/192)`; the `k = 0`
frequency cases of `T_d` are not bookkept; and Result 4 still needs the passage
from sliding windows to the actual fibres and a truncation of the parity square
waves. No defect found is fatal, but the argument is not established and its
margins are small powers of `P`.

**7. Lemma E1: Paper B's Lemma 4.4 and Lemma A.3 at shifts up to `P^(5/32)`
(written proof, 24 September 2026; AI-assisted, not independently reviewed).**

*Statement.* Fix `C`. Let `P` be large, `h >= 1` an integer, `u = j/2` with
`1 <= |j| <= C P^(1/24)`, `|i|, |k| <= C P^(1/24)`, and suppose `|u| h <= c_0 P^(1/4)`
for a small absolute `c_0`. Then the sum (4.4) of Paper B satisfies
`<< P^(7/8)(1 + h^(1/2)) + (1 + |u|) h P^(3/4) + |u| P^(1/4) + P^(5/6)`.
Paper B states (4.4) for `h <= P^(1/12)` only.

*Proof.* Follow Paper B's proof of Lemma 4.4 and check each step at larger `h`.
(4.5) and `A_h'' = O(h^2 P^(-7/4))` use only `2h/x = o(1)`. The deletion (4.6)
costs `|u| h P^(3/4) + |u| P^(1/4)` for every `h`, since
`Delta_h(x^(3/4)) = O(h P^(-1/4))` and `E = O(P^(-3/4))`. The gap cells of
`G = floor(Delta_h X)` number `O(1 + h P^(1/2))` for `h <= P^(1/2)`, and (4.7),
(4.8) and the Lemma 4.3 sawtooth errors `O(P^(5/6) + P^(3/4) log P)` do not depend
on `h`. In (4.9) the main curvature is `|u| h P^(-3/4)` up to constants and the
error ratios are `h/P`, `(|i|/|u|) P^(-3/4)` and `(|k|/|u|) P^(-9/8)`, all `o(1)`.
The second-derivative estimate on the cells gives (4.10),
`(uh)^(1/2) P^(5/8) + (h/u)^(1/2) P^(7/8)`. For a nonzero carry mode `r`,
`1 <= |r| <= R = P^(1/4)`, the added curvature `|r| P^(-1/2)` dominates (4.9)
because `|u| h P^(-3/4) / (|r| P^(-1/2)) <= |u| h P^(-1/4) <= c_0`; this replaces
Paper B's `P^(-1/8)` and is the only use of `uh << P^(1/4)`. The per-mode cost
`|r|^(1/2) P^(3/4) + h |r|^(-1/2) P^(3/4)`, weighted by `1/|r|`, sums to
`R^(1/2) P^(3/4) + h P^(3/4)`. Collecting terms gives the bound. `QED`

*Consequence for Lemma A.3.* With `h_1 <= P^(5/32)`, `h_2 <= P^(1/24)`,
`J = floor(P^(1/24))` and `u = q`, `1 <= |q| <= J`, (A.13) for `W_1 = Delta_1 Y` costs
`sum_q q^(-1) [P^(7/8) h_1^(1/2) + q h_1 P^(3/4)] << P^(61/64) log P + P^(91/96)`,
below `P^(23/24)` by margins `P^(1/192)` and `P^(1/96)`; the condition
`q h_1 <= J h_1 = P^(19/96) <= c_0 P^(1/4)` holds. For `D`, the value error of
(A.14) is `(h_1+h_2) P^(-1/4) = P^(-3/32)`, and `J P^(-3/32) -> 0`; the monotone
count (A.2) gives `P a_0 = P^(13/32+gamma)` on the zero branch and
`P^(23/24) log P` otherwise. Hence (A.13) holds for every argument at
`h_1 <= P^(5/32)`.

## Open questions

The first-pass bookkeeping (Result 5) finds no binding constraint for `OOOEE`
at `delta = 5/32`, with three local repairs: centering at the full coefficient
floor in C.5 and C.8, a Lemma 7.5 collision estimate in C.8, and Theorem B.1 run
with outer shifts `P^delta` and, at bounded frequencies, `H = P^(1/8)`. It needs an
independent line-by-line audit before any proof is written. `OOEOE` needs its own
bookkeeping.

## Decision

**PARK, pending audit.** Phase-0's stop criterion fired on present
estimates: the production reduces to depth-five parity control on windows of
length `P^(5/32)`. The later bookkeeping (Result 5) indicates that Paper B's
Appendix B and C machinery, run with outer shifts `P^delta`, keeps a power saving
for `OOOEE` up to `delta < 1/6`, or `delta < 3/16` at bounded frequencies, after
three local repairs. That would be the averaged substitute, but it is a first-pass
reading of a dense proof and does not meet the promotion criterion. The pricing
stands: `OOOEE` alone would lift the ideal contagion from `0.633` to `0.6915`, both
depth-five words to `0.7512`. Best next question: Lemma E1 closes the Lemma 4.4 gap with
margin `P^(1/192)`; does the uncentered C.8 repair, written out with the uniform
coefficient bound `|a_r(beta)| + |a_r'(beta)| << 1/(1+|r+beta|)`, keep a power
saving at `Pi` near `P^(1/8)`?

## Publication assessment

Status: `EXPLORATORY`.
