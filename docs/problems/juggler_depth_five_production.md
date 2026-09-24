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

`FateOOOEEAssembly.lean` (Result 18) is the four-production assembly, conditional on
the `OOOEE` production. The depth-four chain is `FateOOEEWeighted.lean` and its imports.

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
`T_d = sum e(phi(n+2d) - phi(n))` over odd `n` in `(P, 2P]`. The diagonal gives `P^(-5/32)`, so
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

**8. Lemma E2: the zero-offset case of Appendix C at `Pi` up to `P^(19/96)`
(written proof, 24 September 2026; AI-assisted, not independently reviewed).**

*Statement.* In Paper B's Appendix C with first shift `h_1 <= P^(5/32)`, second
shift `h_2 <= P^(1/24)`, bounded `k` and `Pi = k h_1 h_2 <= P^(19/96)`, the
`t = 0`, `b = 0` part of the double correlation is `<< P^(29/32+eps)`. (An
earlier version also claimed that the `b = 0` part of the nonzero-`t` case meets
Theorem B.1's hypotheses; that is false, see Result 9.)

*Proof.* At `b = 0` the theta coefficient `B` of (C.20) is no longer bounded: it is
`-(243/128) Pi x^(-1/8)` up to smaller terms, of size up to `P^(1/32+gamma)`, with
`B' = O(Pi P^(-9/8))`. Do not center (Result 6 shows centering fails).

*Coefficients.* For every real `beta`, `a_r(beta) = int_0^1 e(-(beta+r)t) dt`
satisfies `|a_r(beta)| + |a_r'(beta)| << 1/(1+|r+beta|)`: the integral is at most
one, and one integration by parts gives `1/|r+beta|`. Split `(P, 2P]` into
`O(1 + Pi P^(-1/8))` stretches on which `B` varies by at most one, and on each
stretch keep the modes `|r + B_0| <= R = P^(5/16)` around a fixed value `B_0` of
`B`. The truncation error is Paper B's positive error at cutoff `R`, and the sum of
sup norms and variations of `a_r(B(x))` is `O(log P)` per stretch, uniformly in the
size of `B`. Each retained mode has a fixed integer frequency `r`.

*Curvature.* After the carry expansion put `l = r + s`. With the frozen offsets
fixed, (C.25) holds for each mode with the continuous reference
`Lambda = -(27/32) alpha_0 x^(-3/4) + (3645/2048) Pi x^(-5/8) + (3/4) l x^(-1/2)`
and error `O(Pi P^(-3/4))`, so `rho << P^(-1/8)`. Every term in the (C.25) error list
is at most `Pi P^(-3/4)` times a negative power of `P` at these shifts, using
`h_1 + h_2 <= 2 Pi`, `|a_1| << k h_2 P^(1/8) + J` and `|a_2| << k h_1 P^(1/8) + J`.

*Lemma 7.5.* Write `Lambda = x^(-5/8) g(x)` with
`g = (3645/2048) Pi + (3/4) l x^(1/8) - (27/32) alpha_0 x^(-1/8)`. For `l` near the
collision value `-(1215/512) Pi x^(-1/8)`, the `l`-term of `g'` dominates the
`alpha_0`-term by a factor `J P^(-1/8)`, so `g` is monotone and the sublevel sets and
dyadic bands have total length `O(Ps)`; away from it `|Lambda|` is comparable to
the larger of `Pi P^(-5/8)` and `|l| P^(-1/2)`. `M <= 1`, `MP^2 >= 1` and
`rho <= 1/8` hold. The partition has `O(P^(21/32))` cells (original runs at shift
`h_1`, `G`-level cuts, `N_a` windows and stretch ends).

*Costs.* At a collision `M` is comparable to `Pi P^(-5/8)`, and (7.4) gives
`Pi^(1/2) P^(11/16) + P^(31/32) Pi^(-1/2) + P^(7/8)`, at most `P^(29/32)` for
`Pi` in `[P^(1/8), P^(19/96)]`. The colliding pairs `(r, s)` carry total weight
`O(log P)`: for fixed `l` the combined weight is `<< log P / (1 + |l + B|)`, at a
collision `l + B` is about `-(2187/512) Pi x^(-1/8)`, and there are `O(1)` colliding
`l` per stretch over `Pi P^(-1/8)` stretches, so the full (7.4) cost per stretch is
paid with total weight `log P`. In the near-collision band `|Lambda|` is comparable
to `|l - l_*| P^(-1/2)` with weights about `1/(Pi P^(-1/8))`, which costs
`Pi^(1/2) P^(11/16) + P^(31/32) Pi^(-1/2)`; the heavy modes near `l = -B` have
`M` comparable to `Pi P^(-5/8)` and cost at most `P^(29/32) log P`; the remaining
modes cost `R^(1/2) P^(3/4) + P^(21/32+1/4) = P^(29/32)`, as in (C.27). The
`(h_1 + h_2) P^(-3/4)` rounding term of (C.24) is comparable to `Pi P^(-3/4)/k`
rather than smaller by a power of `P`, which still gives `rho << P^(-1/8)`. Applying (7.4) on each
stretch adds `(P/M)^(1/3)` per stretch, in total `P^(5/12 + 2 pi/3)` with
`Pi = P^pi`. Hence the `t = 0`, `b = 0` part is `<< P^(29/32+eps)`.

*Nonzero `t` at `b = 0`.* The uncentered expansion in C.5 shifts the mode range
by `|B| << R`, so (C.18) keeps `|Phi'''| << P^(-13/12)`. This does not place the
nonzero-`t` terms under Theorem B.1: see Result 9. `QED` for the `t = 0`, `b = 0`
statement.

**9. Audit of Lemmas E1 and E2 (24 September 2026).** An independent adversarial
reviewer re-derived both. **E1 holds**: every step of Lemma 4.4 at large `h`, the
mode dominance including opposite signs (ratio at most `(9/8) c_0`), the (A.13)
margins `P^(1/192)` and `P^(1/96)`, and the `D` argument. **E2's `t = 0`, `b = 0`
bound holds in substance**; the reviewer confirmed the formula
`B = -(243/128) Pi x^(-1/8)`, that truncation to `|r + B_0| <= R` is the centred
expansion at `round(B_0)` with its error charged once globally, Lemma 7.5's
hypotheses, and the `O(log P)` colliding weight; the near-collision and heavy-mode
bookkeeping and the (C.24) rounding term are now written into Result 8. Stretches
must be cut by total variation, since `B` jumps by `P^(-3/32)` at `N_2` windows.

**E2's nonzero-`t` clause was false** and has been withdrawn. In C.5 the terms
`a_1 W_1` and `c_11 A` enter Theorem B.1 with `r_j = h_{l,1} = h_1 = P^(5/32)`,
above its printed `C P^(1/24)`, and the partition density is `P^(-11/32)` rather than
`P^(-11/24)`. With those hypotheses widened, `D_h` comparable to `P^(21/32)` makes
the (B.16) endpoint term `P^(33/32) (|t| h)^(-1/2)`, above `P` for `h < P^(1/16)`;
after averaging over `H = P^(1/12)` it gives `|U| << P^(191/192)`, not (B.3)'s
`P^(31/32)`. This is the desk figure of Result 5, and it is not yet a written
theorem. A widened Theorem B.1 is therefore an open piece, and it carries the
thinnest margin of the route, `P^(1/192)`.

**10. Theorem E3: Paper B's Theorem B.1 at shifts up to `P^(5/32)` (written
proof, 24 September 2026; AI-assisted, audited in Result 11).**

*Statement.* Fix `C`, `M` and `delta` with `1/24 <= delta <= 5/32`. Keep every
hypothesis of Paper B's Theorem B.1 except the following, which are widened:
`e_j, r_j <= C P^delta` (still `|a_j| r_j <= C P^(1/2)`); an interval of length `L`
meets at most `C(1 + L P^(-(1/2-delta)))` cells of the partition, so there are
`O(P^(1/2+delta))` cells; the D2 objects have `h_{l,1} <= C P^delta` and
`k_l, h_{l,2} <= C P^(1/24)`; and `s_l, v_l = O(P^delta)`. Then
`|U(P)| << P^(max(31/32, 29/32 + delta/2) + eps)`. At `delta = 5/32` this is
`P^(63/64+eps)`; for `delta <= 1/8` it is Paper B's `P^(31/32+eps)`.

*Proof.* Follow Paper B's Appendix B with the A-process range `H = P^(1/8)`
instead of `P^(1/12)`, and recheck each step at the widened sizes.

- *B.1, D1 linearization.* The carry offset `j` stays bounded because the mixed
  difference of `X` is `O(h r P^(-1/2)) = O(P^(1/8+5/32-1/2)) = o(1)`. (B.5) and
  the global charge (B.6), `|a| P^(1/4) + |a| h r P^(-1/4) << P^(3/4)/r + h P^(1/4)`,
  use only `|a| r <= C P^(1/2)`; the D1 curvature (B.7) is unchanged, and its ratio
  to `M_h = |t| h P^(-3/4)` is `(|t| h r)^(-1) + P^(-1/2)/|t|`.
- *B.2, differencing.* Cell-boundary crossings number `O(h P^(1/2+delta))`, which
  is at most `P^(25/32)` per `h`. The twist ratio (B.9) is `P^(-1/3)/|t|`. The
  theta and `E` cost (B.11) is `|t| h P^(3/4) + |t| P^(1/4)`, at most `P^(11/12)`
  for `h < P^(1/8)` and `|t| <= C P^(1/24)`. (B.12) holds uniformly for `h <= P^(1/8)`, because
  `A_h'' = O(h^2 P^(-7/4))` is `o(M_h)`.
- *B.3, Lemma A.1 at `h_{l,1} = P^delta`.* Lemma A.1 is printed for
  `h <= P^(1/8)`, which covers the new `H`. With `p = h_1 h_2 <= P^(19/96)` and
  `D << (h_1+h_2) P^(1/2) = P^(1/2+delta)` runs: `j` stays bounded
  (`p P^(-1/2) = o(1)`); (A.4) holds, with `j != 0` dominating because
  `p P^(-1/2) = o(1)`. In (A.3) at `Q = P^(5/16)`, the zero-offset term is
  `D/(Qa) << ((h_1+h_2)/(h_1 h_2)) P^(15/16) <= P^(15/16)`, since the derivative
  scale `a = p P^(-3/4)` grows with `h_1 h_2`; the other terms are `P^(11/16)`,
  `p P^(1/4) = P^(43/96)` and `D = P^(21/32)`. For `j != 0`,
  `(P + D P^(1/4))/Q + P^(3/4) + D << P^(3/4)`. The mismatch count (A.6) is
  `<< P^(3/4)`, and (A.7) is `h (P^(3/4) + P^(21/32)) <= P^(7/8)`. The coefficient
  windows number `O(1 + k h P^(1/8)) = O(P^(7/24))`, not Paper B's `P^(1/4)`. In
  (A.10), measured against
  `M = |t| h P^(-3/4)`, the four ratios are at most `P^(-3/16)`, `P^(-47/96)`,
  `P^(-1/3)` and `P^(-61/96)`, so `|Phi_q''| << P^(-15/16)` as in (B.13). Moving
  the base and coefficient by `O(P^delta)` changes derivative comparisons by
  factors `1 + O(P^(delta-1))`. Lemma A.1's closing remark (A.11), with exponent
  `11/12`, fails at `h_1 = P^delta`: its term `(h_1+h_2)(uh)^(-1/2) P^(7/8)` is
  `P^(33/32)` at `h = 1`. Appendix B never cites (A.11); the same cost is the
  `D_h` endpoint term of (B.16) below, where it is charged.
- *B.4, first-floor carries.* Lemma A.2 is printed for `h <= P^(1/12)`, but its
  proof uses `h` only through the shift size. It applies at shifts
  `O(h + P^delta)`: its endpoint-crossing argument uses only the convexity of `X`, and (A.12) is uniform
  in translations `O(P^delta)`. The cell count becomes
  `D_h << (h + P^delta) P^(1/2)`, which absorbs the input cells, the D2 runs and the
  coefficient windows.
- *B.5, the retained modes.* (B.16) becomes
  `(|t| h)^(1/2) P^(5/8) + (sqrt(h/|t|) + P^delta (|t| h)^(-1/2)) P^(7/8)`.
  A nonzero carry mode `v` still dominates: `M_h/(|v| P^(-1/2)) <= |t| h P^(-1/4)
  <= P^(-1/12)`. (B.17) becomes `P^(7/8) + (h + P^delta) P^(3/4) <= P^(29/32)`.

Collect the per-`h` costs: the D2 error `P^(15/16)`, (B.16), (B.17), (B.11),
(A.12), (B.6) and the boundary crossings. Insert them in (B.8) with `H = P^(1/8)`
(the negligible terms `P^(41/24)`, `P^(57/32)`, `P^(11/6)` and `P^(7/4)` from the
first (B.16) term, the crossings, (A.12) and (B.6) are omitted):
`|U|^2 << P^2/H + P^(31/16) + H^(1/2) P^(15/8) + H^(-1/2) P^(15/8+delta)
+ |t| H P^(7/4) + P^(61/32)`. With `|t| >= 1/2` the terms are `P^(15/8)`,
`P^(31/16)`, `P^(31/16)`, `P^(29/16+delta)`, `P^(23/12)` and `P^(61/32)`. The
largest is `P^(31/16)` for `delta <= 1/8` and `P^(29/16+delta)` above it.
`QED`

The binding term is the (B.16) endpoint cost at small `h`. With Paper B's own
`H = P^(1/12)` the same collection gives `|U| << P^(191/192+eps)` at
`delta = 5/32`. Paper B also used `h <= P^(1/12)` in the B.2 crossing cost, the
(B.13) window count, the B.5 carry-mode ratio `P^(-1/8)` (now `P^(-1/12)`), the
`P^(11/12)` remark after (B.16), and Lemma A.2's printed range; each is rechecked
above.

*Consequence for Appendix C.* In C.5 at `h_1 <= P^(5/32)`, `h_2 <= P^(1/24)`,
bounded `k` and `Pi <= P^(19/96)`, the retained terms meet the widened hypotheses.
Each hypothesis checks as follows:

- The terms `a_1 W_1` and `c_11 A` have `r = h_{l,1} = h_1 <= P^(5/32)`, `e_j = 0`
  and coefficient shift `v = d_1 + d_2 = O(P^(5/32))`.
- `|a_1| h_1 << (k h_2 P^(1/8) + J) P^(5/32) = O(P^(31/96))`, and
  `|a_2| h_2 << k h_1 P^(1/8) P^(1/24) = O(P^(31/96))`.
- The original runs have local density `(h_1+h_2) P^(-1/2) = P^(-11/32)`. The `N_*`
  windows and E2's `O(1 + Pi P^(-1/8)) = O(P^(7/96))` stretches are sparser.
- (C.18) keeps `|Phi'''| << P^(-13/12)`, because `Pi P^(-13/8) = P^(-137/96)` and the
  mode range `|r| <= R + |B|` is `O(R)`.
- *Centering at nonzero `b` (added after the audit, Result 11).* C.5 centers at
  `N_* = floor((27/32) k b x^(3/8))` and needs `B_core - N_*` bounded. By (C.17) the
  remainder is `O(Pi P^(-1/8) + k(h_1+h_2) P^(-5/8))`, bounded only because (C.10)
  has `Pi << P^(5/48)`; at `Pi = P^(19/96)` it is `P^(7/96)` for every `b`. Center
  instead at `N = floor(B_core)` on the windows where it is constant. `B_core'` is
  `O(k P^(-5/8) + Pi P^(-9/8))`, so the windows have local density at most
  `P^(-7/12)`, below `P^(-11/32)`. Nothing else needs to be continuous across
  windows, since Theorem B.1 lets `phi` jump between cells. On a window the
  residual `B_core - N` lies in `[0, 1)` and has variation at most one. Lemma 4.7
  expands it with coefficient masses `O(log R)`. The frequency `(r - N) X` has
  `|N| << |N_*| + P^(7/96) << P^(5/12)`, so (C.18) is unchanged. Result 6's
  objection to piecewise centering concerns Lemma 7.5's curvature at `t = 0`; it
  does not apply here.

So the nonzero-`t` row of C.9 is `<< P^(63/64+eps)` at these sizes. The positive
errors (E1) and the `t = 0`, `b = 0` row (E2) are written. The `t = 0`, nonzero-`b`
row (C.6, C.7) at these sizes rests only on Result 5's desk reading. If that row
holds, the double correlation is `<< P^(63/64+eps)`.

**11. Audit of Theorem E3 (24 September 2026).** An independent adversarial
reviewer re-derived every exponent from Paper B's text. **The main bound holds**,
including `P^(63/64)` at `delta = 5/32`; no step fails. The reviewer:

- confirmed Lemma A.1 at `h_1 = P^(5/32)`, including all four (A.10) ratios;
- confirmed Lemma A.2 at shifts `O(h + P^delta)`;
- recomputed the (B.8) collection with ten terms, and the maximum is `29/16 + delta`
  above `delta = 1/8`;
- found nothing that scales with `D_h` or the cell count beyond what is charged.

It found four wording faults, now fixed in Result 10. The claim that (B.11) was the
only use of `h <= P^(1/12)` was false; five other uses exist, and each passes.
(A.11)'s printed exponent fails at the wider shift, harmlessly. The `a_2` budget was
missing. The collected formula dropped four negligible terms.

It found one gap in the Appendix C consequence. The C.5 centering at nonzero `b`
relied on (C.10)'s `Pi << P^(5/48)`, which the widened `Pi` breaks for every `b`.
I verified this at the source (note (C.10) and (C.17)). The repair, centering at the
floor of the whole coefficient on its own windows, is now written in Result 10. The
nonzero-`t` row is therefore `<< P^(63/64+eps)` at `h_1 <= P^(5/32)`,
`Pi <= P^(19/96)`, subject to that added paragraph, which the reviewer proposed
but did not re-audit.

**12. Lemma E4: the `t = 0`, nonzero-`b` case of Appendix C at `Pi` up to
`P^(19/96)` (written proof, 24 September 2026; AI-assisted, audited in
Result 13).**

*Statement.* In Paper B's Appendix C, take first shift `h_1 <= P^(5/32)`, second
shift `h_2 <= P^(1/24)`, `1 <= k <= C P^(1/24)` and `Pi = k h_1 h_2 <= P^(19/96)`.
Keep `J = floor(P^(1/24))`, `R = P^(5/16)` and `R_c = P^(1/4)`. Then the `t = 0`,
nonzero-`b` part of the double correlation is
`<< (k^(1/2) P^(15/16) + k^(-1/2) P^(13/16)) log^C P`. This is (C.23) unchanged:
`P^(23/24)` in general, and `P^(15/16)` at bounded `k`.

*Proof.* Follow C.6 and C.7 and recheck each step. Throughout,
`p = h_1 h_2 <= P^(19/96)`, the original runs number `D << (h_1+h_2) P^(1/2) =
P^(21/32)`, and (C.13) becomes
`|a_1| h_1 + |a_2| h_2 << Pi P^(1/8) + J(h_1+h_2) << P^(31/96)`.

- *Floor exceptions (C.6).* Replacing `A` by `J_F = floor(G)` at nonzero `b`
  uses (A.3) with derivative scale `a = P^(-1/4)` and distance
  `delta << P^(-3/4) + p P^(-5/4)`. The count is
  `delta (P + D/a) + P a + D << P^(1/4) + P^(21/32 - 1/2) + P^(3/4) + P^(21/32)`,
  which is `O(P^(3/4))` as printed.
- *First-difference Taylor step (C.6).* The error `|a_a| h_a P^(-7/4)` per point
  sums to `P^(31/96 - 3/4) = P^(-41/96)`, still bounded.
- *The theta coefficient is no longer a bounded shift of `N_*`.* The wave part of
  `B` in (C.20) is `<< Pi P^(-1/8) + J(h_1+h_2) P^(-1/4)`, which Paper B bounds by
  `O(1)` using (C.10). Here it is `O(P^(7/96))`. The (C.17) remainder is
  `O(P^(7/96))` for the same reason (Result 11). So `B - N_*` is not bounded.

  *Repair.* Center at `N = floor(B)` for the whole coefficient `B` of (C.20),
  instead of at `N_*`, as in Result 10's nonzero-`t` repair.
  - `B` is monotone on each cell of the common partition (original runs, on which
    `beta_a` and `b` are fixed, intersected with the `N_1`, `N_2` windows); it jumps
    by about `k P^(3/8)` where `b` changes. The leading part of
    `B'` is `(81/256) k b x^(-5/8)`, of size at least a constant times `P^(-5/8)`
    because `b` is a nonzero integer. The other parts of `B'` are
    `Pi P^(-9/8) + J(h_1+h_2) P^(-5/4) + k h_1 P^(-13/8) << P^(-89/96)`.
  - `B` jumps by `O(h_a P^(-1/4))` where `N_a` changes. This is harmless, because
    the `N` windows are taken inside those cells.
  - The windows number `O(k P^(3/8))` plus `O(1)` per cell.
  - On each window the residual `B - N` lies in `[0, 1)` and is monotone. Lemma 4.7
    expands it with coefficient mass `O(log R)`, and its positive error is charged
    once globally, as in (A.12).
- *Curvature (C.21)-(C.22).* The `-N X''` row of (C.21) changes by
  `|N - N_*| X'' << P^(7/96 - 1/2) = P^(-41/96)`. That is below the allowed error
  `P^(-3/16) = P^(-18/96)`, so the leading coefficient `-243/512` stands. The
  (C.22) error list at these sizes:

  | Error term | Size |
  |---|---|
  | `Pi P^(-5/8)` | `P^(-41/96)` |
  | `k(h_1+h_2) P^(-9/8)` | at most `P^(-89/96)` |
  | `k P^(-7/8)` | at most `P^(-5/6)` |
  | `(\|a_1\| h_1 + \|a_2\| h_2) P^(-3/4)` | `P^(-41/96)` |
  | `(R + R_c + 1) P^(-1/2)` | `P^(-3/16)`, unchanged and still the largest |
  | `R_c (h_1+h_2) P^(-3/2)` | `P^(-35/32)` |
  | the `q`, `l` and `phi_0''` terms | smaller |

  So (C.22) holds with error smaller than the main curvature by `O(P^(-1/16)/k)`.
- *Interval count.* The `G`-levels give `O(P^(3/4))` cuts, since `|G'|` is about
  `P^(-1/4)` at nonzero `b`. The other cuts are smaller:
  - original runs, `P^(21/32)`;
  - `N_1`, `N_2` windows, `O(k h_1 P^(1/8)) = O(P^(31/96))`;
  - `N` windows, `O(k P^(3/8))` plus `O(1)` per cell;
  - endpoint-order cuts, a fixed multiple of these.

  The total stays `O(P^(3/4))`.
- *Sum.* The second-derivative test over these intervals, with curvature about
  `k P^(-1/8)`, gives `P (k P^(-1/8))^(1/2) + P^(3/4) (k P^(-1/8))^(-1/2)`, which
  is (C.23). The floor exceptions (`P^(3/4)`), the Lemma 4.7 and carry positive
  errors (`P^(5/6) log P`), and the replacements of `q D` by `q G` (`P^(7/24)`) and
  of the fifth coordinate (`O(1)`) are smaller. `QED`

*Consequence.* With E1 (the positive errors, `P^(23/24)`), E2 (`t = 0`, `b = 0`,
`P^(29/32)`), E3 (nonzero `t`, `P^(63/64)`) and E4, every row of C.9 is written at
`h_1 <= P^(5/32)`, `h_2 <= P^(1/24)`, bounded `k` and `Pi <= P^(19/96)`. The deleted
master term grows from `P^(11/48)` to `P^(31/96)`, and the extra-power errors stay
`P^(7/24)`. The double correlation is therefore `<< P^(63/64+eps)`. A van der Corput
step in `h_2 < P^(1/24)` then gives `|T_d|^2 << P^(2-1/24) + P^(1+63/64+eps)`, so
`|T_d| << P^(127/128+eps)` for the frequency vectors with bounded `k != 0` at
`d <= P^(5/32)`. E4's wider range `k <= C P^(1/24)` does not extend this: E2 and E3
assume bounded `k`, and at `k = P^(1/24)` the product `Pi` would reach `P^(23/96)`.
The `k = 0` vectors (C.2) are not covered.

**13. Audit of Lemma E4 (24 September 2026).** An independent adversarial
reviewer re-derived every exponent from Paper B's text. **E4's bound and its repair
hold**, and no step fails.

- It confirmed the constant `81/256 = (27/32)(3/8)`. It also confirmed that the
  rest of `B'` is smaller than the leading term by `P^(-29/96)`.
- It confirmed that re-centring at `floor(B)` is legitimate here. C.7 applies the
  plain second-derivative test interval by interval, so Result 6's objection
  (Lemma 7.5 at `b = 0`) does not apply. The only curvature change is
  `P^(-41/96)`.
- It recomputed the whole (C.22) error table, the floor-exception count, the
  interval count and (C.23).
- It checked the six rows of C.9 and the van der Corput step to
  `|T_d| << P^(47/48) + P^(127/128)`.

It also checked, and passed, uses of the old sizes that E4 had not written:

- `-1 <= b <= 2`;
- the value comparison for `beta_a`;
- the (C.16) and (C.15) errors;
- the dominance of `G'` at nonzero `b`.

It found three wording faults, now fixed:

- The ledger row stated `|T_d| << P^(127/128)` for `k != 0` without "bounded".
  E2 and E3 assume bounded `k`, so that was an overclaim.
- `B` is monotone on cells of original runs intersected with the `N_a` windows. It
  is not monotone on the `N_a` cells alone, because `B` jumps by about `k P^(3/8)`
  where `b` changes.
- The `N`-window count omitted its `O(1)` per cell.

The consequence stands for bounded `k != 0`, subject to E3's claim that (A.12) is
uniform under translations of size `P^(5/32)`. E2's `b = 0` part was audited in
Result 9.

**14. Lemma E5: the `k = 0` frequency cases of `T_d` at shifts up to `P^(5/32)`
(written proof, 24 September 2026; AI-assisted, audited in Result 15).**

*Statement.* Let `(i, j, l)` be a bounded, nonzero integer vector. Take `k = 0` and
`1 <= d <= P^(5/32)`. By (C.4)-(C.6) the phase is
`phi = iX/2 + jY/2 + l m^(9/8)/2`, up to a replacement costing `O(|l| P^(7/16))`
at each endpoint. Then, for `T_d = sum_n e(phi(n+2d) - phi(n))` over the odd
`n` in `(P, 2P]`:

| Case | Bound on `\|T_d\|` |
|---|---|
| `j != 0` | `P^(7/8) d^(1/2) + d P^(3/4) + P^(5/6)`, which is `<< P^(61/64)` |
| `j = 0`, `l != 0` | `P^(7/8) log P` |
| `j = l = 0`, `i != 0` | `P^(1/2)/d + 1` |

Paper B's C.2 treats the undifferenced sums. Its `j != 0` subcase applies an
A-process and then bounds exactly this differenced sum at `h <= P^(1/12)`. E5 is
that inner step with the range widened to `h = d`, so no A-process is applied here.

*Proof, `j != 0`.* `T_d` is Paper B's sum (4.4) at `h = d`, plus the term
`(l/2) Delta_d(m^(9/8))`. Use E1 (Result 7), which is Lemma 4.4 for
`|u| h <= c_0 P^(1/4)`. Here `|u| d << P^(5/32)`, so E1 applies. Add the `l`-term
as C.2 does:

- On a gap cell with `g = m(n+2d) - m(n)` fixed,
  `Delta_d(m^(9/8)) = V_g(m)` with `V_g(z) = (z+g)^(9/8) - z^(9/8)`.
- By (C.7), `|V_g'(X)| << d P^(-13/16)`. So replacing `V_g(m)` by `V_g(X)` costs
  `|l| d P^(3/16) <= P^(11/32)` in total.
- The identity (4.8) holds for any phase attached to each branch. So add
  `(l/2) V_{G+epsilon}(X)` to `F_{G,epsilon}`. No new cell or carry is needed.
- Its curvature is `O(d P^(-21/16))`. That is at most `P^(-9/16)` times E1's main
  curvature `u d P^(-3/4)`, and at most `P^(-21/32)` times a carry mode's
  `|r| P^(-1/2)`. The first ratio holds for every `d`; the second is
  `d P^(-13/16)`, so it needs `d <= P^(5/32)`.
- The E1 bound therefore holds with the extra cost `P^(11/32)`.

At `d = P^(5/32)` the bound is `P^(61/64) + P^(29/32) + P^(5/6)`.

*Proof, `j = 0`, `l != 0`.* Expand each endpoint by (C.8). With
`B = (9l/16) x^(3/16)`, `N_B = floor(B)` and cutoff `T = floor(P^(1/8))`, we have
`e(phi(n)) = sum_{|r| <= T} a_r(B - N_B) e(f_r(n)) + O(E_T(X(n)))`, where
`f_r = (l/2) x^(27/16) + (i/2 + r - N_B) X`.

- *Errors.* The positive errors at `n` and `n + 2d` total `O(P^(7/8) log P)`,
  as in C.2.
- *Windows.* Put `N_1 = N_B(x + 2d)` and `N_2 = N_B(x)`. Since
  `B(x+2d) - B(x) << d P^(-13/16) = o(1)`, the difference `N_1 - N_2` is 0 or
  `sign(l)`. It is constant on the `O(1 + P^(3/16))` intersections of the two
  families of windows.
- *Phases.* For the pair `(r, r')` the phase is
  `F = f_r(x + 2d) - f_{r'}(x) = (l/2) Delta_d(x^(27/16)) + c_1 X(x+2d) - c_2 X(x)`,
  with `c_1 = i/2 + r - N_1` and `c_2 = i/2 + r' - N_2`.

Put `Delta = c_1 - c_2`.

- *`Delta != 0`.* Write
  `F'' = Delta X''(x+2d) + c_2 Delta_d X'' + (l/2) Delta_d(x^(27/16))''`. The
  integer `Delta` gives curvature about `|Delta| P^(-1/2)`. The other two terms are
  `O(d P^(-21/16))`: `|c_2| <= |i| + T + |N_2| << P^(3/16)` and
  `Delta_d X'' << d P^(-3/2)`. That is a factor `P^(-21/32)` smaller. Weighted by
  `|a_r a_{r'}| << 1/((1+|r|)(1+|r'|))`, the second-derivative test gives
  `(T^(1/2) P^(3/4) + P^(3/16) P^(1/4)) log^2 P << P^(13/16) log^2 P`.
- *`Delta = 0`.* Then
  `F'' = Delta_d[(l/2)(x^(27/16))''] + c Delta_d X''`, with `c = c_1 = c_2`.
  Freeze `N_1` and write `N_1 = B(x) + O(1)`. The leading part is
  `(243/4096) l d x^(-21/16)`, from
  `2d [(1/2)(27/16)(11/16)(-5/16) + (9/16)(3/8)] = (243/4096) d`. (A
  50-digit finite difference at `x = 10^12`, `d = 1000`, `l = 1` gives
  `0.0593261717`, against `243/4096 = 0.0593261719`.) Relative to it, the
  `(i/2 + r) Delta_d X''` part is `O((|i| + T) P^(-3/16)) = O(P^(-1/16))`, and the
  `O(1)` in `N_1` contributes `O(P^(-3/16))`. So `F''` is one-signed, of size about
  `|l| d P^(-21/16)`, which exceeds `P^(-2)`. The test gives
  `d^(1/2) P^(11/32) + (1 + P^(3/16)) d^(-1/2) P^(21/32) << P^(27/32)`. The
  diagonal weights sum to `O(1)`.

The coefficient variation is `O(1/(1+|r|))` on each window, as in C.2. Hence
`|T_d| << P^(7/8) log P`.

*Proof, `j = l = 0`.* The phase `(i/2) Delta_d X` has derivative about
`(3i/4) d x^(-1/2)`. It is monotone, and after the change to odd `n` its absolute value
is below `1/4`. The Kusmin-Landau inequality gives `O(P^(1/2)/d + 1)`. `QED`

*Consequence.* This case needs neither Proposition 7.6 nor a curvature collision.
With E1-E4 (Results 7-13), every bounded nonzero frequency vector has
`|T_d| << P^(127/128+eps)` for `1 <= d <= P^(5/32)`. At small `d`, E2's cost line,
written for `Pi` in `[P^(1/8), P^(19/96)]`, still applies: its formula
`Pi^(1/2) P^(11/16) + P^(31/32) Pi^(-1/2)` stays below `P^(31/32)` for smaller `Pi`,
where Paper B's own C.8 also applies. The `k != 0` vectors give
`P^(127/128)` and the `k = 0` vectors at most `P^(61/64)`. The only unwritten step
of the `OOOEE` route is now the poor-tail reduction from sliding windows to the
actual fibres, including the square-wave truncation. That is where the frequencies
stop being bounded, and it decides whether this saving is enough.

**15. Audit of Lemma E5 (24 September 2026).** An independent adversarial
reviewer re-derived all three cases from Paper B's text. **All three hold**, and no
step fails. It confirmed:

- **Coverage.** At `k = 0`, `T_d` is exactly (4.4) at `h = d` plus the `l`-term.
  The `k = 0` vectors are exactly those that E1-E4 do not cover.
- **Case `j != 0`.** The branchwise `l`-term leaves (4.8), the Lemma 4.3 errors and
  both curvature comparisons intact. The exponent is `61/64`.
- **Case `j = 0`, `l != 0`.**
  - The constant `243/4096` checks out, both analytically and at `l = -3`.
  - The product `a_r(beta(n+2d)) conj(a_{r'}(beta(n)))` is a legitimate
    bounded-variation weight, so no cross term is missing.
  - The sum is `P^(27/32)`, largest at `d = 1`.
- **Case `j = l = 0`.** The Kusmin-Landau step is correct.
- **Small `d`.** E1-E4 apply at small `d` too, since their hypotheses are upper
  bounds.

It found seven wording faults, now fixed:

- "Both ratios hold for every `d`" was false. The carry ratio needs
  `d <= P^(5/32)`.
- The `Delta != 0` bound did not name the `c_2 Delta_d X''` term, which reaches the
  bound's own order `d P^(-21/16)`.
- The "nine digits" check was not recorded. It is now stated with its parameters
  (about nine digits).
- Result 4's `T_d` omitted "odd `n`".
- The relation to C.2's inner step was unstated.
- E2's cost line is written only for `Pi >= P^(1/8)`. It extends below that range
  trivially, which is now said.
- The ledger row omitted the `+1` in the Kusmin-Landau bound, the forced `i != 0`,
  and the `O(P^(-1/16))` relative error of the diagonal curvature.

With E1-E5, `|T_d| << P^(127/128+eps)` for every bounded nonzero frequency vector
at `1 <= d <= P^(5/32)`. Each lemma has had one AI audit and no human review.

**16. Lemma E6: the `OOOEE` count-poor tail (written proof, 24 September 2026;
AI-assisted, audited in Result 17).**

*Setting.* The word `OOOEE` means that `n`, `J(n)` and `J^2(n)` are odd and
`J^3(n)` and `J^4(n)` are even. Put `X = n^(3/2)`, `m = floor(X)`,
`Y = m^(3/2)`, `Z = floor(Y)^(3/2)` and `U = floor(Z)^(1/2)`. Then
`J(n) = floor(X)`, `J^2(n) = floor(Y)`, `J^3(n) = floor(Z)`, and on the word
`J^4(n) = floor(U)`. The parity of `floor(v)` is decided by `{v/2}`. So for odd
`n` the word is `chi_1(X) chi_2(Y) chi_3(Z) chi_4(U)`, where each `chi_i` is the
indicator of a half arc of `{v/2}`: `[1/2, 1)` for odd, `[0, 1/2)` for even. Paper
B's phase `(iX + jY + kZ + lU)/2` has exactly these coordinates.

The composite `G(n) = floor(floor(U)^(1/2))` is nondecreasing on all `n`, as a
composition of nondecreasing maps; on the word it equals `J^5(n)`. So the
target-`t` fibre is `F_t = {n in I_t odd : n has word OOOEE}`, where
`I_t = G^(-1)(t)` is an interval of integers. Let `H_t` be the number of odd
integers in `I_t`.

*Fibre geometry.* The floor losses propagate as follows:

- `floor(Y) = n^(9/4) - O(n^(3/4))`;
- `Z = n^(27/8) - O(n^(15/8))`;
- `U = n^(27/16) - O(n^(3/16))`.

`U` is nondecreasing with smooth rate about `n^(11/16)`. Now `G(n) = t` exactly
when `U` lies in `[t^2, (t+1)^2)`, a range of width `2t + 1`. So
`|I_t| = (32/27) t^(5/27)(1 + o(1)) + O(1)`, and the fluctuation shifts each
endpoint by `O(n^(3/16 - 11/16)) = o(1)`. Hence
`H_t = (16/27) t^(5/27)(1 + o(1))` and `max I_t <= (t+1)^(32/27)(1 + o(1))`.

Define
`Poor_eta = {t : |#F_t / H_t - 1/16| >= eta}`.

*Statement.* For each `eta > 0` there are `D` and `M` such that, for every
`U_0 >= M`, `sum_{t > U_0, t in Poor_eta} 1/t <= D U_0^(-1/109)`.

*Proof.* Fix a dyadic source block `(P, 2P]`. Assign each target to the block
containing the left end of `I_t`. Its fibre then lies in
`(P, 2P + O(P^(5/32))]`, inside Paper B's range `[P, 3P]`. Let `L_min` be the least
`H_t` among these targets, about `(16/27) P^(5/32)`, and put
`L_1 = floor(eta L_min / 10)`.

- *Square waves.* Take a degree `J` and the Beurling-Selberg (Vaaler) majorant
  `chi_i^+` and minorant `chi_i^-` of each closed or open half arc. Then
  `chi^- <= chi <= chi^+` everywhere, including at integer values of `v/2`. The
  difference `Delta_i = chi_i^+ - chi_i^-` is nonnegative with mean `2/(J+1)`.
  All coefficients are bounded, and `sup |chi^+| <= A` for an absolute `A`.
  Telescoping gives
  `|prod chi_i - prod chi_i^+| <= A^3 sum_i Delta_i`. The constant term of
  `prod chi_i^+` is `(1/2 + O(1/J))^4 = 1/16 + O(1/J)`. The coordinates separate,
  so its Fourier coefficients are products of one-dimensional ones.
  Hence, for any set `B` of consecutive odd `n`, with
  `S_nu(B) = sum_{n in B} e((nu_1 X + nu_2 Y + nu_3 Z + nu_4 U)/2)`,
  the deviation `dev(B) = #{n in B : word OOOEE} - #B/16` satisfies
  `|dev(B)| <= C_0 #B / J + (1 + 4A^3) sum_{0 < |nu|_inf <= J} |S_nu(B)|`.
  Choose `J = ceil(40 C_0 / eta)`. Every `nu` here is a bounded nonzero integer
  vector, with bound depending only on `eta`.
- *Blocks.* Cut the odd integers of the range into blocks of `L_1` consecutive
  odd integers, starting at an offset `s` in `[0, L_1)` chosen below. Call a
  block bad if `|dev(B)| >= (eta/2) L_1`.
  - *A poor fibre contains a bad block.* `I_t` is a union of `k` full blocks and at
    most two partial pieces of fewer than `L_1` odd integers each. For a partial
    piece `|dev| <=` its size. If no full block is bad, then
    `|dev(I_t)| < (eta/2) k L_1 + 2 L_1 <= (eta/2 + eta/5) H_t < eta H_t`, so `t`
    is not poor. The intervals `I_t` are disjoint, so the number of poor targets
    in the block is at most the number of bad blocks.
  - *A bad block has a large sum.* In a bad block,
    `sum_nu |S_nu(B)| >= (eta/2 - eta/40) L_1 / (1 + 4A^3)`. So some `nu` has
    `|S_nu(B)| >= c_eta L_1`, with
    `c_eta = eta / (3 (1 + 4A^3) (2J+1)^4)`.
- *Second moment.* For each `nu`, sum over all starts `a` of windows of `L_1`
  consecutive odd integers:
  `sum_a |S_nu(a)|^2 <= L_1 P + 2 L_1 sum_{0 < d < L_1} |T_d^nu| + O(L_1^3)`,
  where `T_d^nu` is the differenced sum of Result 4 at frequency `nu`. The average
  over the offset `s` of `sum_{B in grid(s)} |S_nu(B)|^2` is this divided by
  `L_1`. Choose `s` so that the total over the `O_eta(1)` vectors `nu` is at most
  its average. Fibres may run to `2P + O(P^(5/32))`. The windows there cost
  `O(P^(5/32) L_1^2) = O(P^(15/32))`, and Paper B's estimates hold on `[P, 3P]`.

  Since `L_1 <= P^(5/32)`, Results 7-15 give `|T_d^nu| << P^(127/128+eps)` for
  every such `nu` and `d`. So
  `#bad <= sum_nu sum_B |S_nu(B)|^2 / (c_eta L_1)^2
  << P / L_1^2 + P^(127/128+eps) / L_1 << P^(11/16) + P^(107/128+eps)`.
- *Reciprocal mass.* The targets assigned to the block are at least a constant
  times `P^(27/32) = P^(108/128)`. So the poor targets there carry reciprocal
  mass `<< P^(-1/128+eps)`. Summing over dyadic `P` from about
  `U_0^(32/27)` gives `<< U_0^(-(32/27)(1/128) + eps) = U_0^(-1/108 + eps)`.
  This proves the statement with exponent `1/109`. `QED`

*Consequence: a written `OOOEE` production and a route to `2/3` (conditional).*
Take `eta = 1/200`.

- *Count to weight.* For a target `t` that is not poor, and large enough,
  `sum_{n in F_t} 1/n >= (1/16 - eta) H_t / max I_t
  = (1 - 16 eta)(1 - o(1)) / (27 t)`. This is at least `1/(30 t)`, since
  `(0.92)(30/27) > 1.02`.
- *Production inequality.* As in the depth-four
  [weighted production](../theory/juggler_ooee_weighted_production_note.md):
  discard the targets up to a fixed `U_0` and the poor tail, which costs a
  constant independent of `A`. The sources lie below the cutoff by
  `max I_t <= t^(32/27)(1 + o(1))`. Distinct fibres are disjoint, and they are
  disjoint from the other words' sources because the parity prefixes differ.
  Backward closure places every source in `A`. This gives
  `(1/30) fullMass A (27t/32 - O(1)) <= sourceMass A OOOEE (cutoff t) + C`,
  uniformly in `A`.
- *Assembly.* Add this to the three certified productions: `E` at 1, `OE` at
  `33/100` and `OOEE` at `11/100`. The root of
  `(1/2)^lam + (33/100)(3/4)^lam + (11/100)(9/16)^lam + (1/30)(27/32)^lam = 1`
  is `[0.679304053427 +/- 6e-13]`. This enclosure was certified by the Arb MCP
  (`arb_production_root`, python-flint 0.9.0, 128 bits). The root exceeds `2/3`.
- *What would follow.* Unconditional contagion `logMass A X >> (log X)^(2/3)`,
  and the Tao and pressure thresholds lowered from `3/8` to `1/3`.

That consequence rests on three things:

- the six written lemmas E1-E6, none of them human-reviewed, with E6 not yet
  audited;
- the production inequality's `O(1)` in `27t/32 - O(1)`, which still needs an
  explicit constant;
- a four-production version of `FateOOEEAssembly`, which is not written. Only
  `recursion_lemma` is generic. `rate`, `coeff` and `shifted_recurrence` are fixed
  at three productions. `rate_bounds` caps the rates at `3/4`, below `27/32`. The
  shift `16` and the constant `5C` must grow: the shift to at least about `26`
  plus the new `O(1)`, and the multiplier to at least about `6.4`. The
  pressure-threshold instance hard-codes `3/8` and must be redone at `1/3`.

It is not proved, and nothing here is kernel-checked. It also falls short of the
branch's promotion criterion `lambda > 0.74`, which needs `OOEOE` as well.

**17. Audit of Lemma E6 (24 September 2026).** An independent adversarial
reviewer re-derived E6 from the dossier and Paper B. **E6's tail bound holds**,
conditional on E1-E5; no step fails. The reviewer confirmed:

- the parity encoding against Paper B's `U = floor(Z)^(1/2)`;
- the ideal fraction `1/16` and coefficient `1/27`;
- the telescoped Vaaler bound;
- the coverage of the one-coordinate `Delta_i` vectors by E1-E5;
- the grid-block and offset argument;
- the second moment;
- the exponents `11/16`, `107/128` and `1/108`.

It also recomputed the four-production root, `0.6793040534268`; the sum at
`lambda = 2/3` is `1.00709`.

Fixed in Result 16:

- the mean of `Delta_i` is `2/(J+1)`;
- `G` is nondecreasing on all `n`;
- the fibre geometry is now derived, not cited from Result 2, which has no proof;
- fibres running past `2P` are now charged.

**The assembly is not a drop-in.** Result 16 called the existing exponent
certificate "generic in the family". That is false for the current Lean code; I
checked `FateOOEEAssembly.lean` (lines 176-235). Only `recursion_lemma` is generic.
`rate` and `coeff` are defined on `Fin 3`. `rate_bounds` caps the rates at `3/4`.
`shifted_recurrence` absorbs the `-4` losses with a shift of `16`, which requires
rate at most `3/4`, and subtracts `5C` for three losses. At rate `27/32` with a
fourth production, both constants must be rederived. The pressure-threshold
instance also hard-codes `3/8`.

The Decision section now says the production "would give" `2/3`. The ledger row
and the obstruction record have also been corrected. The conditional
consequence stands: an `OOOEE` production at `1/30`, and contagion `2/3` once a
four-production assembly is written and E1-E6 are reviewed.

**18. The four-production assembly (kernel-checked, conditional; 24 September
2026).** [FateOOOEEAssembly.lean](../../formal/Problems/Juggler/FateOOOEEAssembly.lean)
takes the `OOOEE` production as its single explicit input. `OOOEEProductionBound A`
says that for some `b, C >= 0` and all large `t`,
`(1/30) fullMass A (27t/32 - b) <= sourceMass A OOOEEGuard (cutoff t) + C`. The
guard is the actual parity word: `n`, `J n` and `J^2 n` odd, and `J^3 n` and `J^4 n`
even. The `E`, `OE` and `OOEE` productions are the unconditional ones of
`FateOOEEWeighted`.

The module proves:

- the four-way disjoint source partition;
- the recurrence with one constant `3C`;
- the shift `16 + 32b/5`, which absorbs the `-4` losses at rates up to `3/4` and
  the `-b` loss at `27/32`;
- the loss multiplier `7`, since `7 (sum c - 1) = 7 * 71/150 >= 3`;
- the rational certificate `sum c_i rate_i^(2/3) > 1`, from lower bounds
  `0.6299`, `0.8254`, `0.6814` and `0.8928` on the four powers (sum `1.0070`);
- through the generic `recursion_lemma` with `emax = 27/32`:
  - `logMass_growth_of_oooee`, contagion `K (log X)^(2/3)`;
  - the Tao-rate implication at `e > 1/3`;
  - the pressure (Theorem 9.2) and no-momentum (Proposition 9.3) corollaries at
    `e > 1/3`.

The module builds (3,658 jobs). `AxiomCheckOOOEEAssembly` shows that all 11
theorems depend only on propext, Classical.choice and Quot.sound. The Lean style
check reports no new violations.

This answers Result 17's objection: the assembly needed rederived constants, not
new mathematics. It does not prove the `OOOEE` production. That input is E1-E6
(Results 7-17), written and AI-audited but not human-reviewed, and not in Lean.
The scale-average form of the pressure theorem (`FateScaleAverage`) is not redone
at `1/3`.

**19. Lemma E7: the `OOEOE` differenced sums at shifts up to `P^(5/32)` (written
proof, 24 September 2026; AI-assisted, audited in Result 21).**

*Setting.* Paper B's Section 4.3 uses the coordinates `X = n^(3/2)`,
`m = floor(X)`, `Y = m^(3/2)`, `U = floor(Y)^(1/2)` and `W = floor(U)^(3/2)`. With
`theta = {X}` and `xi = {U}`, its (4.18) reads:

- `U = n^(9/8) - (3/4) theta n^(-3/8) + O(P^(-9/8))`;
- `kW/2 = (k/2) n^(27/16) - C theta - B xi + O(k P^(-9/16))`, with
  `B = (3k/4) x^(9/16)` and `C = (9k/16) x^(3/16)`.

Let `phi = (iX + jY + l U + kW)/2` for a bounded nonzero integer vector
`(i, j, l, k)`, and let `T_d = sum e(phi(n+2d) - phi(n))` over odd `n` in `(P, 2P]`.

*Statement.* For `1 <= d <= P^(5/32)`, `|T_d| << P^(61/64) log^2 P`. More precisely:

| Case | Bound on `\|T_d\|` |
|---|---|
| `j != 0` | `(P^(7/8) d^(1/2) + d P^(3/4) + P^(15/16)) log^2 P` |
| `j = 0`, `k != 0` | `P^(7/8) log P` |
| `k = 0`, `j = 0`, `(i, l) != 0` | `P^(7/8)` |

*Idea.* Paper B centres `B` at its floor on windows of length `P^(7/16)/k`. For a
differenced sum that fails when `j = 0`: the pairs of modes `(r, r')` with
`r != r'` keep a phase `(r - r') x^(9/8)`, whose curvature `P^(-7/8)` is worth one
curvature scale per window. So there is no saving across `P^(9/16)` windows.
Instead, keep `B` smooth and treat the gap of `floor(U)` as a carry, as Lemma 4.4
treats the gap of `floor(X)`.

*The `U`-carry.*

- *Common coefficient.* Replacing `B(n+2d)` by `B(n)` costs `k d P^(-7/16)` per
  point, `P^(23/32)` in total. The two `xi`-terms then combine to
  `-B(n)(Delta_d U - g)`, where `g = floor(U(n+2d)) - floor(U(n))`.
- *Noise.* Write `Delta_d U = S + nu`. Here `S = Delta_d (x^(9/8))` is smooth, and
  `nu = -(3/4)[theta(n+2d)(n+2d)^(-3/8) - theta(n) n^(-3/8)] + O(P^(-9/8))`.
- *Theta cancellation.* `-B nu` cancels the two `C theta` terms of `kW/2` up to
  `O(k d P^(-7/16) P^(-3/8))` per point, because `(3/4) B x^(-3/8) = C`. This is
  (4.19) at each endpoint.
- *Carry.* Put `G = floor(S)` and `z = S - G`, which is monotone in `[0, 1)` on each
  `G`-cell. Then `g = G + kappa` with `kappa = 1[{U(n)} >= 1 - z]`, except where
  `{U(n)} + z` lies within `|nu| << P^(-3/8)` of an integer. Since
  `U(n) + z = U(n+2d) - nu - G`, that forces `||U(n+2d)|| << P^(-3/8)`. The
  discrepancy bound (4.17), on the shifted odd block, then gives `O(P^(5/8) + P^(7/8))`
  such points.
- *Cell count.* `S` is about `(9/4) d x^(1/8)` with `S'` about `d P^(-7/8)`, so
  there are `O(d P^(1/8))` `G`-cells.
- *Interpolation.* On a cell, the exact interpolation (4.8) gives
  `(1 - z) e(F_{G,0}) + z e(F_{G,1})` plus sawtooth terms
  `b(U(n)) - b(U(n) + z)`, with
  `F_{G,epsilon} = (k/2) Delta_d(x^(27/16)) - B (S - G - epsilon) + (i/2) Delta_d X
  + (l/2) S + [j-part]`.
- *Sawtooth terms.* Lemma 4.3 at cutoff `R_U` expands them into modes
  `e(s U(n))` and `e(s (U(n) + S))` with weights `1/|s|`. The truncation error is
  `P log R_U / R_U + P^(7/8)`, by (4.17). For the second argument,
  `E_R(U(n) + z)` is comparable to `E_R(U(n+2d))`, because `R_U |nu| <= P^(-1/4)`;
  points inside the strip are already counted as mismatches. The `theta`-noise in
  `s U` costs `|s| P^(-3/8)` per point, which is `P^(3/4) log` in total at `R_U <= P^(1/8)`.

*Zero-mode curvature at `j = 0`.* The leading terms of `(k/2) Delta_d x^(27/16)` and
`B S` are both `(27/16) k d x^(11/16)`, and they cancel exactly. With
`G + epsilon` frozen, what remains is
`F'' = -(1701/4096) k d x^(-21/16) (1 + O(P^(-1/8)))`. A 60-digit numerical
differentiation at `x = 10^14`, `d = 1000` gives `-0.41528320312`, against
`-1701/4096 = -0.41528320313`. The errors, relative to `k d P^(-21/16)`, are:

- the frozen `z` term, `B'' = O(k P^(-23/16))`, relative `P^(-1/8)/d`;
- the `i` term, relative `P^(-3/16)`;
- the `l` term, relative `P^(-9/16)`.

A carry mode `s` adds curvature `s P^(-7/8)`, which dominates by at least
`P^(9/32)`.

*Case `j = 0`, `k != 0`.* Take `R_U = P^(1/8)`. The zero modes give
`P (k d P^(-21/16))^(1/2) + d P^(1/8) (k d P^(-21/16))^(-1/2)
<< P^(11/32) d^(1/2) + P^(25/32) d^(1/2) <= P^(55/64)`. The nonzero modes give
`R_U^(1/2) P^(9/16) + d P^(1/8) P^(7/16) <= P^(23/32)`. The errors are:

- `P^(7/8) log P` from truncation;
- `P^(7/8)` from the carry mismatches;
- `P^(3/4) log P` from the `theta`-noise;
- `l P^(5/8)` from the `l`-noise;
- `k P^(7/16)` from the Taylor step (4.18).

*Case `j != 0`.* The `Y`-wave is Paper B's Lemma 4.4 at `h = d`, which E1
(Result 7) extends to `|u| d <= c_0 P^(1/4)`. Take the product of the two exact
interpolations, for the `X`-gap and the `U`-gap, on their common cells:
`O(d P^(1/2))` cells, plus `O(d P^(1/8))`. The weights are products of monotone
`z`'s. Relative to E1's main curvature `u d P^(-3/4)`:

- the `U`-part zero-mode curvature `k d P^(-21/16)` is `O(P^(-9/16))`;
- a `U`-mode `s <= R_U = P^(1/16)` adds `s P^(-7/8)`, relative at most
  `P^(-1/16)`;
- an `X`-mode `rho` adds `rho P^(-1/2)`, which dominates everything, as in E1.

This is not E1's statement applied as a black box. It reruns E1's proof, and the
steps are as follows:

- The two carries enter the phase additively, so the product of their exact
  interpolations is exact.
- Products of monotone weights have bounded variation on the common cells.
- The zero mode keeps E1's curvature, up to the relative perturbations above.
- The cell count grows by `O(d P^(1/8))`, which is below E1's `d P^(1/2)`.

E1's bound, `P^(7/8) d^(1/2) + d P^(3/4) + P^(5/6)`, therefore holds with doubled
log masses. The `U`-truncation at `P^(1/16)` costs `P^(15/16) log P`.

*Case `k = 0`.*

- If `j != 0`: E1 applies. The `l` term is smooth plus noise costing `P^(5/8)`,
  with curvature `l d P^(-15/8)`, negligible.
- If `j = 0`: the phase is `(i/2) Delta_d X + (l/2) S` plus noise costing
  `P^(5/8)`. Its derivative is monotone, of size about `d P^(-1/2)` if `i != 0`
  and `d P^(-7/8)` if `i = 0`, and below `1/4` on the odd lattice. Kusmin-Landau
  gives `P^(1/2)/d` or `P^(7/8)/d`. `QED`

**20. Lemma E8: the `OOEOE` count-poor tail (written proof, 24 September 2026;
AI-assisted, audited in Result 21).**

*Setting.* The word `OOEOE` means that `n` and `J(n)` are odd, `J^2(n)` is even,
`J^3(n)` is odd and `J^4(n)` is even. Then `J(n) = floor(X)`, `J^2(n) = floor(Y)`,
`J^3(n) = floor(floor(Y)^(1/2)) = floor(U)` (because `J^2 n` is even), and
`J^4(n) = floor(W)` (because `J^3 n` is odd). The target is
`G(n) = floor(floor(W)^(1/2))`, which is nondecreasing on all `n`. The word is the
product of four half-arc indicators of `{X/2}`, `{Y/2}`, `{U/2}` and `{W/2}`:
Paper B's Section 4.3 coordinates.

*Fibre geometry.* `U = n^(9/8) - O(P^(-3/8))`, and
`W = n^(27/16) - O(P^(9/16))`: the loss of `floor(U)`, times `W'` in `U`. Since
`W' ~ n^(11/16)`, each fibre endpoint moves by `O(P^(-1/8))`. So
`H_t = (16/27) t^(5/27)(1 + o(1))` and `max I_t <= (t+1)^(32/27)(1 + o(1))`, as
for `OOOEE`. The multiplier is `27/32`, the ideal fraction is `1/16` and the ideal
coefficient is `1/27`.

*Statement and proof.* For each `eta > 0`,
`sum_{t > U_0, t in Poor_eta} 1/t << U_0^(-1/19)`. The proof is E6's word for word,
with E7 in place of Results 7-15. Every bounded nonzero `nu` has
`|T_d^nu| << P^(61/64) log^2 P`, so:

- `#bad << P^(11/16) + P^(61/64 - 5/32 + eps) = P^(51/64 + eps)`;
- against `P^(54/64)` targets per block, the poor mass per block is
  `P^(-3/64 + eps)`;
- the dyadic sum gives `U_0^(-(32/27)(3/64) + eps) = U_0^(-1/18 + eps)`.

`QED`

*Consequence (conditional).* Take `eta = 1/500`. For both depth-five words, the
fibres that are not poor then carry at least
`(1 - 16 eta)(1 - o(1))/(27 t) >= 1/(28 t)`, since `0.968 * 28/27 = 1.00385 > 1`. The
`OOEOE` sources are disjoint from the `E`, `OE`, `OOEE` and `OOOEE` sources, by
their parity prefixes. With `E` at 1, `OE` at `33/100`, `OOEE` at `11/100`, and
both depth-five words at `1/28`, Arb certifies the contagion root
`[0.740571591021 +/- 8e-13]`. That exceeds the branch's promotion threshold
`0.74`, with a margin of `5.7e-4`, conditional on E1-E8 and a five-production
assembly.

**21. Audit of Lemmas E7 and E8 (24 September 2026).** An independent adversarial
reviewer re-derived both lemmas from Paper B's text. **E7 and E8 hold**, and no
step fails. It confirmed:

- the (4.18) expansions, including that the `{Y}` loss inside `U` is charged;
- the exact `theta`-cancellation at each endpoint;
- the exact `U`-carry identity;
- the constant `-1701/4096`. With mpmath it computed `-0.41528319` to
  `-0.4152832031250` at `x` from `10^8` to `10^20` and `d` from `1` to
  `P^(5/32)`, so the curvature is one-signed throughout;
- every exponent;
- the E8 parity encoding and fibre geometry;
- the root `0.7405715910211`, with the sum at `0.74` equal to `1.000311`.

It also agreed with E7's diagnosis: Paper B's windows give no saving for the
differenced sum. That holds even for the diagonal pairs, whose `lambda^(-1/2)`
exceeds the window length.

It found five wording faults, now fixed:

- the `W` display lacked the factor `k/2`;
- two appeals to (4.17) needed the reduction `U(n) + z = U(n+2d) - nu - G`;
- the `j != 0` case reran E1's proof but presented it as E1's statement; the
  rerun is now written out;
- "`0.968 * 28/27 > 1.0039`" was false. The product is `1.00385`, still above `1`;
- the Open questions stated the `0.74` root without "if".

## Open questions

Lemmas E1-E8 and Theorem E3 (Results 7-20) write out both depth-five productions:

- `OOOEE`, through E1-E6;
- `OOEOE`, through E7 and E8.

If both productions hold at coefficient `1/28`, the contagion root would be
`0.74057 > 0.74`. Arb certifies the root of that equation, not the productions.
E1 and E3-E8 have each had one AI audit; E2 was audited with its nonzero-`t`
clause withdrawn. None has had human review. The four-production assembly for `OOOEE` alone is
kernel-checked (Result 18). Still open:

- a five-production assembly at `37/50`;
- human review of E1-E8;
- a Lean proof of either production.

## Decision

**PARK, pending audit.** Phase-0's stop criterion fired on the estimates then
available. Results 7-16 have since written out, for `OOOEE`, the averaged
substitute that Phase-0 said was missing: Paper B's Appendices A-C at first shifts
up to `P^(5/32)`, the `k = 0` cases, and the count-poor tail. Together they would
give an `OOOEE` production at coefficient `1/30`. With the certified depth-four
productions, the Arb-certified contagion root would be `0.6793 > 2/3`. The branch
is not promoted, for three reasons:

- the proofs are AI-written and not human-reviewed;
- the four-production assembly is kernel-checked (Result 18), but only with the
  `OOOEE` production as a hypothesis; the production itself is not in Lean;
- the promotion criterion `lambda > 0.74` needs `OOEOE`, which has not been
  bookkept.

Best next question: does a five-production Lean assembly at
`lambda = 37/50`, conditional on both depth-five productions at `1/28`, certify
contagion `0.74` and thresholds `13/50`?

## Publication assessment

Status: `EXPLORATORY`.
