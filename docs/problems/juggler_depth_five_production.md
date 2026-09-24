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
(written proof, 24 September 2026; AI-assisted, not independently reviewed).**

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

Paper B's C.2 treats the undifferenced sums. `T_d` is already differenced once, so
no A-process is applied here.

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
  `|r| P^(-1/2)`. Both ratios hold for every `d`.
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

- *`Delta != 0`.* The curvature is `Delta X''`, of size about `|Delta| P^(-1/2)`,
  up to `O(d P^(-21/16))`, a factor `P^(-21/32)` smaller. Weighted by
  `|a_r a_{r'}| << 1/((1+|r|)(1+|r'|))`, the second-derivative test gives
  `(T^(1/2) P^(3/4) + P^(3/16) P^(1/4)) log^2 P << P^(13/16) log^2 P`.
- *`Delta = 0`.* Then
  `F'' = Delta_d[(l/2)(x^(27/16))''] + c Delta_d X''`, with `c = c_1 = c_2`.
  Freeze `N_1` and write `N_1 = B(x) + O(1)`. The leading part is
  `(243/4096) l d x^(-21/16)`, from
  `2d [(1/2)(27/16)(11/16)(-5/16) + (9/16)(3/8)] = (243/4096) d`. (A
  high-precision finite difference agrees to nine digits.) Relative to it, the
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
`|T_d| << P^(127/128+eps)` for `1 <= d <= P^(5/32)`. The `k != 0` vectors give
`P^(127/128)` and the `k = 0` vectors at most `P^(61/64)`. The only unwritten step
of the `OOOEE` route is now the poor-tail reduction from sliding windows to the
actual fibres, including the square-wave truncation. That is where the frequencies
stop being bounded, and it decides whether this saving is enough.

## Open questions

Lemmas E1, E2, E4 and E5 and Theorem E3 (Results 7, 8, 10, 12 and 14) bound
`T_d` for every bounded nonzero frequency vector at `1 <= d <= P^(5/32)`:
`|T_d| << P^(127/128+eps)`. The `k != 0` vectors come from all rows of Paper B's
Appendix C at bounded `k` and `Pi <= P^(19/96)`, and the `k = 0` vectors are E5.
E1, E3 and E4 have been audited; E2 has been audited with its nonzero-`t` clause
withdrawn; E5 is unreviewed. Still unwritten: the poor-tail reduction from sliding
windows to the actual fibres, including the square-wave truncation and the passage
from bounded to growing frequencies. `OOEOE` needs its own bookkeeping.

## Decision

**PARK, pending audit.** Phase-0's stop criterion fired on present
estimates: the production reduces to depth-five parity control on windows of
length `P^(5/32)`. The later bookkeeping (Result 5) indicates that Paper B's
Appendix B and C machinery, run with outer shifts `P^delta`, keeps a power saving
for `OOOEE` up to `delta < 1/6`, or `delta < 3/16` at bounded frequencies, after
three local repairs. That would be the averaged substitute, but it is a first-pass
reading of a dense proof and does not meet the promotion criterion. The pricing
stands: `OOOEE` alone would lift the ideal contagion from `0.633` to `0.6915`, both
depth-five words to `0.7512`. Best next question: does the poor-tail reduction, from
sliding windows of length `P^(5/32)` to the actual fibres with the square-wave
truncation, close with the saving `|T_d| << P^(127/128)` at bounded frequencies?

## Publication assessment

Status: `EXPLORATORY`.
