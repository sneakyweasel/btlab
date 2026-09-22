# Actual OOEE fibres and sparse slow-parity resonances

Status: **PARK**, 22 September 2026. Exact finite census and elementary
written bounds; no new contagion coefficient or termination theorem.

## Problem

Can the successful OE poor-fibre argument be extended to a production
containing two consecutive odd steps? The existing OE coefficient already
reaches its ideal value asymptotically. Substituting the conserved logarithmic
weight alone cannot improve it.

## Exact statement

Let O(n)=floor(n^(3/2)), Q(n)=floor(sqrt(n)), and
w(n)=log((e(n)+1)/(e(n)-1)), where e(n)=n+(n mod 2). Define

\[
 F_m=\{n\ge1:n,O(n)\text{ odd},\ O^2(n),Q(O^2(n))\text{ even},
             \ Q^2(O^2(n))=m\},\qquad
 R_m=\frac{\sum_{n\in F_m}w(n)}{w(m)}.
\]

The question is whether, for every fixed 0<eta<1/9,

\[
 \sum_{m\ge1:\ R_m<1/9-\eta}\frac1m<\infty.
 \tag{1}
\]

The ideal coefficient 1/9 is **unproved** for these actual fibres. It is
the formal value 2^(-4)/(9/16), not a consequence of the census or of the
global Paper B parity count. All four guards are retained. The unguarded
map is the nested Q^2 O^2, not floor(n^(9/16)).

## Current literature

This is a local continuation of the
[OE poor-fibre theorem](../theory/juggler_oe_poor_fiber_tail_note.md),
already kernel-checked, and the
[exact source-mass law](juggler_code_mass_transport.md).
[Paper B](../theory/juggler_parity_discrepancy_note.md), Theorem 4.5 and
Corollary 4.6, provides a global OOEE count; its error does not control
each source interval of length P^(7/16).
The [production calculus](../theory/juggler_contagion_exponent_calculus.md)
already lists this short-scale production as unavailable. The separate
[closed localization attempt](juggler_kernel_localize.md) concerns longer
OOOEE/OOEOE fibres and supplies no estimate here. No new external literature
claim or priority claim is made.

## Branch budget

- **Target:** Are deficient actual OOEE fibres summable in reciprocal target mass?
- **Novelty hypothesis:** Their deficit may occur only near sparse arithmetic resonances.
- **Falsifier:** Persistent deficient mass, or reliance on the closed localization shortcut.
- **Already killed by?:** Uniform Paper B localization is closed; this asks about exceptional targets and retains the joint guards.
- **Existing machinery:** Exact inverse fibres, conserved weight, and the OE poor-fibre theorem.
- **Maximum Phase-0 scope:** Exact fibre construction and a bounded deficiency/resonance census: all targets 2..4095, 64 fixed midpoints per dyadic block for exponents 12..20, then five targets around each slow-slope integer 4..16 and 27.
- **Promotion criterion:** A proved summable exceptional-set estimate.
- **Stop criterion:** PARK with a precise missing lemma if the census alone supports the idea.

## Balanced-ternary formulation

All source and target integers admit canonical balanced-ternary representations.
No digit constraint is used in the fibre construction or the estimates.

## Why BT may be relevant

The exact signed Collatz code and source-weight transport remain available.
They do not determine physical predecessor production within a code fibre.
This probe retains the actual source heights explicitly.

## Candidate operations / invariants

**EXACT — HUMAN PROOF** (elementary inversion, not Lean checked here).
Put B(a)=ceil(a^(2/3)). Since O(n)>=a iff n^3>=a^2,
the unguarded fibre is exactly

\[
 [A_m,A_{m+1})\cap\mathbb N,\qquad A_m=B(B(m^4)).
 \tag{2}
\]

For every m>=1, the full actual fibre has the uniform mass cap

\[
 0\le\sum_{n\in F_m}w(n)<\frac5m.
 \tag{3}
\]

Indeed m^(16/9)<=A_m<=m^(16/9)+2, by applying the ceiling bound twice
and the subadditivity of x^(2/3). Over consecutive odd n, the product
of (n+2)/n telescopes. Thus the sum over all odd candidates is at most

\[
 \log\frac{A_{m+1}+1}{A_m}
 \le\frac{16}{9}\log(1+1/m)
       +\log\left(1+\frac3{(m+1)^{16/9}}\right)
 \le\frac{43}{9m}<\frac5m.
\]

An empty candidate interval causes no problem. This cap means that an
exceptional set with finite reciprocal mass would contribute finite source
mass, uniformly for any subset of targets. Unlike the previously closed
pressure-scale deletion, the discarded object's weight is appropriate.
The cap does not prove that the exceptional set is small.

## Experiments

Runner: `python -m research.juggler_sequence.ooee_poor_fibres`.
[Source](../../src/research/juggler_sequence/ooee_poor_fibres.py),
[tests](../../tests/research/juggler_sequence/test_ooee_poor_fibres.py), and
[stored output](../../data/research/juggler/ooee_poor_fibres/summary.json).

All inverse endpoints, source membership, guard counts, and threshold
classifications use exact integers or rational numbers. Decimal mass ratios
and reciprocal sums are diagnostics. If c sources remain with first f and
last l, the exact enclosure is

\[
 \frac{c(e(m)-1)}{l+2}\le R_m\le\frac{c(e(m)+1)}f.
 \tag{4}
\]

This follows from x/(1+x)<=log(1+x)<=x. Empty fibres have ratio zero.
Classification thresholds are 1/18, 1/12, and 1/10. Overlapping brackets
are reported as unresolved, never rounded into a decision.

The main schedule contains 4,670 target evaluations: 4,094 exhaustive
targets below 4096 and 576 midpoint samples above it. Midpoint samples are
deterministic and, here, even; they are not a representative random sample
or a density measurement. The separate resonance diagnostic makes 70
evaluations around exact centers floor((8a/9)^(9/2)). It deliberately
searches for outliers and must not be combined into a density estimate.

## Conjectures

No new conjecture is registered. Equation (1) is an open research target.

## Counterexamples

**COMPUTATIONALLY VERIFIED.** Actual fibres can be completely empty well
beyond the exhaustive range. Counts below are over all odd candidates in
the exact interval (2); the middle columns are individual guards, not
assertions of independence.

| Target m | Odd candidates | O(n) odd | O^2(n) even | Q(O^2(n)) even |
|---:|---:|---:|---:|---:|
| 301 | 76 | 32 | 36 | 0 |
| 3737 | 534 | 270 | 259 | 0 |
| 11584 | 1287 | 643 | 648 | 0 |
| 1625364 | 60199 | 30122 | 30270 | 0 |

The last witness has exact source interval
[110075336112,110075456510). It refutes any claimed positive lower bound
at every target beyond 10^6. It does **not** refute an eventual lower
bound with an unspecified threshold, or the summable-exception question.

## Formalization

No new Lean module. The exact even-fibre weight and both signed transports
are already kernel-checked in
[CodeMassTransport.lean](../../formal/Problems/Juggler/CodeMassTransport.lean).
The new integer census is independently checked against forward Juggler
orbits and exact rational products. No analytic bound is inferred from it.

## Results

In the exhaustive dyadic blocks with exponents 8, 9, 10, 11, the mean
ratios are approximately 0.110627, 0.109807, 0.111763, 0.110728.
The corresponding certified counts below 1/18 are 4, 8, 0, 4.
All 320 midpoint samples in blocks with exponents 16..20 have ratio
at least 1/10, certified by (4). Nevertheless the targeted diagnostic
finds zero mass at 1625364 in that same range. This is a direct warning
against interpreting the midpoint sample as a uniform result.

The slow parity has a natural resonance scale. Write P=m^(16/9).
The smooth approximation to Q(O^2(n)) is n^(9/8), and on odd sources
the step of n^(9/8)/2 is approximately

\[
 \alpha_m=\frac98 m^{2/9}.
\]

The source interval has length of order P^(7/16); the cumulative quadratic
variation has order P^(-7/8) times P^(7/8), hence order one. The final
parity can consequently remain locked. The four displayed empty fibres
have alpha_m near integers 4, 7, 9, and 27, respectively. These smooth
quantities explain the diagnostic locations; the reported zero counts
were checked using the nested floors themselves.

**EXACT — HUMAN PROOF** (elementary resonance count only). For fixed
Q>=1 and C>0, define

\[
 \mathcal R_{Q,C}=\{m\ge1:\exists\,1\le q\le Q,
       \ \|q\alpha_m\|\le C m^{-7/9}\}.
\]

This set has O_{Q,C}(M^(2/9)) members in [M,2M), and consequently
reciprocal tail O_{Q,C}(U^(-7/9)). For a fixed q, the derivative of
q alpha_m is (q/4)m^(-7/9). Each resonance arc on [M,2M) therefore
has preimage length at most 8 C 2^(7/9)/q. There are
O(q M^(2/9)+C+1) integer levels; each interval contains at most its
length plus one integers. Sum over the finitely many q and then over
dyadic M. This proves sparsity of the proposed resonance family only.

**Missing implication:** poor actual OOEE fibres have not been shown to
belong to such a family, even after adding another summable exceptional
set. The first two parity guards may correlate with the slow guard.
Separate marginal balances do not establish joint production.

## Open questions

Let H_m be the number of odd candidates in (2), and C_m=|F_m|. A concrete
arithmetic estimate sufficient for this phase's target is, for some delta>0,

\[
 \sum_{M\le m<2M}(C_m-H_m/8)^2
       \ll M^{23/9-\delta}.
 \tag{5}
\]

Here H_m=(8/9)m^(7/9)+O(1), and (4) relates the count to the mass.
For fixed eta, a deficient mass ratio eventually forces a count error
of order eta*m^(7/9). Thus (5) would bound the poor-target count by
O_eta(M^(1-delta)), making (1) summable. No proof of (5), or of its
needed one-sided variant, is supplied. Global Paper B prefix estimates
and the already known two-predecessor Fourier transfer do not supply
this short-fibre second moment merely by reindexing.

## Decision

**PARK.** The bounded phase identifies an exact slow-parity failure mechanism
and a summable candidate resonance family, but does not control all deficient
fibres. The most promising next question within this direction is whether
the actual joint-guard count admits a power-saving second moment such as
(5). That requires an arithmetic proof, not a larger midpoint census or
another formal transport identity. This phase opens no follow-up campaign.

## Publication assessment

Status: **EXPLORATORY**. Diagnostic evidence and elementary supporting bounds.
No paper, verification floor, contagion exponent, or termination claim changes.
