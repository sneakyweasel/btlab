# Actual OOEE fibres and sparse slow-parity resonances

Status: **PROMOTE**, 22 September 2026. The follow-up now supplies an
AI-assisted written poor-fibre tail and the averaged OOEE coefficient
arbitrarily close to 1/9. The subsequent
[E/OE/OOEE assembly](../theory/juggler_ooee_contagion_note.md) gives written
contagion at 5/8 and a sufficient Tao-rate threshold e>3/8. Its strengthened
Lean theorem now retains only the precise OOEE production bound: the OE
input has been discharged in `FateOEWeighted.lean`. Independent review
and analytic Lean verification are outstanding; the published manuscripts
and termination status are unchanged.
The classical finite differencing input is now proved in
`BTCalculus.WeylDifferencing`; the actual correlation estimates remain written.
[Analytic argument](../theory/juggler_ooee_poor_fibre_tail_note.md).

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

The written theorem now proves that, for every fixed 0<eta<1/9,

\[
 \sum_{m\ge U:\ R_m<1/9-\eta}\frac1m\ll_\eta U^{-7/9}\qquad(U\ge1).
 \tag{1}
\]

The limiting averaged coefficient 1/9 equals the formal value 2^(-4)/(9/16),
but its justification is the new analytic proof, not the census or the
global Paper B parity count. For every coefficient below 1/9 there is
a bounded additive production loss, uniformly over arbitrary target sets.
All four guards are retained. The unguarded map is the nested Q^2 O^2,
not floor(n^(9/16)). Uniform positivity at every large target is not asserted.

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

The first phase ended **PARK**. The explicitly resumed follow-up has
the same mathematical target and tests a specific new calculation:
recount the carry cells for shifts at most P^(1/16) on intervals of
length P^(7/16). Its budget is the local mixed-mode proof and poor-target
inclusion, stopping at the first unsupported error estimate. Its promotion
criterion is the complete written bound retaining actual floors and all
guards. It does not include a new census, contagion recursion, or manuscript
revision. That criterion is met in the linked analytic note.

The third phase, explicitly resumed, is limited to assembling the disjoint
E/OE/OOEE sources with exact cutoffs and bounded additive losses. Its target
is contagion at 5/8 and the sufficient Tao threshold 3/8. Overlapping source
sets or cutoff losses erasing the exponent margin would falsify it. This
assembly was not previously killed: the missing actual OOEE production now
has a written proof. Existing conserved weight, backward closure, and the
generic Lean recursion supply the machinery. Promotion requires a compiled
implication whose analytic hypotheses match the written production theorem;
any unmatched premise must remain explicit. This phase includes no further
analytic estimate or manuscript revision.

The fourth phase discharges OE in that assembly. Its target is the actual
conserved-weight inequality with coefficient 33/100 and source cutoff
floor(exp(t)), without any new analytic hypothesis. An unbounded weight
conversion or cutoff error would falsify it. It uses the existing proved
OE poor-fibre tail; no closed localization route is reopened. The budget
is the exact weight comparison, weighted OE production, and connection
to the existing assembly. Promotion requires that unconditional input
to compile; the new OOEE estimate remains outside this phase.

The fifth phase formalizes the classical finite van der Corput inequality
used by the written OOEE estimate. Lost boundary terms or an assumed
correlation bound would falsify this consolidation. Finite sums and
Cauchy--Schwarz suffice, without any closed localization shortcut. The
budget is the complete inequality with exact overlap correlations, stopping
before derivative tests and discrepancy. Promotion requires compilation
without an assumed analytic estimate; this criterion is met.

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

No new conjecture is registered. Equation (1) now has an AI-assisted
written proof, with independent review outstanding.

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

The exact even-fibre weight and both signed transports
are already kernel-checked in
[CodeMassTransport.lean](../../formal/Problems/Juggler/CodeMassTransport.lean).
The integer census is independently checked against forward Juggler
orbits and exact rational products. No analytic bound is inferred from it.
The new analytic note identifies the existing kernel-checked linearization
and carry identities in `PaperBAssembly.lean` and `GapCells.lean`.
The short-interval estimates and poor-tail theorem remain written;
those earlier Lean identities do not cover the new analytic claim.

The third phase adds
[FateOOEEAssembly.lean](../../formal/Problems/Juggler/FateOOEEAssembly.lean).
It checks the actual source partition, even cutoff, reciprocal weight
comparison, removal of bounded losses, positive seed, exact 5/8 certificate,
and Tao implication. Both actual odd-source inequalities remain explicit
in `OddProductionBounds`; this module does not prove that analytic input.
The [assembly note](../theory/juggler_ooee_contagion_note.md) supplies its
written derivation, including the physical source-height cutoffs.

[FateOEWeighted.lean](../../formal/Problems/Juggler/FateOEWeighted.lean)
now proves a uniform mass-conversion error at most 6 and discharges the
actual OE production for every backward-closed class. Its consequence
`logMass_growth_of_ooee` retains only `OOEEProductionBound`. The new
short-interval OOEE estimate itself is still not formalized.

[WeylDifferencing.lean](../../formal/BTCalculus/WeylDifferencing.lean) now
proves the finite van der Corput inequality from zero padding and
Cauchy--Schwarz, with constants 2 and 4 and exact correlation length N-d.
Its odd-lattice specialization retains the actual phase difference.
This is a classical analytic tool, not a bound on these correlations.
[Proof mapping and exact statement](../theory/finite_weyl_differencing_note.md).

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

**Follow-up: the missing implication is now proved in writing.** For each
fixed eta>0, sufficiently large targets with |R_m-1/9|>eta belong to
one such fixed resonance family. The
[analytic note](../theory/juggler_ooee_poor_fibre_tail_note.md) proves the
short-interval bound O(P^(13/32)) for every fixed mixed Fourier mode
with at least one nonzero earlier coordinate. The source length is
P^(7/16)=P^(14/32), giving a genuine saving. The pure slow modes are
handled by their distance from resonance. Applying three-dimensional
box discrepancy to the actual floor phases then proves joint production,
without assuming that the marginal parity conditions are independent.
The resulting poor reciprocal tail is O_eta(U^(-7/9)).

**Third phase: written contagion at 5/8.** The disjoint E, OE, and OOEE
families give coefficients 1, 33/100, and 11/100 at logarithmic scales
1/2, 3/4, and 9/16. A translation by 16 and subtraction of 5C remove
the common cutoff shift and total additive loss 2C. At exponent 5/8 the
weighted power sum is at least 50011/50000>1, by exact rational comparisons
in Lean. Every nonempty backward-closed positive class therefore has
reciprocal mass at least K*(log X)^(5/8) eventually. The complete written
claim inherits the OOEE analytic review boundary; only the implication
from `OddProductionBounds` is kernel-checked. The Tao failure-rate bound
at any e>3/8 would then imply termination, but that rate remains open.

**Fourth phase: the OE hypothesis is removed.** Lean proves that conserved
mass differs from twice reciprocal mass by at most 6 for every predicate
and finite cutoff. The established OE poor-fibre theorem, exact disjoint
source fibres, and n^3<(m+1)^4 then give coefficient 33/100 with a fixed
additive loss. This is unconditional in Lean. The improved contagion
implication now assumes only the actual OOEE production bound.

**Fifth phase: finite differencing is kernel-checked.** For a complex
sequence of length N with modulus at most one and 1<=H<=N, Lean proves
|S|^2 <= 2*N^2/H + (4*N/H)*sum_(1<=d<H)|T_d|, with each T_d taken over
exactly N-d terms. No cancellation hypothesis occurs in this theorem.
The written OOEE application still needs its correlation bound
O(P^(3/8)), as well as its derivative and discrepancy estimates.

## Open questions

The first phase proposed a second-moment route. Let H_m be the number
of odd candidates in (2), and C_m=|F_m|. A sufficient alternative estimate
would be, for some delta>0,

\[
 \sum_{M\le m<2M}(C_m-H_m/8)^2
       \ll M^{23/9-\delta}.
 \tag{5}
\]

Here H_m=(8/9)m^(7/9)+O(1), and (4) relates the count to the mass.
For fixed eta, a deficient mass ratio eventually forces a count error
of order eta*m^(7/9). Thus (5) would bound the poor-target count by
O_eta(M^(1-delta)). No proof of (5) is supplied or needed for the new
result: the resonance inclusion proves (1) directly. Global Paper B
prefix estimates and the already known two-predecessor Fourier transfer
still do not supply a short-fibre second moment merely by reindexing.

Independent review of the new local proof remains outstanding. The next
proof obligation is to discharge `OOEEProductionBound` in Lean for every
backward-closed class. Its main analytic ingredient is the actual OOEE
poor-fibre theorem. The OE production and a uniform weight conversion
are now formal; the OOEE source-cutoff consequence must also be retained.
Finite differencing is now formal too. The next analytic prerequisite is
a first-derivative cancellation estimate with explicit hypotheses; it
supports both the pure slow modes and the second-derivative test.

## Decision

**PROMOTE.** The written poor-fibre theorem now has a complete cutoff
assembly yielding contagion at 5/8 and the sufficient Tao threshold 3/8.
The assembly and its OE input are kernel-checked; the new OOEE analytic
theorem still awaits independent review and Lean proof. Exactly one best
next question: can the first-derivative cancellation estimate needed by
the actual OOEE proof be discharged in Lean?
This phase stops at that boundary.

## Publication assessment

Status: **THEOREM**. Written analytic result and conditional Lean assembly,
with independent analytic review outstanding. The research note improves
the written contagion exponent to 5/8; no paper, verification floor, or
unconditional termination claim changes.
