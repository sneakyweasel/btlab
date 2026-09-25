# Actual OOEE fibres and sparse slow-parity resonances

Status: **PROMOTE**, 22 September 2026. The follow-up now supplies an
AI-assisted written poor-fibre tail and the averaged OOEE coefficient
arbitrarily close to 1/9. The subsequent
[E/OE/OOEE assembly](../theory/juggler_ooee_contagion_note.md) gives written
contagion at 5/8 and a sufficient Tao-rate threshold e>3/8. Both are now
kernel-checked through `FateOOEEWeighted.lean`: the actual OOEE production
is proved with coefficient 11/100, a uniform bounded loss and its physical
source cutoff. The rate hypothesis and independent mathematical review
remain open; the published manuscripts and termination status are unchanged.
Classical finite differencing and both derivative tests are now proved
in Lean. The quantitative second-derivative estimate has explicit
constants and covers the actual odd lattice. The actual carry-cell curvature
and unweighted O(P^(3/8)) cell sums are now proved uniformly for
1<=h<=P^(1/16). The actual carry partition and weighted smooth contribution
are now formal too, including endpoint losses. The fractional-part carry
term is now O(P^(5/16)*log(P)) in Lean, and the complete retained carry
correlation is O(P^(3/8)). The original linearization comparison and
mixed-mode differencing are now proved too, giving O(P^(13/32)) for
every fixed mixed mode and uniformly over fixed finite frequency sets.
The actual last-root comparison, pure slow modes outside explicit resonance
windows, and the joint three-guard count are now kernel-checked too.
[Joint-parity proof map](../theory/juggler_ooee_joint_parity_note.md).
Exact fibre geometry and its normalized count estimate are now kernel-checked
in `OOEEFibreGeometry.lean` and `OOEEFibreParity.lean`.
[Fibre proof map](../theory/juggler_ooee_fibre_parity_note.md).
Fixed count deviations now force slow resonances in Lean, and their
reciprocal tail is O_eta(U^(-7/9)), including the infinite-series bound.
[Count-poor tail proof map](../theory/juggler_ooee_count_poor_tail_note.md).
[Weighted production and cutoff](../theory/juggler_ooee_weighted_production_note.md)
are now proved for the coefficient 11/100 needed by the contagion theorem.
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

The sixth phase, following the completed first-derivative formalization,
proves the quantitative second-derivative test. A lost endpoint, hidden
cancellation premise, or parameter-dependent constant would falsify it.
The existing Kusmin--Landau bound and mean-value theorem suffice; no
closed global-count localization is reopened. Scope is the finite bound,
its continuous-derivative interface, and either sign on the odd lattice.
Promotion requires compilation without an assumed analytic estimate.
The phase stops before the actual carry-cell and discrepancy applications.

The seventh phase proves those actual carry-cell derivatives and their
uniform curvature. A surviving first-order shift remainder or failure of
main-term dominance would falsify it. Existing real-power calculus and
the second-derivative theorem suffice; the closed longer-fibre localization
is not involved. Scope is the actual phase, explicit size and floor
conditions, and the resulting unweighted cell sum. Promotion requires
deriving the analytic hypotheses rather than assuming them. The compiled
bound retains the endpoint term and works for all 1<=h<=P^(1/16).
Carry Fourier errors and complete discrepancy assembly are outside this phase.

The eighth phase proves the actual weighted smooth carry contribution.
An uncontrolled cell count, weight variation, or endpoint loss would
falsify it. The proved gap monotonicity, partial summation, and curvature
bound suffice. Scope is sampled-cell partition, weighted sums, and finite
assembly, stopping before Fourier remainders and full discrepancy.
Promotion requires a compiled bound without a cell-count or cancellation
premise; this is met with at most 3L+2 levels and O(P^(3/8)) total norm.

The ninth phase closes the retained carry correlation. Boundary losses
or Fourier perturbations consuming the exponent margin would falsify it.
Finite Fejer smoothing at cutoff P^(1/4) replaces the ordinary truncated
sawtooth series, retaining all actual boundary hits and complex weights.
Its scope is the perturbed modes, centered smoothing, actual cells and
retained correlation; it stops before original linearization and full
fibre production. Promotion requires no assumed carry cancellation or
smoothing estimate. The three compiled modules meet that criterion.

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

[SecondDerivative.lean](../../formal/BTCalculus/SecondDerivative.lean) now
proves the quantitative test from integer-band partitioning and the proved
first-derivative estimate. The continuous version derives the actual
increment bounds by two mean-value comparisons. It covers both fixed
curvature signs and the lattice of spacing two, with explicit constants.
[Exact hypotheses and proof](../theory/second_derivative_cancellation_note.md).

[OOEECurvature.lean](../../formal/Problems/Juggler/OOEECurvature.lean)
now derives the actual carry-cell curvature and its unweighted sum bound.
The first two shift terms in the anchor curvature vanish; the remaining
error is dominated uniformly by the frozen carry term. All 26 theorems
are selected by the module audit. [Exact bounds and support conditions](../theory/juggler_ooee_curvature_note.md).

[OOEECarryCells.lean](../../formal/Problems/Juggler/OOEECarryCells.lean)
and [PartialSummation.lean](../../formal/BTCalculus/PartialSummation.lean)
now prove the actual sampled-cell partition, endpoint loss, and weighted
smooth carry bound. All 13 theorems are selected by the dependency audit.
The exact carry decomposition identifies the remaining sawtooth term.
[Exact hypotheses and proof](../theory/juggler_ooee_carry_cells_note.md).

[FejerWeighted.lean](../../formal/BTCalculus/FejerWeighted.lean),
[OOEEFourierModes.lean](../../formal/Problems/Juggler/OOEEFourierModes.lean)
and [OOEECarryFourier.lean](../../formal/Problems/Juggler/OOEECarryFourier.lean)
now close the retained carry correlation. The exact finite statement and
the alternative centered-smoothing proof are in the
[carry Fourier note](../theory/juggler_ooee_carry_fourier_note.md).
The dependency audit selects every one of their 29 theorems.

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
O(P^(3/8)) and its phase-specific analytic estimates.

**Sixth phase: quantitative second derivatives are kernel-checked.**
If lambda<=f''<=C*lambda throughout the closed support interval, or
-C*lambda<=f''<=-lambda throughout it, the unit-lattice sum is at most
4*C*N*sqrt(lambda)+8/sqrt(lambda). The spacing-two constants are 8 and 4.
No correlation or cancellation estimate is assumed. Both derivative
tests are now available; the actual OOEE curvature and carry-discrepancy
applications remain to be formalized.

**Seventh phase: actual cell curvature and sums are kernel-checked.**
For fixed u>0,v,w, sufficiently large P, and every 1<=h<=P^(1/16),
the actual phase on a closed carry cell in [P,2P] satisfies
-2*u*h*P^(-3/4)<=F''<=-u*h*P^(-3/4)/16. If the N odd-lattice terms
have N<=L*P^(7/16), their unweighted sum is at most
(64*L*sqrt(u)+16/sqrt(u))*P^(3/8). The explicit sufficient size
conditions, both real-power derivatives, floor inequalities, and eventual
validity for fixed coefficients are proved. The closed support includes
the final increment; half-open cell splitting and its endpoint losses
remain to be assembled with the carry Fourier argument.

**Eighth phase: the weighted smooth contribution is kernel-checked.**
Under the same size conditions and N<=L*P^(7/16), the whole smooth sum
is bounded by 4*(3L+2)*(64L*sqrt(u)+16/sqrt(u)+1)*P^(3/8).
The number of carry levels is at most 3L+2; each actual occupied fibre
is consecutive, and removing one last sample supplies closed support.
Both weights have variation at most one. The exact carry identity keeps
the fractional-part difference explicit, so the full correlation bound
is not inferred from its smooth part.

**Ninth phase: the complete retained carry correlation is kernel-checked.**
For H=floor(P^(1/4)), the actual unweighted and phase-weighted nonzero
Fourier sums are O(P^(5/16)). Weighted centered Fejer smoothing gives
the carry contribution O(P^(5/16)*log(P)), including integer samples.
Exact carry-cell partition and logarithm absorption yield O(P^(3/8))
for the complete retained phase. Added size conditions hold eventually
for fixed u>0,v,w, uniformly in h<=P^(1/16). The following phase now
bounds the original nested-floor linearization loss and applies differencing.

**Tenth phase: the original mixed modes are kernel-checked.**
The [actual mixed-mode proof](../theory/juggler_ooee_mixed_modes_note.md)
proves 0<=E(x)<=x^(-3/4), bounds the summed original-to-retained error
by 10*pi*abs(u)*L*P^(1/4), and obtains O(P^(13/32)) by finite differencing
with exact overlaps N-d and H=floor(P^(1/16)). Negative coefficients,
empty and short sums, and the smooth j=0,i-nonzero modes are included.
For any fixed finite family with (i,j) not both zero, one constant and
one threshold work for every eligible interval. No cancellation premise
remains in this mixed-mode theorem; pure slow modes remain excluded.

**Twelfth phase: exact fibres and their parity count are kernel-checked.**
Both inverse ceilings are retained. The odd candidate count differs from
(8/9)m^(7/9) by at most 3. For m>=64, all candidates satisfy the actual
source-window hypotheses. The joint-parity theorem therefore gives an
estimate on the exact guarded fibre, with normalized errors m^(-1/18),
m^(-2/3), m^(-7/9) and the two fixed-cutoff losses. The constants and
threshold are uniform in the resonance-width parameter. No assumed
fibre geometry remains. The fixed-deficit inclusion and weighted tail
are outside this phase; its result is recorded in the linked fibre note.

**Thirteenth phase: count-poor inclusion and reciprocal tail are kernel-checked.**
For each eta>0, fixed H,C and a target threshold put every actual count
deviation abs(card(F_m)/H_m-1/8)>=eta in the resonance family
abs(q*(9/8)*m^(2/9)-z)<=C*m^(-7/9), 1<=q<=H. On (u,2u], u>=1,
that family has at most H*(80C+10H)*u^(2/9) members and reciprocal
tail at most 3H*(80C+10H)*U^(-7/9). Thus the count-poor targets have
an eventual reciprocal tail of the required exponent, with both finite
cutoffs and the infinite series verified. The proof includes both signs,
closed resonance windows, fixed cutoff order and all integer endpoints.
The conserved-weight ratio is not yet part of this theorem.

**Fourteenth phase: actual weighted production and 5/8 contagion are kernel-checked.**
Choose count tolerance 1/10000. For m>=10^9 the exact source window and
candidate error give card(F_m)>=(1107/10000)*m^(7/9), hence reciprocal
fibre mass at least 11/(100m), outside the count-poor targets. Their
summable tail makes the discarded target mass uniformly bounded over
every predicate A. The exact source cutoff, disjointness and backward
closure give reciprocal production; the uniform mass-conversion error
gives the conserved-weight inequality with one constant for all A and t.
Thus OOEEProductionBound is discharged. Existing assemblies now prove
unconditional 5/8 contagion and sufficient rates e>3/8 and r-eta>3/8.
The actual rate estimates remain open. The threshold 10^9 is analytic;
the computational verification floor remains unchanged.

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

Independent review remains outstanding. The retained production argument
is complete in Lean at coefficient 11/100: cancellation, joint parity,
exact target fibres, summable exceptional targets, weight conversion,
source cutoff and contagion assembly are all proved. The next mathematical
obstruction is the actual growing-depth stopped-pressure estimate, or a
sufficient failure-rate bound. Neither follows from a fixed four-step
production theorem. No proof of the optional second-moment estimate above
or the full arbitrary-coefficient weighted-ratio asymptotic is claimed here.

## Decision

**PROMOTE.** The actual OOEE production and its physical cutoff are
kernel-checked, yielding unconditional contagion at 5/8 and sufficient
Tao and cumulative-pressure thresholds 3/8. The actual arithmetic rate
remains open. This phase stops after the weighted-production assembly;
it does not open a longer-fibre or new cycle attack.

## Publication assessment

Status: **THEOREM**. Kernel-checked actual production and unconditional
contagion at 5/8. On 25 September 2026 the English statement of
J-ooee-contagion-five-eighths was compared with `FateOOEEWeighted.logMass_growth`
and found covered (closure under one-step preimages of the Juggler map, a
positive member, K > 0 and a threshold N, the reciprocal-sum log-mass), so the
row is EXACT — LEAN VERIFIED. Paper C 1.3.0 states the result as kernel-checked.
Independent review is outstanding. No computational verification floor or
unconditional termination claim changes.
