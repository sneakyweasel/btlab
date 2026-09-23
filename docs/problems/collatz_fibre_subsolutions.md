# Capped periodic weights and the remaining fixed-root estimate

23 September 2026. **EXACT — HUMAN PROOF** for the order reduction and
conditional implications, with Lean declarations. Advisory statement
coverage and independent review remain pending. The finite brackets are
**COMPUTATIONALLY VERIFIED** by exact Python arithmetic, not kernel-checked data.

## Problem

Can bounded periodic weights retain mass at a fixed ordinary root while
their inverse reproduction rates approach one? The
[block-minimum construction](collatz_fibre_block_weights.md) fails because
normalizing its growing residue peaks suppresses the fixed-root value.

## Exact statement

Fix either sign s, a ternary level r>=1, and a rate q>=0. Write u_r for the
unit indicator modulo 3^r. Call h feasible if

\[
 0\le h\le u_r,\qquad qh(b\bmod3^r)\le (L_s h)(b)
 \quad(b\bmod3^{r+1}),                                      \tag{1}
\]

where L_s is the complete positive-exponent inverse coefficient operator.
There is a greatest feasible table H_(r,q), dominating every feasible h at
every coordinate simultaneously. It can be zero. At a fixed q>=0,

\[
 H_{r,q}(a\bmod3^r)\le H_{r+1,q}(a\bmod3^{r+1}).              \tag{2}
\]

For a fixed level, increasing q can only decrease H. In particular, (2)
says nothing about increasing the level and the rate together.

For every positive ordinary root a and depth d,

\[
 C_d^s(a)\ge q^d H_{r,q}(a\bmod3^r).                         \tag{3}
\]

The remaining arithmetic target is a sequence r_i, rates 0<=q_i<1 tending
to one, and a constant c_a>0 such that

\[
 H_{r_i,q_i}(a\bmod3^{r_i})\ge c_a(1-q_i)\quad\hbox{for all }i. \tag{4}
\]

The existing minorant theorem, specialized in Lean here, makes (4) sufficient
for divergence of sum_d C_d^s(a). Neither such a family nor (4) is proved.
For a nonperiodic positive odd root the earlier signed comparison theorems
then give divergent reciprocal mass of distinct odd ancestors. This is not
a termination theorem and supplies no Juggler stopped-pressure estimate.

## Current literature

The signed inverse recurrence and the Syracuse cell problem are **KNOWN**;
see `tao-2019-almost-all-collatz` and Tao's
[inverse-density note](https://terrytao.wordpress.com/2020/01/25/equidistribution-of-syracuse-random-variables-and-density-of-collatz-preimages/).
Greatest subsolutions of positive operators and monotone iterations are
standard order arguments. No priority is claimed for those methods.
Their role here is to specify the strongest bounded periodic certificate
for the laboratory's actual operator and rigorously measure finite root
values. A finite optimum does not settle the asymptotic arithmetic question.

## Branch budget

- **Target:** can capped inverse updates preserve stronger weights at a fixed root?
- **Novelty hypothesis:** capping during construction avoids the block normalization loss.
- **Falsifier:** even the greatest bounded subsolution loses the required root prefactor.
- **Already killed by?:** block-minimum normalization is closed; capped subsolutions are a different family.
- **Existing machinery:** exact transfer rows, existing subcritical certificates and the Lean minorant criterion.
- **Maximum Phase-0 scope:** levels 1–4, four fixed rational rates, exact bounds and Lean monotonicity proofs; at most 2,000 updates per case.
- **Promotion criterion:** an all-level estimate preserving the root prefactor as the rates tend to one.
- **Stop criterion:** park after a canonical reduction and finite bounds if that estimate remains open.

## Balanced-ternary formulation

The tables are indexed by residues modulo 3^r. Balanced digits give another
notation for the same refinement. An ordinary integer a is fixed throughout
(2)–(4); it is not replaced by a maximizing residue that changes with r.

## Why BT may be relevant

The three lifts of each residue expose which refined constraint limits a
weight. The digit representation alone provides no bound on (4).

## Candidate operations / invariants

For q>0 define the capped update

\[
 T_{r,q}(h)(a)=\min\left(u_r(a),\frac1q
       \min_{b\bmod3^{r+1}:\ b\equiv a\ (3^r)}(L_s h)(b)\right).
\]

The map is monotone. A feasible h satisfies h<=T(h). If h<=g<=T(h), then
qg<=Lh<=Lg at every refined target, so g remains feasible. This sandwich
implication is in Lean. It justifies rounding an increasing update down
on an integer grid; rounding cannot fall below an old value on that grid.

For universal upper bounds, start U_0=u_r and round each capped update
up on the same grid. Every feasible h is below U_0. If h<=U_j then
h<=T(h)<=T(U_j)<=U_(j+1), proving h<=U_(j+1). The rounded upper sequence
decreases: it starts below the grid-valued cap, and the update is monotone.
Thus an upper replay from the cap bounds H, even without reaching a fixed
point. An arbitrary fixed point alone would not justify that bound.

This finite iteration argument is written here and independently replayed
in Python. Its numerical records and rounding algorithm are not represented
as kernel-checked computation in Lean.

## Experiments

Run `python tools/lab.py run research.collatz.fibre_subsolutions`.
The [probe](../../src/research/collatz/fibre_subsolutions.py) uses both signs,
levels r=1..4, and respective rates 1/4, 1/2, 2/3, 3/4. Scale is 10^12;
initial lower weights are the previously saved exact certificates, evaluated
at these lower rates. Upper weights start at the unit cap. Stop when the
largest integer gap is <=1,000, or after 2,000 updates. Every case reaches
that tolerance in at most 109 updates, giving coordinate widths <=10^(-9).

All positive exponents are folded exactly into the period P=2*3^r with
denominator 2^P-1. No exponent cutoff or floating optimization is used.
The [saved data](../../data/research/collatz/fibre_subsolutions.json) contain
both vectors, their seed, the iteration count, rate, scale, exact lower
slack and rational root ratios. Decimal values below summarize certified
intervals; they are not asserted to be exact rational optima.

| r | q | Initial h(7)/(1-q), plus | Best H(7)/(1-q), plus | Initial h(47)/(1-q), minus | Best H(47)/(1-q), minus |
|---|---|---:|---:|---:|---:|
| 1 | 1/4 | 0.666667 | 1.066667 | 0.666667 | 1.066667 |
| 2 | 1/2 | 0.250000 | 0.313459 | 0.250000 | 0.313459 |
| 3 | 2/3 | 0.210724 | 0.400463 | 0.210724 | 0.400463 |
| 4 | 3/4 | 0.280836 | 0.465726 | 0.145636 | 0.255636 |

Each improvement compares weights at the same rate, not at the seed's
original, larger certified rate. Ratios across different rows do not
establish an asymptotic trend.

The [ten controls](../../tests/research/collatz/test_fibre_subsolutions.py)
independently form rows using ordinary positive odd predecessors and replay
both integer sequences from their stated starts. They check monotonicity,
final feasibility, every coordinate bracket and the saved root ratios.
At level one and q=1/4, the exact capped fixed point has nonzero entries
4/5 and 1, with their order reversed between signs; both records bracket it.

## Conjectures

No new registered conjecture. The family in (4) remains an explicit open
target, without claiming that the four finite examples establish it.

## Counterexamples

The zero table is always feasible and is a capped fixed point. Finding a
fixed point does not make it greatest or give a universal upper bound.
The upper certificate here depends on replay from the unit cap. Also,
monotonicity in level at a fixed rate cannot offset an unspecified increase
in the rate; the two monotonicities have opposite directions.

## Formalization

[FibreSubsolutions.lean](../../formal/Problems/Collatz/FibreSubsolutions.lean)
defines the feasible set and its coordinatewise supremum. Positivity of
the complete transfer makes that supremum feasible. The module proves its
greatest-element property, bounds, rate monotonicity, lifting under ternary
refinement, (2), (3), the safe increasing-update rule, and the conditional
divergence consequence of (4).

The cross-level comparison formerly private in FibreStopping is moved to
the reusable public theorem `FibreActual.transfer_le_of_residue_le`.
FibreStopping uses that theorem unchanged. Actual integer representatives
and the full summable exponent rows justify lifting a periodic weight.

The [executable audit](../../formal/AxiomCheckCollatzSubsolutions.lean)
covers the nine new public theorems and the reused comparison, with
[expected dependencies](../../formal/AxiomCheckCollatzSubsolutions.expected).
The finite brackets retain their separate computational evidence label.

The full active build passes 9,029 jobs. The ten audited theorems use only
propext, Classical.choice and Quot.sound; the style gate reports no new
violations. All ten independent finite-bracket controls pass.

## Results

Every bounded periodic candidate is dominated by one canonical table at
the same level and rate. Hence no search over differently normalized tables
can outperform H there. The finite brackets show strict root improvements
over the earlier certificates at the stated rates, without paying for a
moving global peak through division by its height.

The open issue has become the dependence of H_(r,q)(a) on both r and q
near one. The proof of existence and the finite computation do not provide
that dependence. The recent fixed-root O_a(d+1) upper bound constrains
coefficients but supplies no lower estimate for H.

## Open questions

Can one prove (4) for the canonical greatest tables at a prescribed ordinary
nonperiodic positive odd unit root, for each sign? This asks for an arithmetic
estimate uniform along an explicit sequence of levels and near-critical
rates, not a larger finite table or another order-theoretic reformulation.

The tested rates for r=2,3,4 are exactly q_r=1-1/r. Thus a concrete first
candidate is H_(r,1-1/r)(a)>=c_a/r for all sufficiently large r. Neither
feasibility at those rates for arbitrarily large r nor this lower bound is
known. Failure of this specific scale would not refute the general family
question (4).

The subsequent [rate-barrier audit](collatz_fibre_rate_barrier.md) shows
that even strict positivity of such tables at rates tending to one already
forces the uniform subexponential minimum-cell bound. The proposed scale
is therefore downgraded as an easier local attack: it requires that global
arithmetic input as well as the fixed-root prefactor. The finite brackets
and conditional statements remain valid.

## Decision

**PARK** further finite computation after the stated four-level test.
The next best question is (4): control the fixed-root value as rates approach
one. Capping survives this bounded test, but the required all-level bound
remains open. No signed coefficient divergence, Juggler pressure estimate,
termination or infinite escape is proved.

## Publication assessment

Status: `STRUCTURAL`. Standard order arguments instantiated for the exact
signed operator, with reproducible finite brackets and an unresolved
arithmetic target. No paper or publication claim is changed.
