# The block-minimum construction loses its fixed-root prefactor

23 September 2026. **EXACT — HUMAN PROOF**, with kernel-checked upper bounds
and normalization obstruction. Independent review and advisory statement
coverage remain pending.

## Problem

The [near-critical minorant criterion](collatz_fibre_critical_minorants.md)
needs normalized periodic weights h_i with L_s h_i>=q_i h_i, q_i tending to
one, and h_i(a)>=c_a*(1-q_i) at one fixed ordinary root. Can the standard
geometric block of complete inverse generations supply such weights?

## Exact statement

Fix either sign s, and write K_d=L_s^d u, where u is one on units modulo
three and zero on nonunits. For every nonperiodic positive odd root a there
is an explicit A_s(a)>=1 such that

\[
 0\le K_d(a)\le A_s(a)(d+1),\qquad
 0\le C_d(a)\le\frac{21}{5}A_s(a)(d+1)\quad(d\ge0).        \tag{1}
\]

Here C_d is the complete all-source coefficient. Nonperiodic means
S_s^j(a) differs from a for every j>0; the root may be preperiodic.
The bound is pointwise in a, not uniform over all root heights.

For N>=1 and 0<=q<1, define the finite periodic table

\[
 H_{N,q}(b)=\sum_{k=0}^{N-1}q^{N-1-k}K_k(b),\qquad
 M_{N,q}=\max_{b\bmod3^N}H_{N,q}(b),\qquad h_{N,q}=H_{N,q}/M_{N,q}.
\]

Suppose its rate is certified by the complete block minimum:

\[
 q^N\le K_N(b)\quad\hbox{at every unit residue }b\bmod3^{N+1}.     \tag{2}
\]

Then the checked bounds give

\[
 \frac{h_{N,q}(a)}{1-q}
 \le4A_s(a)N^3(2/3)^{N-1}.                              \tag{3}
\]

Thus for any family of such rates, the left side tends to zero with N.
This remains true if the rates tend to one. These blocks cannot meet the
positive lower bound required by the earlier criterion.

This conclusion is specific to (2). It does not cover arbitrary periodic
weights, arbitrary positive combinations of generations, or certifying a
different reproduction rate for the same table. No lower bound on K_d or
assertion about termination follows from (1).

## Current literature

The signed inverse recurrence is **KNOWN**, with the plus formulation in
`tao-2019-almost-all-collatz`. Tao's
[2020 inverse-density discussion](https://terrytao.wordpress.com/2020/01/25/equidistribution-of-syracuse-random-variables-and-density-of-collatz-preimages/)
connects block minima with asymptotic inverse counts. Harmonic upper bounds
and geometric sums of operator iterates are standard methods.

This phase combines the laboratory's existing exact height-budget and
uniform signed distortion results. No priority is claimed for the general
methods or for the new formal synthesis. The recently located
`nikpour-rabbani-2026-certified-density` preprint remains an unchecked
abstract-level reference; none of its claimed certificates is used here.

## Branch budget

- **Target:** can normalized positive sums of inverse generations meet the fixed-root criterion?
- **Novelty hypothesis:** a block estimate may construct the missing near-critical weights.
- **Falsifier:** normalization makes the fixed-root weight too small relative to 1-q.
- **Already killed by?:** the finite-weight obstruction excludes q=1; it does not settle this varying-level construction.
- **Existing machinery:** complete inverse coefficients, height budgets, uniform path distortion and residue peaks.
- **Maximum Phase-0 scope:** one explicit block construction, its all-depth bounds and Lean checks; no larger census.
- **Promotion criterion:** a construction with controlled fixed-root weight as q approaches one.
- **Stop criterion:** close this construction if its normalization necessarily loses the required bound.

## Balanced-ternary formulation

H_N is a finite table modulo 3^N. The large value at the repeated one-halving
residue persists under any digit notation. Its positive integer representative
can change with N, unlike the fixed integer at which (1) is evaluated.

## Why BT may be relevant

The residue representation exposes the normalization loss. Balanced digits
do not remove the difference between a moving residue peak and a fixed root.

## Candidate operations / invariants

**Written construction identity.** Linearity and the complete recurrence give

\[
 L_s H_{N,q}-qH_{N,q}=K_N-q^N u.                         \tag{4}
\]

All tables are lifted periodically to the common modulus. The finite sum
commutes with the complete nonnegative exponent sum. Thus (2) is a sufficient
certificate for L_s H>=qH; normalization preserves that inequality.
This elementary construction identity is written and checked exactly at the
stated small lengths. The Lean obstruction below concerns the explicit H,
M and (2), and does not silently claim a separate formalization of (4).

For actual paths with total exponent at most B, each source is a positive odd
integer n<=a*2^B. The deterministic forward map and its exact valuations
give at most one inverse word of a specified depth for each endpoint n.
This is the arithmetic input behind (1), rather than a model of independent
parities or an averaged density claim.

## Experiments

Run `python tools/lab.py run research.collatz.fibre_block_weights`. It is
hard-capped at both signs and lengths N=1..4. An exact binary search produces
the largest multiple of 10^(-9) whose Nth power is no larger than the computed
block minimum. Every refined residue checks (4) and its nonnegative remainder.
The saved [records](../../data/research/collatz/fibre_block_weights.json)
retain the minimum, rate, normalizer and root prefactor.

| N | Certified q, either sign | h(7)/(1-q), plus | h(47)/(1-q), minus |
|---|---:|---:|---:|
| 1 | 0.238095238 | 1.312500 | 1.312500 |
| 2 | 0.370302080 | 0.424680 | 0.424680 |
| 3 | 0.458518020 | 0.247321 | 0.247321 |
| 4 | 0.529240909 | 0.172082 | 0.146816 |

These are rates of this particular construction, not optimal periodic-weight
rates. Their finite trend is not used to infer (3).

The [fifteen controls](../../tests/research/collatz/test_fibre_block_weights.py)
also enumerate actual integer words through depths 1..3 with budget B=8d,
check unique endpoints, reconstruct all forward valuations, verify the exact
affine product and compare retained mass with the complete rational table.
The omitted mass stays below (19683/32768)^d. The exact first-digit class mean
is 2/3 in these controls; the all-depth Lean proof only needs the weaker 3/4
upper bound for a table's unit minimum.

## Conjectures

No new conjecture. The existence of some other family satisfying the
near-critical fixed-root criterion remains open.

## Counterexamples

For the minus sign the fixed point a=1 has K_d(1)>=(3/2)^d. Hence (1) cannot
be asserted for all positive odd roots without an exception. Nonperiodicity
is an explicit hypothesis of both formal modules. The plus-map proof uses
only positivity of its affine correction, but the public common interface
retains the nonperiodicity hypothesis for both signs.

## Formalization

[FibreRootBounds.lean](../../formal/Problems/Collatz/FibreRootBounds.lean)
first isolates an endpoint with an indicator weight. An induction proves
that its budget coefficient is no larger than the coefficient of its unique
actual path. Finite linearity decomposes the budget into those endpoints.
`unitBudget_le_harmonic` gives the resulting reciprocal upper bound;
`kernel_le_logarithmic`, `kernel_le_linear` and `coarse_le_linear` prove (1).

[FibreBlockWeights.lean](../../formal/Problems/Collatz/FibreBlockWeights.lean)
defines the actual tables and their finite supremum norm. It proves the
uniform block floor bound, exponential peak lower bound, quadratic root
bound, rate deficit, (3), and `anchor_ratio_tendsto_zero`. The last theorem
quantifies over every rate sequence satisfying (2), with no assumed limit
for those rates. Its conclusion is specific to this construction.

The executable audits are
[root bounds](../../formal/AxiomCheckCollatzRootBounds.lean) and
[block weights](../../formal/AxiomCheckCollatzBlockWeights.lean), with saved
[root dependencies](../../formal/AxiomCheckCollatzRootBounds.expected) and
[block dependencies](../../formal/AxiomCheckCollatzBlockWeights.expected).
The Python records are computational evidence, not kernel-checked data.
Advisory statement coverage remains pending; no external request is sent.

The active build passes all 9,028 jobs. Both executable audits cover twelve
public theorems and report only propext, Classical.choice and Quot.sound.
The style gate reports zero new violations. All fifteen new exact controls
pass; the block construction's finite identity and the all-depth obstruction
retain the separate evidence scopes described above.

## Results

Let D_+=1 and D_-=exp(reciprocalBudget), the previously proved absolute
negative-path distortion constant. Every actual depth-d path ending at a
has homogeneous coefficient at most a*D_s/n at its source n. After the
endpoint decomposition, the finite budget therefore satisfies

\[
 B_{d,B}(a)\le aD_s\sum_{n=1}^{a2^B}\frac1n
 \le aD_s(1+\log a+B\log2).
\]

The existing tail estimate with B=8d gives

\[
 K_d(a)\le aD_s(1+\log a+8d\log2)+(19683/32768)^d.
\]

One explicit choice in (1) is
A_s(a)=aD_s*(1+log a+8log2)+1. The once-only unit comparison gives the
21/5 factor for C_d. No endpoint count is assumed to be asymptotically sharp.

For the block obstruction, positivity and (1) give H_N(a)<=A_s(a)N^2.
At the repeated one-halving residue, its last summand gives
M_N>=(3/2)^(N-1). To bound the rate deficit, take the first-digit class
opposite the parents of the e=1 and e=3 branches. Both of those rows vanish
on that class. Their total mass is (3/2+3/8) times the input table sum.
Adding the hypothesized minimum on the other class and using conservation
of the total sum gives min K_N<=3/4. Thus (2) and
1-q^N<=N*(1-q) imply 1-q>=1/(4N). Combining these three inequalities gives
(3), whose right side tends to zero.

This is an all-depth obstruction, not an extrapolation of the eight records.
The fixed-root linear bound also explains why moving exponential peaks cannot
be used as pointwise lower evidence at a nonperiodic ordinary integer.

## Open questions

Can a periodic subsolution construction anchored at one ordinary integer
avoid the normalization loss of these block-minimum weights while its
certified rates tend to one?

## Decision

**CLOSE** the block-minimum geometric-sum construction as a route to the
required prefactor. Retain the kernel-checked fixed-root upper bounds as
useful constraints on further constructions. The next question is the
root-anchored construction in the preceding paragraph; this phase stops
without trying another family or expanding the residue census.

The subsequent [capped-subsolution phase](collatz_fibre_subsolutions.md)
constructs the greatest feasible bounded table at any fixed level and rate.
Finite exact brackets improve root values at four stated rates; the required
all-level root-to-deficit bound remains open.

## Publication assessment

Status: `STRUCTURAL`. A formal synthesis of actual endpoint bounds and a
specific normalization obstruction. No manuscript, termination claim,
infinite escape claim or Juggler analytic input is changed.
