# Finite height budgets preserve signed inverse coefficient divergence

23 September 2026. **EXACT — HUMAN PROOF**, with kernel-checked declarations;
independent review and advisory statement coverage remain pending.

## Problem

Does the fixed-integer coefficient-series question require uncontrolled
source heights or arbitrarily large halving exponents at a fixed generation?

## Exact statement

For either sign s, let S_s be the positive odd accelerated map and
K_d^s=L_s^d 1_units the complete homogeneous coefficient from the
[fibre dossier](collatz_fibre_mass.md). Fix a positive odd target a. Define
B_(d,b)^s(a) as the coefficient of the actual depth-d unit ancestors whose
total halving exponent is at most b. Each retained path with exponent sum
H contributes 3^d/2^H. The finite operator has the explicit recurrence

\[
 B_{0,b}^s(a)=1_{3\nmid a},\qquad
 B_{d+1,b}^s(a)=\sum_{\substack{1\le k\le b\\2^k a\equiv s\ (3)}}
       \frac3{2^k}B_{d,b-k}^s\left(\frac{2^k a-s}{3}\right).
\]

For every d,b>=0,

\[
 0\le K_d^s(a)-B_{d,b}^s(a)\le6^d(3/4)^b.
\]

Every retained source n is positive, odd, satisfies S_s^d(n)=a, and is
at most a*2^b. Thus, with rho=19683/32768<1,

\[
 0\le K_d^s(a)-B_{d,8d}^s(a)\le\rho^d,
 \qquad n\le a\,256^d.
\]

The two nonnegative depth series are summable simultaneously. Their partial
sums differ by at most 1/(1-rho)=32768/13085, uniformly in the number of
generations, target and sign. Hence complete coefficient-series divergence
can be proved using only these finite, controlled-height inverse families.
Neither series is proved divergent here.

For a nonperiodic target, divergence of the finite-budget series implies
divergence of the ordinary reciprocal series of its actual positive odd
unit ancestors. This last implication uses the already checked
[uniform generation comparison](../theory/collatz_uniform_generation_mass_lean_note.md).
It is conditional for both signs; periodic targets are excluded from this
ancestor-series conclusion because generations would overlap.

## Current literature

The complete recurrence is the density-normalized signed version of
`tao-2019-almost-all-collatz`, Lemma 1.12; see
[Tao, Section 1.4](https://arxiv.org/html/1909.03562#S1.SS4).
The exponential-moment tail argument is standard. The explicit signed
budget, actual source-height support and summability equivalence are the
**PROJECT-SPECIFIC** consequence recorded here. No literature priority is claimed.
Tao's averaged fine-scale mixing is not a pointwise coefficient lower bound
at the specified ordinary integer a.

## Branch budget

- **Target:** bound coefficient mass lost beyond a finite exponent budget.
- **Novelty hypothesis:** a summable tail makes fixed-root divergence accessible
  through controlled-height ancestors.
- **Falsifier:** the estimate omits admissible paths or loses actual integer height.
- **Already killed by?:** bounded stopping forbids uniform reproduction, not
  approximation of a complete generation with a summable error.
- **Existing machinery:** complete signed predecessor bijection and uniform
  coefficient-to-mass comparisons.
- **Maximum Phase-0 scope:** the signed tail theorem and finite-height divergence
  consequence, with small independent integer controls.
- **Promotion criterion:** checked summable error and explicit actual source support.
- **Stop criterion:** stop at the reduction; the arithmetic block lower bound remains open.

## Balanced-ternary formulation

The existing ternary-residue operator defines K_d exactly. The truncation uses
the actual inverse affine equations; changing digit notation does not improve it.

## Why BT may be relevant

Ternary residues enforce integrality. The new height estimate comes from the
geometric halving weights, not from balanced ternary or a mixing hypothesis.

## Candidate operations / invariants

The total exponent H is a genuine cumulative budget, not a separate cutoff
at each generation. An inverse step spends k>=1 and leaves b-k for its subtree.
The tilted one-step coefficient has the exact unrestricted sum

\[
 \sum_{k\ge1}\frac3{2^k}(4/3)^k=6.
\]

Discarding integrality restrictions only enlarges this nonnegative sum.

## Experiments

Run `python tools/lab.py run research.collatz.fibre_height_budget`. It compares
the finite budget with the independently implemented complete residue operator
at depths 0..3, at plus target 7 and minus target 47. This is a small control,
not a root search or evidence for the infinite-depth lower bound.

Seven checks in
[test_fibre_height_budget.py](../../tests/research/collatz/test_fibre_height_budget.py)
include independent forward enumeration from every positive odd source below
a*2^b, for b in {0,4,8}, depths 0..3, and targets (plus,1), (plus,7),
(minus,1), (minus,47). The forward calculation independently records actual
halving valuations and compares the resulting rational coefficient sum.
Other checks cover the complete residue operator, exact geometric allowance,
sterile sources, insufficient total budgets, and the odd-target domain.

## Conjectures

No new conjecture is promoted. Fixed-root coefficient-series divergence remains open.

## Counterexamples

The [bounded-stopping obstruction](collatz_bounded_fibre_stopping.md) remains
valid. Approximating K_d increasingly well does not make K_d>=1 or provide
reproduction at any prescribed finite depth. The cutoff theorem therefore
does not contradict that obstruction.

## Formalization

[FibreHeightBudget.lean](../../formal/Problems/Collatz/FibreHeightBudget.lean)
defines the signed complete coefficient and the finite budget operator.

- `unitBudget_bounds` and `kernel_le_unitBudget_add`: nonnegative retained
  coefficient and the uniform all-depth error.
- `budget_congr_height`: terminal weights are inspected only at positive
  integers below a*2^b.
- `budget_congr_ancestors`: for odd targets these are actual odd depth-d
  ancestors of that target, within the same height bound.
- `linear_budget_error`, `summable_kernel_iff_budget`, `cumulative_error_le`:
  the summable linear-budget error, exact summability equivalence and total allowance.
- `ancestor_reciprocals_not_summable`: conditional actual reciprocal divergence
  for both signs at nonperiodic targets.

The formal error and height bounds also hold at positive even algebraic targets.
The actual predecessor interpretation explicitly requires an odd target;
the Lean ancestor-support theorem and Python evaluator retain that condition.
The [public audit](../../formal/AxiomCheckCollatzHeightBudget.lean) and
[saved dependencies](../../formal/AxiomCheckCollatzHeightBudget.expected) cover
all nine public theorems, using only propext, Classical.choice and Quot.sound.
The active Lean build passes all 9,020 jobs and the style gate reports no new
violations. All seven independent finite-budget controls pass. The related
mathematical and documentation-link checks also pass. A transient ledger-file
write failure initially left its generated Markdown stale; regeneration and
the repeated generation check resolve that failure.

In the isolated tracked-source snapshot, the other 66 selected checks pass.
The global link gate finds two pre-existing journal links to ignored scratch
scripts, `tmp/ferrers_conj36_certify.py` and `tmp/ferrers_conj36_verify.py`.
All links introduced by this phase resolve. The older journal entries and
unrelated staged work are preserved in the scoped commit.
The English claim retains its human-proof label pending advisory coverage;
kernel trust is recorded separately. No external request is sent.

## Results

**Error proof.** Let q=3/4. The unrestricted tilted coefficient is
3*2^(-k)/q^k, whose sum is 6. Inductively, every included first branch has
error at most its coefficient times 6^d*q^(b-k). For k>b, the elementary
complete bound K_d<=3^d<=6^d and q^(b-k)>=1 give the same allowance.
Summing includes all omitted exponents and gives 6^(d+1)*q^b.
Lean handles the negative remaining exponent by positive real division;
there is no natural-number subtraction silently dropping that tail.

**Height proof.** An admissible positive child is (2^k*a-s)/3<=2^k*a.
Multiplying along a retained path gives n<=a*2^H<=a*2^b. The complete
predecessor bijection makes every positive odd branch actual, and the
forward map fixes its depth-d path uniquely. These observations identify
the finite recurrence with the claimed inverse-family coefficient.

**Quantitative written consequence.** Suppose, for the same fixed nonperiodic
target a, complete depth-block sums from D=2^j to 2D-1 are at least c(a)>0
for infinitely many j. Their retained sums are at least
c(a)-rho^D/(1-rho), hence eventually at least c(a)/2. Every such retained
block lies below a*2^(16D). If the block premise holds for every sufficiently
large j, the existing actual coefficient comparison and disjoint generations
give an ancestor reciprocal lower bound of order log log X. If the good
blocks are only infinitely many, this proves divergence without that rate.
This quantitative block consequence is a written corollary, not an additional
Lean declaration; its arithmetic premise is not established.

## Open questions

Can the finite quantities B_(d,8d)^s(a), at one fixed nonperiodic unit a in
each full fate class, be proved to have a divergent depth sum? Establishing
a positive lower bound on infinitely many disjoint dyadic depth blocks would
suffice. Both the root and its fate must remain fixed while depth grows.

No Juggler pressure estimate follows: Juggler's source-weight transport and
the growing-depth arithmetic estimate at r-eta>3/8 remain separate obligations.

## Decision

**PROMOTE** the explicit cutoff reduction. Large source heights can be
discarded with a summable coefficient error for both signs, so height escape
is not an additional obstacle to this fixed-root series target. The next
question is the arithmetic lower bound for these finite depth blocks.
This phase stops without a new counting campaign or a termination claim.

The later [conditioned-Syracuse reading audit](collatz_conditioned_syracuse.md)
identifies the finite-budget coefficient with two selected ternary cells in
each total-exponent slice. The available conditional Fourier estimate reaches
the required modulus but, after direct absolute-value inversion, has insufficient
relative precision. It supplies no fixed-root block lower bound.

## Publication assessment

Status: `STRUCTURAL`. This is an exact reduction of the remaining arithmetic
question, not a new manuscript or an assertion of coefficient divergence.
