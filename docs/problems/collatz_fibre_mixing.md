# Fine-scale mixing alone does not give fixed-root coefficient divergence

23 September 2026. **EXACT — HUMAN PROOF**, with kernel-checked declarations;
independent review and advisory statement coverage remain pending.

## Problem

Can positivity, coherent ternary refinement and strong fine-scale mixing
force divergence of densities along a specified ordinary integer?

## Exact statement

For every positive integer a coprime to three, there is an explicit artificial
family U_l on residues modulo 3^l, l>=1, with these properties:

- U_1=(0,1,1); U_l is positive exactly on unit residues and at most 4/3.
- Each parent density is the average of its three children. Thus the mean
  over unit residues is one at every level.
- If a finer residue extends a level-l cylinder, its density differs from
  the parent by at most 3^(1-l), uniformly in the refinement depth.
- Along the prescribed root, U_(d+1)(a mod 3^(d+1))=3^(-d). The depth series
  has sum 3/2.

The normalization V_l(b)=(b mod 3)*U_l(b) has first row (0,1,2), mean one
over all residues, the same coherence, and refinement error at most 2*3^(1-l).
Its selected-root series has sum (a mod 3)*3/2. This also matches the first
row of the coherent Syracuse density without forcing root-series divergence.

These models are **not** the actual signed inverse recurrence or its stationary
measure. Lean checks a separating arithmetic constraint: the actual unit
coefficient at depth one is at least 3/2 at plus target 17 and minus target 1,
whereas every U cylinder has density at most 4/3.

## Current literature

`tao-2019-almost-all-collatz`, [Section 1.4](https://arxiv.org/html/1909.03562#S1.SS4),
supplies the actual affine recurrence, coherent projections and an averaged
fine-scale mixing estimate. Coherence is weaker than stationarity under that
specific recurrence. The counterexample addresses only an inference from the
listed general properties, not Tao's full arithmetic process or theorem.

The unit iterate K_d starts from (0,1,1); it is not itself the coherent
Syracuse density sequence. Its first refinement has coarse row (0,2/3,4/3).
The Syracuse density starts from (0,1,2); positivity of the common plus
operator compares its level-(d+1) density with K_d between factors one and
two. The V model prevents confusing that normalization issue with the
pointwise gap. The finite comparison is written here; the model theorems
are formalized below.

Tao's Remark 1.4 also gives tightness: for each positive epsilon, a bounded
collection of targets captures lower logarithmic density at least 1-epsilon.
It does not specify target 7, target 47, or every fate class. No deduction of
the proposed fixed-root block estimate from that statement was found here.

The construction is an elementary cylinder-density example, **KNOWN** in
method. No literature priority or new Collatz lower bound is claimed.

## Branch budget

- **Target:** whether coherence and fine-scale mixing imply a fixed-root lower bound.
- **Novelty hypothesis:** averaging depth might close the pointwise gap.
- **Falsifier:** a coherent positive model with exponential refinement control
  and a summable selected-root series.
- **Already killed by?:** the prior dossier warns of the averaging gap; this
  phase supplies an explicit model, without weakening the actual recurrence.
- **Existing machinery:** geometric series, ternary cylinders and the actual
  signed one-halving spike.
- **Maximum Phase-0 scope:** one model in two initial normalizations, a Lean
  proof and small exact residue controls.
- **Promotion criterion:** new arithmetic information beyond the general model properties.
- **Stop criterion:** close the generic implication; leave the actual lower bound open.

## Balanced-ternary formulation

The proof uses ordinary ternary digits in least-significant-first order.
Balanced digits would relabel the same nested residue cylinders.

## Why BT may be relevant

Ternary refinement represents inverse integrality information. Digit notation
by itself supplies no additional constraint at ordinary integer roots.

## Candidate operations / invariants

Let r be the digit path of a. Define D_r(empty)=1. For a nonempty word xw,
set D_r(xw)=D_shift(r)(w)/3 if x=r_0, and 4/3 otherwise. Within the selected
initial unit digit, use D; on the other unit digit use one, and on zero use
zero. This is U. Multiplying by the initial digit gives V.

## Experiments

Run `python tools/lab.py run research.collatz.fibre_mixing`. The evaluator
uses the valuation of the first difference of integer residues, independently
of Lean's recursive word definition. Seven exact controls cover all cells
through level four at roots 1, 7, 17 and 47, two-level refinements, first-row
normalizations, geometric partial sums and the signed operator distinction.
The actual one-step spike coefficients are 34/21 in both examples.

## Conjectures

No new conjecture. The actual fixed-root coefficient-series question remains open.

## Counterexamples

The selected cylinder becomes thinner at every level while remaining positive.
Its shrinking density is compatible with the exact total mean: sibling cells
receive the compensating mass. Uniform convergence does not require a positive
limiting density at every integer. This is not a realized Collatz inverse tree.

## Formalization

[FibreMixing.lean](../../formal/Problems/Collatz/FibreMixing.lean) checks
positivity, boundedness, coherence, level sums, uniform refinement errors,
the exact selected-root geometric series, ordinary integer digit paths,
and the explicit distinction from the two signed operators. It also checks
the Syracuse first-row normalization, coherence, mean and root series.
The public axiom audit covers all 21 theorems:
[audit](../../formal/AxiomCheckCollatzFibreMixing.lean),
[dependencies](../../formal/AxiomCheckCollatzFibreMixing.expected).
The active build passes all 9,021 jobs. Every audited theorem uses only
propext, Classical.choice and Quot.sound, and the style gate has no new
violations. All 58 selected mathematical, ledger and link checks pass in the
shared worktree. In the isolated tracked-source snapshot, the 57 non-link
checks pass; the global link check finds two older journal references to
ignored scratch scripts, `tmp/ferrers_conj36_certify.py` and
`tmp/ferrers_conj36_verify.py`. All links introduced by this phase resolve.
The English claim retains its human-proof label pending advisory coverage;
kernel trust is recorded separately. No external statement request is sent.

## Results

Child conservation follows from 1/3+4/3+4/3=3. Along the selected path,
each new digit multiplies D by 1/3; after leaving it, D remains constant.
Induction therefore gives the uniform refinement estimate and exact geometric
series. Multiplication by the initial digit preserves coherence and costs at
most a factor two in the refinement estimate.

The uniform density estimate implies an averaged fine-scale estimate after
normalizing cylinder masses. It still permits a zero limiting density at
the chosen root. The actual signed transfer constraint is the extra arithmetic
information absent from the artificial model.

**Difficulty of the remaining target.** A divergent ancestor reciprocal
series precludes every eventual ancestor-count upper bound O(X^alpha) with
alpha<1, by summation over dyadic height blocks. Thus the
[finite-height block target](collatz_fibre_height_budget.md) requires a
substantial arithmetic advance beyond the known X^0.84 lower bound. Finite
depth data, coherence and conserved averages have not supplied it.

## Open questions

Can the exact signed recurrence prevent summable depth blocks at one fixed
nonperiodic ordinary integer? Both the root and its fate must stay fixed.
Neither a lower bound for those blocks nor Juggler pressure is obtained here.

## Decision

**CLOSE** inference from coherence, positivity and fine-scale mixing alone.
The actual signed coefficient-divergence problem remains open. Best next
question: which constraint of the exact affine recurrence gives a lower bound
on the selected root's depth blocks that fails for this artificial model?
This phase stops without a larger census, another abstract mixing model,
or a termination claim.

## Publication assessment

Status: `STRUCTURAL`. A checked method boundary, not a new manuscript.
