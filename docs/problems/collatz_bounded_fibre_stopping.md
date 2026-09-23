# Bounded stopping does not repair signed inverse-fibre reproduction

23 September 2026. **EXACT — HUMAN PROOF**, with kernel-checked declarations;
independent review and advisory statement coverage remain pending.

## Problem

Can separate stopping decisions on each inverse branch compensate for poor
Collatz fibres when all branches have one common finite depth budget?

## Exact statement

Fix either sign s, a level r>=1, and a nonnegative weight h periodic modulo
3^r, zero on multiples of three and positive at residue -s. Let L_s be the
complete homogeneous inverse operator from the
[fibre dossier](collatz_fibre_mass.md). Define, with the natural residue lifts,

\[
 U_0=h,\qquad U_{d+1}=\max\{h,L_sU_d\}.
\]

For every d>=0 there is a unit residue a modulo 3^(r+d+1) such that

\[
 (L_sU_d)(a)<h(a).
\]

U_d is the attained optimum over policies which may stop immediately or
take at most d inverse steps. Thus every policy forced to take a first step,
then stop by depth d+1 on every branch, has coefficient payoff below h(a)
at every positive integer in that residue. A policy may depend on the actual
integer and its entire inverse history. All positive halving exponents are
included; there is no branching cutoff.

The payoff is the sum of terminal h-values times the products of 3/2^k
along stopped paths. It is a homogeneous coefficient, not the exact sum of
terminal reciprocals. The result does not assert a uniform deficit size,
a deficient fixed integer for all horizons, or failure of unbounded stopping.

## Current literature

The max/continuation recursion is the standard Bellman optimal-stopping
construction; see Carmona's
[2007 winter-school notes, Chapter 1](https://staff.fnwi.uva.nl/a.khedher/winterschool/6carmona.pdf).
Here L_s is a positive coefficient operator, not a Markov transition
probability. The proof uses positivity and complete summability directly;
no optional-stopping theorem or stochastic normalization is assumed.

The signed operator is the density-normalized version of the recurrence
in `tao-2019-almost-all-collatz`, Lemma 1.12. Its conserved mean and
finite-weight obstruction were already established in the fibre dossier.
The bounded-policy extension is a **PROJECT-SPECIFIC** consequence of that
obstruction. No literature priority is claimed.

## Branch budget

- **Target:** uniform reproduction with variable stopping depths bounded by D.
- **Novelty hypothesis:** branch-specific stopping compensates where fixed depths fail.
- **Falsifier:** its envelope gives a forbidden finite periodic weight.
- **Already killed by?:** fixed-depth reproduction was closed, but did not itself
  cover different stopping choices on different branches.
- **Existing machinery:** complete signed operator, mean identity, finite-weight
  obstruction and actual predecessor parametrization.
- **Maximum Phase-0 scope:** prove or refute the envelope reduction for both signs;
  check only two-step controls and the existing three tiny residue levels.
- **Promotion criterion:** a valid compensation inequality or a precise obstruction.
- **Stop criterion:** close bounded stopping if the reduction holds, retaining
  unbounded stopping and fixed-target coefficient divergence as open questions.

## Balanced-ternary formulation

The finite horizon produces a finite ternary-periodic value function. Balanced
digits change its notation without changing the obstruction.

## Why BT may be relevant

Ternary levels track the inverse integrality restrictions exactly. They provide
the finite periodicity needed by the proof, not an integer distribution theorem.

## Candidate operations / invariants

Use the complete transfer L_s and the max/continuation envelope. Positivity
makes U_d monotone in d. Each U_d is nonnegative, zero on nonunits and
positive at -s. No periodicity is required of the policies being bounded.

## Experiments

Four exact regression controls in
[test_fibre_stopping.py](../../tests/research/collatz/test_fibre_stopping.py)
check both signs. At plus target 7 and minus target 47, the optimal
two-step continuation coefficient is 437756/1835001<1. These targets
are nonperiodic. Independent integer-child sums enclose that exact value
using a geometric bound on every omitted exponent.

Two other controls show that branch-specific stopping strictly improves
on choosing the better of the two fixed depths. The new obstruction therefore
cannot be justified by replacing the adaptive optimum with max(K_1,K_2).
These finite checks do not supply the all-horizon quantifier; Lean does.

## Conjectures

No new conjecture. Fixed-integer coefficient-series divergence remains open.

## Counterexamples

For unit terminal weight, the first three forced budgets have the following
optimal deficits. Residues are labels; actual positive odd representatives exist.

| Maximum depth | Modulus | Plus residue | Minus residue | Optimal coefficient |
|---|---:|---:|---:|---:|
| 1 | 9 | 7 | 2 | 5/21 |
| 2 | 27 | 7 | 20 | 437756/1835001 |
| 3 | 81 | 61 | 20 | 7695605503924658996/32124819513409084827 |

The poor residue can change with the budget. One cannot exchange
"for every budget, some target" with "some target, for every budget."

## Formalization

[FibreStopping.lean](../../formal/Problems/Collatz/FibreStopping.lean) defines
the complete envelope and an inductive policy tree. Every expanded node has
a separate continuation policy for each halving exponent. The existing
`FibreActual` theorem identifies those branches with actual predecessors
when the positive target is odd.

- `bounded_stopping_deficit`: the all-level, both-sign envelope obstruction.
- `payoff_bounds`: every policy has nonnegative payoff bounded by its envelope;
  the proof establishes summability of each complete branch sum.
- `envelope_attained`: an actual bounded policy attains the envelope.
- `forced_payoff_le`: the forced first step is bounded by L_s U_d.
- `bounded_policy_deficit`: one residue defeats every such bounded policy at
  every positive integer representative, including positive odd representatives.

The [axiom audit](../../formal/AxiomCheckCollatzFibreStopping.lean) and
[saved dependencies](../../formal/AxiomCheckCollatzFibreStopping.expected) cover
all five public theorems, using only propext, Classical.choice and Quot.sound.
The full active Lean build passes 9,019 jobs and the style gate has no new
violations. The four new exact controls, existing fibre checks, ledger and
documentation-link gates pass. A ledger declaration-path check now uses the
existing normalizer, accepting both supported Lean path conventions.
In the isolated tracked-source snapshot, the other 43 selected checks pass;
the global documentation-link check finds two pre-existing journal links to
ignored scratch scripts under tmp. All links introduced by this phase resolve.
Those older entries and unrelated staged changes are preserved.
The claim retains its human-proof label pending advisory
coverage; kernel trust is recorded separately. No external request is sent.

## Results

The key reduction is short. Suppose L_s U_d>=h everywhere. For d>=1,
monotonicity gives L_s U_d>=L_s U_(d-1), hence

\[
 L_sU_d\ge\max\{h,L_sU_{d-1}\}=U_d.
\]

For d=0 the same conclusion follows from U_0=h. But U_d is a finite periodic
nonnegative unit-supported weight, positive at -s. The existing one-step
finite-weight obstruction forbids L_s U_d>=U_d everywhere. This proves the
strict deficit for every finite budget. The Lean proof handles level lifts
through evaluation at actual positive integer representatives.

Policy domination is proved by induction on the tree. At each expanded
node, positivity bounds every child by its envelope; a summable geometric
majorant justifies the complete sum. Choosing the larger of stopping and
continuing at every node attains the envelope.

There is a further written consequence using the already proved sibling
coverage argument in the fibre dossier. Every full fate class contains
representatives of every ternary residue, through a complete sibling ray.
Thus each finite budget has deficient targets even inside any specified
full fate class. This use of sibling coverage remains a written corollary;
it is not included in the new Lean declaration coverage. It says nothing
about how much reciprocal mass those targets carry.

## Open questions

Can unbounded inverse depth, controlled in terms of actual target height,
give a nonsummable coefficient lower bound at one fixed nonperiodic unit in
each full fate class? The uniform affine comparison is available for both
signs. Neither this obstruction nor Tao's averaged mixing answers that
fixed-integer question. Juggler's growing-depth pressure estimate is unchanged.

## Decision

**CLOSE** uniform reproduction by bounded variable-depth stopping with a
finite periodic terminal weight. Allowing every branch its own stopping
choice does not evade the finite-weight obstruction. The best next question
is whether a genuinely unbounded, height-controlled inverse construction
forces coefficient-series divergence at a fixed nonperiodic integer.
This phase stops here.

## Publication assessment

Status: `STRUCTURAL`. This sharpens an existing method boundary; it is not
a coefficient-divergence theorem, a termination proof, or a new manuscript.
