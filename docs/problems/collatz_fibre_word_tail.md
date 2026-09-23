# Every fixed repeated inverse block has summable mass at a nonperiodic root

23 September 2026. **EXACT — HUMAN PROOF**, with kernel-checked declarations;
independent review and advisory statement coverage remain pending.

## Problem

Can repeating a more elaborate inverse word repair the summable contribution
of the [one-halving family](collatz_fibre_run_tail.md) at a fixed integer?

## Exact statement

Let s be either sign and a a positive odd nonperiodic root of the odd
accelerated map S_s. Read inverse words from the target outward. Fix a
nonempty block w of positive exponents, of length L and total exponent H.
Set A=2^H, B=3^L, and define the integer offset by

    Q([])=0,    Q(e::v)=2^(sum v)+3Q(v).

Put Delta=A-B and D_w(a)=|Delta|*a+|Delta+3Q(w)|. For D>=1 let R_D^s(a;w)
sum the coefficient (3/2^e)*(B/A)^D over every e>=1 for which the word
consisting of e followed by D copies of w is realized by positive odd
integers. Every intermediate state is checked; there is no exponent cutoff.
Then

\[
 0\le R_D^s(a;w)\le 6D_w(a)A^{-D},\qquad
 \sum_{D\ge1}R_D^s(a;w)\le\frac{6D_w(a)}{A-1}.
\]

The root need not avoid a cycle forever: a preperiodic root is covered
provided it never returns to itself. Outer sources divisible by three are
allowed. Excluding them only decreases the mass. This is a bound for each
fixed block, not arbitrary concatenations of different blocks.

## Current literature

The affine itinerary identity and geometric exponent weights are **KNOWN**;
see `tao-2019-almost-all-collatz`, Section 1.4 and Lemma 1.12 of
[Tao's paper](https://arxiv.org/html/1909.03562#S1.SS4).
The explicit summable allowance for this complete signed family extends the
laboratory's all-one-block result. It is a **PROJECT-SPECIFIC** consequence
of elementary divisibility; no mathematical priority is claimed.

The [near-critical rate audit](collatz_fibre_rate_barrier.md) separately shows
why periodic minorants are not a weaker substitute for the global cell
problem. The present theorem bounds an actual family at one ordinary root.

## Branch budget

- **Target:** one free inverse exponent followed by repetitions of any fixed block.
- **Novelty hypothesis:** integrality makes every such family summable at a nonperiodic root.
- **Falsifier:** a realized word escapes the divisor bound, or a zero anchor need not imply a cycle.
- **Already killed by?:** only the all-one block has been bounded; general fixed blocks remain to be checked.
- **Existing machinery:** signed numerator identities, actual odd returns and the geometric-tail argument.
- **Maximum Phase-0 scope:** arbitrary fixed blocks and both signs; exact small-word controls and Lean proofs.
- **Promotion criterion:** an unconditional summable bound with the periodic-root exception retained.
- **Stop criterion:** stop at this family; do not infer a bound for arbitrary mixtures of blocks.

## Balanced-ternary formulation

The power B^D=3^(LD) measures the growing integrality condition. The same
root a must satisfy it as an ordinary integer, not merely as a changing
representative of a ternary residue class.

## Why BT may be relevant

The distinction between finite congruence solvability and fixed-integer
realization supplies the estimate. Digit notation alone does not supply
a lower count for the remaining words.

## Candidate operations / invariants

For an actual block from x_j to x_(j+1),

    B*x_(j+1)=A*x_j-s*Q.

Thus B*(Delta*x_(j+1)-s*Q)=A*(Delta*x_j-s*Q). The first free exponent
gives 3*x_0+s=2^e*a. With

    Z_e=Delta*2^e*a-s*(Delta+3Q),

telescoping gives the integer identity

    B^D * (3*Delta*x_D-3*s*Q) = A^D * Z_e.

Coprimality implies B^D divides Z_e. If Z_e=0, the first actual block
has x_1=x_0. Its actual return gives S_s^L(x_0)=x_0, and S_s(x_0)=a
then gives S_s^L(a)=a. Nonperiodicity excludes exactly this resonance.
Therefore

    B^D <= |Z_e| <= D_w(a)*2^e.

Every realized coefficient is at most 3*D_w(a)/A^D. Choose the least
realized first exponent if one exists, and dominate all subsequent
exponents by its complete geometric tail, of factor two. This proves
the bound, and summing A^(-D) gives the stated total allowance.

## Experiments

[Sixteen exact controls](../../tests/research/collatz/test_fibre_word_tail.py)
cover both signs and blocks (1), (2), (1,2), (2,1), (2,2), (1,3), with
repetition counts 1..3. Plus roots are 7,11; minus roots are 11,47.
Finite forward traces confirm these examples are preperiodic and not
periodic. Independent chronological affine composition checks the suffix
offset formula, while every actual inverse step checks the exact valuation.

For each case all first exponents in a complete period 2*3^(LD) are
checked. The affine congruence and actual realization agree. The complete
periodic exponent sum is evaluated with rational arithmetic, including
its infinite geometric tail. These controls do not prove the all-block
or all-depth assertion; that assertion is checked in Lean.

Three periodic controls and one invalid-exponent/order control retain the
essential hypotheses. The five previous run-tail controls also cover the
shared geometric-mask refactor.

## Conjectures

No new registered conjecture. A nonsummable lower bound for the complete
fixed-root coefficient remains open.

## Counterexamples

For the minus root 5, the first exponent 2 reaches 7 and block (1,2)
repeats 7 -> 5 -> 7 in inverse order. Hence R_D^-(5;(1,2)) is at least
(3/4)*(9/8)^D. This grows, so nonperiodicity is essential for summability.
The minus fixed point 1 with block (1) is another growing exception.

For the plus fixed point 1 with first exponent 2 and block (2), the
single repeated path has coefficient (3/4)^(D+1). This is summable,
but already at D=4 defeats the stronger A^(-D) bound without its root
hypothesis. Periodicity does not always mean divergent repeated mass.

## Formalization

[FibreWordTail.lean](../../formal/Problems/Collatz/FibreWordTail.lean)
defines `RealizedWord`, `RealizedRepeat`, `wordOffset`, `wordAllowance`
and `repeatCoefficient`. Its eight public theorems check affine endpoints,
actual returns, divisibility, the exact periodic resonance, the geometric
bound, summability, the total allowance and the growing negative cycle.

[GeometricMask.lean](../../formal/BTCalculus/GeometricMask.lean) supplies
two generic masked-geometric-series lemmas, now shared with `FibreRunTail`.
The [executable audit](../../formal/AxiomCheckCollatzWordTail.lean) and
[saved dependency output](../../formal/AxiomCheckCollatzWordTail.expected)
cover all ten public theorems. Advisory statement review is pending; no
external statement request was made.

The active Lean build passes all 9,032 jobs. The new audit reports only
propext, Classical.choice and Quot.sound, and the six-theorem run-tail
audit remains identical after refactoring. The style gate has no new
violations. All 41 selected word-tail, run-tail, ledger and documentation
checks pass; the only warning is an existing unwritable pytest cache.

## Results

**PROMOTE** the stated fixed-block summable allowance and exact periodic
exception. A finite union of these families has finite total contribution,
by summing their allowances, even if some words are counted more than once.
This last finite-union consequence is written rather than a separate Lean
declaration. It does not cover arbitrary switching between those blocks.

The result rules out any finite menu of pure repeated-block families as
the sole source of fixed-root divergence. It supplies no lower bound for
the complement and no estimate of Juggler stopped pressure.

## Open questions

Can genuinely varying actual inverse words supply a nonsummable lower
bound after averaging over depths at one fixed nonperiodic unit root?
A concrete sufficient target, writing C_d^s(a) for the complete actual
inverse coefficient, is

\[
 \exists c_a>0\ \exists j_a\ \forall j\ge j_a:\qquad
 \sum_{2^j\le d<2^{j+1}} C_d^s(a)\ge c_a.
\]

The constant may depend on the ordinary integer a; no periodic extension
or uniformity over roots is required. This target implies coefficient
divergence by summing disjoint depth blocks. It remains unproved, and is
stronger than bare divergence. Removing any fixed finite menu of the
summable families above preserves such an eventual lower bound, with
at most a smaller constant. This is the signed-Collatz arithmetic question,
not yet a Juggler termination input. The actual Juggler rate r-eta>3/8
remains open.

## Decision

**PROMOTE** the unconditional all-fixed-block bound. The best next question
within this signed-word programme is the depth-averaged lower count for
varying actual words at a fixed root. Stop this phase here; neither the
lower count nor a new termination branch is opened by this result.

## Publication assessment

Status: `STRUCTURAL`. A checked extension of the fixed-root summable-family
reduction. No paper revision, coefficient divergence or termination claim.
