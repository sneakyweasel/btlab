# Complete halving averages control the final unit restriction

23 September 2026. **EXACT — HUMAN PROOF**, with kernel-checked declarations;
independent review and advisory statement coverage remain pending.

## Problem

Can summing over all halving totals control the two-cell correction in the
conditioned-Syracuse audit relative to its coarse-cell probability?

## Exact statement

For either sign s, let L_s be the existing complete signed inverse coefficient
operator. Put C_d^s=L_s^d 1 and K_d^s=L_s^d 1_units. Then at every integer
target a and every d>=1,

\[
 \frac5{21}C_d^s(a)\le K_d^s(a)\le\frac{20}{21}C_d^s(a).       \tag{1}
\]

These constants are independent of depth. In particular the two nonnegative
depth series are summable simultaneously. Combining (1) with the existing
height-budget theorem gives, for a>=1 and d>=1,

\[
 \frac5{21}C_d^s(a)\le B_{d,8d}^s(a)+(19683/32768)^d.          \tag{2}
\]

Here C is the all-source coefficient, not an unnormalized number of ancestors.
At positive odd targets, it includes actual odd ancestors divisible by three
at their initial state; K excludes these sterile sources. Such a source can
occur only at the outermost boundary of a positive-depth inverse tree.

In the notation of the [conditioned audit](collatz_conditioned_syracuse.md),
let c_d and p_d average c_(d,H) and p_(d,H) with the complete geometric weights
binom(H-1,d-1)*2^(-H), over every H>=d. Then C_d=3^d*c_d and K_d=3^d*p_d.
Consequently (1) gives 5*c_d/21<=p_d<=20*c_d/21. This relative estimate
uses the actual affine process, not the preprint's Fourier bound. It does
not hold with H fixed, nor is it asserted for a restricted central H window.

## Current literature

The operator is **KNOWN**: `tao-2019-almost-all-collatz`, Lemma 1.12.
The geometric sibling identity and the one-step mod-9 table are already in
the [fibre dossier](collatz_fibre_mass.md). Their all-depth comparison and
finite-budget consequence are the **PROJECT-SPECIFIC** reduction here;
no mathematical priority is claimed.

Tao's [2020 discussion of inverse density](https://terrytao.wordpress.com/2020/01/25/equidistribution-of-syracuse-random-variables-and-density-of-collatz-preimages/)
studies the smallest Syracuse cell probability c_n. His conjectural
c_n=3^(-n+o(n)) implies ancestor counts X^(1-o(1)); the conjecture is an
assumption, not a bound available for this proof. The present reading checks
that formulation, not every step of the blog's conditional argument.
Even subexponential decay of normalized cells need not give a divergent
depth series: exp(-sqrt(d)) is summable. Thus this reference does not settle
the laboratory's fixed-root harmonic target.

## Branch budget

- **Target:** a relative bound for the final unit restriction after complete halving averaging.
- **Novelty hypothesis:** geometric sibling weights control the loss independently of depth.
- **Falsifier:** an actual root and depth violates the proposed 5/21 lower ratio.
- **Already killed by?:** fixed-H zeros and finite-weight reproduction deficits do not address this relative comparison.
- **Existing machinery:** the exact signed transfer operator, mod-9 table and height budgets.
- **Maximum Phase-0 scope:** the all-depth comparison and independent small exact controls.
- **Promotion criterion:** a checked relative bound removing the final unit restriction as a separate gap.
- **Stop criterion:** stop at the comparison without assuming a coarse-count lower bound.

## Balanced-ternary formulation

The final ternary digit removes sources divisible by three. Changing the digit
convention does not change the geometric sibling weights or improve (1).

## Why BT may be relevant

Ternary residue classes encode integrality and the source restriction. The
relative estimate comes from the signed affine fibre and its geometric weights.

## Candidate operations / invariants

Complete halving summation, positivity of L_s, and the distinction between
L_s^d 1 and L_s^d 1_units. The unit restriction is imposed at the terminal
source; its relative loss is not multiplied once per generation.

## Experiments

The eight cases in
[test_fibre_unit_comparison.py](../../tests/research/collatz/test_fibre_unit_comparison.py)
push the affine random offset forward from zero in the finite cyclic group,
summing the infinite geometric exponent law by its exact period. This is
independent of the inverse-child implementation. For both signs and depths
1..3, every target residue agrees with the complete coefficient and the
coarse Syracuse density, and satisfies (1). Separate cases attain both
constants at positive odd targets. These finite controls do not supply a
fixed-root asymptotic lower bound.

## Conjectures

No new conjecture. Divergence of the fixed-root coarse coefficient series
remains open.

## Counterexamples

At plus target 7, d=1 and H=2, the unique predecessor is the sterile source 9.
Thus the fixed-H ratio is zero. Complete geometric averaging is essential.
The existing finite-weight reproduction obstruction remains valid because
(1) compares K_d with C_d, not with its initial weight or a positive constant.

## Formalization

[FibreUnitComparison.lean](../../formal/Problems/Collatz/FibreUnitComparison.lean)
defines C using the same signed operator as the existing K.

- `coarse_nonneg` and `kernel_bounds`: nonnegativity and (1).
- `summable_kernel_iff_coarse` and `summable_coarse_iff_budget`: the two
  summability equivalences at a fixed integer.
- `coarse_le_budget_add`: the finite-budget inequality (2).
- `ancestor_reciprocals_not_summable`: the conditional actual reciprocal
  consequence for both signs at a nonperiodic positive odd target.

The active Lean build passes all 9,022 jobs. The
[public audit](../../formal/AxiomCheckCollatzUnitComparison.lean) and
[saved dependencies](../../formal/AxiomCheckCollatzUnitComparison.expected)
cover all six public theorems, using only propext, Classical.choice and
Quot.sound. The style gate reports no new violations. All eight independent
affine-distribution controls pass. The English claim keeps its human-proof
label pending advisory coverage; no external statement request was sent.

All 46 selected mathematical, ledger and link checks pass in the shared
worktree. In the isolated tracked-source snapshot, the other 45 checks pass;
the global link gate finds two pre-existing journal references to ignored
scratch scripts, `tmp/ferrers_conj36_certify.py` and
`tmp/ferrers_conj36_verify.py`. All twelve introduced local links resolve.
Unrelated journal, ledger and staged changes are preserved in the scoped commit.

The probability interpretation follows the written affine-word identification
and the independent controls; no new probability-space formalization is claimed.

## Results

For one inverse fibre the admissible exponents are k_0+2j and its homogeneous
coefficients are proportional to 4^(-j). The children satisfy
n_(j+1)=4*n_j+s, so their residues modulo three advance by s. Exactly one
index class j_0 modulo three is sterile. Its proportion of the total weight is

\[
 \frac{4^{-j_0}/(1-4^{-3})}{1/(1-4^{-1})}
 =\frac{16}{21}4^{-j_0},\qquad j_0\in\{0,1,2\}.
\]

The retained fractions are therefore 5/21, 17/21 and 20/21. Sterile targets
have both one-step coefficients zero. Applying the positive operator
L_s^(d-1) to this one-step inequality proves (1) with the same constants.
Comparison of nonnegative series proves the summability equivalence;
the already proved summable height error gives (2).

The primitive Fourier correction from the preceding audit, after complete
halving averaging, therefore satisfies the relative bound

\[
 -\frac37c_d\le p_d-\frac23c_d\le\frac27c_d.                 \tag{3}
\]

This is sufficient control of the last digit for the divergence question.
No telescoping identity or analytic lower bound for c_d has been obtained.

## Open questions

Can one fixed nonperiodic ordinary integer in each relevant fate class have
coarse depth-block sums bounded below by a positive constant on infinitely
many disjoint dyadic blocks? Such a bound transfers to finite unit coefficients
through (2). Neither that premise nor a Juggler source-weight transfer is proved.

## Decision

**PROMOTE** the relative comparison as a reduction of the fixed-root target.
The final unit restriction is no longer an independent lower-bound obligation
after complete halving averaging. The remaining question is the coarse
Syracuse density at the same ordinary integer as depth grows. This phase stops
at that boundary, without a new census or a termination claim.

## Publication assessment

Status: `STRUCTURAL`. Formal consolidation of a consequence of the known
operator, with a sharper statement of the remaining arithmetic problem.
