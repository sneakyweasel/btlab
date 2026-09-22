# Finite ternary weights for the complete signed odd-return operator

22 September 2026. Kernel-checked formalization of the existing coefficient
obstruction in [the fibre dossier](../problems/collatz_fibre_mass.md).
Independent review and advisory statement coverage remain open.

## Exact scope

For s in {1,-1}, a weight h on residues modulo 3^r, and a target residue
a modulo 3^(r+1), define the homogeneous operator by

\[
 (L_s h)(a)=\sum_{k\ge1}\frac3{2^k}
   \sum_{\substack{b\bmod3^r\\2^ka\equiv3b+s\pmod{3^{r+1}}}}h(b).
\]

There is at most one child in the inner sum. This is the ordinary
odd-return coefficient formula: a child exists exactly when 2^k*a-s
is divisible by three, and then its residue is (2^k*a-s)/3 modulo 3^r.
The Lean representation uses k+1 for the positive halving exponent.
It includes all exponents in an infinite sum, with no truncation or
assumed coefficient table.

For r>=1 and d>=1, if h vanishes on multiples of three and is strictly
positive on the other residues, there is a unit residue a modulo 3^(r+d)
such that

\[
 (L_s^d h)(a)<h(a\bmod3^r).
\]

The stronger formal theorem only requires h>=0 and h(-s)>0, together
with the same vanishing condition. Positivity at every unit is unnecessary.
No actual-integer mass estimate or fate-distribution hypothesis is assumed.

## Concrete operator and proof

[FibreMass.lean](../../formal/Problems/Collatz/FibreMass.lean) defines
multiplication by two as a permutation at every ternary level. Its inverse
iterates assign each child b its parent 2^(-k)*(3b+s). `parent_signed_iff`
proves the signed integer congruence displayed above; `parent_injective`
proves uniqueness of the child for each exponent. `row_at_parent` identifies
its exact coefficient, and `transfer_formula` exposes the complete sum.

For nonnegative h, `row_summable` dominates each row by a geometric series.
Finite-sum interchange is therefore justified. Every child has exactly one
parent for each k, and sum_(k>=1) 3/2^k=3. Hence `transfer_sum` proves

\[
 \sum_a L_s h(a)=3\sum_b h(b).
\]

`iterate_sum` gives the factor 3^d. Independently, `project_sum` proves
that lifting the original weights to the larger table has that same sum.
The k=1 branch carries residue -s at the child level to -s at the parent
level. `iterate_spike` proves

\[
 (L_s^d h)(-s)\ge(3/2)^d h(-s)>h(-s).
\]

If all unit rows reproduced at least the original weight, the nonunit
rows would also satisfy that inequality by nonnegativity and the vanishing
condition. The strict row above would then force the total sum to increase,
contradicting the two exact sum identities. `exists_deficit` proves the
stronger nonnegative-weight version; `finite_weight_obstruction` specializes
it to strictly positive unit weights.

## Boundaries

This formalizes the homogeneous coefficient theorem. The
[actual-mass continuation](collatz_actual_fibre_mass_lean_note.md) separately
formalizes the actual one-generation error, deficient arithmetic progression
and divergent reciprocal mass. The actual error at higher fixed depths, full
ternary coverage of sibling rays, and conditional generation-series criterion
remain written proofs in the dossier. They are not included in this theorem's
Lean coverage.

The result prevents a uniform finite-periodic-weight replacement for
Juggler's harmonic production, for either sign and any fixed grouping depth.
It does not exclude fate-specific averaging, nonperiodic weights or variable
stopping depths. It does not improve the Juggler pressure threshold 3/8 or
prove termination, infinite escape, or a new cycle exclusion.

## Validation

The full Lean build passes all 9,090 jobs. The
[dependency audit](../../formal/AxiomCheckCollatzFibreMass.lean) covers all
31 theorems; its [saved output](../../formal/AxiomCheckCollatzFibreMass.expected)
contains only propext, Classical.choice and Quot.sound. No additional
mathematical assumption or compiler-evaluated proof enters the result.
The shared-worktree regression run passes 90 tests. Its 17 failures are
in the concurrently edited OOE/Paper E surface: orbit notation parsed as
Markdown links and a newly added archive input not yet in the release
inventory. Fibre, ledger and formalpedia checks pass. Changed-document
links and generated registries are also checked on the scoped commit,
which excludes the concurrent edits.

## Decision

**PROMOTE** the formal consolidation of the coefficient obstruction.
The finite-weight search remains closed. Actual growing-depth Juggler
pressure remains open; this phase opens no further attack.
