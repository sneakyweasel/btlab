# Actual signed Collatz fibre mass and persistent deficits

22 September 2026. Formal continuation of the
[complete coefficient obstruction](collatz_fibre_mass_lean_note.md).
The result verifies the existing one-generation argument in the
[fibre dossier](../problems/collatz_fibre_mass.md). Independent review
and advisory statement coverage remain open.

## Exact scope

For s in {1,-1}, let S_s(n)=(3n+s)/2^v2(3n+s) on positive odd integers.
Let h be a nonnegative real table modulo 3^r, bounded above by H. For a
positive odd target m define its full actual predecessor mass by

\[
 W_h(m)=\sum_{\substack{n\ge1,\ n\text{ odd}\\S_s(n)=m}}
             \frac{h(n\bmod3^r)}n.
\]

The series converges and, for the complete homogeneous operator L_s,

\[
 \left|mW_h(m)-(L_s h)(m\bmod3^{r+1})\right|
       \le \frac{H}{m-1/2}.
\]

This estimate allows r=0, targets divisible by three, and weights on
nonunit residues. Those weights simply specialize to zero in the obstruction.

Now assume r>=1, h is zero on multiples of three, and h is strictly
positive on all other residues. For either sign there is a unit residue
a modulo 3^(r+1), a real delta>0, and B>=1 such that every odd m>=B in
that residue satisfies m*W_h(m)<=h(m mod 3^r)-delta. These deficient
targets have divergent reciprocal mass. Consequently, for every set E
with finite sum of 1/m over its positive members, there exists a positive
odd unit m outside E with m*W_h(m)<h(m mod 3^r).

The last conclusion quantifies over the ambient integer targets. It
does not bound the intersection of those targets with a prescribed fate
class. No termination, infinite escape, or fate-class divergence is inferred.

## From congruences to actual predecessors

[FibreActual.lean](../../formal/Problems/Collatz/FibreActual.lean) uses
`plus=true` for s=1 and `plus=false` for s=-1. Its `oddReturn` definition
uses the actual integer numerator and its 2-adic valuation; the plus
specialization is the existing accelerated map.

`Problems.Collatz.FibreActual.predecessor_iff` identifies all actual
predecessors with the candidates (2^(k+1)*m-s)/3 whose numerator is
divisible by three. Positivity and oddness are proved. Because m is odd,
the valuation of 2^(k+1)*m is exactly k+1. This proves both the return
equation and uniqueness of the exponent. The resulting `predecessorEquiv`
is a bijection, so the sum contains every predecessor exactly once.

`Problems.Collatz.FibreActual.parent_child_iff` identifies each congruence
branch of the existing coefficient operator with its actual integer child.
`Problems.Collatz.FibreActual.actualMass_predecessors` then exposes the
literal series over positive odd predecessors, with no orbit or residue
distribution assumption.

## Error and deficient progression

[FibreMassError.lean](../../formal/Problems/Collatz/FibreMassError.lean)
compares each actual normalized term with its homogeneous coefficient.
For p=2^(k+1), the difference is

\[
 \frac{3m h(n)}{pm-s}-\frac{3h(n)}p
       =\frac{3s h(n)}{p(pm-s)}.
\]

The denominator obeys pm-s>=p*(m-1/2)>0. The absolute error is at most
3H/(p^2*(m-1/2)). Summing the geometric series with ratio 1/4 gives the
displayed bound. Both the actual terms and the error series are proved
summable. `Problems.Collatz.FibreMassError.predecessor_summable` states
convergence directly on the actual predecessor subtype;
`Problems.Collatz.FibreMassError.predecessor_mass_error` states the bound
there. The use of an infinite sum does not rely on its default value for
a divergent series.

[FibreDeficit.lean](../../formal/Problems/Collatz/FibreDeficit.lean)
specializes the existing homogeneous obstruction to one generation.
For a row with gap g>0, the error is at most g/2 once
m>=1/2+2H/g. Its explicit odd progression has common difference
2*3^(r+1). A comparison with the harmonic series proves divergence of
its reciprocal sum.

`Problems.Collatz.FibreDeficit.deficient_mass_not_summable` proves the
ambient divergence. `Problems.Collatz.FibreDeficit.outside_finite_mass`
gives the deletion obstruction, and
`Problems.Collatz.FibreDeficit.exists_predecessor_mass_lt` writes that
conclusion directly using the full actual predecessor series.

## Formal boundary and consequence for the research program

The homogeneous obstruction is already formal for every fixed positive
generation depth. This continuation formalizes the actual affine error
and deficient-progression consequence at one generation. The fixed-depth
actual error and full ternary coverage of sibling rays remain written
proofs in the dossier. The
[generation-series continuation](collatz_generation_mass_lean_note.md)
now separately formalizes the conditional coefficient-to-ancestor implication
at a given nonperiodic target; its divergence premise remains open.

Juggler's OOEE production succeeds by bounding the reciprocal mass of
poor targets. For the proposed uniform signed Collatz production using
a positive finite periodic table, the deficient targets instead have
infinite ambient reciprocal mass. Thus a global finite-mass deletion
cannot copy that step. Fate-specific averaging, nonperiodic weights and
variable stopping depths are outside this obstruction.

The Juggler pressure threshold remains 3/8. The missing growing-depth
arithmetic estimate is unchanged.

## Validation

The [complete theorem audit](../../formal/AxiomCheckCollatzActualMass.lean)
and its [saved output](../../formal/AxiomCheckCollatzActualMass.expected)
cover all 54 theorems in the three modules. Their dependencies contain only
propext, Classical.choice and Quot.sound. The full Lean build passes all
9,093 jobs. The public-declaration style gate reports no new violations;
ledger rendering, branch-index consistency and the Paper E release check
pass. The latter was rerun after an unrelated concurrent pyproject edit
cleared. The targeted regression run passes 88 tests and initially reports
one stale-catalogue failure after concurrent tooling changes. Refreshing
the catalogue makes that exact test pass; the declaration-resolution and
documentation-link checks also pass on rerun, for three passing rechecks
and no remaining failure in the selected suite.

The scoped commit separately regenerates all five catalogue artifacts with
its own committed generator and checks them for exact agreement. It includes
only this phase's three ledger rows and journal entry, preserving the
concurrent catalogue implementation and its other ledger edits.

## Decision

**PROMOTE** the formal bridge to actual integer masses and the persistent
one-generation obstruction. The finite-weight search stays closed;
the broader termination goal remains open. This phase opens no new attack.
