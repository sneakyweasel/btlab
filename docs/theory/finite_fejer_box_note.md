# Finite Fejer discrepancy for half-open boxes

22 September 2026. **EXACT — LEAN VERIFIED.** The complete finite estimate
below is checked by Lean.
It discharges obligation Q3 in the
[effective modular-return audit](juggler_effective_modular_return_audit.md).
This is a formalization of a classical smoothing argument; no new
discrepancy method or external novelty is claimed.

## Statement

Let H,N be positive integers and E>=0. Let z_0,...,z_(N-1) be arbitrary
points of the product of two unit circles. Suppose every integer pair
(k,l) other than (0,0), with abs(k),abs(l)<=H, satisfies

\[
 \left|\frac1N\sum_{n<N}e(kz_{n,1}+lz_{n,2})\right|\le E,
 \qquad e(t)=\exp(2\pi i t).
\]

For real endpoints a<=b<=a+1 and c<=d<=c+1, let B be the product
of the images of the half-open intervals [a,b) and [c,d) on the circles.
Then

\[
 \left|\frac{\#\{n<N:z_n\in B\}}N-(b-a)(d-c)\right|
 \le \frac5{\sqrt{H+1}}+(3+2\log H)^2E.
\]

The covering declaration is
`BTCalculus.FejerBox.finite_box_discrepancy` in
[FejerBox.lean](../../formal/BTCalculus/FejerBox.lean).
Its hypotheses contain the mode bound, positivity, and interval lengths.
There is no assumed smoothing estimate, polynomial sandwich, boundary
avoidance, equidistribution, or independence of the sample coordinates.
Zero-length arcs are empty, length-one arcs are the whole circle, and
arcs may wrap through zero. The left endpoints are included and the
right endpoints excluded in the actual counted predicate.

## Proof map

1. [FejerKernel.lean](../../formal/BTCalculus/FejerKernel.lean) defines
   the actual kernel as the squared norm of the finite Dirichlet sum
   divided by H+1. It proves nonnegativity, integral one, the exact
   double character expansion, and the bound
   F_H(t)<=1/(4*(H+1)*t^2) for 0<abs(t)<=1/2. Integrating proves
   a circle tail at most 1/(2*(H+1)*delta), with a two-coordinate
   union bound of 1/((H+1)*delta).
2. [FejerArc.lean](../../formal/BTCalculus/FejerArc.lean) defines arcs
   as images of genuine half-open real intervals. The change of variables
   to real interval integration and the reciprocal-frequency coefficient
   bound are proved. Expanded arcs saturate at length one; contracted
   arcs saturate at length zero. Small circle elements have small real
   representatives, giving both pointwise smoothing inequalities with
   no exception for sample boundary hits.
3. The same module proves the exact finite expansion of the convolution.
   Retaining repeated frequency labels from the Dirichlet-square sum
   avoids a separate triangular-multiplier identity. Each coefficient
   row has mass at most 1+2*harmonic(H), so after division by H+1 the
   same bound holds. The constant coefficient sums exactly to the arc
   length. Taking products gives coefficient mass at most
   (1+2*harmonic(H))^2 and constant coefficient equal to box area.
4. [FourierDiscrepancy.lean](../../formal/BTCalculus/FourierDiscrepancy.lean)
   supplies finite averaging and counting transfer. Its generic sandwich
   theorem is conditional, but the final theorem constructs and proves
   every required sandwich and coefficient estimate. Each coordinate
   length changes by at most 2*delta, giving area error at most 4*delta.
5. For H>=3 choose delta=1/sqrt(H+1). The proved identity
   4*delta+1/((H+1)*delta)=5/sqrt(H+1) yields the constant five.
   The harmonic bound gives the logarithmic coefficient. For H=1,2
   the claimed error exceeds the trivial discrepancy bound one.

## Verification and scope

The four modules are included in the default `BTCalculus` build.
[AxiomCheckFejerBox.lean](../../formal/AxiomCheckFejerBox.lean) checks
every supporting theorem as well as the covering declaration; its
[recorded output](../../formal/AxiomCheckFejerBox.expected) uses only
`propext`, `Classical.choice`, and `Quot.sound`. There is no additional
analytic assumption or compiler-evaluated proof step.
The default Lean build passes (9070 jobs). The repository's single-row
Jev advisory returned "covered" (0.75), followed by direct comparison
of the English claim with the quantified Lean statement.

The targeted integration, ledger, formalpedia, effective-return, layer,
and branch-index run collected 248 tests: 231 passed, 15 skipped, and
two workspace registration checks failed because a concurrent task had
created the unregistered `OOEEFourierModes.lean` draft. Both exact failing
checks pass against a clean snapshot of committed sources plus these
Q3 changes. All five generated formalpedia artifacts match that snapshot;
the concurrent OOEE and weighted-Fejer drafts are excluded from them.
The ledger renderer and branch-index consistency gates pass.

The effective OOE theorem now has a complete formal proof. A subsequent
[higher-derivative formalization](higher_derivative_finite_note.md)
supplies an alternative input for Q1; its
[OOE specialization](juggler_ooe_effective_modes_note.md) and the uniform
mode estimate Q2 are proved. Q4 (quantitative OOE assembly) and Q5
(bounded witness extraction) are now also proved in the
[complete return module](juggler_ooe_effective_return_lean_note.md).
The mode bound above is the natural input of a discrepancy
theorem; proving the specific OOE rate is Q2, not part of Q3.
Paper E version 0.7.0 includes the complete theorem in its expanded
56-declaration audit. Its separate ledger advisory ruling remains pending.

## Decision

**PROMOTE** the complete finite box estimate. Stop this direction here.
The subsequent Q1/Q2 and Q4/Q5 applications are complete. This does not
authorize a new word or an optimization of the modulus exponent.
