# Uniform curvature of the OOEE carry-cell phases

22 September 2026. Kernel-checked in
[OOEECurvature.lean](../../formal/Problems/Juggler/OOEECurvature.lean).
This formalizes the phase-specific curvature and unweighted cell estimate
in equations (13)--(14) of the
[written OOEE argument](juggler_ooee_poor_fibre_tail_note.md).
Advisory statement coverage remains pending, separately from kernel checking.
No new analytic method or external priority claim is made.

## Exact phase and cancellation

Put s=2h, y=x+s, and Delta_s f(x)=f(x+s)-f(x). The definitions are

\[
 A_s(x)=\frac32x^{3/2}y^{3/4}-x^{9/4}-\frac12y^{9/4},
 \qquad
 F_{G,\epsilon}(x)=uA_s(x)+\frac32u(G+\epsilon)y^{3/4}
       +\frac v2\Delta_s(x^{3/2})+\frac w2\Delta_s(x^{9/8}).
\]

The coefficient G+epsilon is held fixed when differentiating in x.
`anchor_original` identifies A_s with the expression in the written proof.
Both x derivatives of F are proved from the real-power derivative rules.
For the anchor curvature, differentiating twice in s gives four monomials
whose absolute sum is at most 3*x^(-7/4) when x>0 and s>=0.
Both its value and its first s derivative vanish at s=0. Two mean-value
comparisons therefore prove

\[
 |A_s''(x)|\le3s^2x^{-7/4}.
\]

The negative-power differences are bounded by their derivatives. For x>=1,
`cell_curvature_error` consequently proves the exact finite estimate

\[
 \left|F_{G,\epsilon}''(x)+\frac9{32}u(G+\epsilon)y^{-5/4}\right|
 \le3|u|s^2x^{-7/4}+(|v|+|w|)s x^{-3/2}.
 \tag{1}
\]

This estimate is proved, not supplied as a curvature hypothesis.

## From actual carry bounds to signed curvature

Suppose x,h>=1, 0<=epsilon<=1, and

\[
 G\le (x+2h)^{3/2}-x^{3/2}\le G+1.
 \tag{2}
\]

The mean-value theorem and the unit floor error give

\[
 2h\sqrt{x}\le G+\epsilon\le4h\sqrt{x+2h}.
\]

In particular, (2) holds on an actual cell with
floor((x+2h)^(3/2)-x^(3/2))=G. `floor_cell_bounds` proves this implication
for integer G. The weak upper inequality also covers the boundary in
the closure of a cell.

If u>0, h<=x/1024, and |v|+|w|<=u*x^(3/4)/1024, then y<=2x.
The magnitude of the principal negative term in (1) lies between
(9/64)*u*h*x^(-3/4) and (9/8)*u*h*x^(-3/4).
The error is at most (14/1024)*u*h*x^(-3/4). Thus
`cell_curvature_pointwise` proves

\[
 -2uhx^{-3/4}\le F_{G,\epsilon}''(x)
                 \le-\frac18uhx^{-3/4}.
\]

Now let P<=x<=2P and assume

\[
 P\ge1,\quad 1\le h\le P^{1/16},\quad P^{15/16}\ge1024,
 \qquad |v|+|w|\le uP^{3/4}/1024.
 \tag{3}
\]

`cell_curvature_uniform` derives the pointwise size conditions and proves

\[
 -2uhP^{-3/4}\le F_{G,\epsilon}''(x)
                 \le-\frac1{16}uhP^{-3/4}.
 \tag{4}
\]

`size_conditions_eventually` proves that the conditions on P in (3)
hold for all sufficiently large P for each fixed u>0,v,w. This threshold
does not depend on h, G, epsilon, the cell position, or its length.

## Finite sums with the endpoint term retained

Let N be a natural number and [a,a+2N] be contained in [P,2P]. Assume
(2) throughout this closed interval for one integer G, and (3).
The proved second-derivative theorem applies with
lambda=u*h*P^(-3/4)/16 and curvature ratio C=32. `cell_sum_bound` gives

\[
 \left|\sum_{n=0}^{N-1}e(F_{G,\epsilon}(a+2n))\right|
 \le256N\sqrt{\frac{uhP^{-3/4}}{16}}
              +\frac4{\sqrt{uhP^{-3/4}/16}}.
 \tag{5}
\]

For any L>=0 with N<=L*P^(7/16), `cell_sum_power_bound` proves

\[
 \left|\sum_{n=0}^{N-1}e(F_{G,\epsilon}(a+2n))\right|
 \le\left(64L\sqrt u+\frac{16}{\sqrt u}\right)P^{3/8}.
 \tag{6}
\]

Indeed the first term in (5) is at most 64*L*sqrt(u)*P^(3/32),
and the second at most 16*P^(3/8)/sqrt(u). Both comparisons, including
the growing upper bound on h, are proved in Lean. No limit is taken
with h fixed. The empty sum is included.

The closed support contains one lattice step beyond the final summand.
Applications to a half-open carry cell must retain this condition, or
remove and bound a final summand. The subsequent
[weighted carry-cell proof](juggler_ooee_carry_cells_note.md) now performs
that partition and retains the final-term loss. The actual epsilon
values 0 and 1 are both covered.

## What this closes and what remains

The phase-specific curvature and the unweighted sums of e(F_G,0) and
e(F_G,1) are now formal. The audit
[AxiomCheckOOEECurvature.lean](../../formal/AxiomCheckOOEECurvature.lean)
selects every one of the module's 26 theorems.
Every selected theorem depends only on propext, Classical.choice, and
Quot.sound. The full project build also passes.

The subsequent weighted carry-cell proof closes the partition and partial
summation with z and 1-z. Nonzero carry Fourier modes, pointwise Fourier
remainder, finite discrepancy, and assembly into actual fibre production
remain separate obligations. In particular, (6) alone is not a bound
on the complete correlation in equation (12) of the written argument.

`OOEEProductionBound` remains explicit in `FateOEWeighted.lean`.
The unconditional Lean contagion exponent is still 100/203; its
strengthening to 5/8 is conditional on that production bound.
The failure-rate estimate needed for termination remains open.
