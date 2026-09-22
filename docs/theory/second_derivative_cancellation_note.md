# Quantitative second-derivative cancellation

22 September 2026. Classical analytic input, kernel-checked in
[SecondDerivative.lean](../../formal/BTCalculus/SecondDerivative.lean).
This formalizes the second-derivative test used in the written OOEE proof;
it does not prove that proof's phase-specific curvature or carry estimates.
The classical resonance-partition argument appears in
[Jammes, Theorem 2.5](https://math.univ-cotedazur.fr/~pjammes/publications/diviseurs95.pdf).
No novelty or optimal-constant claim is made. Advisory statement coverage
remains pending, separately from Lean kernel verification.

## Exact continuous statement

Let N be any natural number, a a real number, lambda>0, and C>=1.
On the closed interval [a,a+N], suppose f has derivative g, and g has
derivative q. Assume either

\[
 \lambda\le q(x)\le C\lambda\quad\hbox{for every }x,
 \qquad\text{or}\qquad
 -C\lambda\le q(x)\le-\lambda\quad\hbox{for every }x.
\]

The sign is common throughout the interval. No derivative monotonicity
of q, correlation bound, or equidistribution hypothesis is assumed.
Writing e(t)=exp(2*pi*i*t), the theorem
`signed_second_derivative_sum_bound` proves

\[
 \left|\sum_{n=0}^{N-1}e(f(a+n))\right|
 \le 4CN\sqrt\lambda+\frac8{\sqrt\lambda}.
 \tag{1}
\]

The closed interval includes a+N, one lattice step beyond the final
summand. This endpoint is used by the last phase increment. The empty
sum N=0 is covered. For negative curvature the proof conjugates the sum.

On [a,a+2N], the analogous derivative hypotheses give

\[
 \left|\sum_{n=0}^{N-1}e(f(a+2n))\right|
 \le 8CN\sqrt\lambda+\frac4{\sqrt\lambda}.
 \tag{2}
\]

`odd_lattice_second_derivative_sum_bound` proves (2) by the actual affine
change of variable, whose second derivative has scale 4*lambda. If a
is an odd integer, these are precisely consecutive odd source positions.

## Finite proof and constants

For a real sequence F, put d(n)=F(n+1)-F(n). For U>=0 the discrete theorem assumes
for all 0<=i<=j<N the actual increment inequalities

\[
 \lambda(j-i)\le d(j)-d(i)\le U(j-i).
\]

For every 0<delta<=1/2, `increment_gap_sum_bound` proves

\[
 \left|\sum_{n<N}e(F(n))\right|
 \le (UN+2)\left(\frac{2\delta}{\lambda}+2+\frac1\delta\right).
 \tag{3}
\]

The proof retains the finite support and every endpoint:

1. Partition the indices by the integer floor of d(n). Monotonicity
   places all occupied bands in one integer interval of cardinality
   at most UN+2; unused bands cause no problem.
2. Within each band k, the indices with d(n)<k+delta and those with
   d(n)>k+1-delta each number at most delta/lambda+1. The proof bounds
   their index span using separation, then bounds cardinality by span+1.
3. The remaining indices form a consecutive interval. Subtract the
   integer linear phase k*n, whose exponential is one, and apply the
   proved Kusmin--Landau inequality to obtain a sum bound 1/delta.
   Both inequalities defining this middle block are inclusive.
4. The three pieces partition the band exactly. Summing their bounds
   over all bands proves (3).

Take U=C*lambda. If sqrt(lambda)<=1/2, choose delta=sqrt(lambda).
The second factor in (3) is at most 4/sqrt(lambda), giving (1).
If sqrt(lambda)>1/2, the trivial sum bound N suffices.

`secant_bounds` proves the mean-value comparison for every closed interval,
including a single point. Applied first to g, and then to the function
x mapped to f(x+1)-f(x), it gives the required discrete increment bounds.
Thus the continuous theorem proves its discrete hypotheses instead of
assuming a separate cancellation estimate.

## Consequence for the termination program

The [OOEE note](juggler_ooee_poor_fibre_tail_note.md), equations (6), (14),
and (15), now has this classical finite input available alongside the
proved first-derivative and differencing estimates. In equation (14),
N=O(P^(7/16)) and lambda is comparable to u*h*P^(-3/4). Equation (2)
then has precisely the two required terms

\[
 O\bigl(P^{1/16}\sqrt{uh}+(uh)^{-1/2}P^{3/8}\bigr).
\]

For fixed nonzero mode u and 1<=h<=P^(1/16), their written bound is
O(P^(3/8)). The phase-specific uniform curvature inequalities, splitting
into the actual carry cells, partial summation, carry Fourier error, and
finite discrepancy inequalities are not proved by this generic theorem.
The [subsequent formalization](juggler_ooee_curvature_note.md) now proves
that uniform curvature and the unweighted cell bound, with explicit
floor and size conditions. Carry partition, weighted sums, Fourier errors,
and finite discrepancy remain. Qualitative fixed-box counting does not
replace the quantitative discrepancy step here.

`OOEEProductionBound` remains an explicit Lean hypothesis. The unconditional
Lean contagion exponent remains 100/203; the written 5/8 improvement still
awaits the OOEE analytic formalization and independent review. The actual
failure-rate bound, universal termination, and integer escape remain open.

## Audit

[AxiomCheckSecondDerivative.lean](../../formal/AxiomCheckSecondDerivative.lean)
checks all 17 theorems. The accepted dependencies are only propext,
Classical.choice, and Quot.sound. No placeholder, custom axiom, or
compiler-trust proof is used.
