# Explicit finite third- and fifth-derivative tests

22 September 2026. **EXACT — LEAN VERIFIED.** The finite statements
below are checked by Lean.
This supplies an alternative quantitative analytic input for Q1 of the
[effective OOE audit](juggler_effective_modular_return_audit.md).
It is classical derivative differencing; no new method is claimed.

## Statements

Write e(t)=exp(2*pi*i*t) and S=sum(e(f(a+n)),0<=n<N), with N a positive
integer. A derivative chain means functions f_0,...,f_r with f_0=f and
f_j'=f_(j+1) at every point of the closed interval [a,a+N], for j<r.
Let lambda>0. If the third derivative throughout this interval lies in
[lambda,4*lambda], or throughout in [-4*lambda,-lambda], then

\[
 |S|\le12N\max\{\lambda^{1/6},(N/2)^{-1/2},
                         (N\sqrt\lambda)^{-1/2}\}.
\]

If the fifth derivative lies throughout in [lambda,6*lambda], or
throughout in [-6*lambda,-lambda], then

\[
 |S|\le7N\max\{\lambda^{1/30},(N/6)^{-1/8},
                         (N\sqrt\lambda)^{-1/8}\}.
\]

These are `third_derivative_rate` and `fifth_derivative_rate` in
[HigherDerivative.lean](../../formal/BTCalculus/HigherDerivative.lean),
namespace `BTCalculus.HigherDerivative`. No small-curvature hypothesis,
monotonicity, assumed correlation estimate, or eventual threshold is used.
The bounds can exceed the trivial bound N.

Equivalent automatic-cutoff forms are |S|<=12N/sqrt(q_3) and
|S|<=7N/sqrt(q_5), where

\[
 q_3=\min\{\lambda^{-1/3},N/2,N\sqrt\lambda\},\qquad
 q_5=\min\{\lambda^{-1/15},(N/6)^{1/4},
                                  (N\sqrt\lambda)^{1/4}\}.
\]

For real A<=B, set L=floor(B)-floor(A). When L>0, the declarations
`third_derivative_real_interval` and `fifth_derivative_real_interval`
bound the actual sum over A<n<=B by the corresponding cutoff form with
N=L. They require the derivative chain and its signed top bound on
**[A,B+1]**. The one-unit extension supplies the final increment of the
underlying second-derivative test. It is an explicit hypothesis, not a
claim of the weaker support in the written source.

## Proof map

1. `chain_difference` and `difference_top_bounds` prove derivative chains
   and curvature bounds for actual shifted differences on the shrinking
   overlap. The latter uses the proved mean-value secant bounds.
2. `uniform_differencing` keeps an ambient length N for shorter overlaps.
   `higher_derivative_sum_bound` inducts over a list of integer windows,
   ending at the proved second-derivative estimate. Its nested bound is
   sqrt(2/H+4*previous) at each step. The actual correlations, support,
   and accumulated derivative scales are derived in the induction.
3. Negating the whole chain and conjugating the sum gives the negative
   sign case. An absolute-value curvature assumption alone is not used.
4. For order three, round q upward. The hypotheses 2q<=N,
   lambda*q^3<=1, q<=N*sqrt(lambda), q>=1 give constant 12.
   For order five, round q,q^2,q^4 upward. The hypotheses
   2(q+q^2+q^4)<=N, lambda*q^15<=1, q^4<=N*sqrt(lambda), q>=1
   give constant 7. All three roundings and overlap lengths are checked.
5. The displayed minima meet these hypotheses when q>=1. When q<1,
   the trivial sum bound proves the same conclusion. Reciprocal square
   roots of minima give the explicit maximum formulas.
6. `integer_sum_eq_range` is an exact finite-sum reindexing.
   `integer_support` proves the required support inclusion, including
   noninteger endpoints. There is no replacement of sample count by
   interval length without an error bound.

## Relation to the effective OOE theorem

The written OOE proof cites Arias de Reyna's
[explicit derivative estimate, v1](https://arxiv.org/html/2407.02094v1).
The formulas above are independently derived finite alternatives; they
are not a formalization of that source's exact 11-times-maximum formula.
The existing written proof remains unchanged.

The high OOE mode requires order five with derivative ratio six; the
remaining axis requires order three with ratio four. Their actual
derivative chains, signed estimates on the extended support, comparison
with the constant 32, and dyadic all-T bound (Q2) are now proved in the
[OOE specialization](juggler_ooe_effective_modes_note.md). Error assembly
(Q4) and bounded witness extraction (Q5) are now proved in the
[complete return module](juggler_ooe_effective_return_lean_note.md). Q3 is proved in
[FejerBox.lean](../../formal/BTCalculus/FejerBox.lean).
The effective theorem is included in Paper E 0.7.0's selected audit;
its separate ledger advisory coverage ruling remains pending.

## Verification and decision

The module compiles and is included in the default BTCalculus build.
[AxiomCheckHigherDerivative.lean](../../formal/AxiomCheckHigherDerivative.lean)
selects every theorem in this module; its
[recorded output](../../formal/AxiomCheckHigherDerivative.expected)
documents their dependencies. All 29 theorems use only `propext`,
`Classical.choice`, and `Quot.sound`. The full default Lean build passes
(9077 jobs). No added axiom, deferred proof, or compiler-evaluated
certificate is used. Jev's single-row advisory returned "covered" (0.63);
the final coverage ruling follows direct comparison of the quantified
English statement and the declarations. Repository registration checks
are recorded in the journal.

**PROMOTE** these explicit finite derivative estimates. The subsequent OOE
specialization and constant comparison are now proved; no new word,
modulus optimization, or general termination assertion is part of this result.
