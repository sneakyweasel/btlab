# Polynomial stationary duals and the signed Collatz gap

22 September 2026. **CLOSE** direct iteration of the polynomial-dual
mechanism. The exact arithmetic classification and phase identities below
are kernel-checked. They give no new exponential-sum estimate or termination
theorem. The ledger retains its human-proof label pending advisory coverage.

## Problem

Does the rational cubic cancellation behind the first inverse-cell estimate
extend to smooth leading phases of longer Juggler words?

## Exact statement

Let o,L be positive integers, 2^L<3^o, and rho=3^o/2^L. For the smooth
odd-source phase f(s)=h*(2s+1)^rho/2, h>0, the stationary relation is
r=h*rho*(2s+1)^(rho-1). Its dual is

\[
 F(r)=\frac r2-\frac{h(\rho-1)}2
             \left(\frac r{h\rho}\right)^{\rho/(\rho-1)}.
\]

The dual exponent is

\[
 D=\frac{\rho}{\rho-1}=\frac{3^o}{3^o-2^L}.
\]

**Classification.** D is an integer if and only if 3^o=2^L+1,
if and only if (o,L)=(1,1) or (2,3). The corresponding degrees are
3 and 9. In particular no expanding word of length greater than three
has an integer dual exponent for its smooth leading monomial.

The stationary differentiation displayed here is an elementary written
calculation. Lean verifies the rational degree identity, the complete
arithmetic classification, and the specialized ninth-degree algebra.

## Current literature

The B-transform uses the phase f(s_r)-r*s_r; see
[Vandehey, equation (1) and Theorem 1.1](https://arxiv.org/pdf/1205.0090).
The present formula is its elementary monomial specialization, **KNOWN**.
The unit-gap exception list was already recorded in
[the Knight comparison](juggler_negative_lemma_eight_window.md), using
`mihailescu-2004-catalan`. Here it is proved elementarily in Lean, without
using Catalan's theorem. Neither the exception list nor the monomial
Legendre transform is a new number-theory theorem. Identifying this gap
as the exact limit of the laboratory's polynomial-dual shortcut is the
project-specific consequence.

## Branch budget

```text
Mathematical target     Classify integer stationary dual exponents of expanding words.
Novelty hypothesis      The denominator is precisely the signed Collatz cycle gap.
Falsifier               An integral dual exponent with a gap greater than one.
Already killed by?      Unit-gap exceptions and OOE guard failures are known;
                        their connection to polynomial duals was not recorded.
Existing machinery      OddCubicPhase, CollatzRational, elementary coprimality.
Maximum Phase-0 scope   Exact classification and phase identities in Lean;
                        decide whether direct iteration can supply deeper weights.
Promotion criterion     A new estimate for actual deeper itinerary weights.
Stop criterion          Exceptional smooth phases only, without parity-guard control.
```

## Balanced-ternary formulation

The numerator is a ternary place value and the competing scale is binary.
The proof uses coprimality and factorization; no digit representation is
needed.

## Why BT may be relevant

No new role for balanced ternary is asserted in this phase.

## Candidate operations / invariants

The invariant is the gap g=3^o-2^L. For a signed Collatz word with the
repository's nonnegative offset c_w, the minus-sign fixed-point equation
is g*q=c_w. The plus-sign equation is g*q=-c_w. Consequently the same
denominator controls the smooth Juggler dual degree and the rational
signed Collatz fixed point. These are distinct numerators: integrality
of c_w/g does not force g=1, whereas integrality of 3^o/g does.

## Experiments

No orbit scan or floor increase. The classification covers all positive
o,L. Lean is the verification tool for the exact results, not a bounded
enumeration of candidate exponents.

## Conjectures

No new conjecture is introduced.

## Counterexamples

The all-odd word of length two has multiplier 9/4 and dual degree 9/5.
Thus replacing one odd step by two already leaves the polynomial family.
Repeating OOE also leaves it: two copies have multiplier 81/64 and
dual degree 81/17.

The exceptional smooth OOE multiplier 9/8 does not remove its guards.
For every odd s>=3, the source s^8 has first odd images s^12 and s^18,
both odd. The advertised final E is therefore invalid, although the
smooth composite endpoint s^9 is an integer. This is an unbounded family
illustrating the already-recorded
[hidden-parity obstruction](juggler_cycle_cubic_induction.md).

## Formalization

[PolynomialDual.lean](../../formal/Problems/Juggler/PolynomialDual.lean)
contains `dualDegree_eq`, `rational_degree_iff`, `gap_coprime`,
`integral_degree_iff_gap_one`, `unit_gap_classification`,
`integral_degree_classification`, `rational_degree_classification`, and
`no_integral_degree_after_three`. `pullback_fixed_gap` links the same
gap to the existing rational Collatz word definition.

`ninth_stationary_algebra` and `ninth_stationary_index` verify the
parametrized ninth-degree phase. `half_monomial_antiperiodic` proves
the general wave identity used by `ninth_odd_antiperiodic` and
`ninth_odd_complete_mean_zero`.

No theorem here asserts that a nested floor phase equals its smooth
leading monomial, or estimates an incomplete sum or a selected sum.

## Results

**Arithmetic proof.** Coprimality of 3^o and 2^L gives gcd(g,3^o)=1,
so g divides 3^o exactly when g=1. To classify that case, L=1 gives
o=1 and L=2 is impossible modulo 3. If L>=3, reduction modulo 8 forces
o even, say o=2k. Then

\[
 (3^k-1)(3^k+1)=2^L.
\]

Both factors are positive powers of two, differing by two. The only
such pair is 2,4: if the smaller were divisible by four, so would be
the larger, contradicting their difference. Hence k=1 and L=3.

**Ninth-degree phase.** For rho=9/8, putting t=8r/(9h) gives
s=(t^8-1)/2 and

\[
 F(r)=\frac r2-\frac{2^{23}r^9}{3^{18}h^8}.
\]

For odd positive h, Q=3^18*h^8 is odd. With e(x)=exp(2*pi*i*x),
e(F(r+Q))=-e(F(r)) for every natural r, so the complete sum of
2Q terms is zero. This is exact cancellation, not an incomplete-sum
bound. The ordinary cubic case has Q=27*h^2 instead.

The exceptional words correspond to the actual positive 3n-1 fixed
point 1 and the cycle 5 -> 7 -> 10 -> 5, and by negation to negative
3n+1 cycles. This correspondence neither realizes these words as
Juggler cycles nor supplies any integer orbit escaping to infinity.

## Open questions

The first inverse-cell estimate remains valid at its stated scope and
review status. No result here controls a second actual predecessor
weight or the growing-depth pressure in `FateScaleAverage.lean`.
Noninteger dual exponents do not rule out other analytic methods,
perturbations of a shorter phase, or cancellations between frequencies.

## Decision

**CLOSE** direct extension of polynomial periodicity to arbitrary
longer smooth word phases. The classification retains a useful exact
connection, but the analytic promotion criterion is unmet. This is
not a closure of the existing perturbed cubic method or all possible
iteration arguments. Stop this phase.

Exactly one next question: can averaging the actual second-cell Fourier
frequencies recover a quantitative saving after both predecessor
restrictions, without replacing them by smooth unguarded words?

## Publication assessment

Status: **STRUCTURAL**. This is a kernel-checked consolidation and a
method boundary, not a new termination result or a paper candidate.
