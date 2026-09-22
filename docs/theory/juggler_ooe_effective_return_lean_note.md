# Effective OOE returns: complete Lean proof

22 September 2026. The quantitative obligations Q4 and Q5 are now proved in
[OOEEffectiveReturn.lean](../../formal/Problems/Juggler/OOEEffectiveReturn.lean).
Together with the previously proved mode estimate and finite Fejer box
inequality, this closes the entire effective OOE theorem. Independent
mathematical review remains open. The ledger retains its human-proof label
until the separately authorized advisory coverage check and direct ruling.

## Statement and exact coverage

For all natural M,T>=1, let A_M(T) count parameters 0<=t<T with
s=1+2Mt>=16, floor(s^(9/2)) even, and floor(s^(9/4))=1 modulo 2M.
The formal statements give

\[
|A_M(T)-T/(4M)|
\le [5+128M^{1/4}(3+\log(T)/16)^2]T^{63/64}+8
\le 2^{14}M^{1/4}T^{127/128}.
\]

At T=2^2176*M^160, they give A_M(T)>=T/(8M)>0 and an actual
OOE modular return with t<T and n=(1+2Mt)^2<2^4354*M^322.
Every prefix state is at least n, the exit is strictly greater than n,
and both endpoints are 1 modulo 2M.

| English clause | Covering declaration |
| --- | --- |
| Exact natural-floor predicate, including M=1 and both boundary conventions | `return_parameter_iff` |
| First displayed error, for every positive M,T | `count_error` |
| The displayed first error is at most the second | `error_power_bound` |
| Combined simpler count bound | `count_error_power` |
| Explicit cutoff T=2^2176*M^160 | `witnessCutoff` |
| Count at least T/(8M) and strictly positive | `count_at_witnessCutoff` |
| Strict t and n bounds and actual orbit conclusions | `exists_bounded_modular_return` |

`ModularReturn` is the existing exact orbit predicate in
[PaperEModularReturn.lean](../../formal/Problems/Juggler/PaperEModularReturn.lean),
not a hypothesis about a symbolic word. The witness invokes the proved
`modular_return_of_box` at k=1,b=1. No cancellation estimate, smoothing
assumption, eventual threshold, or existence premise remains undischarged.

## Proof structure

`sample_mode` identifies the concrete product character with the exact
two-power phase in `OOEEffectiveModes.normalized_mode_bound`.
`sample_mem_box` identifies its half-open rectangle with ReturnBox(2,1,M).
The finite Fejer theorem then yields `box_discrepancy` for every admissible
integer Fourier cutoff. The residue equivalence uses Euclidean division
of the natural floor and applies at included left and excluded right
endpoints; no boundary-avoidance assertion is used.

The cutoff is floor(T^(1/32)). Its lower bound, upper bound, square-root
error, rate exponent, and logarithm comparison are proved separately.
The resulting `box_discrepancy_power` is valid even at T=1 and at exact
32nd powers. `threshold_count_bound` proves the difference between the
box count and ReturnParameter count is at most eight by an inclusion
of the discarded indices in range(8).

For logarithm absorption put u=log(T)/128>=0. The cubic Taylor lower
bound for exp(u) and the identity

\[
1+u+u^2/2+u^3/6-(3+8u)^2/64
=u(u-2)^2/6+(u-5/4)^2/6+115/192
\]

give (3+log(T)/16)^2<=64*T^(1/128). This proves the same stated constant
without requiring the maximization argument used in the original prose.
The final coefficient comparison is 5+128*64+8=8205<16384.

`witnessCutoff_root` proves T^(1/128)=131072*M^(5/4). The error is
exactly T/(8M) at this cutoff, so the count is positive. Finite-set
nonemptiness extracts t. The strict inequality 1+2Mt<2MT, which uses
integrality and M>=1, gives the stated strict start bound.

## Dependencies and publication

The [mode proof map](juggler_ooe_effective_modes_note.md),
[finite derivative tests](higher_derivative_finite_note.md), and
[Fejer proof map](finite_fejer_box_note.md) specify the complete analytic
chain. It is an independent sufficient formal proof, not a claim that
the precise external Arias de Reyna formula has been formalized.

[AxiomCheckOOEEffectiveReturn.lean](../../formal/AxiomCheckOOEEffectiveReturn.lean)
checks all 23 theorems; its
[saved output](../../formal/AxiomCheckOOEEffectiveReturn.expected) contains
only propext, Classical.choice, and Quot.sound (or subsets).
Paper E 0.7.0 expands its selected audit from 49 to 56 declarations and
includes the full transitive local analytic chain in its source archive.

The constants remain impractical. The OOE word-code denominator is one;
this does not quantify the paper's large-denominator family. There is no
new arbitrary-word, cycle, termination, or infinite-concatenation result.

## Decision

**PROMOTE** the complete effective OOE formalization. Q1's application
and Q2-Q5 are closed. Independent review remains open; optimizing the
modulus exponent or moving to other words is outside this branch.
