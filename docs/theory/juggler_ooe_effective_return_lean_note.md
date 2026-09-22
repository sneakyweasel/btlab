# Effective OOE returns: complete Lean proof

22 September 2026. The quantitative obligations Q4 and Q5 are now proved in
[OOEEffectiveReturn.lean](../../formal/Problems/Juggler/OOEEffectiveReturn.lean).
Together with the previously proved mode estimate and finite Fejer box
inequality, this closes the entire effective OOE theorem. Independent
mathematical review remains open. The authorized Jev check is complete;
the ledger retains its human-proof label while the advisory packet's
coverage discrepancy remains open, as recorded below.

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

## Jev coverage review

On 22 September 2026 the user explicitly authorized sending only
`J-effective-ooe-modular-return` and its six covering declarations to Jev.
One fresh request to `jev-1.13.0` used 1792 input tokens and returned:

| Advisory question | Score |
| --- | --- |
| Declarations cover the claim | 0.22 |
| Claim is broader than the declarations | 0.89 |
| Declarations are narrower than the claim | 0.32 |
| A declaration is a different result | 0.13 |

These are separate advisory scores, not a probability that a Lean proof
is correct. Under the repository thresholds the packet is **not covered**.
Jev returned no explanatory prose, so its reason cannot be inferred from
these scores alone. The original verdict is retained in the coverage cache
and review queue; no repeated requests were made to obtain a higher score.

Local inspection found the following limitations in the submitted packet.
The standard exporter ends a declaration at `:=`, so `witnessCutoff`
appeared only as `def witnessCutoff (M : Nat) : Nat`, omitting its value
`2^2176*M^160`. The packet also omitted the definitions of `count` and
`ModularReturn`. The former is the cardinality of the filtered range
`0 <= t < T`. The latter asserts the actual OOE itinerary, the lower bound
on every prefix state, the strictly larger exit, and both endpoint residues.
The row additionally describes the proof's analytic dependency chain and
the word-code denominator; these are not separately displayed in the six
exported headers.

The direct local comparison confirms that `count_error` followed by
`error_power_bound` gives both errors for all positive natural M,T.
Unfolding `witnessCutoff` gives the stated positive count at the explicit
cutoff, and unfolding `ModularReturn` gives the actual orbit conclusions
of `exists_bounded_modular_return`. The OOE denominator-one observation
also follows from `PaperEModularReturn.runCode_den` at a=2,b=1:
the numerator is 9-8=1 and the gcd is gcd(5,1)=1. That theorem was not
among the six declarations sent to Jev.

**Ruling:** retain `EXACT — HUMAN PROOF` with `lean_trust: kernel`.
The main quantitative theorem remains kernel-checked; this review found
an incomplete advisory presentation, not a failed Lean proof. Promotion
of the whole ledger entry requires resolving that presentation discrepancy,
for example by separating its mathematical conclusion from proof metadata
and giving the relevant definitions in the coverage packet. No Lean source,
mathematical constant, manuscript theorem, or external-review status changed.

## Decision

**PROMOTE** the complete effective OOE formalization. Q1's application
and Q2-Q5 are closed. Independent review remains open; optimizing the
modulus exponent or moving to other words is outside this branch.
