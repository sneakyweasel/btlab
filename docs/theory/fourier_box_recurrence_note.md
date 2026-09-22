# Fourier recurrence and completion of Paper E Theorem 4.1

22 September 2026. Classical analytic formalization, with no new
equidistribution theorem or quantitative estimate claimed.

## The qualitative Fourier criterion

[FourierBoxRecurrence.lean](../../formal/BTCalculus/FourierBoxRecurrence.lean)
proves the following on the unit torus of any finite dimension. Suppose
every nonzero integer Fourier mode has sample averages tending to zero.
Then the sample averages of every continuous complex-valued function
converge to its normalized Haar integral.

The proof computes the integral of each monomial from Mathlib's
orthonormality theorem and handles the zero mode separately. Linear
combinations inherit the limit. Mathlib's Stone-Weierstrass argument
establishes uniform density of these combinations. Both empirical
averaging and normalized Haar integration have norm at most one, so
uniform approximation passes the limit to every continuous function.

For every nonempty open set U and every natural T, some sample with
index at least T belongs to U. Urysohn's lemma provides a nonnegative
continuous function equal to one at a chosen point and supported inside
U. Its Haar integral is strictly positive. If the sequence avoided U
after T, the function's samples would eventually vanish and their averages
would tend to zero, contradicting the continuous-function limit.

The module identifies the open circle image of an interval (a,b), with
0<=a<b<=1, with the corresponding fractional-part condition. Products
of these intervals give simultaneous boxes. It also proves that a torus
monomial on real representatives is the exponential of the integer dot
product, matching the mixed-power cancellation theorem exactly.

## Distinct powers and the exact Paper E box

[PowerBoxRecurrence.lean](../../formal/BTCalculus/PowerBoxRecurrence.lean)
combines the Fourier criterion with
[mixed-power cancellation](mixed_power_cancellation_note.md). For distinct
positive noninteger p_i, arbitrary nonzero real w_i, A>0 and real B,
the vector w_i*(A*n+B)^p_i visits every fixed open fractional-part box
arbitrarily late. No cancellation or recurrence premise remains.

[PaperERecurrence.lean](../../formal/Problems/Juggler/PaperERecurrence.lean)
uses indices j=0,...,b and exponents 3^a/2^(j+1). They are distinct,
positive, and noninteger: equality to a natural number would identify
an odd numerator with an even multiple. The weights are 1/2 except at
j=b, where the weight is 1/(2M). The progression is 2M*t+1.

The chosen open intervals are (0,1/2) at j<b and
(1/(2M),2/(2M)) at j=b. Their endpoints lie in the unit interval for
every M>=1, including M=1. Their visits imply the weak lower-bound
conditions in the existing ReturnBox definition. Thus `box_recurrence`
proves BoxRecurrence for every natural a,b and M>0.

## Unconditional theorem and trust boundary

`PaperERecurrence.theorem41` has precisely the hypotheses a,b,M>0 and
2^(a+b)<3^a. Its conclusion combines:

- Infinitely many distinct actual starts above every bound, with the
  prescribed expanding prefix, no state below the start, and both
  endpoints congruent to one modulo 2M.
- The exact reduced denominator formula for the periodic-word code.
- Unbounded denominators at every fixed positive even-run length b.

The earlier conditional assembly remains available as a reusable lemma.
The new theorem applies it to a proved recurrence statement. It assumes
no exponential-sum estimate, equidistribution theorem, or termination
conjecture. The phase estimates are qualitative for fixed parameters;
there is no shrinking-target or growing-depth uniformity claim.

[AxiomCheckFourierRecurrence.lean](../../formal/AxiomCheckFourierRecurrence.lean)
audits all 19 new public theorems across the three modules. The paper's
combined audit includes the unconditional theorem and the main analytic
interfaces among 37 selected declarations. Only propext,
Classical.choice, and Quot.sound are permitted. Independent prose-to-Lean
coverage, specialist novelty review, and external publication remain
separate from this formal completion.
