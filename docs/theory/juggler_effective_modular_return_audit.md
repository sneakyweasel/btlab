# Audit of the effective OOE modular-return theorem

22 September 2026. Fresh internal AI-assisted proof audit of
`J-effective-ooe-modular-return`, first recorded in commit `31ebaf9c`.
This is a second derivation and source check by the same assistant, not
independent human review, external referee approval, or Lean verification.

## Verdict and scope

**PROMOTE: the written bounds survive this audit without changing any
constant or exponent.** The proof has been expanded at its compressed
steps: source regularity, the pure low-power mode, noninteger dyadic
endpoints, saturated circular intervals, and exact residue boundaries.
The sentence about the M=1 right endpoint was ambiguous; it now explicitly
excludes 1. This is a clarification of the displayed half-open box, not a
change in the predicate or its main term.

For positive integers M,T, the count in the
[proof note](juggler_effective_modular_return_note.md) still satisfies

\[
 |A_M(T)-T/(4M)|
 \le [5+128M^{1/4}(3+\log(T)/16)^2]T^{63/64}+8
 \le 2^{14}M^{1/4}T^{127/128}.
\]

The resulting witness bounds remain t<2^2176*M^160 and n<2^4354*M^322.
This audit treats the cited classical analytic theorem as an external
input. It checks its statement and the entire local deduction; it does not
independently reprove that source. No claim of external novelty is made.
The existing Paper E release and its selected Lean audit are unchanged.

## 1. Analytic input and uniformity

The pinned primary source is J. Arias de Reyna,
[*Explicit van der Corput's d-th derivative estimate*, v1](https://arxiv.org/html/2407.02094v1),
Theorem 11, equation (15), and Table 1. Its estimate uses the real interval
length, allows real endpoints, and requires continuous derivatives through
the chosen order and a positive two-sided bound for that derivative.
The order-3 and order-5 constants are all below 11. No small-curvature or
monotonicity assumption is needed for this cited theorem.

For the local application, M>=1 and x>0 make both phases smooth. Each
retained interval is (N,2N], with N>=max(H^2,6); hence floor(N)>5.
Neither the real endpoint nor the derivative-order hypothesis is lost.
For a negative derivative, conjugate the entire phase sum. Taking an
absolute value of the derivative without first proving a common sign
would not justify the application; the sign proof below is essential.

Put s=1+2Mx. On this interval, 2MN<=s<=5MN. Direct differentiation gives

\[
 f_h^{(5)}(x)=\frac{945}{2}h_1M^5s^{-1/2}
              +\frac{945}{64}h_2M^4s^{-11/4},
 \qquad
 f_{(0,h_2)}^{(3)}(x)=\frac{45}{16}h_2M^2s^{-3/4}.
\]

For h_1 nonzero, the absolute ratio of the second fifth-derivative term
to the first is at most H*s^(-9/4)/(32M). Since s>=H>=1, this is at most
1/32. This includes coefficients of opposite signs, large M, and the
axis h_2=0. The derivative has the sign of h_1. The lower and upper bounds
100*|h_1|*M^(9/2)*N^(-1/2) and 600 times the same scale follow from

\[
 \frac{945}{4\sqrt5}>100,\qquad
 \frac{2835}{4\sqrt2}<600.
\]

For h_1=0, h_2 is nonzero and the third derivative has its sign. The
corresponding constants 1/2 and 2 are valid because

\[
 \frac{45}{16\,5^{3/4}}>\frac12,\qquad
 \frac{45}{16\,2^{3/4}}<2.
\]

To check all three terms of the analytic maximum separately, use the
following table. The entries already include the factor 11 and enlarge
|h_i| to H for a positive exponent or to 1 for a negative exponent.

| Mode | First term | Second term | Third term |
| --- | --- | --- | --- |
| h_1 nonzero | 11*(6/N)^(1/16) | 11*(3600*H*M^(9/2)*N^(-1/2))^(1/30) | 11*(100*M^(9/2)*N^(9/2))^(-1/16) |
| h_1=0 | 11*(4/N)^(1/4) | 11*(8*H*M^(5/4)*N^(-3/4))^(1/6) | 11*((1/2)*M^(5/4)*N^(9/4))^(-1/4) |

For the high mode, divide by G=H^(1/30)*M^(3/20)*N^(-1/60).
The three quotients are at most 11*6^(1/16), 11*3600^(1/30), and
11*100^(-1/16), respectively: every remaining factor is at most one.
Each quotient is less than 22, so the chosen constant 32 is safe.
For the low mode, division by H^(1/6)*M^(5/24)*N^(-1/8) gives quotients
at most 11*4^(1/4), 11*8^(1/6), and 11*2^(1/4), all below 22.

The reduction of the low mode to the common scale uses precisely
H^(2/15)<=N^(1/15), followed by -7/120<=-1/60. The only modulus
enlargements are M^(3/20)<=M^(1/4) and M^(5/24)<=M^(1/4).
Thus the common normalized bound
32*H^(1/30)*M^(1/4)*N^(-1/60) is uniform in M. No threshold depending
on M, no missing coordinate-axis case, and no coefficient cancellation
remain hidden in it. The bound may exceed one; that is not a failure.

## 2. Initial segments, including small T

Retain consecutive intervals (T/2^(j+1),T/2^j] as long as their lower
endpoint is at least K=max(H^2,6). These intervals partition (R,T],
with 0<R<2K, even if their endpoints are nonintegral. If there are no
retained intervals, R=T<2K. There are exactly floor(R) remaining positive
integer indices. Changing the whole sum from 1,...,T to 0,...,T-1 adds
only the two endpoint terms, with norm at most two.

It follows that the discarded contribution is at most
floor(R)+2<=2H^2+14<=16H^2. For 1<=H<=T^(1/4), division by T bounds
this by 16*T^(-1/2), which is at most
16*M^(1/4)*H^(1/30)*T^(-1/60).
The retained contributions sum to less than
64*M^(1/4)*H^(1/30)*T^(59/60), because
1/(2^(59/60)-1)<2. This last comparison follows already from
59/60>3/4 and 2^3>(3/2)^4.

Thus the total constant is at most 80, below the stated 128. The
argument covers T=1 and the transition where an interval is first
retained; an eventual large-T condition is not being substituted for
the claimed all-T statement.

## 3. Half-open boxes and arbitrarily narrow residue intervals

The critical boundary question is whether the smoothing inequality is
pointwise at the original box endpoints. A null-boundary assertion alone
would not suffice for a finite sample that could hit those endpoints.

For an interval of length ell in (0,1), use the explicit expansions and
contractions in the revised proof. The expanded length is min(1,ell+2*delta)
and the contracted length is max(0,ell-2*delta). Empty and full intervals
are treated separately and unchanged. This is necessary when delta is
larger than the residue interval width. There is **no** assumption
delta<1/(2M).

For every shift with both coordinate distances strictly less than delta,
membership in B implies shifted membership in B^+, while shifted
membership in B^- implies membership in B. These implications are true
at the included left and excluded right endpoints. With product Fejer
kernel K, the remaining shifts have mass at most
q=1/((H+1)*delta). Positivity and total mass one then give, at every z,

\[
 (\mathbf1_{B^-}*K)(z)-q
 \le\mathbf1_B(z)
 \le(\mathbf1_{B^+}*K)(z)+q.
\]

This provides a direct derivation of both inequalities; it does not use
equidistribution or assume the sample avoids the boundary. The kernel
tail follows by integrating 1/(4*(H+1)*x^2) over both sides of the circle.
The product tail is a union bound over the two coordinates, without
any independence assumption on the sample points.

Each coordinate length changes by at most 2*delta, so the box volume
changes by at most 4*delta. Each interval coefficient is bounded by
1/max(1,|h|), including h=0; the Fejer multiplier is at most one.
Summing over all nonzero modes of the two-dimensional cutoff gives at
most (1+2*sum(1/h,h=1,...,H))^2-1 <= (3+2*log(H))^2. Negative modes
and both axes occur in this sum. The constant coefficient is exactly the
expanded or contracted volume.

For H>=3 choose delta=(H+1)^(-1/2)<=1/2. Then 4*delta+q=5/sqrt(H+1).
For H=1,2, the asserted right side already exceeds the trivial discrepancy
bound one. Consequently the claimed box estimate holds for all H>=1,
with no loss depending on the box location or width.

## 4. Exact predicate, assembly, and witness

For x>=0 and integers m>=1 and 0<=r<m, divide floor(x) by m. If its
remainder is r', then fract(x/m)=(r'+fract(x))/m. This proves the
equivalence of floor(x)=r modulo m and membership in the half-open
interval with endpoints r/m and (r+1)/m. It also fixes both endpoint
conventions without a limiting argument.

At m=2, r=0 the parity condition excludes fractional part 1/2. At M=1
the exit interval is [1/2,1), with 1 excluded and fractional part zero
rejected. Such boundary hits are real possibilities: if
s=(1+6M)^4, then both real powers are integers, the exit residue is 1,
but u is odd. The parity box correctly rejects this parameter.

The floor identity also proves that this count is precisely the
a=2,b=1 specialization of `ReturnParameter` in
[PaperECorollaries.lean](../../formal/Problems/Juggler/PaperECorollaries.lean).
The threshold there is 2^(2^(b+1))=16. The excluded initial parameters
number min(T,1+floor(7/M)), at most eight. Only their box hits are actually
subtracted, so an error allowance of eight is valid in both directions.

For H=floor(T^(1/32)), H>=1 and H<=T^(1/4). Also H+1>T^(1/32),
H^(1/30)*T^(-1/60)<=T^(-1/64), and 2*log(H)<=log(T)/16.
These are inequalities in the needed directions, even at perfect
32nd powers. They prove the first counting bound.

To absorb the logarithm, the derivative of
g(x)=(3+x/16)^2*exp(-x/128) has the sign of 208-x for x>=0.
Its maximum is 256*exp(-13/8)<64. After division of the counting error
by T, both 5*T^(-1/64) and 8/T can be enlarged to their corresponding
constants times M^(1/4)*T^(-1/128). The resulting constant is
5+128*64+8=8205<16384. This verifies the second bound.

At T=2^2176*M^160, its relative error is at most
2^14*M^(1/4)/(2^17*M^(5/4))=1/(8M). The main term is 1/(4M), so
the count is at least T/(8M)>0. This integer T is admissible for every M.
For a counted t<T, integrality gives 1+2Mt<=2MT-(2M-1)<2MT, producing
the strict start bound n<(2MT)^2=2^4354*M^322.

Finally the actual orbit is s^2, s^3, floor(s^(9/2)), floor(s^(9/4)).
The nested-root identity holds exactly. Since s>=16, s^(1/4)>=2,
so floor(s^(9/4))>=2*s^2>s^2. The odd images are also above the start.
Both endpoints are 1 modulo 2M. These are the hypotheses and conclusions
of the existing `modular_return_of_box` at k=1,b=1, with 8<9.

## 5. Precise Lean obligations and current status

This table separates the missing quantitative proof from existing exact
construction and qualitative convergence. The dependency order is
Q1 to Q2; Q2 and Q3 to Q4; Q4 and the existing construction to Q5.

| Obligation | Required statement | Existing reusable material | Status |
| --- | --- | --- | --- |
| Q1 | Explicit derivative estimates at orders 3 and 5 sufficient for the OOE bound, with real endpoints and both signs | HigherDerivative plus OOEEffectiveModes | Closed for the OOE application: independent finite tests with constants 12 and 7 recover the dyadic constant 32, including actual derivative chains and extended support; the exact cited formula (5) is not claimed as formalized |
| Q2 | For M,H,T>=1 and H<=T^(1/4), every nonzero cutoff mode has normalized norm at most 128*M^(1/4)*H^(1/30)*T^(-1/60) | OOEEffectiveModes | Closed: `normalized_mode_bound`, including both axes, signs, real dyadic endpoints, the discarded initial segment and the two endpoint terms |
| Q3 | For integers H,T>=1, any T samples, and every half-open torus box, discrepancy is at most 5/sqrt(H+1)+(3+2*log(H))^2*E_H, where E_H bounds every nonzero cutoff mode | FejerKernel, FejerArc, FourierDiscrepancy, and FejerBox | Closed: `BTCalculus.FejerBox.finite_box_discrepancy`, including saturation and every pointwise boundary case |
| Q4 | For the exact ReturnParameter(2,1,M,t) count, both displayed all-M, all-T errors | Existing count and ReturnParameter definitions, exact root/box guards | Cutoff, threshold count, and explicit error assembly unformalized |
| Q5 | Positive count at T=2^2176*M^160 yields a witness with the strict t and n bounds and ModularReturn(2,1,M,n) | modular_return_of_box, with k=1,b=1 | Quantitative extraction unformalized; orbit implication already formalized |

In particular, `tendsto_fract_box_count` proves a qualitative limit and
does not supply Q3. Assuming Q1 or Q2 in a new Lean theorem would verify
only a conditional implication. The universal effective theorem cannot
receive a Lean-verified label until the whole dependency chain is closed.
Q3 is now kernel-checked; its [proof map and exact scope](finite_fejer_box_note.md)
record all hypotheses and the 72-theorem dependency audit. The covering
theorem constructs the smoothing bounds rather than assuming them.
Q1 now has an independently proved alternative: `third_derivative_rate`,
`fifth_derivative_rate`, and their real-interval forms. Their
[proof map](higher_derivative_finite_note.md) records the exact support.
The [OOE specialization](juggler_ooe_effective_modes_note.md) proves the
actual derivative chains and signed bounds on that support, verifies the
constant 32, and proves the uniform all-T constant 128 by finite dyadic
induction. Thus Q1's application and Q2 are closed. This does not assert
formalization of the exact external formula (5). Q4 and Q5 remain open;
the universal effective return theorem is not yet Lean verified.

## 6. Verification record and decision

The existing 22 exact scalar checks and 32768 actual-prefix comparisons
were retained. Added regression checks cover rational residue endpoints
(including the wrap at 1), actual perfect-power boundary hits, real
dyadic partitions including tiny T, and the exact threshold-exception
count for small and very large moduli. These checks support the arithmetic
and guard audit; they do not test or prove the analytic cancellation rate.
Integration, ledger, registry, branch-index, and targeted theorem checks
pass: **182 passed, 15 skipped**. The saved exact report matches a fresh
recomputation, the generated ledger and branch index are current, and the
existing Paper E source/manifest consistency check passes. No Lean source
was changed in that initial audit. The subsequent Q3 formalization is
recorded separately in the proof maps linked above, as is the later
alternative higher-derivative input.

**PROMOTE** the clarified written result. No counterexample or incorrect
constant was found in this internal audit. Independent external review
and the quantitative Lean obligations above remain open. Optimizing the
modulus exponent and extending beyond OOE are separate research decisions.
