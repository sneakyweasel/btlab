# Uniform effective OOE Fourier modes

22 September 2026. **EXACT — LEAN VERIFIED.** The finite statements
below are checked by Lean.
This closes the actual quantitative cancellation input Q2 and the
remaining Q1 application in the
[effective-return audit](juggler_effective_modular_return_audit.md).
The argument is a formalized application of classical derivative tests;
no new analytic method or external novelty is claimed.

## Statements

For real M,H>=1 and integers u,v, define

\[
 f_{u,v}(x)=\frac u2(1+2Mx)^{9/2}
              +\frac v{2M}(1+2Mx)^{9/4},\qquad
 e(y)=\exp(2\pi i y).
\]

Assume (u,v) is nonzero and abs(u),abs(v)<=H. For every real
P>=max(H^2,6),

\[
 \left|\sum_{P<n\le2P}e(f_{u,v}(n))\right|
 \le32H^{1/30}M^{1/4}P^{59/60}.
\]

For every positive integer T with H<=T^(1/4),

\[
 \frac1T\left|\sum_{0\le t<T}e(f_{u,v}(t))\right|
 \le128M^{1/4}H^{1/30}T^{-1/60}.
\]

These are `dyadic_mode_power` and `normalized_mode_bound` in
[OOEEffectiveModes.lean](../../formal/Problems/Juggler/OOEEffectiveModes.lean),
namespace `Problems.Juggler.OOEEffectiveModes`. The latter is precisely
the uniform mode input of the written effective OOE counting proof.
It holds for every admissible T, including the smallest values; it is
not an eventual convergence theorem. Integer moduli are a specialization
of the stated real-M result. No derivative, correlation, cancellation,
or dyadic summation estimate is an assumed hypothesis.

## Proof map

1. `powerChain` uses the falling factorial and the exact affine base
   1+2Mx. `deriv_powerChain` proves each derivative, and `modeChain`
   combines the two powers. At order five the result is exactly
   (945/2)*u*M^5*s^(-1/2)+(945/64)*v*M^4*s^(-11/4).
   On the low axis, the third derivative is
   (45/16)*v*M^2*s^(-3/4).
2. On the extended interval [P,2P+1], `support_scale` proves
   2MP<=s<=5MP. The fifth derivative has the sign of u and lies in
   the signed range with lower scale 100*abs(u)*M^(9/2)*P^(-1/2)
   and ratio six. The low-axis third derivative has the sign of v,
   lower scale (1/2)*abs(v)*M^(5/4)*P^(-3/4), and ratio four.
   The lower-power term is controlled in absolute value even when
   the coefficients have opposite signs. All support estimates include
   the one-unit extension required by the finite derivative test.
3. The [proved finite derivative tests](higher_derivative_finite_note.md)
   supply three rate terms in each case. `high_leading_rate`,
   `low_leading_rate`, `high_rate_terms`, and `low_rate_terms` bound
   them by at most twice the common frequency scale. The inequality
   H^2<=P controls the low-axis frequency exponent. Modulus factors
   are bounded using M>=1; no M-dependent threshold is introduced.
4. `dyadic_count_bounds` treats the actual integer count
   L=floor(2P)-floor(P), proving P/2<=L<=7P/6 and L>0. Applying the
   derivative tests to this exact length and their proved support
   inclusion gives constant 32 for both cases. `dyadic_mode_bound`
   performs the exhaustive integer-mode split, using abs(u)>=1 or
   abs(v)>=1 when the corresponding coefficient is nonzero.
5. `positiveSum_bound` uses finite strong induction with P=T/2 and
   K=floor(P). The exact half-open partition retains the sum through
   K and the dyadic interval (P,2P]. Its bound is
   64*H^(1/30)*M^(1/4)*T^(59/60)+14H^2. The inequality
   2^(59/60)>=3/2 pays for the induction. When P is below the retained
   threshold, the trivial whole-sum bound supplies the initial segment.
6. `range_endpoint_bound` proves that moving from 1,...,T to
   0,...,T-1 costs at most two. Since H>=1 and H<=T^(1/4), the
   resulting 16H^2 term is absorbed into the stated constant 128.

## Verification and scope

The source compiles without deferred proofs or added assumptions.
[AxiomCheckOOEEffectiveModes.lean](../../formal/AxiomCheckOOEEffectiveModes.lean)
selects every theorem, with output recorded in
[AxiomCheckOOEEffectiveModes.expected](../../formal/AxiomCheckOOEEffectiveModes.expected).
All 36 theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
The default Lean build passes (9078 jobs). The targeted repository run
has 223 passes, 15 skips and ten failures in concurrent publication and
OOEE work. The exact theorem-index freshness check, ledger declaration
check and Paper E gate pass on a snapshot of committed sources plus this
result. Concurrent drafts and publication edits are excluded from that
snapshot and from this result's commit. Details are in the journal.

The authorized single-row Jev advisory returned "doubtful" (coverage
0.44; claim-broader probability 0.62). Direct inspection gives the
following coverage ruling; the advisory is not a proof checker.

| English clause | Exact formal coverage |
| --- | --- |
| Real M,H>=1 and integer u,v | Real implicit parameters M,H, integer explicit u,v, hypotheses hM and hH |
| Nonzero cutoff mode | hne: u!=0 or v!=0; huH and hvH bound the real absolute values |
| The displayed phase | `mode`, with coefficients u/2 and v/(2M) and exponents 9/2,9/4 |
| Real P>=max(H^2,6) | Separate hP: 6<=P and hHP: H^2<=P in `dyadic_mode_power` |
| Exactly P<n<=2P | Integer `Finset.Ioc floor(P) floor(2P)` |
| Dyadic coefficient and rate | 32 times `amplitude M H` times P^(59/60); `amplitude` is H^(1/30)*M^(1/4) |
| Every positive integer T | Natural T with hT: 1<=T in `normalized_mode_bound` |
| Cutoff restriction | hHT: H<=T^(1/4) |
| Normalization and constant | The norm of the actual sum over `range T`, divided by T, is bounded by the displayed 128-times expression |

Both covering theorems have exactly these hypotheses. Neither assumes a
cancellation estimate, excludes negative coefficients, removes an axis,
or imposes an eventual size threshold. The English row is therefore
covered despite the advisory flag; no statement was weakened or retagged
solely to improve the advisory score.

The proof uses the laboratory's independently derived constants 12 and 7,
rather than asserting a formalization of the exact external derivative
formula quoted in the original written proof. It recovers the required
constants 32 and 128 and thus closes the same OOE analytic obligation.
The written theorem and its exponents are unchanged.

Q3, the finite half-open Fejer box inequality, is already kernel-checked.
Q4 still requires connecting these actual Fourier modes to the exact
return predicate, choosing the cutoff, counting threshold exclusions,
and proving the two explicit counting errors. Q5 requires extracting a
bounded witness and applying the existing orbit construction. Therefore
the effective return theorem still has its **EXACT — HUMAN PROOF** label.
This result does not change the Paper E manuscript or its selected audit.

## Decision

**PROMOTE** the uniform quantitative OOE mode bound. The next bounded
step is Q4, the exact counting and error assembly. Modulus optimization,
other words, and an infinite concatenation are outside this result.
