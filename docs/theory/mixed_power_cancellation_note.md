# Noninteger mixed-power cancellation in Lean

22 September 2026. Classical analytic formalization for Paper E, with no
claim of new number theory or a quantitative estimate.

## Main theorem

Let S be a finite index set, with distinct positive noninteger real
exponents p_i. Let c_i be arbitrary real coefficients, at least one
nonzero. For every real A>0 and B,

\[
 \frac1N\sum_{n=0}^{N-1}
  \exp\!\left(2\pi i\sum_{i\in S}c_i(An+B)^{p_i}\right)
 \longrightarrow0.
\]

[PowerPhaseAsymptotics.lean](../../formal/BTCalculus/PowerPhaseAsymptotics.lean),
`tendsto_distinct_noninteger_power_average`, proves this statement without
an assumed correlation bound, derivative estimate, or equidistribution
theorem. Zero coefficients are removed before choosing the largest
exponent. The initial values at nonpositive An+B use Lean's real power;
only finitely many samples can be nonpositive, and they do not affect
the limit. In Paper E the progression is positive from the start.

The stronger intermediate theorem `tendsto_mixed_power_average_affine`
only requires the unique top exponent to be positive and noninteger and
its coefficient nonzero. Lower exponents may be arbitrary real numbers.
The integer m appearing there satisfies m<p_top<m+1; the final theorem
constructs m from the natural floor.

## Exact differences and derivative asymptotics

`HasPowerAsymptotics f p c` records a derivative tower D_k and real
coefficients a_k with

\[
 D_0=f,\qquad a_0=c,\qquad
 a_{k+1}=a_k(p-k),\qquad
 \frac{D_k(x)}{x^{p-k}}\longrightarrow a_k.
\]

For each fixed k, D_k has derivative D_(k+1) for all sufficiently large
x. The definition does not assume a single common threshold for all
derivative orders. It contains no exponential-sum cancellation premise.

The central difference lemma assumes g=f' eventually and
g(x)/x^r tends to d. For any fixed h>0 it proves

\[
 \frac{f(x+h)-f(x)}{x^r}\longrightarrow hd.
\]

The proof chooses a mean-value point t(x) strictly between x and x+h.
Then t(x) tends to infinity, t(x)/x tends to one, and
t(x)^r/x^r tends to one. Substitution into the exact mean-value identity
g(t(x))=(f(x+h)-f(x))/h gives the claimed limit, for arbitrary real r
and d, including d=0.

Applying this separately to each derivative proves

\[
 \operatorname{HasPowerAsymptotics}(f,p,c)
 \Longrightarrow
 \operatorname{HasPowerAsymptotics}
   \bigl(f(\,\cdot+h)-f,p-1,hcp\bigr).
\]

This is a theorem about the actual shifted difference. Differences of
powers are never identified with pure powers.

## Cancellation induction

For 0<p<1 and c>0, the first derivative is asymptotic to
cp*x^(p-1), and the second derivative is asymptotic to
cp*(p-1)*x^(p-2). Consequently, beyond a fixed threshold the first
derivative lies between (cp/2)*x^(p-1) and 1/2, and is decreasing.
The already proved first-derivative estimate bounds every shifted sum
by a constant times (A+N)^(1-p). After division by N this tends to zero.
The finite-prefix lemma removes the initial shift. Complex conjugation
handles negative c.

For m<p<m+1 with m>=1, every fixed positive integer difference has
exponent p-1 and a nonzero coefficient. Induction gives cancellation
of every such difference. The proved qualitative van der Corput theorem
then gives cancellation of the original phase. No uniformity in the
shift or derivative order is required.

## Mixed powers and progressions

The module proves the derivative tower explicitly for c*x^p, using
the recursively defined falling-product coefficients. At a higher
scale q>p every normalized derivative of this term tends to zero.
Finite addition therefore preserves the coefficient of the unique
largest power.

For x mapped to Ax+B with A>0, the kth derivative is
A^k*D_k(Ax+B). The ratio (Ax+B)^r/x^r tends to A^r; hence the transformed
leading coefficient is A^p*c at every order. This proves the progression
version before the finite-sum theorem is applied to natural samples.

## Audit and remaining paper work

[AxiomCheckPowerPhase.lean](../../formal/AxiomCheckPowerPhase.lean) audits
all 19 public theorems. The expected dependency report records only
propext, Classical.choice, and Quot.sound. Ledger statement-coverage
review is separate from kernel verification and remains pending.

This supplies the mixed-power Fourier cancellation input needed by
Paper E Theorem 4.1. The remaining formal work is to pass from all
nonzero Fourier modes to visits to the specified simultaneous box,
verify the particular exponent vector and box parameters, and discharge
`BoxRecurrence` in `PaperEModularReturn`. No quantitative discrepancy,
shrinking-target estimate, growing-depth uniformity, or termination
claim follows here.

The full paper formalization goal remains active. The version 0.3.0 PDF
and its selected 32-declaration audit are unchanged at this stage; they
will be refreshed after the remaining paper proof obligations close.
