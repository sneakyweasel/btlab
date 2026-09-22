# First-derivative estimates and sublinear power cancellation

22 September 2026. Formalization of classical analytic inputs for Paper E.
The finite estimate is the Kusmin--Landau argument; see
[J. Arias de Reyna, On Kuzmin-Landau Lemma, Lemma 1](https://arxiv.org/html/2002.05982).
No mathematical novelty or optimal constant is claimed here.

## Finite discrete estimate

Let f be a real-valued sequence and delta>0. Suppose its increments
d(n)=f(n+1)-f(n), for 0<=n<N, lie in the interval from delta to 1-delta
and are either nondecreasing or nonincreasing. Then

\[
 \left|\sum_{n=0}^{N-1}e^{2\pi i f(n)}\right|\le\frac1\delta.
\]

The implemented hypothesis includes the last increment f(N)-f(N-1),
even though f(N) is not a summand. The N=0 case is included.
[KusminLandau.lean](../../formal/BTCalculus/KusminLandau.lean) proves the
bound directly, without an assumed correlation or exponential-sum bound.

Write e(t)=exp(2*pi*i*t). For 0<t<1, the coefficient

\[
 a(t)=-\frac12-\frac{i}{2}\frac{\cos(\pi t)}{\sin(\pi t)}
\]

satisfies a(t)(e(t)-1)=1. Its real part is constant and its imaginary
part is increasing. The latter fact follows from the sine subtraction
identity and positivity of sine between 0 and pi; no variation bound
is supplied as a premise.

Jordan's sine inequality gives |e(t)-1|>=4*delta on the prescribed
interval, hence |a(t)|<=1/(4*delta). With z(n)=e(f(n)), summation by
parts gives, for N>=1,

\[
 \sum_{n=0}^{N-1}z(n)
 =a(d(N-1))z(N)-a(d(0))z(0)
  +\sum_{n=0}^{N-2}\bigl(a(d(n))-a(d(n+1))\bigr)z(n+1).
\]

The variation sum telescopes because the imaginary parts are monotone.
Its norm bound is at most the sum of the two endpoint coefficient norms.
Adding the two boundary contributions gives 1/delta.

## Continuous derivative form and a varying gap

For a real a and natural N, assume f is continuous on the closed interval
from a to a+N and has derivative g on its interior. If g is monotone in
either direction and delta<=g(x)<=1-delta there, then

\[
 \left|\sum_{n=0}^{N-1}e^{2\pi i f(a+n)}\right|\le\frac1\delta.
\]

`exists_increment_deriv` places a mean value point strictly inside each
unit cell. The ordered cells transfer both the derivative bounds and
monotonicity to the actual discrete increments. `first_derivative_sum_bound`
then applies the finite theorem. This formalized version concerns the
derivative band between 0 and 1, not arbitrary integer bands.

`tendsto_phase_average_zero_of_gap` permits a gap delta(N) depending on
the prefix length. If every positive prefix satisfies its gap bounds,
the increments are monotone, and N*delta(N) tends to infinity, the
normalized complex averages tend to zero. This follows from the proved
bound, not from a cancellation hypothesis.

## Unconditional sublinear power theorem

[SublinearPowerCancellation.lean](../../formal/BTCalculus/SublinearPowerCancellation.lean)
proves, for every real c!=0 and 0<theta<1,

\[
 \frac1N\sum_{n=0}^{N-1}e^{2\pi i c n^\theta}\longrightarrow0.
\]

For c>0 choose a positive initial shift A large enough that
c*theta*A^(theta-1)<=1/2. The derivative c*theta*x^(theta-1) is positive
and decreasing. Taking delta=c*theta*(A+N)^(theta-1), the continuous
estimate proves the explicit bound

\[
 \left|\sum_{n=0}^{N-1}e^{2\pi i c(A+n)^\theta}\right|
 \le\frac1{c\theta(A+N)^{\theta-1}}.
\]

After division by N the right side is
((A+N)/N)*(A+N)^(-theta)/(c*theta), which tends to zero.
The existence of a suitable natural A is proved from derivative decay.
A general finite-prefix lemma removes the shift, including the sample
at zero. Complex conjugation handles negative c.

## Audit and remaining Paper E obligations

[AxiomCheckFirstDerivative.lean](../../formal/AxiomCheckFirstDerivative.lean)
audits all 25 theorems in the two modules. Their proofs use only the
standard logical dependencies propext, Classical.choice, and Quot.sound.
The ledger's advisory statement-coverage review remains separate from
kernel verification.

This completes the first-derivative input and a genuine base case for
power-phase cancellation. It does not prove Paper E Theorem 4.1:

- Higher noninteger powers and finite mixed-power phases still need a
  differencing induction with control of the actual shifted differences.
- Differences of powers are not silently identified with pure powers.
- The joint Fourier-to-box recurrence argument is still missing.
- `BoxRecurrence` therefore remains an explicit premise of the existing
  Lean assembly.

The version 0.3.0 manuscript, its PDF, and its selected 32-declaration
audit are unchanged. This subsequent progress has its own proof note and
audit; it supplies no termination or integer-realization theorem.
