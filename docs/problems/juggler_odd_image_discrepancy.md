# Juggler odd-image discrepancy

Status: **PROMOTE** (22 September 2026): a written square-root-plus-epsilon
bound now sharpens the historical estimate below. The analytic proof is
AI-assisted and awaits independent review. Lean checks its exact cubic
phase identities, not the analytic estimate. The older census record is
retained as history; the current result and decision are at the end.

Follow-up of the parked image-parity census. This page records that
historical census and the later one-step analytic theorem. Neither
establishes an all-depth parity law or claims that every positive
integer reaches 1.

## Problem

Can the odd-start sign sequence \(s(n)=(-1)^{\lfloor n^{3/2}\rfloor}\)
be given an explicit sublinear discrepancy bound on intervals, and
does that cancellation survive on sets produced by \(J\)?

## Exact statement

Write \(S_O(N)=\sum s(n)\) over odd \(n\le N\). Phase 0 asks for
an explicit \(F(N)=o(N)\) with \(|S_O(N)|\le F(N)\), obtained from
the cell multiplicities \(c_m\) or from the exact fractional-part
form of \(s\). After an interval bound exists, the same sum is
evaluated on \(J([1,N])\), \(J^{2}([1,N])\), and selected Atlas
words. Totality is unclaimed.

## Current literature

- Parent census [juggler_parity_discrepancy.md](juggler_parity_discrepancy.md)
  **PARK** / `IMAGE_PARITY_CENSUS`. \(D_O=-S_O/2\).
- `odd_preimage_unique` / `odd_preimage_iff` —
  **EXACT — LEAN VERIFIED**.
- `floorPower_odd_macro_direction` —
  **EXACT — LEAN VERIFIED**.
- Even-cell \(|D_E|\le\lfloor\sqrt N\rfloor+1\) —
  **EXACT — HUMAN PROOF**; not the target.
- 2-adic bridge, landing-θ, PE / residual / LD model —
  **CLOSE**. Do not reopen.
- Prasad–Prasad 2025 (`prasad-prasad-2025-juggler-like`) —
  motivation only.
- Van der Corput / Erdős–Turán —
  **KNOWN** analytic tools, applied here to `n^{3/2}/2` mod 1.

Project relationship: **extended** from the parked census.
Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Prove |S_O(N)| <= F(N) with F=o(N) for
                        s(n)=(-1)^{floor(n^{3/2})} on odd n;
                        then test S_O on J([1,N]) and J^2([1,N]).
Novelty hypothesis      Cell pairing cancellation, or an explicit
                        fractional-part discrepancy rate
Falsifier               Pairing is linear variation only; no honest
                        F; images concentrate one sign
Existing machinery      odd_preimage_unique; parity_discrepancy D_O;
                        floor_power; follows_itinerary / image_after
Maximum Phase-0 scope   Exact S_O; c_m prefix; pairing/runs;
                        one analytic rate; image/word tests on
                        the existing grids; no CUDA; no Lean ANT
Promotion criterion     Explicit F=o(N) with a proof, and a
                        transfer statement on J-images
Stop criterion          Pairing useless and rate only KNOWN
                        method with no transfer; machinery gravity;
                        halt claim; promoting N^{1/3}
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The 2-adic / BT bridge is closed.

## Candidate operations / invariants

- \(S_O=-2D_O\) —
  **EXACT — HUMAN PROOF**
- \(c_m\in\{0,1\}\) —
  **EXACT — LEAN VERIFIED**
- Adjacent pairing bound —
  **REFUTED** as a sublinear estimate
- \(|S_O(N)|\ll N^{5/6}\) —
  **EXACT — HUMAN PROOF**
- Observed \(N^{1/3}\) —
  **OBSERVATION**, not promoted
- Interval bound on \(J([1,N])\) without transfer —
  not claimed
- `parity_frequency_theorem` —
  stays false
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.odd_image_discrepancy`
- Records: [juggler_odd_image_discrepancy.md](../research/juggler_odd_image_discrepancy.md),
  [juggler_odd_image_discrepancy.json](../research/juggler_odd_image_discrepancy.json)
- Dataset: `data/research/juggler/parity_discrepancy_next/`
- Tests: `tests/research/juggler_sequence/test_odd_image_discrepancy.py`

The historical census used no GPU and added no Lean file. The cubic
continuation below now has a separate exact-algebra module.

## Conjectures

None opened. The \(N^{1/3}\) envelope is not entered as a
conjecture.

## Counterexamples

- Adjacent cell pairing as a sublinear variation bound: variation
  over `#odds` is `1.0`
  on `n<=1000000`.
- “`N^{1/3}` is proved”: descriptive slope
  `0.34595847` on `[1000, 1000000]`.

## Formalization

The historical census added none; the cell uniqueness lemma already
existed. The cubic continuation now verifies exact phase identities in
`OddCubicPhase.lean`. The further `CubicInverseCell.lean` module checks
the perturbed phase algebra, sign factors, and exponent margins.
The analytic number theory remains a written proof.

## Results

Classification **ODD_IMAGE_DISCREPANCY_GREEN**.

S_O(N) = -2 D_O(N) and the cell rewrite S_O = sum_m (-1)^m c_m with c_m in {0,1} are exact. Adjacent pairing has linear variation and is not a cancellation theorem. The fractional-part identity plus van der Corput / Erdős–Turán give the explicit interval bound |S_O(N)| << N^{5/6}. The observed N^{1/3} envelope is not promoted. One-step Juggler images stay small relative to |A_odd|; that is a census, not a transfer theorem.

On `n<=1000000`: `S_O=146`,
`max|S_O|=256` at `n=985351`.
`c_m<=1` on the prefix: `True`.

## Open questions

Sharpen \(N^{5/6}\) toward the census envelope, or prove a
transfer estimate for \(S_O(J([1,N]))\). Do not iterate by
numerics. Do not claim termination.

## Historical decision

**PARK**. S_O(N) = -2 D_O(N) and the cell rewrite S_O = sum_m (-1)^m c_m with c_m in {0,1} are exact. Adjacent pairing has linear variation and is not a cancellation theorem. The fractional-part identity plus van der Corput / Erdős–Turán give the explicit interval bound |S_O(N)| << N^{5/6}. The observed N^{1/3} envelope is not promoted. One-step Juggler images stay small relative to |A_odd|; that is a census, not a transfer theorem. Do not claim
termination. Do not flip `parity_frequency_theorem`.

Best next question: prove a transfer bound for \(S_O\) on
\(J([1,N])\), or replace \(N^{5/6}\) by an effective
\(N^{1/2+\varepsilon}\) estimate without a Weyl engine.

## Publication assessment

Status: `EXPLORATORY`. An exact cell rewrite plus a classical
discrepancy rate on one sequence, not a paper candidate and not a
Juggler totality result.

## Rational cubic continuation (22 September 2026)

### Triage

```text
Mathematical target     |S_O(N)| = O_epsilon(N^(1/2+epsilon)).
Novelty hypothesis      The exact rational cubic dual phase has zero mean
                        at odd harmonics; even resonances are summable.
Falsifier               A frequency range or a boundary error exceeds the rate.
Already killed by?      No: the qualitative Hardy shortcut has no shrinking-target
                        rate; this uses a quantitative arithmetic identity.
Existing machinery      Classical B-transform and cubic Gauss-sum estimates;
                        the existing odd-image discrepancy problem.
Maximum Phase-0 scope   One written interval estimate; Lean for the exact
                        stationary-point and finite-period identities only.
Promotion criterion     Uniform frequency bounds, resonances, and endpoints close.
Stop criterion          Unproved analytic input or an asserted image-set transfer.
```

### Statement and coverage

**EXACT — HUMAN PROOF**, AI-assisted, pending independent review.
For every epsilon > 0 there is C_epsilon such that, for every real
P >= 2 and every interval I contained in (P,2P],

\[
 \left|\sum_{\substack{n\in I\cap\mathbb N\\n\text{ odd}}}
       (-1)^{\lfloor n^{3/2}\rfloor}\right|
 \le C_\varepsilon P^{1/2+\varepsilon}.                 \tag{C1}
\]

Dyadic summation yields
the same bound for S_O(N), with P replaced by N. In particular,

\[
 \#\{n\le N:n\text{ odd},\ T(n)\text{ odd}\}
       =N/4+O_\varepsilon(N^{1/2+\varepsilon}).          \tag{C2}
\]

The interval bound is in the ambient scale P, not in the length of I.
No iterated-image or growing-depth uniformity is asserted. This replaces
the one-step 5/6 error in this dossier; it does not revise Paper B's
published mixed-mode exponents or establish the live-pressure hypothesis.
No priority claim is made for the analytic application.

The exact algebra in (C4)-(C5) and the complete-period cancellation are
kernel-checked in
[OddCubicPhase.lean](../../formal/Problems/Juggler/OddCubicPhase.lean).
The B-transform, complete-sum inequalities, Fourier completion,
resonance average, and Vaaler assembly below are written mathematics,
**not** Lean theorems. The separate algebra ledger row retains HUMAN
PROOF pending advisory statement coverage; no new external submission
has been made.

### Analytic inputs

Put e(x)=exp(2*pi*i*x). The following standard results are used with
uniform implied constants.

1. The C4 van der Corput transform: if f'' is comparable to T/M^2,
   |f'''| is bounded by a constant times T/M^3, and |f''''| by
   a constant times T/M^4 on an interval of length at most M, the
   transform has error O(M/sqrt(T)+log(2+f'(b)-f'(a))) for amplitude 1.
   See [Vandehey, Theorem 1.1](https://arxiv.org/pdf/1205.0090), which
   states Huxley's Lemma 5.5.3. Endpoint conventions change the result
   by the same permitted error. The older C3 error is insufficient here.
2. For U(q,a,b)=sum over r mod q of e((a*r^3+b*r)/q), with (a,q)=1,
   \(|U(q,a,b)|\ll_\delta q^{1/2+\delta}(q,b)^{1/2}\).
   This is d=1 in
   [Brüdern–Rydin Myerson, Lemma 4.2](https://arxiv.org/pdf/2409.16795).
   Their equation (4.4) is stronger. Coefficients may be reduced modulo
   q, so their natural-number presentation permits the signed integers
   used below.
3. Write q=q_2*q_3, where q_2 contains exactly the prime-power factors
   of exponent 1 or 2 and q_3 those of exponent at least 3. Set
   kappa(q)=q_2^(1/2)*q_3^(1/3). Uniformly in b and (a,q)=1,
   \(|U(q,a,b)|\ll_\delta q^{1+\delta}/\kappa(q)\), by
   [Brandes–Parsell–Poulias–Shakan–Vaughan, Lemma 4.1](https://arxiv.org/pdf/2001.05629).
4. Vaaler's sawtooth approximation: a degree-H polynomial with nonzero
   coefficients O(1/|h|) approximates psi(x)={x}-1/2 with error at most
   E_H(x)=F_H(x)/(2(H+1)), where F_H is the Fejer kernel of degree H.
   At integers the convention psi=-1/2 is still allowed: the polynomial
   is zero there and E_H=1/2. This is the same approximation used in
   [Paper B, Section 4.2](../theory/juggler_parity_discrepancy_note.md).

We allow arbitrary positive delta in intermediate estimates, then
choose it sufficiently small in terms of the epsilon in (C1).

### Exact transform and odd-harmonic completion

For 1 <= h <= sqrt(P), set

\[
 S_h(I)=\sum_{n\in I,\ n\text{ odd}}e(hn^{3/2}/2),\qquad
 f_h(s)=\frac h2(2s+1)^{3/2}.
\]

Use s=(n-1)/2. On the source interval, uniformly in h,
f_h''(s)=(3h/2)(2s+1)^(-1/2),
f_h'''(s)=-(3h/2)(2s+1)^(-3/2), and
f_h''''(s)=(9h/2)(2s+1)^(-5/2).
Thus input 1 applies with M=P and T=h*P^(3/2), including subintervals.
The dual integers r range over an interval of size O(h*sqrt(P)) with
r comparable to h*sqrt(P), and

\[
 S_h(I)=e(1/8)\sum_r\frac{2\sqrt r}{3h}
       e\left(\frac r2-\frac{2r^3}{27h^2}\right)
       +O(P^{1/4}h^{-1/2}+\log(2+h\sqrt P)).           \tag{C3}
\]

Indeed the stationary point and its curvature give exactly

\[
 s_r=\frac{(2r/(3h))^2-1}{2},\quad
 f_h(s_r)-rs_r=\frac r2-\frac{2r^3}{27h^2},\quad
 f_h''(s_r)=\frac{9h^2}{4r}.                           \tag{C4}
\]

Lean declarations: `stationary_sqrt`, `stationary_derivative`,
`stationary_phase`, and `stationary_curvature`. They check these values
at the specified point; they do not assert the analytic transform.

Suppose h is odd and put q=27h^2, which is odd. The dual wave z(r)
satisfies z(r+q)=-z(r), because its phase increment is

\[
 q/2-6r^2-6rq-2q^2\equiv 1/2\pmod1.                 \tag{C5}
\]

Consequently its complete mean over 2q is zero. Lean declarations:
`halfCubic_antiperiodic`, `dual_odd_antiperiodic`, and
`dual_odd_complete_mean_zero`.

We need a bound for incomplete periods as well. Take the unnormalized
DFT with coefficient b modulo 2q. It is zero for b even. For b odd,
splitting the two half-periods gives

\[
 \widehat z(b)=2U\left(q,-2,\frac{q-b}{2}\right),\qquad
 |\widehat z(b)|\ll_\delta q^{1/2+\delta}(q,b)^{1/2}.
\]

Here the cubic coefficient -2 is a unit modulo odd q. Fourier completion
of any interval of at most one period bounds its sum by
O_delta(q^(1/2+delta)) times
sum_{1<=b<=q}(q,b)^(1/2)/b. The latter is at most

\[
 (1+\log q)\sum_{d\mid q}d^{-1/2}\ll_\delta q^\delta.
\]

This follows by majorizing (q,b)^(1/2) by the sum of sqrt(d) over
common divisors and summing multiples of d. Full periods contribute
zero. Thus every dual interval has sum O_delta(q^(1/2+delta)), after
renaming delta. Partial summation with the positive monotone weight
2*sqrt(r)/(3h), whose supremum and variation are O(P^(1/4)*h^(-1/2)),
now gives

\[
 |S_h(I)|\ll_\delta P^{1/4}h^{1/2+\delta}
                    +\log(2+P),\qquad h\text{ odd}. \tag{C6}
\]

### Even harmonics: retain and average the resonant mean

For h=2j, put Q=54j^2. The dual wave is
z_j(r)=e((-r^3+(Q/2)r)/Q). Let

\[
 G(j)=U(Q,-1,Q/2),\qquad c(j)=\sqrt j\,|G(j)|/Q.
\]

Its mean is G(j)/Q and need not vanish. For example G(1)=18: the
wave has period 27 and reduces to e(13*r^3/27); multiples of 3
contribute 9 per period, while the other terms cancel under r -> r+3
by cubic-root orthogonality. Thus (C3) at h=2 on (P,2P] actually has
a nonzero term of order P^(3/4). Fourier completion after
subtracting this mean again gives O_delta(Q^(1/2+delta)) for every
interval. For clarity, the nonzero-frequency divisor sum here is

\[
 \sum_{1\le |b|\le Q/2}\frac{(Q,Q/2-b)^{1/2}}{|b|}
       \ll_\delta Q^\delta.                         \tag{C7}
\]

To verify this, expand the gcd bound over divisors d of Q. If d divides
Q/2, the permitted nonzero b are multiples of d. Otherwise Q/d is odd
and the permitted b are congruent to d/2 modulo d. In either case
their reciprocal sum is O((1+log Q)/d). Summing sqrt(d) times this
bound proves (C7); negative representatives satisfy the same estimate.
The cubic coefficient -1 is a unit for every Q. Complete periods of
the mean-subtracted wave vanish, so the bound applies to arbitrarily
long dual intervals.

The weighted mean contributes at most O(P^(3/4)*c(j)); an extra endpoint
weight is absorbed by the completion error. Hence (C3) implies

\[
 |S_{2j}(I)|\ll_\delta P^{3/4}c(j)
                +P^{1/4}j^{1/2+\delta}+\log(2+P).   \tag{C8}
\]

The necessary average is

\[
 \sum_{j\le H}c(j)\ll_\delta H^{1/2+\delta}.          \tag{C9}
\]

Here is a proof that includes exceptional prime powers. Uniquely write
j=t*a*b with t=2^u*3^v, a squarefree with primes >=5, and b powerful
(every prime exponent is at least 2), with (a,b)=1 and (ab,6)=1.
Input 3, applied to Q=54j^2, gives

\[
 c(j)\ll_\delta j^\delta t^{-1/6}a^{-1/2}b^{-1/6}.
\]

For primes >=5 of exponent 1 in j, the local factor sqrt(j)/kappa(Q)
is p^(-1/2); for exponent e>=2 it is p^(-e/6). At 2 and 3 it is at
most a fixed constant times the corresponding factor t^(-1/6):
the exponents in Q are 1+2u and 3+2v. This accounts for every prime.
Summing over a<=H/(tb), and dropping its squarefree and coprimality
restrictions, bounds (C9) by a constant times

\[
 H^{1/2+\delta}
   \sum_{u,v\ge0}(2^u3^v)^{-2/3}
   \sum_{b\ \mathrm{powerful}}b^{-2/3}.
\]

Both series converge. For the second, write a powerful b uniquely as
c^2*d^3 with d squarefree; dropping squarefreeness bounds it by
zeta(4/3)*zeta(2). This proves (C9). In particular, replacing every
even harmonic by the odd-harmonic estimate (C6) would be unjustified.

### Vaaler assembly, including exact square endpoints

The identity

\[
 (-1)^{\lfloor x\rfloor}
    =2\psi((x+1)/2)-2\psi(x/2)                       \tag{C10}
\]

holds for all real x when psi(x)={x}-1/2, including integers.
Apply input 4 to both terms. Their polynomial difference has only odd
harmonics, with coefficients O(1/|h|). The sum of the two nonnegative
error majorants has only even harmonics, each with coefficient O(1/H),
and constant coefficient O(1/H). Therefore

\[
 |S_O(I)|\ll P/H+
   \sum_{\substack{1\le h\le H\\h\text{ odd}}}\frac{|S_h(I)|}{h}
   +\frac1H\sum_{1\le j\le H/2}|S_{2j}(I)|.          \tag{C11}
\]

This explicitly retains the boundary errors. Integer values n^(3/2),
which occur at odd squares, are covered by E_H(0)=1/2; they have not
been discarded by an almost-everywhere Fourier identity. Using
(C6), (C8), and (C9) in (C11) yields

\[
 |S_O(I)|\ll_\delta P/H+
 P^{1/4}H^{1/2+\delta}+P^{3/4}H^{-1/2+\delta}
 +(\log(2+P))^2.                                    \tag{C12}
\]

Choose H=floor(sqrt(P)) (small P is absorbed in the constant) and
then a sufficiently small delta. This proves (C1). Dyadic summation
proves the prefix bound. Since the number of odd n<=N is N/2+O(1),
the identity OO(N)=(#odd starts-S_O(N))/2 proves (C2).

### What the result changes

The one-step odd-source discrepancy now has a square-root-plus-epsilon
written bound. The gain uses the particular rational cubic dual phase,
including its half-period sign; it is not a generic exponent-pair bound
for every phase with the same derivative sizes.

An additional inverse-cell phase j*m^(2/3) destroys periodicity of the
full transformed wave. The continuation below recovers cancellation
at this first weighted level. Further dynamically selected sources
and the stopped pressure at depth comparable to log log y remain
open. Neither result proves infinite escape, excludes an escape
trajectory, or proves termination.

## First inverse-cell continuation (22 September 2026)

The [complete mixed-frequency proof](../theory/juggler_cubic_inverse_cell_note.md)
gives, on every interval I in (M,2M],

\[
 \sum_{m\in I,\ m\text{ odd}}
 e(hm^{3/2}/2+jm^{2/3}/2)\ll M^{2/3-1/25000}
\]

uniformly for integer 1<=|h|<=M^(1/50000) and
1<=|j|<=M^(1/3+1/50000). Removing the rational cubic exposes a
remainder whose third derivative is nonzero and monotone. Robert's
2005 theorem supplies the small gain at the critical frequency;
its sum-length condition is retained by a C3 extension argument.

For the **actual** odd-predecessor weight
w(m)=ceil(((m+1)^(2/3)-1)/2)-ceil((m^(2/3)-1)/2), this implies
sum over odd m in I of w(m)*e(h*m^(3/2)/2)
=O(M^(2/3-1/50000)) over the same h range. Shifted cell endpoints
and perfect powers are included. This is a rated first inverse-cell
estimate, not an invocation of qualitative shrinking-target convergence.

**EXACT — HUMAN PROOF**, AI-assisted, pending independent review.
The associated OOO count is weaker than the existing Paper B count;
no published exponent is improved here. The new retained statement
is the mixed-frequency estimate with a nonzero inverse-cell frequency.
`CubicInverseCell.lean` checks the exact phase decomposition, period,
normalized derivative quotients and sign factors, and rational exponent
budget. It does not formalize the analytic transform or derivative tests.

## Decision

**PROMOTE** the written one-step bound (C1)-(C2), with independent
analytic review outstanding, and the kernel-checked exact phase
identities. The subsequent bounded phase also **PROMOTE**s the
mixed-frequency and first inverse-cell estimates, with the same
analytic review limitation. The next substantive question is whether
an actual additional itinerary restriction preserves a useful
derivative structure at its smaller count scale. That deeper estimate
remains open; end this phase without asserting an iteration.
