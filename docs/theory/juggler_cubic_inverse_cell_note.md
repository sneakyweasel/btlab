# Rational cubic removal with an inverse-cell frequency

22 September 2026. **EXACT — HUMAN PROOF**, AI-assisted, independent
analytic review outstanding. The exact rational algebra and exponent
budget are kernel-checked; the analytic inequalities are not Lean theorems.
This is a specialized estimate at one inverse-cell level. It does not
establish the growing-depth pressure required for termination.

## Scope and budget

```text
Mathematical target     A mixed sum below M^(2/3), retaining the inverse-cell
                        frequency past M^(1/3).
Novelty hypothesis      Removing the rational cubic exposes a monotone third
                        derivative, permitting Robert's positive saving.
Falsifier               Wrong derivative signs, insufficient length, or frequency
                        costs exhausting the saving.
Already killed by?      The generic exponent-pair route is closed. This uses
                        integer half-frequencies and a nonzero perturbation.
Existing machinery      OddCubicPhase, C4 B-transform, Robert's derivative theorem.
Maximum Phase-0 scope   One mixed estimate, its first inverse-cell consequence,
                        and Lean checks of algebra and exponent arithmetic.
Promotion criterion     Uniform saving including both shifted cell endpoints.
Stop criterion          Missing analytic hypothesis or an unjustified iteration.
```

Set beta=1/50000 and delta=1/25000=2*beta. Write e(x)=exp(2*pi*i*x).
All constants below are uniform in the displayed integer frequencies
and intervals, with these numerical exponents fixed.

**Theorem 1 (mixed sum).** For M>=2, an interval I in (M,2M], and integers
1<=|h|<=M^beta and 1<=|j|<=M^(1/3+beta),

\[
 S_{h,j}(I):=\sum_{\substack{m\in I\cap\mathbb N\\m\text{ odd}}}
 e\left(\frac h2m^{3/2}+\frac j2m^{2/3}\right)
       \ll M^{2/3-\delta}.                                      \tag{1}
\]

The **nonzero j** condition matters. At j=0 some even h have a
nonzero M^(3/4) main term; see the preceding
[odd-source discrepancy proof](../problems/juggler_odd_image_discrepancy.md).
No estimate for arbitrary real leading coefficients is asserted.

**Theorem 2 (actual inverse-cell weight).** Let

\[
 a_m=(m^{2/3}-1)/2,\quad b_m=((m+1)^{2/3}-1)/2,\quad
 w(m)=\lceil b_m\rceil-\lceil a_m\rceil.
\]

Thus w(m) is exactly the number, zero or one, of odd positive n with
floor(n^(3/2))=m. For 1<=|h|<=M^beta,

\[
 W_h(I):=\sum_{\substack{m\in I\cap\mathbb N\\m\text{ odd}}}
       w(m)e(hm^{3/2}/2)\ll M^{2/3-\beta}.                       \tag{2}
\]

Consequently the same weighted sum with e(hm^(3/2)/2) replaced by
(-1)^floor(m^(3/2)) is O(M^(2/3-1/100000)). This gives a rated first
inverse-cell parity balance. Its implied OOO prefix error is
O(N^(1-3/200000)), **weaker** than Paper B's existing 23/24 error.
The new retained object is (1), not an improvement of that short count.

## Analytic inputs

The C4 van der Corput transform is used in the form of
[Vandehey, Theorem 1.1](https://arxiv.org/pdf/1205.0090): its error on
scale M and second derivative comparable to T/M^2 is
O(M/sqrt(T)+log(2+f'(b)-f'(a))) for amplitude one. The derivative
conditions through order four must hold uniformly.

We use the classical third-derivative estimate

\[
 \sum_{k\in K}e(g(k))\ll L\lambda^{1/6}
                       +L^{1/2}\lambda^{-1/6}                 \tag{3}
\]

on an interval of length at most L, when |g'''| is comparable to
0<lambda<1. The additional input is Robert's theorem: when g''' is
monotone and the sum length is at least lambda^(-1), the bound is
L*lambda^theta, where theta=1/6+1/1354. See
[Robert, 2005, Theorem 1](https://perso.univ-st-etienne.fr/rool6510/derivmonotone.pdf),
also stated clearly as Theorem 8 in his
[2016 survey](https://perso.univ-st-etienne.fr/rool6510/robert-2015-indag.pdf).
Literature id: `robert-2005-monotone-third-derivative`.

We need a version valid for partial intervals:

\[
 \sum_{k\in K}e(g(k))\ll (L+\lambda^{-1})\lambda^\theta.         \tag{4}
\]

To obtain it, extend g beyond the right endpoint by its cubic Taylor
polynomial there. This is a C3 extension with constant third derivative
on the added part, preserving monotonicity and the derivative bounds.
Append an integer number J comparable to lambda^(-1), sufficiently
large for Robert's length condition. Apply the theorem to the extended
sum and to the added tail, then subtract. Both constants depend only
on the fixed derivative-comparability constants. This proves (4) for
short intervals as well; it does not discard the length hypothesis.
Negative third derivatives are handled by replacing g by -g.

## Exact dual remainder and its monotonicity

By conjugation assume h>0. Put m=2s+1 and
f(s)=(h/2)(2s+1)^(3/2)+(j/2)(2s+1)^(2/3). At the stationary
point f'(s)=r write t=(2s+1)^(1/6). Then

\[
 r=\frac{3h}{2}t^3+\frac{2j}{3t^2},\qquad
 u=\frac{8j}{27ht^5},\qquad s=(t^6-1)/2.                         \tag{5}
\]

Uniformly in (1), |u| is O(M^(-1/2+beta)); for sufficiently large M
it is at most 1/100. Bounded M can be absorbed into the final constant.
In this region f''>0, r is comparable to h*sqrt(M), and t to M^(1/6).
The first three relevant derivatives of the source phase are exactly

\[
 f''=\frac{3h}{2t^3}(1-u),\quad
 f'''=-\frac{3h}{2t^9}(1-8u/3),\quad
 f''''=\frac{9h}{2t^{15}}(1-112u/27).                            \tag{6}
\]

Thus the C4 transform applies with T=h*M^(3/2), uniformly in j. For
F(r)=f(s_r)-r*s_r, its exact decomposition is

\[
 F(r)=\frac r2-\frac{2r^3}{27h^2}+R(r),\qquad
 R(r)=\frac j2t^4+\frac{4j^2}{27ht}
                    +\frac{16j^3}{729h^2t^6},                 \tag{7}
\]

where t depends on r through (5). The leading cubic wave in (7) has
integer period Q=54h^2 for **every** positive integer h. Unlike the
previous odd-harmonic argument, no zero-mean assertion is needed.

Differentiating the Legendre relation gives
F''=-1/f'', F'''=f'''/(f'')^3, and
F''''=(f''''*f''-3*(f''')^2)/(f'')^5. Inserting (6) and subtracting
the cubic derivatives gives the exact identities

\[
 R'''(r)=\frac{-4u(1-9u+3u^2)}{27h^2(1-u)^3},\qquad
 R''''(r)=\frac{40u(1-16u)}{243h^3t^3(1-u)^5}.                  \tag{8}
\]

For |u|<=1/100 the factors 1-u, 1-9u+3u^2, and 1-16u are
positive; the ratio (1-9u+3u^2)/(1-u)^3 lies between 1/2 and 2.
Since j is nonzero with fixed sign, R''' is nonzero and monotone,
and |R'''| is comparable to |j|*h^(-3)*M^(-5/6).
These are uniform comparisons; a small undifferentiated remainder
alone would not establish them.

The transformed amplitude 1/sqrt(f'') has supremum and total variation
O(h^(-1/2)*M^(1/4)): f'''<0 in this region, so the amplitude is
monotone. The transform error is O(M^(1/4)*h^(-1/2)+log(2+M)).

## Residue classes and exponent budget

Split the dual integers r into their Q residue classes. On each class
the cubic wave is constant. For g(k)=R(r_0+Q*k), (8) gives

\[
 L\asymp M^{1/2}/h,\qquad
 \lambda\asymp |j|h^3M^{-5/6}.                                 \tag{9}
\]

The actual summation interval can be shorter; (3)-(4) are used with
this upper length bound. We have lambda=O(M^(-1/2+4*beta))<1 and
L tending to infinity, uniformly. Summing Q class bounds, then using
partial summation for the amplitude, gives from (3)

\[
 |S_{h,j}(I)|\ll
 h|j|^{1/6}M^{11/18}+h^{1/2}|j|^{-1/6}M^{23/36}
 +M^{1/4}+\log(2+M).                                          \tag{10}
\]

From (4) the corresponding bound, apart from the same smaller errors, is

\[
 h^{1/2+3\theta}|j|^\theta M^{3/4-5\theta/6}
 +h^{-1+3/1354}|j|^{\theta-1}M^{1/4+5(1-\theta)/6}.             \tag{11}
\]

Set alpha=1/2708. For |j|<=M^(1/3-alpha), use (10). The two exponent
upper bounds are 11/18+(1/3-alpha)/6+beta and 23/36+beta/2.
For larger |j| use (11). Its first term is largest at h=M^beta,
|j|=M^(1/3+beta); its second is largest at h=1,
|j|=M^(1/3-alpha), since -1+3/1354<0 and theta-1<0.
The resulting savings below 2/3 are respectively

| Term | Exact saving |
|---|---|
| (10), first | 4219/101550000 |
| (10), second | 24991/900000 |
| (11), first | 70249/203100000 |
| (11), second | 85/1374987 |

Every entry is strictly greater than delta=1/25000. This proves (1),
including partial source intervals. The constants can be large;
these asymptotic exponents are not a finite computational certificate.

## From the mixed sum to the exact inverse cell

Let ell_m=b_m-a_m. Define psi_+(x)=x-ceil(x)+1/2, including its
value +1/2 at integers. Then

\[
 w(m)=\ell_m+\psi_+(a_m)-\psi_+(b_m).                           \tag{12}
\]

Vaaler's degree-J sawtooth polynomial P_J has coefficients O(1/|j|)
and a nonnegative error majorant E_J=F_J/(2(J+1)), with F_J the
Fejer kernel. It approximates this endpoint convention too:
P_J(k)=0 and E_J(k)=1/2 at integers. Take J=floor(M^(1/3+beta)).
On odd m the total error in (12) is

\[
 \sum_m(E_J(a_m)+E_J(b_m))\ll M/J+M^{1/2+\beta/2}
                         \ll M^{2/3-\beta}.                  \tag{13}
\]

Here is the needed one-dimensional check. For 1<=j<=M^(1/3), the
phase j*(2s+1)^(2/3)/2 has derivative bounded away from integers
with reciprocal size O(M^(1/3)/j), giving that bound for its sum.
For larger j<=J use the second-derivative test, which gives
O(j^(1/2)*M^(1/3)+j^(-1/2)*M^(2/3))=O(M^(1/2+beta/2)).
Each nonconstant Fejer coefficient is O(1/J), so summing these bounds
proves (13); the low-frequency term is O(M^(1/3)*log(2+M)/J).
The same argument applies to m+1 in b_m and to negative frequencies.

Multiply (12) by e(h*m^(3/2)/2). The ell_m term is
O(h^(1/2)*M^(5/12)+h^(-1/2)*M^(-1/12)) by partial summation and
the ordinary second-derivative estimate for the h phase. Its size is
smaller than the right side of (2).

The polynomial at a_m is controlled by (1). At b_m, write the extra
phase as (j/2)*((m+1)^(2/3)-m^(2/3)). Its exponential has total
variation O(|j|*M^(-1/3)). Partial summation and the interval-uniform
version of (1) therefore bound both polynomial contributions by

\[
 M^{2/3-\delta}\sum_{1\le j\le J}
       \frac{1+ jM^{-1/3}}j
 \ll M^{2/3-\delta}\bigl(\log(2+M)+M^\beta\bigr)
 \ll M^{2/3-\beta}.                                           \tag{14}
\]

Combining (13)-(14) proves (2). Perfect-cube cell endpoints are
included throughout; neither a lower nor an upper endpoint has been
replaced by an almost-everywhere identity.

For the final parity consequence, use the paired sawtooth identity
for (-1)^floor(x) with degree H=floor(M^beta). Since w(m)>=0 and
sum w(m)=O(M^(2/3)) by the exact predecessor count, its constant
majorant costs only M^(2/3)/H. The nonconstant terms use (2), giving
O(M^(2/3-beta)*log(2+M)). Absorbing the logarithm proves the stated
1/100000 saving. Applying the same one-dimensional estimates used in
(13) to the 1/j polynomial coefficients in (12) also gives
sum over odd m of w(m) = sum over odd m of ell_m + O(M^(2/3-beta)):
the low modes cost O(M^(1/3)) and the high modes
O(M^(1/2+beta/2)*log(2+M)), both smaller than this error.
Pairing the monotone ell_m on adjacent integers replaces their
odd-index sum by half their full telescoping sum with error
O(M^(-1/3)). The leading count is half this odd-target mass, giving
the OOO main term N/8 after dyadic summation and M of order N^(3/2).
This count is a scope check, not a claimed improvement of Paper B.

## Formal coverage and decision

[CubicInverseCell.lean](../../formal/Problems/Juggler/CubicInverseCell.lean)
checks (7), the period Q, the rational quotients in (8), their sign
factors, and the exact inequalities underlying (10)-(14). It does
not formalize differentiating the inverse function, the B-transform,
Robert's theorem, Fourier approximation, or the asymptotic bounds.
These remain written analytic arguments, pending independent review.
The [symbolic calculus tests](../../tests/research/juggler_sequence/test_cubic_inverse_cell.py)
independently differentiate the original source phase and Legendre
relation to verify (6)-(8). They do not test the analytic inequalities.

**PROMOTE** (1)-(2) as a specialized quantitative arithmetic lemma.
The existing short-count exponents and all published papers remain
unchanged. The deeper target uses nested floors, and no estimate for
that target has been established here. Best next question: can an
actual additional itinerary restriction retain a derivative structure
that meets a quantitative bound at its smaller source-count scale?
End this phase without asserting such an iteration.
