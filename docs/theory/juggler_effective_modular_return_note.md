# Effective OOE modular returns

22 September 2026. **EXACT — HUMAN PROOF**: AI-assisted written derivation
from an explicitly cited analytic theorem. Independent mathematical review
and Lean formalization of the quantitative argument remain outstanding.
The [fresh internal audit](juggler_effective_modular_return_audit.md)
rederives the estimates and confirms the constants, with boundary and
small-parameter details expanded below. It is not external peer review.

## 1. Statement

Let M and T be positive integers. For each nonnegative integer t put
\[
s=1+2Mt,\qquad n=s^2,\qquad
u=\lfloor s^{9/2}\rfloor,\qquad v=\lfloor s^{9/4}\rfloor.
\]
Define
\[
A_M(T)=\#\{0\le t<T:s\ge16,\ u\equiv0\pmod2,
                         \ v\equiv1\pmod{2M}\}.
\]
This is exactly the thresholded OOE construction counted by Paper E,
Corollary 4.2, with a=2 and b=1.

**Theorem (explicit counting error).** Uniformly for all integers M,T>=1,
\[
\left|A_M(T)-\frac{T}{4M}\right|
\le \left[5+128M^{1/4}\left(3+\frac{\log T}{16}\right)^2\right]
       T^{63/64}+8
\le 2^{14}M^{1/4}T^{127/128}. \tag{1}
\]
The logarithm is natural. No unspecified asymptotic constant or threshold
occurs in (1).

**Corollary (first witness).** For every integer M>=1 there is a parameter
\[
0\le t<2^{2176}M^{160} \tag{2}
\]
whose start satisfies
\[
n<2^{4354}M^{322}. \tag{3}
\]
Its actual Juggler itinerary for three steps is OOE; every state in this
prefix is at least n, its endpoint is strictly greater than n, and
\[
J^3(n)\equiv n\equiv1\pmod{2M}. \tag{4}
\]
More strongly, at T=2^(2176)M^(160) the count is at least T/(8M).

These bounds are deliberately coarse. Even M=1 gives a start bound with
more than 1300 decimal digits. They establish a uniform polynomial
dependence on M, but are not a practical search budget. The word remains
OOE throughout; the result does not quantify arbitrary a,b or construct
an infinite concatenation. Its periodic-word denominator is 1, so this
special case alone does not provide large nonintegral word codes.

## 2. Explicit analytic input

Write e(x)=exp(2*pi*i*x). We use J. Arias de Reyna,
[*Explicit van der Corput's d-th derivative estimate*, v1](https://arxiv.org/html/2407.02094v1),
Theorem 11 and Table 1, only at derivative orders k=3 and k=5.
In notation adapted to this proof, if floor(Y)>k, f has continuous
derivatives through order k on (X,X+Y], and its k-th derivative lies
between positive lambda and Lambda,
then, with D=2^k,
\[
\frac1Y\left|\sum_{X<m\le X+Y}e(f(m))\right|
\le 11\max\left\{
 \left(\frac{\Lambda}{\lambda Y}\right)^{2/D},
 \left(\frac{\Lambda^2}{\lambda}\right)^{1/(D-2)},
 (\lambda Y^k)^{-2/D}\right\}. \tag{5}
\]
The source gives constants smaller than 11 for both orders. A derivative
of constant negative sign is handled by replacing f by -f, which
conjugates the exponential sum. No monotonicity hypothesis is needed
in this higher-derivative estimate. This cited result is a written
proof input, not an imported Lean theorem or a new claim of this project.
Our phases are smooth for x>0, and every retained interval has Y=N>=6,
so floor(Y)>5>=k. The normalization is by the real interval length Y,
not by the number of integer summands.

## 3. Uniform estimates for every truncated Fourier mode

Let H>=1 be an integer and let integers h_1,h_2 satisfy
0<max(|h_1|,|h_2|)<=H. Consider
\[
f_h(x)=\frac{h_1}{2}(1+2Mx)^{9/2}
       +\frac{h_2}{2M}(1+2Mx)^{9/4}. \tag{6}
\]
On a real interval N<x<=2N with N>=max(H^2,6),
\[
2MN\le1+2Mx\le5MN. \tag{7}
\]

### Nonzero high-power coefficient

If h_1 is nonzero, the fifth derivative is
\[
f_h^{(5)}(x)=\frac{945}{2}h_1M^5s^{-1/2}
             +\frac{945}{64}h_2M^4s^{-11/4},\qquad s=1+2Mx.
\]
The absolute ratio of the second term to the first is at most
H*s^(-9/4)/(32M)<=1/32, using |h_1|>=1, N>=H, and s>=2MN.
The derivative therefore has the sign of h_1 throughout the interval.
The weaker factors 1/2 and 3/2 around its leading term give valid bounds
\[
\lambda=100|h_1|M^{9/2}N^{-1/2},\qquad
\Lambda=600|h_1|M^{9/2}N^{-1/2}. \tag{8}
\]
Indeed 945/(4*sqrt(5))>100 and 2835/(4*sqrt(2))<600.
Substitution into (5), with k=5, gives
\[
\frac1N\left|\sum_{N<m\le2N}e(f_h(m))\right|
\le32H^{1/30}M^{3/20}N^{-1/60}. \tag{9}
\]
For clarity, the three terms before enlargement are bounded by
11*(6/N)^(1/16),
11*(3600*H*M^(9/2)*N^(-1/2))^(1/30), and
11*(100*M^(9/2)*N^(9/2))^(-1/16).
The scalar inequalities 6<2^16 and 3600<2^30 suffice for the constant 32.

### Vanishing high-power coefficient

If h_1=0, then h_2 is nonzero and
\[
f_h^{(3)}(x)=\frac{45}{16}h_2M^2s^{-3/4}.
\]
Use
\[
\lambda=\tfrac12|h_2|M^{5/4}N^{-3/4},\qquad
\Lambda=2|h_2|M^{5/4}N^{-3/4}.
\]
The endpoint comparisons follow from
45/(16*5^(3/4))>1/2 and 45/(16*2^(3/4))<2.
Estimate (5), now with k=3, bounds the normalized sum by
22*H^(1/6)*M^(5/24)*N^(-1/8).
The three terms before enlargement are at most
11*(4/N)^(1/4),
11*(8*H*M^(5/4)*N^(-3/4))^(1/6), and
11*((1/2)*M^(5/4)*N^(9/4))^(-1/4).
Each is bounded by the displayed common expression using H,M,N>=1.
Since H^2<=N,
\[
H^{1/6}N^{-1/8}
\le H^{1/30}N^{-7/120}
\le H^{1/30}N^{-1/60}.
\]
Together with (9), this proves the single bound
\[
\frac1N\left|\sum_{N<m\le2N}e(f_h(m))\right|
\le32H^{1/30}M^{1/4}N^{-1/60}. \tag{10}
\]
All signs and both coordinate-axis cases are covered.

### Passage to an initial segment

Suppose 1<=H<=T^(1/4). Split (0,T] into intervals (N,2N] with
N=T/2, T/4, ... while N>=max(H^2,6). The remaining initial interval
is (0,R], where R<2*max(H^2,6); take R=T if no interval is retained.
The intervals are disjoint as half-open sets, even at noninteger endpoints.
The remainder has floor(R) integer summands. The change from indices
1,...,T to 0,...,T-1 is exactly e(f_h(0))-e(f_h(T)), of norm at most 2.
Their total contribution is at most
floor(R)+2<=2H^2+14<=16H^2, including when no interval is retained.
Moreover,
\[
\sum_{j\ge0}(T/2^{j+1})^{59/60}
=\frac{T^{59/60}}{2^{59/60}-1}<2T^{59/60}.
\]
Since H^2<=T^(1/2), (10) and the initial remainder imply
\[
\frac1T\left|\sum_{0\le t<T}e(f_h(t))\right|
\le128M^{1/4}H^{1/30}T^{-1/60}. \tag{11}
\]
The intermediate constant is at most 64+16=80; 128 is a convenient
enlargement. Integer endpoints require no integrality of the dyadic N.

## 4. An explicit half-open box estimate

For arbitrary points z_0,...,z_(T-1) on the two-dimensional unit torus,
let E_H bound the normalized sums of every nonzero Fourier mode with
max(|h_1|,|h_2|)<=H. For every half-open product of circular intervals B,
\[
\left|\frac{\#\{t<T:z_t\in B\}}T-|B|\right|
\le\frac5{\sqrt{H+1}}+(3+2\log H)^2E_H. \tag{12}
\]
Here is a proof with constants and endpoints retained. The Fejer kernel
\[
F_H(x)=\frac1{H+1}\left|\sum_{j=0}^H e(jx)\right|^2
\]
is nonnegative, has integral one, and has Fourier coefficients
1-|h|/(H+1) for |h|<=H and zero otherwise. For 0<delta<=1/2,
sin(pi*x)>=2*x on 0<=x<=1/2 gives
\[
\int_{\|x\|\ge\delta}F_H(x)\,dx
\le\frac1{2(H+1)\delta}.
\]
The product kernel K=F_H tensor F_H therefore has mass at most
q=1/((H+1)*delta) outside the coordinate delta-neighbourhood of zero.
Expand and contract each interval of B by delta on the circle, obtaining
B^+ and B^-. A contracted interval can be empty and an expanded one full;
both cases are retained. More precisely, write a proper circular interval
as the image of [a,a+ell), with 0<ell<1. Its expansion is the image of
[a-delta,a+ell+delta) if ell+2*delta<1, and the whole circle otherwise.
Its contraction is the image of [a+delta,a+ell-delta) if ell>2*delta,
and empty otherwise. Empty and full original intervals are left unchanged.
For shifts y with each circular distance ||y_i||<delta, these definitions
give z in B implies z-y in B^+, and z-y in B^- implies z in B.
The exceptional shifts have K-mass at most q. Since 0<=1_B*K<=1,
the following inequalities hold at every point,
including the original interval endpoints:
\[
\mathbf1_{B^-}*K-q\le\mathbf1_B\le\mathbf1_{B^+}*K+q.
\]
The changes in volume are at most 4*delta. A circular interval's
Fourier coefficient has absolute value at most 1/max(1,|h|), also
for the empty or full interval. Thus the sum of absolute nonconstant
coefficients of either convolution is at most
\[
\left(1+2\sum_{h=1}^H\frac1h\right)^2-1
\le(3+2\log H)^2.
\]
Averaging the pointwise inequalities proves an error at most
4*delta+q+(3+2*log(H))^2*E_H. Take delta=(H+1)^(-1/2) for H>=3.
For H=1 or 2, the trivial discrepancy bound one already implies (12).

## 5. Assembly and first-witness extraction

Apply (12) to
\[
z_t=\left(\frac{s^{9/2}}2,\frac{s^{9/4}}{2M}\right)\pmod1,
\qquad B=[0,1/2)\mathbin{\times}[1/(2M),1/M).
\]
Its area is 1/(4M). For any x>=0 and integers m>=1 and 0<=r<m, writing
floor(x)=m*q+r' with 0<=r'<m gives fract(x/m)=(r'+fract(x))/m. Consequently
floor(x)=r modulo m is equivalent to
r/m<=fract(x/m)<(r+1)/m, including equality at the left endpoint.
Box membership is therefore exactly u even and v=1 modulo 2M.
For M=1 the second interval is [1/2,1): its right endpoint is excluded;
an integer value of x/(2M) has fractional part zero and is rejected.
The first interval likewise excludes its endpoint 1/2. No absence of
boundary hits is assumed. Choose H=floor(T^(1/32)), so
H>=1, H<=T^(1/4), and
\[
(H+1)^{-1/2}\le T^{-1/64},\qquad
H^{1/30}T^{-1/60}\le T^{-1/64},\qquad
2\log H\le\frac{\log T}{16}.
\]
Equations (11) and (12) give the first bound in (1) before the final +8.
Exactly min(T,1+floor(7/M)) parameters have 1+2Mt<16. Deleting the box
hits among these parameters changes the count by at most eight.

For the second bound in (1), put x=log(T)>=0. The maximum of
\[
(3+x/16)^2e^{-x/128}
\]
on this half-line is 256*exp(-13/8), attained at x=208, and is less
than 64. For example, the first four terms of the exponential series
already give exp(13/8)>4. Absorb 8/T into 8*T^(-1/128) and
5*T^(-1/64) into 5*T^(-1/128). Since M>=1 and
5+128*64+8=8205<2^14, the second inequality follows.

At T=2^(2176)M^(160), one has T^(1/128)=2^17*M^(5/4). Hence the
error is at most T/(8M), while the main term is T/(4M). Thus A_M(T)>=
T/(8M)>0. Select a counted t. Since t<T is integral,
1+2Mt<2MT, giving (2) and (3).

The actual orbit is
\[
s^2\longmapsto s^3\longmapsto u\longmapsto v.
\]
Both initial sources are odd, the third is even by construction, and
the exact identity isqrt(isqrt(s^9))=floor(s^(9/4)) identifies the exit.
The already proved size threshold s>=16 gives v>s^2; the first two
images are larger still. Finally s=1 modulo 2M gives n=1 modulo 2M,
and the box gives (4). This completes the written proof.

## 6. Verification and value

The registered exact checker is
[effective_modular_return.py](../../src/research/juggler_sequence/effective_modular_return.py),
with [tests](../../tests/research/juggler_sequence/test_effective_modular_return.py).
It checks derivative coefficients, scalar comparisons, exponent accounting,
and the extraction of (2)-(3) using rational arithmetic. Its finite orbit
checks use integer square roots and an independent iteration oracle.
These checks do not prove the analytic estimate (5), the smoothing argument,
or the universal counting theorem. The displayed error is too large to be
nontrivial in the small numerical samples; no experimental rate is claimed.

**PROMOTE** the explicit written theorem as an effective specialization of
classical machinery. It closes the rate-free gap for this one word and
makes the modulus dependence explicit. It is suitable as a candidate
supplement to Paper E after review. The existing 0.5.0 paper and its Lean
coverage remain unchanged: (1) is not yet a kernel-checked theorem.
No external novelty, new general discrepancy method, cycle, or escape
claim is made. Optimizing constants or generalizing the word is a separate
decision, not an automatic continuation.
