---
title: "Parity Statistics of Nested Floor Powers"
subtitle: "Finite-Step Descent and Conditional Extensions for the Juggler Map"
author: Philippe Cochin
date: 9 September 2026
lang: en
---

## Abstract

The Juggler map applies the integer part of the square root at even
positive integers and of the three-halves power at odd positive integers.
We prove that the starting values admitting a power-envelope descent
certificate within four operations have natural density \(13/16\).
We also prove that the five-letter itinerary \(OOEOE\) has count
\(N/32+O(N^{47/48})\). Together these give a specified certificate
class of density \(27/32\), all of whose starts descend within five
operations. The analytic arguments use exact carry expansions and
second-derivative estimates summed over every gap cell. For the
fifth letter, centering a Fourier expansion at the integer part of
a smooth coefficient cancels the growing first-floor term; the
additional interval boundaries are retained in a summed mixed-mode
estimate. We also give a partition-aware curvature estimate for a
basic collision model. The full five-step certificate density \(7/8\)
requires only the remaining formal-chain correlation hypothesis for
\(OOOEE\). Fair-share densities for every fixed-depth odd-rooted
itinerary would imply density-one finite certificates. The general
decorated kernel, its short-interval extension, and the remaining
correlation hypotheses are unproved here. No result asserts universal
arrival at \(1\).

**Keywords:** Juggler map; nested floor powers; parity correlations;
discrepancy; stopping time; conditional descent.

## 1. Scope and relation to earlier work

For a positive integer \(n\), define
\[
J(n)=
\begin{cases}
\lfloor n^{1/2}\rfloor,&n\ \text{even},\\
\lfloor n^{3/2}\rfloor,&n\ \text{odd}.
\end{cases}
\]
This is the Juggler map recorded in OEIS A094683 [1]. The conjecture
that every positive orbit reaches \(1\) remains open. The question
studied here is more limited: which distribution estimates for finite
itineraries would imply that many starting values eventually fall below
their initial value?

Single-floor parity estimates follow from classical exponential-sum
methods [2, 3]. Composing floors creates an additional difficulty. For
\(m=\lfloor n^{3/2}\rfloor\) and \(\theta=\{n^{3/2}\}\),
\[
m^{3/2}=n^{9/4}-\tfrac32\theta n^{3/4}+O(n^{-3/4}).
\]
The coefficient of the fractional part grows with \(n\). A theorem for
the smooth phase \(n^{9/4}\) therefore does not by itself estimate the
nested phase. Nor does a parity estimate over consecutive starting
values automatically apply to a sparse set of orbit images.

The contribution of this note is an explicit reduction: the exact
identities, finite certificate classification, sufficient analytic
hypotheses, and conditional consequences are stated separately. The
single-floor estimate and the probabilistic counting argument use
standard methods. The latter is in the spirit of stopping-time
arguments for the Collatz map, such as Terras [4]; no theorem about
Collatz is transferred to the Juggler map.

This version replaces an earlier working draft and the first conditional
revision. Section 4.2 repairs the restricted \(23/24\) estimate needed
for four-step certificates by a complete small-shift argument.
Section 4.3 proves the fifth-letter split of \(OOEO\), raising the
unconditional certificate class to density \(27/32\). The
general \(95/96\) kernel estimate remains open here. Section 7.2
repairs a basic collision model while stating the additional work
needed for the decorated kernel. The former threshold
\(3.6\cdot10^{13}\) is not certified by this version: the analytic
constants are implicit and no numerical threshold is claimed.
The hypotheses for the higher conditional results remain explicit.

Throughout, \(e(t)=\exp(2\pi it)\), \(\{t\}=t-\lfloor t\rfloor\),
and \(\psi(t)=(-1)^{\lfloor t\rfloor}\). Natural density is measured
among all positive integers. Thus a length-\(d\) odd-rooted word with
count \(2^{-d}N+o(N)\) has relative density \(2^{-(d-1)}\) among odd
starts. Constants in \(O\) and \(\ll\) may depend on fixed words and
explicit fixed parameters. They are not asserted to be uniform in depth.

## 2. Exact itineraries and the power envelope

Let \(w=w_1\cdots w_d\) be a word in \(\{E,O\}\). The itinerary
\(\operatorname{word}_d(n)\) records the parities of
\(n,J(n),\ldots,J^{d-1}(n)\). It contains \(d\) letters and specifies
the \(d\) operations that produce \(J^d(n)\). Write \(o(w)\) for the
number of its odd letters.

**Proposition 2.1 (power envelope).** If \(w\) is realized at \(n\), then
\[
\bigl(J^d(n)\bigr)^{2^d}\le n^{3^{o(w)}}.
\]
Consequently, if \(n\ge2\) and \(3^{o(w)}<2^d\), then \(J^d(n)<n\).

*Proof.* At any positive integer \(x\), the even operation satisfies
\(J(x)^2\le x\), and the odd operation satisfies \(J(x)^2\le x^3\).
Suppose a prefix of length \(r\) with \(o\) odd letters ends at \(x\)
and obeys \(x^{2^r}\le n^{3^o}\). An even operation preserves the
right-hand exponent after raising \(J(x)^2\le x\) to \(2^r\); an
odd operation replaces it by \(3^{o+1}\). Induction starts at the empty
prefix. If \(3^{o(w)}<2^d\) and \(n>1\), the bound is strictly less
than \(n^{2^d}\), proving descent. \(\square\)

A word satisfying \(3^{o(w)}<2^{|w|}\) is called *contracting*. A
realized contracting prefix is a *power-envelope descent certificate*.
Let
\[
\mathcal C_d=\{n\ge2:\text{some contracting prefix of length at most }d
\text{ is realized at }n\}.
\]
Also set
\[
\mathcal C_\infty=\bigcup_{d\ge1}\mathcal C_d.
\]
These sets refer to this particular sufficient certificate. Flooring
can cause descent even when the envelope does not certify it. Therefore
\(\mathcal C_d\) need not equal the set of all starts that descend
within \(d\) steps.

For an odd-rooted target word \(w\), define its *formal chain* for
every odd \(n\), regardless of whether \(n\) realizes \(w\):
\[
x_1^w(n)=n,\qquad
\xi_t^w(n)=\bigl(x_t^w(n)\bigr)^{p_t},\qquad
x_{t+1}^w(n)=\lfloor\xi_t^w(n)\rfloor\quad(1\le t<d),
\]
where \(p_t=3/2\) for \(w_t=O\) and \(p_t=1/2\) for \(w_t=E\).
Set \(s_t^w(n)=\psi(\xi_t^w(n))\), and put \(\epsilon_t=1\) for
\(w_{t+1}=E\), \(\epsilon_t=-1\) for \(w_{t+1}=O\).

**Lemma 2.2 (parity and branch indicators).** For real \(x\),
\(\lfloor x\rfloor\) is odd exactly when \(\{x/2\}\in[1/2,1)\).
For every odd \(n\) and odd-rooted word \(w\),
\[
\mathbf1_{\operatorname{word}_d(n)=w}
=2^{-(d-1)}\prod_{t=1}^{d-1}(1+\epsilon_t s_t^w(n)).
\tag{2.1}
\]

*Proof.* Writing \(x=\lfloor x\rfloor+\{x\}\) proves the first
assertion, including the half-open endpoints. Each factor divided by
two tests the parity of \(x_{t+1}^w\). Until the first failed test, the
formal chain agrees with the true orbit, by induction on \(t\). A
failed test makes the product zero and prevents realization of \(w\).
If all tests pass, the chains agree through the required letters and
the product is one. The empty product covers \(d=1\). \(\square\)

The use of formal chains is essential: the product is defined on every
odd input before any correlation or Fourier expansion is made.

## 3. An unconditional certificate density

Let \(M(N)=\#\{n\le N:n\text{ odd}\}=N/2+O(1)\), and set
\[
S_O(N)=\sum_{\substack{n\le N\\n\ \mathrm{odd}}}\psi(n^{3/2}).
\]

**Theorem 3.1 (single-floor parity).** One has
\[
S_O(N)=O(N^{5/6}).
\]
In particular,
\[
\#\{n\le N:\operatorname{word}_2(n)=OO\}
=N/4+O(N^{5/6}),
\]
\[
\#(\mathcal C_2\cap[1,N])=3N/4+O(N^{5/6}).
\]

*Proof.* Write \(n=2r+1\) and \(g(r)=\tfrac12(2r+1)^{3/2}\).
Then \(g''(r)=\tfrac32(2r+1)^{-1/2}\). On a dyadic block with
\(r\asymp Q\), the classical second-derivative test [2] gives
\[
\left|\sum_{r\asymp Q}e(hg(r))\right|
\ll h^{1/2}Q^{3/4}+h^{-1/2}Q^{1/4}
\quad(h\ge1).
\]
The Erdős--Turán inequality [3, Chapter 2] bounds the unnormalized
interval discrepancy by
\[
\ll Q/H+\sum_{h=1}^{H}\frac1h
\left|\sum_{r\asymp Q}e(hg(r))\right|
\ll Q/H+H^{1/2}Q^{3/4}+Q^{1/4}.
\]
Taking \(H=\lfloor Q^{1/6}\rfloor\) for sufficiently large \(Q\)
gives \(O(Q^{5/6})\). Lemma 2.2 identifies parity with membership in
\([1/2,1)\); summing the dyadic bounds proves the first assertion.
Since \(S_O=M-2\#OO\), it also proves the count of \(OO\).

The only minimal contracting words of length at most two are \(E\)
and \(OE\). The first class has count \(\lfloor N/2\rfloor\), and
the second has count \(M-\#OO=N/4+O(N^{5/6})\). They are disjoint,
and Proposition 2.1 proves the stated certificate count. \(\square\)

This argument estimates starting values in an interval. It makes no
independence assertion about successive orbit parities.

**Proposition 3.2 (the OE third letter).** One has
\[
\#\{n\le N:\operatorname{word}_3(n)=w\}
=N/8+O(N^{5/6}\log(2N)),
\qquad w\in\{OEE,OEO\}.
\]

*Proof.* For every real \(x\ge0\),
\[
\lfloor\sqrt{\lfloor x\rfloor}\rfloor=\lfloor\sqrt x\rfloor:
\]
for an integer \(r\ge0\), the inequalities \(r^2\le\lfloor x\rfloor\)
and \(r^2\le x\) are equivalent. Consequently, with
\(m=\lfloor n^{3/2}\rfloor\), one has
\(\psi(m^{1/2})=\psi(n^{3/4})\) exactly.

On a dyadic block apply the two-dimensional Erdős--Turán--Koksma
inequality to \((\{n^{3/2}/2\},\{n^{3/4}/2\})\) at odd \(n\),
with cutoff \(H=\lfloor P^{1/6}\rfloor\). For a nonzero integer
mode \((i,l)\) in this range, the second-derivative estimate gives
\[
\left|\sum e\bigl(\tfrac i2n^{3/2}+\tfrac l2n^{3/4}\bigr)\right|
\ll
\begin{cases}
|i|^{1/2}P^{3/4}+|i|^{-1/2}P^{1/4},&i\ne0,\\
|l|^{1/2}P^{3/8}+|l|^{-1/2}P^{5/8},&i=0.
\end{cases}
\]
For \(i\ne0\), dominance follows from
\(|l/i|P^{-3/4}\le P^{-7/12}\).
Using the product weights of Proposition 4.2, the discrepancy is
\[
O\bigl(P/H+H^{1/2}P^{3/4}\log(2H)+P^{5/8}\log(2H)\bigr),
\]
hence \(O(P^{5/6}\log P)\). The two boxes selecting even \(m\)
and either parity of \(\lfloor n^{3/4}\rfloor\) have area \(1/4\).
Each therefore counts \(P/8\) odd starts on the block, with the
stated error. Sum dyadically. \(\square\)

## 4. Correlation criteria and proved cases

For a fixed odd-rooted word \(w\) of length \(d\) and nonempty
\(A\subseteq\{1,\ldots,d-1\}\), define
\[
R_{w,A}(N)=\sum_{\substack{n\le N\\n\ \mathrm{odd}}}
\prod_{t\in A}s_t^w(n).
\]

**Hypothesis \(\mathrm H(w;\delta)\).** For some fixed
\(0<\delta<1\), every nonempty \(A\) satisfies
\(R_{w,A}(N)=O_{w,A}(N^{1-\delta})\) as \(N\to\infty\).

**Hypothesis \(\mathrm H_0(w)\).** The same correlations satisfy
\(R_{w,A}(N)=o(N)\), without a prescribed rate.

These are assertions about the formal chains, not assumptions that the
true orbit is a sequence of independent coin tosses. Hypothesis
\(\mathrm H(w;\delta)\) implies \(\mathrm H_0(w)\).

**Proposition 4.1 (conditional word count).** Under
\(\mathrm H(w;\delta)\),
\[
\#\{n\le N:\operatorname{word}_d(n)=w\}
=2^{-d}N+O_w(N^{1-\delta}).
\tag{4.1}
\]
Under \(\mathrm H_0(w)\), the error is \(o(N)\).

*Proof.* Expand (2.1) and sum. The empty subset contributes
\(2^{-(d-1)}M(N)=2^{-d}N+O(1)\). The other \(2^{d-1}-1\) terms
are fixed signed multiples of \(R_{w,A}\), and there are finitely
many for fixed \(w\). \(\square\)

For example, \(\mathrm H(OOEE;\delta)\) concerns the seven nonempty
products of
\[
\psi(n^{3/2}),\qquad \psi(m^{3/2}),\qquad \psi(v^{1/2}),
\quad m=\lfloor n^{3/2}\rfloor,\quad v=\lfloor m^{3/2}\rfloor.
\]
Proposition 4.1 then gives the count \(N/16+O(N^{1-\delta})\)
needed for four-step certificates. Theorem 3.1 establishes the
first estimate. Corollary 4.6 below establishes all seven for every
\(0<\delta<1/24\).

### 4.1 A sufficient Fourier criterion

For \(\mathbf k=(k_1,\ldots,k_{d-1})\in\mathbb Z^{d-1}\), let
\[
S_{w,\mathbf k}(N)=\sum_{\substack{n\le N\\n\ \mathrm{odd}}}
e\left(\frac12\sum_{t=1}^{d-1}k_t\xi_t^w(n)\right).
\]

**Proposition 4.2 (conditional Fourier-to-parity transfer).** Fix
\(d\ge2\), \(w\), and \(0<\eta,\sigma<1\). Suppose, uniformly
over all nonzero integer vectors with
\(\|\mathbf k\|_\infty\le\lfloor N^\eta\rfloor\), that
\[
|S_{w,\mathbf k}(N)|\ll_w N^{1-\sigma}.
\tag{4.2}
\]
Then \(\mathrm H(w;\delta)\) holds for every
\(0<\delta<\min(\eta,\sigma)\). The constants may depend on these
fixed parameters.

*Proof.* Apply the multidimensional Erdős--Turán--Koksma inequality
[3, Chapter 2, p. 116] to the points
\(\mathbf y_n=(\{\xi_1^w(n)/2\},\ldots,\{\xi_{d-1}^w(n)/2\})\).
For any half-open axis-parallel box \(B\subseteq[0,1)^{d-1}\), its
unnormalized discrepancy is
\[
\begin{split}
\left|\#\{n\le N\text{ odd}:\mathbf y_n\in B\}-M(N)|B|\right|
&\ll_d \frac{M(N)}{H}
+\sum_{0<\|\mathbf k\|_\infty\le H}
\frac{|S_{w,\mathbf k}(N)|}{r(\mathbf k)},\\
r(\mathbf k)&=\prod_{t=1}^{d-1}\max(1,|k_t|).
\end{split}
\]
The weight sum is \(O_d((1+\log H)^{d-1})\). With
\(H=\lfloor N^\eta\rfloor\), (4.2) gives box discrepancy
\(O_w(N^{1-\eta}+N^{1-\sigma}(1+\log N)^{d-1})\).
Each nonempty sign product is constant, with value \(1\) or \(-1\),
on the \(2^{d-1}\) boxes obtained by splitting each coordinate at
\(1/2\). Its integral over the unit cube is zero. Summing their
discrepancies therefore bounds \(R_{w,A}\); absorbing the fixed
logarithmic power proves the assertion. \(\square\)

The criterion needs every indicated mixed mode, including vectors
with zero coordinates and mixed signs. A bound for one undecorated
kernel is not a substitute for (4.2). Qualitatively, cancellation
\(S_{w,\mathbf k}(N)=o(N)\) for each fixed nonzero \(\mathbf k\)
also implies \(\mathrm H_0(w)\): keep \(H\) fixed in the displayed
inequality, let \(N\to\infty\), and then let \(H\to\infty\).

### 4.2 A nested estimate sufficient for four-step descent

The general decorated kernel is not needed for four-step certificates.
We prove the smaller mixed family directly. Constants in this subsection
may depend on a fixed \(C\ge1\), but are uniform in all integer modes
in their stated ranges.

**Lemma 4.3 (a truncated carry expansion).** Put
\[
b(t)=\{t\}-\tfrac12,\qquad
b_R(t)=-\sum_{1\le |r|\le R}\frac{e(rt)}{2\pi i r},\qquad
E_R(t)=\min\left(1,\frac1{R\|t\|}\right),
\]
where \(\|t\|\) denotes distance to the nearest integer,
\(E_R(t)=1\) at integers, and \(R\ge2\) is integral. Then
\(b(t)=b_R(t)+O(E_R(t))\), including at integers. For
\(X(x)=x^{3/2}\), any interval \(I\subseteq[P,3P]\) satisfies
\[
\sum_{\substack{n\in I\\n\ \mathrm{odd}}}E_R(X(n))
\ll \frac{P\log(2R)}R+P^{5/6}.
\tag{4.3}
\]

*Proof.* Away from integers, the Fourier series of \(b\) is the
displayed series with infinite range. Summation by parts bounds its
tail by \(O((R\|t\|)^{-1})\). If \(\|t\|\le R^{-1}\), pairing
the modes \(r\) and \(-r\) and using
\(|\sin(2\pi rt)|\le2\pi r\|t\|\) bounds the finite sum by an
absolute constant. At an integer the finite sum is zero and
\(b(t)=-1/2\), so the asserted bound remains valid.

The proof of Theorem 3.1, with phase \((2r+1)^{3/2}\), gives interval
discrepancy \(O(P^{5/6})\) for the fractional parts \(\{X(n)\}\)
with odd \(n\in I\). In particular the number within distance
\(z\le1/2\) of an integer is \(O(Pz+P^{5/6})\). Split these
distances at \(R^{-1},2R^{-1},4R^{-1},\ldots\). Each resulting
weighted count contributes \(O(P/R+2^{-j}P^{5/6})\), proving
(4.3). This is a bound in terms of the ambient scale \(P\); it does
not rescale a global exceptional set by the length of \(I\).
\(\square\)

**Lemma 4.4 (small-shift nested sum).** Write
\(m(n)=\lfloor n^{3/2}\rfloor\), \(Y(n)=m(n)^{3/2}\), and
\(\Delta_h f(n)=f(n+2h)-f(n)\). If
\[
1\le h\le P^{1/12},\qquad
1\le |j|\le CP^{1/24},\qquad |i|,|k|\le CP^{1/24},
\]
where \(i,j,k,h\) are integers, then
\[
\left|\sum_{\substack{P<n\le2P-2h\\n\ \mathrm{odd}}}
e\left(\tfrac i2\Delta_hX(n)+\tfrac j2\Delta_hY(n)
+\tfrac k2\Delta_h(n^{9/8})\right)\right|
\ll_C P^{7/8}(1+h^{1/2}).
\tag{4.4}
\]

*Proof.* Conjugate the whole sum if necessary and put \(u=j/2>0\).
Thus \(u\ge1/2\); integrality of \(u\) is not required. Set
\(\theta=\{X(n)\}\), \(\delta=\Delta_hX(n)\), and
\(g=m(n+2h)-m(n)\). Lemma 7.1 gives the exact identity
\[
\Delta_hY=A_h+\tfrac32g(n+2h)^{3/4}
-\tfrac32\theta\Delta_h(n^{3/4})+\Delta_h E,
\tag{4.5}
\]
where
\[
A_h(x)=\tfrac32x^{3/2}\Delta_h(x^{3/4})
-\tfrac12\Delta_h(x^{9/4}),\qquad
A_h''(x)=O(h^2P^{-7/4}).
\]
For the derivative assertion, write \(A_h(x)=x^{9/4}a(2h/x)\), where
\(a(z)=\tfrac32((1+z)^{3/4}-1)-\tfrac12((1+z)^{9/4}-1)\).
The identities \(a(0)=a'(0)=0\) and bounded derivatives of
\(a(z)/z^2\) near zero give the estimate. No floor is differentiated.

Deleting the last two terms of (4.5) from the phase costs
\[
O(uhP^{3/4}+uP^{1/4}),
\tag{4.6}
\]
because \(\Delta_h(x^{3/4})=O(hP^{-1/4})\),
\(E(x)=O(P^{-3/4})\), and \(|e(t)-1|\le2\pi|t|\).

Partition the interval into level sets of \(G=\lfloor\delta\rfloor\).
Since \(\delta'(x)\asymp hP^{-1/2}\), there are
\(O(1+hP^{1/2})\) cells; their total length is at most \(P\).
On a cell put \(z=\delta-G\). It is monotone in \([0,1)\), and exactly
\[
g=G+\kappa,\qquad
\kappa=z+b(X(n))-b(X(n+2h))\in\{0,1\}.
\tag{4.7}
\]
Define the two smooth phases on this cell by
\[
F_{G,\epsilon}(x)=uA_h(x)+\tfrac{3u}{2}(G+\epsilon)(x+2h)^{3/4}
+\tfrac i2\delta(x)+\tfrac k2\Delta_h(x^{9/8}),
\quad\epsilon\in\{0,1\}.
\]
The exponential left after (4.6) is exactly
\[
\begin{split}
&(1-z)e(F_{G,0})+z e(F_{G,1})\\
&\quad+\bigl(b(X(n))-b(X(n+2h))\bigr)
\bigl(e(F_{G,1})-e(F_{G,0})\bigr).
\end{split}
\tag{4.8}
\]
Apply Lemma 4.3 with \(R=\lfloor P^{1/4}\rfloor\) to the two
sawtooths. Their total error after the partition is
\(O(P^{5/6}+P^{3/4}\log P)\): the cells partition the same input
set, and the multiplying difference of exponentials has modulus
at most two.

On every cell \(G+\epsilon\asymp hP^{1/2}\), and
\[
F_{G,\epsilon}''(x)
=-\tfrac9{32}u(G+\epsilon)(x+2h)^{-5/4}
+O(uh^2P^{-7/4}+|i|hP^{-3/2}+|k|hP^{-15/8}).
\tag{4.9}
\]
The error is \(o(uhP^{-3/4})\), uniformly in the stated ranges.
The second-derivative estimate [2, Theorem 2.2] has scale
\(\lambda\asymp uhP^{-3/4}\) and a bounded curvature ratio.
After \(n=2r+1\) it has the same form for odd integers, with
implicit constants. Summing over all cells, and using partial
summation for the monotone weights \(z\) and \(1-z\), gives
\[
\ll (uh)^{1/2}P^{5/8}+(h/u)^{1/2}P^{7/8}.
\tag{4.10}
\]
Each nonzero Fourier mode adds either \(rX(x)\) or \(rX(x+2h)\)
to one of the phases \(F_{G,\epsilon}\). Its curvature has size
\(|r|P^{-1/2}\), which dominates (4.9), since
\[
\frac{uhP^{-3/4}}{|r|P^{-1/2}}\ll_C P^{-1/8}
\qquad(1\le |r|\le R).
\]
There is no curvature-collision regime in this proof. Summing
the second-derivative estimate over all gap cells costs, per mode,
\[
\ll |r|^{1/2}P^{3/4}+h|r|^{-1/2}P^{3/4}.
\]
The Fourier weights are \(O(1/|r|)\), so their total is
\(O(R^{1/2}P^{3/4}+hP^{3/4})\). Collecting the costs gives
\[
\begin{split}
\ll_C {}&(uh)^{1/2}P^{5/8}+(h/u)^{1/2}P^{7/8}
+P^{7/8}+hP^{3/4}\\
&+uhP^{3/4}+uP^{1/4}+P^{5/6}+P^{3/4}\log P.
\end{split}
\]
Here \(uh\ll_C P^{1/8}\) and \(u\ge1/2\). Every term is
\(O_C(P^{7/8}(1+h^{1/2}))\). Endpoint cells are included;
no estimate is extended across their boundaries. \(\square\)

**Theorem 4.5 (restricted mixed exponential sums).** For every fixed
\(C\ge1\), uniformly over nonzero integer triples \((i,j,k)\) with
\(\max(|i|,|j|,|k|)\le CP^{1/24}\), one has
\[
\left|\sum_{\substack{P<n\le2P\\n\ \mathrm{odd}}}
e\left(\tfrac i2 n^{3/2}+\tfrac j2m(n)^{3/2}
+\tfrac k2n^{9/8}\right)\right|\ll_C P^{23/24}.
\tag{4.11}
\]

*Proof.* If \(j\ne0\), apply the van der Corput differencing
inequality [2] to the sequence indexed by odd integers, with
\(H=\lfloor P^{1/12}\rfloor\). Writing \(T_h\) for (4.4), it gives
\[
|S|^2\ll \frac{P^2}{H}+\frac P H\sum_{1\le h<H}|T_h|
\ll_C \frac{P^2}H+P^{15/8}H^{1/2}
\ll_C P^{23/12}.
\]
If \(j=0\), the phase is smooth. For \(i\ne0\), its curvature
is \(\asymp |i|P^{-1/2}\), because
\(|k/i|P^{-3/8}\ll_C P^{-1/3}\). The bound is
\(O_C(P^{37/48}+P^{1/4})\). For \(i=0\), one has \(k\ne0\),
curvature \(\asymp |k|P^{-7/8}\), and bound
\(O_C(P^{7/12}+P^{7/16})\). Both are smaller than (4.11).
\(\square\)

**Corollary 4.6 (three formal signs).** Put
\(v=\lfloor m^{3/2}\rfloor\). Every sign class of
\[
\bigl(\psi(n^{3/2}),\psi(m^{3/2}),\psi(v^{1/2})\bigr)
\]
on odd \(n\le N\) has count
\[
\frac N{16}+O\bigl(N^{23/24}(\log(2N))^3\bigr).
\tag{4.12}
\]
In particular, \(\mathrm H(OOEE;\delta)\) holds for every
\(0<\delta<1/24\).

*Proof.* On a dyadic block,
\[
|v^{1/2}-n^{9/8}|
\le |v^{1/2}-m^{3/4}|+|m^{3/4}-X^{3/4}|
\ll P^{-9/8}+P^{-3/8}.
\]
Replacing the third phase coordinate in (4.11) by \(v^{1/2}\)
costs \(O_C(|k|P^{5/8})=O_C(P^{2/3})\). Apply the
three-dimensional Erdős--Turán--Koksma inequality, as in Proposition
4.2, to the points
\[
\bigl(\{X/2\},\{Y/2\},\{v^{1/2}/2\}\bigr),
\]
with cutoff \(\lfloor P^{1/24}\rfloor\) on this block. Its box
discrepancy is \(O(P^{23/24}(\log(2P))^3)\).
The eight half-cube boxes encode
the three signs exactly. Summing over dyadic blocks proves
(4.12) and bounds all seven nonempty sign products by the same error.
The cutoff is chosen separately on each block; no uniformity
from a large block is assumed on smaller ones. \(\square\)

This establishes the hypothesis used for four-step certificates.
It does not estimate the expanding third-level coordinate \(v^{3/2}\)
or every formal chain required at length five. The next subsection
handles the \(OOEOE\) chain.

### 4.3 The fifth-letter split of OOEO

Write
\[
X=n^{3/2},\quad m=\lfloor X\rfloor,\quad Y=m^{3/2},
\quad v=\lfloor Y\rfloor,\quad U=v^{1/2},\quad
w=\lfloor U\rfloor,\quad W=w^{3/2}.
\]
The four formal coordinates for \(OOEOE\) are \(X,Y,U,W\).
The new floor is handled by centering its Fourier expansion at the
integer part of a smooth coefficient. This introduces many intervals;
the next two lemmas keep their boundary cost explicit.

**Lemma 4.7 (a centered Fourier expansion).** For \(0\le\beta\le1\), put
\[
a_r(\beta)=\int_0^1e(-(\beta+r)t)\,dt .
\]
For integral \(T\ge2\), uniformly in real \(t\) and \(\beta\),
\[
e(-\beta\{t\})=\sum_{|r|\le T}a_r(\beta)e(rt)+O(E_T(t)),
\qquad
|a_r(\beta)|+|a_r'(\beta)|\ll(1+|r|)^{-1}.
\tag{4.13}
\]
Here \(E_T\) is as in Lemma 4.3. If \(B=N+\beta\), \(N\in\mathbb Z\),
then \(e(-B\{t\})=e(-Nt)e(-\beta\{t\})\) exactly.
On an interval where \(N=\lfloor B(x)\rfloor\) is fixed and
\(\beta(x)\) is monotone, the sum over \(|r|\le T\) of the
supremum norms and total variations of \(a_r(\beta(x))\)
is \(O(\log(2T))\).

*Proof.* The integral defines the coefficients also at the removable
singularities of
\[
a_r(\beta)=\frac{1-e(-\beta)}{2\pi i(r+\beta)}.
\]
Integration by parts gives the asserted bounds for \(|r|\ge2\),
including for the derivative with respect to \(\beta\); the remaining
coefficients and their derivatives are bounded by their integrals.
For \(|r|\ge2\), the coefficient is
\((1-e(-\beta))/(2\pi ir)+O(r^{-2})\), uniformly in \(\beta\).
The tail of the first series is bounded by the argument of Lemma 4.3,
and the absolutely convergent remainder has tail \(O(T^{-1})\).
Near an integer the paired \(r,-r\) terms are bounded as in that lemma.
At the integer itself both sides are bounded and \(E_T=1\).
This proves (4.13) at every point. Finally the variation of \(\beta\)
on one interval is at most one, and summing the coefficient bounds
gives the logarithm. \(\square\)

**Lemma 4.8 (mixed sums over the frequency intervals).** Set
\[
J_0=P^{1/48},\qquad H=\lfloor P^{1/12}\rfloor .
\]
Let \(1\le |k|\le J_0\), \(1/2\le u\le J_0/2\), and \(|i|\le J_0\).
Partition a subinterval of \([P,2P]\) into \(D\) intervals \(I\), with
\[
D\ll |k|P^{9/16},\qquad |I|\ll L:=P^{7/16}/|k|.
\]
For a fixed constant \(C\), define
\[
M_I=\sup_{\substack{|R|\le C|k|P^{9/16}\\ I'\subseteq I}}
\left|\sum_{\substack{n\in I'\\ n\ \mathrm{odd}}}
e\left(\tfrac i2X(n)+uY(n)+\tfrac k2 n^{27/16}+Rn^{9/8}\right)\right|.
\]
The second supremum ranges over subintervals. Then
\[
\sum_I M_I\ll_C P^{23/24}.
\tag{4.14}
\]
The constants in the partition assumptions are fixed. In particular,
this is a bound after summing all the frequency intervals, not a
rescaling of a full-block discrepancy estimate.

*Proof.* Fix a shift \(1\le h<H\). The exact carry argument of
Lemma 4.4 applies on every \(I\). The additional smooth part has
differenced second derivative
\[
O\bigl(|i|hP^{-3/2}+|k|hP^{-21/16}
+|R|hP^{-15/8}\bigr)
=O_C\bigl(J_0hP^{-3/2}+|k|hP^{-21/16}\bigr).
\]
This is \(o(uhP^{-3/4})\). Thus the zero-mode curvature and the
dominance of every nonzero carry mode are unchanged.

Intersecting the frequency intervals with the gap cells produces
\(O(D+hP^{1/2})\) cells in total: on an interval of length \(\ell\),
the gap function has variation \(O(hP^{-1/2}\ell)\).
Retaining these boundaries, the zero carry modes cost
\[
\ll (uh)^{1/2}P^{5/8}
+(h/u)^{1/2}P^{7/8}
+D(uh)^{-1/2}P^{3/8}.
\]
With carry cutoff \(R_0=\lfloor P^{1/4}\rfloor\), the nonzero modes cost
\[
\ll R_0^{1/2}P^{3/4}+hP^{3/4}+DP^{1/4}.
\]
These follow by applying the second-derivative estimate on every
intersection, exactly as in (4.10). The weights \(z,1-z\) in the
carry identity have uniformly bounded variation on each intersection.

The discarded floor terms cost \(O(uhP^{3/4}+uP^{1/4})\).
The truncated carry error costs \(O(P^{5/6}+P^{3/4}\log P)\)
over the whole partition. For each local sum, its two endpoints
\(n,n+2h\) lie in the same \(I\), so this error is bounded by a fixed
multiple of \(\sum_{n\in I}E_{R_0}(X(n))\). The disjoint intervals
therefore charge (4.3) only once. The same bounds hold after taking
the suprema over \(R\) and subintervals, because their local bounds
use only \(|I|\), its gap-cell count, and this nonnegative error sum.

If \(B_h\) denotes the sum over \(I\) of those supremum bounds for
the differenced sums, the collected costs imply
\[
B_h\ll_C P^{7/8}(1+h^{1/2})
+|k|P^{15/16}h^{-1/2}.
\tag{4.15}
\]
Indeed \(uh\le P^{5/48}/2\), \(u\ge1/2\), and
\(DP^{1/4}\ll |k|P^{13/16}\le P^{5/6}\).

Apply van der Corput's inequality to each local sum, padding by zero
inside an interval of length \(O(L)\) when taking a subinterval.
Since \(H\ll L\), its squared bound is
\[
O\left(\frac LH\left(\#I+\sum_{h<H}|T_{I,h}|\right)\right),
\]
where \(\#I\) counts odd integers and endpoint constants are harmless.
Cauchy--Schwarz over the \(D\) intervals, together with \(DL\ll P\),
gives
\[
\begin{split}
\left(\sum_I M_I\right)^2
&\ll_C \frac{P^2}{H}+\frac P H\sum_{h<H}B_h\\
&\ll_C \frac{P^2}{H}+P^{15/8}H^{1/2}
+|k|P^{31/16}H^{-1/2}
\ll_C P^{23/12}.
\end{split}
\]
The three largest exponents are respectively
\(2-1/12\), \(15/8+1/24\), and \(1/48+31/16-1/24\),
all equal to \(23/12\). This proves (4.14), including partial
endpoint intervals. \(\square\)

**Theorem 4.9 (four formal coordinates).** Uniformly over nonzero
integer quadruples with \(\max(|i|,|j|,|\ell|,|k|)\le P^{1/48}\),
\[
\left|\sum_{\substack{P<n\le2P\\n\ \mathrm{odd}}}
e\left(\tfrac i2X+\tfrac j2Y+\tfrac\ell2U+\tfrac k2W\right)\right|
\ll P^{23/24}\log(2P).
\tag{4.16}
\]

*Proof.* We first bound the error in (4.13) along \(U(n)\).
The comparison \(U=n^{9/8}+O(P^{-3/8})\) from Corollary 4.6 gives,
for positive integer \(q\),
\[
\left|\sum e(qU)\right|
\ll q^{1/2}P^{9/16}+q^{-1/2}P^{7/16}+qP^{5/8}.
\]
Erdős--Turán with cutoff \(\lfloor P^{1/8}\rfloor\) gives interval
discrepancy \(O(P^{7/8})\) for \(\{U(n)\}\). The distance-strip
argument of Lemma 4.3 therefore gives
\[
\sum E_T(U(n))\ll P\log(2T)/T+P^{7/8}.
\tag{4.17}
\]
All sums here are over the same odd-input block.

When \(k=0\), Theorem 4.5 and the comparison for \(U\) prove (4.16).
Suppose \(k\ne0\), and put \(\theta=\{X\}\), \(\xi=\{U\}\).
Taylor's theorem, with its second derivative bounded on the unit
floor intervals, gives
\[
\begin{split}
U&=n^{9/8}-\tfrac34\theta n^{-3/8}+O(P^{-9/8}),\\
W&=n^{27/16}-\tfrac98\theta n^{3/16}
-\tfrac32 n^{9/16}\xi+O(P^{-9/16}).
\end{split}
\tag{4.18}
\]
For clarity, \(U=m^{3/4}+O(P^{-9/8})\).
Also \(W=v^{3/4}-(3/2)v^{1/4}\xi+O(P^{-9/16})\),
\(v^{3/4}=m^{9/8}+O(P^{-9/16})\), and
\(v^{1/4}=n^{9/16}+O(P^{-15/16})\); expanding \(m=X-\theta\)
proves both displayed formulas.

Set
\[
B(x)=\tfrac{3k}{4}x^{9/16},\qquad
C(x)=\tfrac{9k}{16}x^{3/16},\qquad T=\lfloor P^{1/8}\rfloor.
\]
Partition by \(N=\lfloor B(x)\rfloor\), and put \(\beta=B-N\).
Since \(|B'|\asymp |k|P^{-7/16}\), this partition has
\(D\ll |k|P^{9/16}\) intervals, each of length
\(O(P^{7/16}/|k|)\). The two endpoint intervals can be shorter.
The total variation of \(\beta\) on any one interval is at most one.

Use (4.18), then expand \(e(-B\{U\})\) by Lemma 4.7. Formula
(4.17) bounds its total truncation error by \(O(P^{7/8}\log P)\);
the initial Taylor error is \(O(|k|P^{7/16})\).
On a fixed interval and for \(|r|\le T\), set
\[
R=r-N+\ell/2 .
\]
This is a fixed frequency on that interval. The corresponding phase is
\[
\tfrac i2X+\tfrac j2Y+\tfrac k2 n^{27/16}+RU-C\theta .
\]
The first formula in (4.18) replaces it by
\[
\tfrac i2X+\tfrac j2Y+\tfrac k2 n^{27/16}+Rn^{9/8}
-\bigl(C+\tfrac34Rn^{-3/8}\bigr)\theta
+O(|R|P^{-9/8}).
\]
The essential cancellation is the exact identity
\[
C+\tfrac34Rn^{-3/8}
=\tfrac34n^{-3/8}(B+R)
=\tfrac34n^{-3/8}(r+\beta+\ell/2).
\tag{4.19}
\]
Its absolute value is \(O((T+P^{1/48})P^{-3/8})\), so the
remaining \(\theta\)-term can be deleted. Since
\(|R|\ll |k|P^{9/16}\), all these replacements, summed with the
coefficient masses, cost
\[
O\bigl((|k|P^{7/16}+P^{5/8}(T+P^{1/48}))\log P\bigr)
\ll P^{3/4}\log P.
\]
Thus it remains to estimate the smooth-frequency phases in Lemma 4.8.
If \(j\ne0\), conjugation if needed makes \(u=|j|/2\ge1/2\).
Partial summation for the coefficients \(a_r(\beta)\), whose summed
supremum norms and variations are \(O(\log P)\) on each interval,
and (4.14) give \(O(P^{23/24}\log P)\).

If \(j=0\), differentiate with \(R\) fixed. The remaining phase
\(\Phi=iX/2+kn^{27/16}/2+Rn^{9/8}\) satisfies
\[
\begin{split}
\Phi''(x)&=\tfrac{3i}{8}x^{-1/2}
+\tfrac{297k}{512}x^{-5/16}
+\tfrac{9R}{64}x^{-7/8}\\
&=\tfrac{243k}{512}x^{-5/16}
+O\bigl(|i|P^{-1/2}+(T+|\ell|+1)P^{-7/8}\bigr).
\end{split}
\]
The last equality substitutes \(R=-B(x)+(r+\beta(x)+\ell/2)\)
only after differentiation. The error is \(o(|k|P^{-5/16})\).
Summing the second-derivative bounds over every frequency interval
costs
\[
O\bigl(|k|^{1/2}P^{27/32}
+D|k|^{-1/2}P^{5/32}\bigr)
\ll |k|^{1/2}(P^{27/32}+P^{23/32}).
\]
The logarithmic coefficient mass still leaves this below (4.16).
All zero coordinates and both signs of every mode have now been covered.
\(\square\)

**Corollary 4.10 (the OOEO split).** Each of the sixteen formal
sign classes of \((\psi(X),\psi(Y),\psi(U),\psi(W))\) over odd
\(n\le N\) has count
\[
N/32+O(N^{47/48}).
\tag{4.20}
\]
In particular, for each \(a\in\{OOEOE,OOEOO\}\),
\[
\#\{n\le N:\operatorname{word}_5(n)=a\}
=N/32+O(N^{47/48}).
\]
The hypothesis \(\mathrm H(OOEOE;1/48)\) holds.

*Proof.* Apply four-dimensional Erdős--Turán--Koksma on each dyadic
block with cutoff \(\lfloor P^{1/48}\rfloor\). Theorem 4.9 bounds
its box discrepancy by
\[
O\bigl(P^{47/48}+P^{23/24}(\log(2P))^5\bigr)
=O(P^{47/48}).
\]
The sixteen half-cubes have volume \(1/16\); the number of odd
inputs is \(P/2+O(1)\). Summing dyadically proves (4.20).
All fifteen nonempty sign products are bounded by summing these
discrepancies. The signs \((-1,+1,-1,\pm1)\) select the two
actual words by Lemma 2.2. This does not count the formal chain
through the expanding third-level coordinate \(v^{3/2}\).
\(\square\)

## 5. Finite-depth descent densities

**Lemma 5.1 (minimal certificates through length five).** The contracting
words of length at most five with no proper contracting prefix are
exactly
\[
E,\qquad OE,\qquad OOEE,\qquad OOOEE,\qquad OOEOE.
\tag{5.1}
\]

*Proof.* An \(E\)-rooted word already contracts at its first letter,
and an \(OE\)-rooted word contracts at its second. Every remaining
word begins with \(OO\). At length three, even two odd letters
give \(3^2>2^3\), so no new certificate appears. At length four,
contraction requires at most two odd letters, giving only \(OOEE\).
After excluding that prefix, the possible fourth-level prefixes are
\(OOEO\), \(OOOE\), and \(OOOO\). At length five, contraction
requires at most three odd letters because \(3^3<2^5<3^4\).
The first two prefixes must therefore end with \(E\), and the third
cannot contract. This proves (5.1). \(\square\)

**Theorem 5.2 (unconditional four-step density).** One has
\[
\#(\mathcal C_4\cap[1,N])
=\frac{13N}{16}+O\bigl(N^{23/24}(\log(2N))^3\bigr).
\]

*Proof.* Lemma 5.1 gives the disjoint prefix classes \(E\), \(OE\),
and \(OOEE\). Theorem 3.1 supplies the first two counts. The
\(OOEE\) class is the sign class \((-1,+1,+1)\) in Corollary 4.6,
so has count \(N/16+O(N^{23/24}(\log(2N))^3)\).
Their densities add to \(1/2+1/4+1/16=13/16\). \(\square\)

**Theorem 5.3 (a five-step subfamily of density \(27/32\)).** Let
\[
\mathcal D_5=\mathcal C_4\ \cup\
\{n\ge2:\operatorname{word}_5(n)=OOEOE\}.
\]
Then \(\mathcal D_5\subseteq\mathcal C_5\) and
\[
\#(\mathcal D_5\cap[1,N])=27N/32+O(N^{47/48}).
\]
In particular the lower natural density of \(\mathcal C_5\) is at
least \(27/32\).

*Proof.* The added prefix is disjoint from \(E,OE,OOEE\), and
\(3^3<2^5\) certifies its contraction. Add Corollary 4.10 to
Theorem 5.2, absorbing the smaller four-step error. The main terms
sum to \(13/16+1/32=27/32\). This does not assert that
\(\mathcal D_5\) exhausts \(\mathcal C_5\). \(\square\)

**Theorem 5.4 (conditional full five-step density).** Suppose
\(\mathrm H(OOOEE;\delta)\) holds for some \(\delta>0\). Then
\[
\#(\mathcal C_5\cap[1,N])
=\frac{7N}{8}+O(N^{1-\min(1/48,\delta)}).
\]
The qualitative hypothesis \(\mathrm H_0(OOOEE)\) suffices for
natural density \(7/8\).

*Proof.* Lemma 5.1 shows that \(\mathcal C_5\) is the disjoint
union of \(\mathcal D_5\) and the \(OOOEE\) class. Proposition 4.1
counts the latter as \(N/32+O(N^{1-\delta})\), or with error
\(o(N)\) in the qualitative case. Add Theorem 5.3. \(\square\)

The exact fractions and their analytic requirements can be read together:

| Certificate family | Minimal prefixes added | Density | Status |
|---|---|---|---|
| \(\mathcal C_1\) | \(E\) | \(1/2\) | Unconditional |
| \(\mathcal C_2\) | \(OE\) | \(3/4\) | Theorem 3.1 |
| \(\mathcal C_4\) | \(OOEE\) | \(13/16\) | Theorem 5.2 |
| \(\mathcal D_5\subseteq\mathcal C_5\) | \(OOEOE\) | \(27/32\) | Theorem 5.3 |
| \(\mathcal C_5\) | \(OOOEE\) | \(7/8\) | Conditional: Theorem 5.4 |

For the remaining word \(OOOEE\), the four tested real images are
\((n^{3/2},m^{3/2},v^{3/2},z^{1/2})\), with
\(z=\lfloor v^{3/2}\rfloor\). The hypothesis concerns all fifteen
nonempty sign products of these coordinates. This formal chain is
different from the one proved in Corollary 4.10.

Separately, if \(\mathrm H_0(w)\) holds for every odd-rooted word of
length four, all eight such classes have density \(1/16\).
This complete census is conditional as well; it is stronger than the
three-sign estimate proved in Corollary 4.6.

## 6. The fixed-depth reduction to density-one certificates

**Hypothesis \(\mathrm{FD}\).** For every fixed \(d\ge1\) and every
odd-rooted word \(w\) of length \(d\),
\[
\#\{n\le N:\operatorname{word}_d(n)=w\}=2^{-d}N+o_w(N).
\]
No common error rate in \(d\) is assumed. The family
\(\mathrm H_0(w)\) over all such words implies \(\mathrm{FD}\).

**Theorem 6.1 (conditional density-one certificate theorem).** Under
\(\mathrm{FD}\), \(\mathcal C_\infty\) has natural density one.

*Proof.* Put \(p=\log2/\log3>1/2\). A word with no contracting
prefix through length \(d\) must in particular have at least \(pd\)
odd letters at length \(d\). All such words begin with \(O\).
For a uniformly chosen odd-rooted word of length \(d\), the number
of odd letters is distributed as \(1+B_{d-1}\), where
\(B_{d-1}\) is a binomial random variable with parameters
\((d-1,1/2)\). This is an auxiliary count on words, not a stochastic
model asserted for the Juggler orbit.

Choose \(q=(p+1/2)/2\), so \(1/2<q<p\). For all sufficiently
large fixed \(d\), \(pd-1\ge q(d-1)\). For \(t>0\), the
exponential Markov inequality and the binomial generating function give
\[
\Pr(B_{d-1}\ge q(d-1))
\le\left(\frac{1+e^t}{2e^{qt}}\right)^{d-1}.
\]
The logarithm of the expression in parentheses is zero at \(t=0\)
and has derivative \(1/2-q<0\) there. Hence some fixed \(t>0\)
makes it a number \(\vartheta<1\).

For fixed \(d\), \(\mathrm{FD}\) and a finite sum over surviving
words show that the natural density of \(\mathbb N\setminus\mathcal C_d\)
is their number divided by \(2^d\). It is at most
\(\tfrac12\vartheta^{d-1}\) for sufficiently large \(d\).
Since \(\mathcal C_d\subseteq\mathcal C_\infty\),
\[
\overline{\operatorname{dens}}(\mathbb N\setminus\mathcal C_\infty)
\le\tfrac12\vartheta^{d-1}.
\]
Letting \(d\to\infty\) proves the assertion. In this argument
\(N\to\infty\) is taken first, with \(d\) fixed. \(\square\)

The conclusion concerns descent below the initial value. It does not
prove that a descended value reaches \(1\), or that subsequent orbit
samples avoid an exceptional set. Even a density-zero exceptional set
can contain a nontrivial cycle. No interchange of the two limits, and
no assertion of finite stopping time for every start, follows from
Theorem 6.1.

## 7. Exact floor defects and the remaining kernel estimate

For \(n\ge3\), write
\[
X=n^{3/2},\quad m=\lfloor X\rfloor,\quad\theta=X-m,
\qquad Y=m^{3/2},\quad v=\lfloor Y\rfloor,\quad\theta_2=Y-v.
\]

**Lemma 7.1 (one-signed linearization).** One has
\[
m^{3/2}=\tfrac32mn^{3/4}-\tfrac12n^{9/4}+E(n),
\qquad
0\le E(n)\le\tfrac38(n^{3/2}-1)^{-1/2}\le\tfrac12n^{-3/4}.
\]

*Proof.* Let \(a=\sqrt m\), \(b=\sqrt X\). Direct factorization gives
\[
E=a^3-\tfrac32a^2b+\tfrac12b^3
=\tfrac12(a-b)^2(2a+b)\ge0.
\]
Moreover \(\theta=b^2-a^2\), and \(Ea\le\tfrac38\theta^2\)
follows from
\(4a(2a+b)\le3(a+b)^2\), equivalent to
\((5a+3b)(a-b)\le0\). Thus
\(E\le\tfrac38m^{-1/2}\), which is at most
\(\tfrac38(X-1)^{-1/2}\). Finally
\((X-1)^{-1/2}\le\tfrac43X^{-1/2}\) for \(n\ge3\).
\(\square\)

**Lemma 7.2 (gap and carry).** For an integer \(h\ge1\), set
\(\Delta_hX(n)=X(n+2h)-X(n)\). Then
\[
m(n+2h)-m(n)=\lfloor\Delta_hX(n)\rfloor+\kappa_h(n),
\quad
\kappa_h(n)=\mathbf1_{\{X(n)\}+\{\Delta_hX(n)\}\ge1}\in\{0,1\}.
\]

*Proof.* Expand \(X(n)+\Delta_hX(n)\) into integer and fractional
parts, and take its floor. The sum of the two fractional parts lies
in \([0,2)\). \(\square\)

For \(1\le h\le P/4\) and \(n\in(P,2P]\), differentiation gives
\((\Delta_hX)'(n)\asymp hP^{-1/2}\). The level sets of
\(\lfloor\Delta_hX\rfloor\) consequently form \(O(1+hP^{1/2})\)
intervals. Full intervals have length \(\asymp P^{1/2}/h\); the
two endpoint intervals can be shorter. A coefficient involving this
floor is frozen only on these intervals. A derivative estimate
proved there must be summed over the partition, or replaced by a
separate global argument with controlled errors.

**Lemma 7.3 (next-level defect).** One has
\[
v^{3/2}=m^{9/4}-\tfrac32v^{1/2}\theta_2-\mathcal R,
\qquad 0\le\mathcal R\le\tfrac38v^{-1/2}\theta_2^2.
\]

*Proof.* Apply Taylor's theorem to \(x^{3/2}\) between \(v\) and
\(v+\theta_2=Y\). Its second derivative is
\(\tfrac34x^{-1/2}\le\tfrac34v^{-1/2}\) on that interval, and is
positive. Rearranging the Taylor formula gives the result.
\(\square\)

These identities alone do not supply cancellation. The restricted
estimate from the earlier draft,

\[
\left|\sum_{\substack{P<n\le2P\\n\ \mathrm{odd}}}
e\bigl(\tfrac i2 n^{3/2}+\tfrac j2m^{3/2}\bigr)\right|
\ll_\varepsilon P^{23/24+\varepsilon},
\quad |i|\le2P^{1/24},\quad1\le|j|\le2P^{1/24},
\tag{7.1}
\]
now follows from Theorem 4.5 with \(k=0\) and \(C=2\).
The remaining kernel target, with \(c_k(n)=\tfrac{3k}{4}n^{9/8}\), is
\[
K_k(P)=\sum_{\substack{P<n\le2P\\n\ \mathrm{odd}}}
e(c_k(n)\theta_2(n)),
\qquad |K_k(P)|\ll_\varepsilon P^{95/96+\varepsilon},
\quad1\le k\le P^{1/24}.
\tag{7.2}
\]
The indices \(i,j,k\) are integers. Estimate (7.1) is unconditional
in this revision; (7.2), with its printed uniformity, remains an
**open target**. Even if (7.2) were established, its transfer to the
mixed-mode families needed at length five would still require proof.
Lemma 4.4 handles half-integer coefficients \(j/2\) directly.
This does not extend the frequency domain of the earlier general
decorated lemma, whose separate applications remain unproved.

Short-interval variants require separate estimates. A bound for a
transition set \(\Omega\subset(P,2P]\) of the form
\(|\Omega|\ll P^a\) implies only
\(|\Omega\cap I|\le\min(|I|,O(P^a))\). It does not imply a bound
proportional to \(|I|/P\). Therefore the earlier localized-kernel
threshold \(|I|\ge P^{29/48+\delta}\) is not asserted here.

### 7.1 An unconditional estimate averaged over a shift

**Proposition 7.4 (shift average).** Let \(L\ge1\), let
\(A_1<\cdots<A_L\) obey
\(|A_t-A_s|\ge a|t-s|\) with \(a>0\), and let \(x_1,\ldots,x_L\)
be real. For
\(S_\lambda=\sum_{t=1}^{L}e(A_t\{x_t+\lambda\})\),
\[
\left|\int_0^1|S_\lambda|^2\,d\lambda-L\right|
\le\frac4\pi\frac La(1+\log L).
\tag{7.3}
\]
For every \(0<\eta<1\), outside a set of shifts of measure at most
\(\eta\),
\[
|S_\lambda|\le
\left[\frac L\eta\left(1+\frac4{\pi a}(1+\log L)\right)\right]^{1/2}.
\]

*Proof.* Expanding the square gives the diagonal term \(L\).
For \(t\ne s\), the integrand
\(e(A_t\{x_t+\lambda\}-A_s\{x_s+\lambda\})\) is periodic in
\(\lambda\). Integrate over a period starting at one of its two
fractional-part breakpoints. There is at most one other interior
breakpoint, giving at most two intervals on which the phase is
affine with slope \(A_t-A_s\). On each interval the integral has
modulus at most \(1/(\pi|A_t-A_s|)\). Hence the off-diagonal
contribution is bounded by
\[
\frac{2}{\pi a}\sum_{t\ne s}\frac1{|t-s|}
=\frac4{\pi a}\sum_{r=1}^{L-1}\frac{L-r}{r}
\le\frac4\pi\frac La(1+\log L).
\]
For \(L=1\) the off-diagonal sum is empty. Markov's inequality
applied to \(|S_\lambda|^2\) gives the second assertion.
\(\square\)

The estimate allows a small exceptional set of shifts. It gives no
bound for a specified shift, including \(\lambda=0\) in (7.2).

### 7.2 Counting the gap cells in a collision estimate

The following lemma repairs the cell-counting problem for a fixed
curvature model. It does not assert that every decorated phase in the
earlier kernel proof meets its hypotheses.

**Lemma 7.5 (curvature estimates over a partition).** Partition an
interval of length at most \(P\) into interval cells, so that every subinterval
of length \(L\) meets \(O(1+\nu L)\) cells. On each cell let \(f\)
be a real \(C^2\) function; its values and derivatives may jump at
cell boundaries. Suppose that a continuous reference function
\(\Lambda\) satisfies \(|\Lambda|\ll M\), and that, for \(0<s\le1\),
both sets
\[
\{|\Lambda|\le sM\},\qquad \{sM<|\Lambda|\le2sM\}
\]
are unions of \(O(1)\) intervals, each set of total length \(O(Ps)\).
Assume
\[
|f''-\Lambda|\le\rho M\quad\text{on every cell},\qquad
0\le\rho\le1/8,\quad 0<M\le1,\quad MP^2\ge1.
\]
All constants in these assumptions are fixed. Then, summing over
integers or over odd integers with the same implicit-constant convention,
\[
\left|\sum e(f(n))\right|
\ll P M^{1/2}+(1+\nu P)M^{-1/2}
+(P/M)^{1/3}+P\rho+1.
\tag{7.4}
\]

*Proof.* Take
\(\tau=\max(4\rho,(MP^2)^{-1/3})\). If \(\tau\) is bounded below
by a positive absolute constant, the terms \(P\rho+(P/M)^{1/3}\)
already give the trivial bound \(O(P)\). Otherwise discard
\(\{|\Lambda|\le\tau M\}\), containing \(O(P\tau+1)\) integers.
Split the remainder into dyadic bands \(|\Lambda|\asymp sM\),
with \(\tau\ll s\ll1\), and the outer set \(|\Lambda|>M\) if necessary.
Each band has total length \(O(Ps)\) and meets
\(O(1+\nu Ps)\) cells. On its intersection with a cell the
curvature has one sign and size \(\asymp sM\).

Apply the second-derivative estimate on every such intersection.
The resulting costs at scale \(s\) are
\[
O\bigl(PM^{1/2}s^{3/2}
+M^{-1/2}s^{-1/2}+\nu P M^{-1/2}s^{1/2}\bigr).
\]
The geometric sum over bands is
\(O(PM^{1/2}+M^{-1/2}\tau^{-1/2}+\nu PM^{-1/2})\).
Our choice gives
\(M^{-1/2}\tau^{-1/2}\le(P/M)^{1/3}\) and
\(P\tau\ll P\rho+(P/M)^{1/3}\), proving (7.4).
One may assign boundary integers to either adjacent cell and
estimate that cell up to its endpoint. \(\square\)

**Proposition 7.6 (the basic frozen-gap collision model).** Let
\(u\ge1/2\), \(1\le h\le P^{1/8}\), \(uh\le P^{1/2}\), and
let \(w>0\) satisfy
\(c_1uhP^{-1/4}\le w\le c_2uhP^{-1/4}\), for fixed
\(0<c_1<c_2\). With \(A_h\) as in Lemma 4.4 and
\(G(x)=\lfloor(x+2h)^{3/2}-x^{3/2}\rfloor\), put
\[
f(x)=uA_h(x)+\tfrac{3u}{2}G(x)(x+2h)^{3/4}+wx^{3/2}.
\]
Then
\[
\left|\sum_{\substack{P<n\le2P\\n\ \mathrm{odd}}}e(f(n))\right|
\ll_{c_1,c_2}
(uh)^{1/2}P^{5/8}+(h/u)^{1/2}P^{7/8}
+(uh)^{-1/3}P^{7/12}+h+P^{1/2}/h+1.
\tag{7.5}
\]

*Proof.* On a gap cell the frozen-coefficient derivative is
\[
f''(x)=-\tfrac9{32}uG(x)(x+2h)^{-5/4}
+\tfrac34wx^{-1/2}+uA_h''(x).
\]
Use the reference function
\[
\Lambda(x)=-\tfrac{27}{32}uhx^{-3/4}+\tfrac34wx^{-1/2},
\qquad M=uhP^{-3/4}.
\]
The identities
\(G(x)=3h\sqrt x+O(1+h^2P^{-1/2})\) and
\(A_h''=O(h^2P^{-7/4})\) show, as a comparison of values,
\[
|f''-\Lambda|\ll M\bigl(h/P+(hP^{1/2})^{-1}\bigr).
\]
This does not differentiate \(G\). The gap-cell partition has
density parameter \(\nu\asymp hP^{-1/2}\).

To verify the sublevel conditions, factor
\(\Lambda(x)=\tfrac34x^{-3/4}(wx^{1/4}-9uh/8)\).
The expression in parentheses is strictly increasing, with
derivative \(\asymp uh/P\) in the stated collision range.
Hence \(|\Lambda|\le sM\) occupies length \(O(Ps)\).
Moreover \(\Lambda'\) has at most one zero, so the sublevel
sets and dyadic bands have a bounded number of components.
Apply Lemma 7.5 with
\(\rho=O(h/P+(hP^{1/2})^{-1})=o(1)\).
Its terms give (7.5); the extra \(M^{-1/2}\) is absorbed by
\((h/u)^{1/2}P^{7/8}\). \(\square\)

For integer \(w\) in the collision range, \(w\ge1\) implies
\(uh\gg P^{1/4}\). Formula (7.5) is then \(O(P^{7/8})\):
its second term is \(h(uh)^{-1/2}P^{7/8}\ll P^{7/8}\),
and the remaining terms are no larger. This verifies that the basic
integer collision band leaves a power saving.

Thus the transition cost need not be paid independently on every
gap cell: a global sublevel argument counts how many cells can meet
each curvature band. To use this in the complete kernel proof one
must still verify the reference-function hypotheses, partition
density, and weighted sums for all additional Fourier modes and
decorations. Neither (7.4) nor (7.5) supplies that verification,
and neither rescales a transition-set bound by an arbitrary
short-interval length.

## 8. Evidence, availability, and remaining work

The status of the principal statements is as follows.

| Statement | Warrant in this version |
|---|---|
| Envelope, branch identity, minimal words, floor defects | Exact proofs in Sections 2, 5, and 7 |
| Certificate density \(3/4\) | Classical analytic proof in Theorem 3.1 |
| Correlation-to-count and Fourier-to-parity implications | Proofs in Propositions 4.1 and 4.2 |
| Certificate density \(13/16\) | Unconditional: Corollary 4.6 and Theorem 5.2 |
| Certificate subfamily density \(27/32\) | Unconditional: Corollary 4.10 and Theorem 5.3 |
| Full five-step certificate density \(7/8\) | Conditional: the \(OOOEE\) hypothesis remains unproved |
| Density-one finite certificates | Conditional on \(\mathrm{FD}\); no depth uniformity assumed |
| Restricted mixed sums | Unconditional: Theorem 4.5 |
| General decorated kernel and short-interval extension | Unproved; no numerical threshold certified |
| Basic frozen-gap collision model | Proposition 7.6; does not certify every decorated phase |
| Shift-averaged estimate | Direct integral proof in Proposition 7.4 |

Supporting software is available in the Balanced Ternary Mathematical
Laboratory repository, [https://github.com/sneakyweasel/btlab](https://github.com/sneakyweasel/btlab).
The accompanying source package contains this manuscript, its LaTeX
build, and an exact-arithmetic validation script. That script checks
the finite certificate list, the indicator identity on a finite census,
and selected algebraic inequalities. A second exact-arithmetic script checks
the differenced identity, carry expansion, and exponent comparisons used in
the four-step repairs. A third checks the exact fifth-letter centering
identity, frozen-frequency curvature coefficient, and interval-boundary
exponent budget. Those checks support reproducibility;
they are not proofs of asymptotic cancellation.

Earlier repository audits and Lean modules concern identities,
inequalities, and arithmetic from the previous draft. This version
claims no Lean formalization of its analytic hypotheses or of the
complete manuscript. Earlier theorem numbers are superseded
and should not be used as citations to unconditional nested estimates.
Companion texts that rely on those estimates require their own review.

The unconditional certificate subfamily proved here has density \(27/32\).
The full five-step density \(7/8\) requires the remaining \(OOOEE\)
correlation hypothesis in Theorem 5.4. Section 7.2 supplies a
partition-aware estimate for a basic collision model, but all
decorated phase families and their weights still need to be
controlled before the former kernel theorem can be restored.
A proof of all fixed-depth counts would imply density-one
certificates by Theorem 6.1; a further argument would still be
required to settle universal termination.

## Acknowledgments and AI assistance

Large language models were used throughout the development of the
earlier draft and this revision, including the formulation and review
of proof arguments, drafting, programming, and discussion of Lean
formalizations. The September 2026 review with OpenAI Codex identified
unresolved analytic steps and prepared this conditional formulation,
its proofs, the subsequent four-step, fifth-letter, and collision-model repairs,
and its release materials. AI assistance and automated
checks are not independent mathematical validation. The author is
responsible for the statements, proofs, code, and final approval of
the preprint. The models are not authors.

## References

1. OEIS Foundation Inc., "Juggler sequence: if n mod 2 = 0 then
   floor(sqrt(n)) else floor(n^(3/2))," *The On-Line Encyclopedia of
   Integer Sequences*, A094683.
   [Sequence record](https://oeis.org/A094683), accessed 9 September 2026.
2. S. W. Graham and G. Kolesnik, *Van der Corput's Method of
   Exponential Sums*, London Mathematical Society Lecture Note Series
   126, Cambridge University Press, 1991.
   [Publisher excerpt](https://beckassets.blob.core.windows.net/product/readingsample/666252/9780521339278_excerpt_001.pdf).
3. L. Kuipers and H. Niederreiter, *Uniform Distribution of Sequences*,
   Wiley-Interscience, New York, 1974. Chapter 2, especially pp. 112--116.
   [University-hosted scan](https://web.maths.unsw.edu.au/~josefdick/preprints/KuipersNied_book.pdf).
4. R. Terras, "A stopping time problem on the positive integers,"
   *Acta Arithmetica* 30 (1976), 241--252.
   [doi:10.4064/aa-30-3-241-252](https://doi.org/10.4064/aa-30-3-241-252).
