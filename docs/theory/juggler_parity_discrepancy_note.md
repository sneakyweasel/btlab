---
title: "Parity Statistics of Nested Floor Powers"
subtitle: "Finite-Step Descent and Conditional Extensions for the Juggler Map"
author: Philippe Cochin
date: 10 September 2026
lang: en
---

## Abstract

The Juggler map applies the integer part of the square root at even
positive integers and of the three-halves power at odd positive integers.
We prove that the starting values admitting a power-envelope descent
certificate within five operations have natural density  \(7/8\).
More precisely, their count up to  \(N\)  is
\(7N/8+O_\varepsilon(N^{127/128+\varepsilon})\)  for every
\(\varepsilon>0\). The four-step subfamily has density  \(13/16\).
The proof uses exact carry identities, centered Fourier expansions,
and van der Corput differencing, with all floor exceptions and
partition endpoints counted. The two five-letter classes  \(OOEOE\)
and  \(OOOEE\)  are treated through their distinct formal chains.
For  \(OOOEE\), the full mixed phase is retained and its signed
curvature is recomputed after each frequency center is frozen.
The complete analytic argument is included in three appendices.
Fair-share densities at every fixed depth would imply density-one
finite certificates; that hypothesis, general decorated estimates,
and short-interval localization remain open. No result asserts
universal arrival at  \(1\).

**Keywords:** Juggler map; nested floor powers; parity correlations;
discrepancy; stopping time; finite-step descent.

## 1. Scope and relation to earlier work

For a positive integer  \(n\), define
\[
J(n)=
\begin{cases}
\lfloor n^{1/2}\rfloor,&n\ \text{even},\\
\lfloor n^{3/2}\rfloor,&n\ \text{odd}.
\end{cases}
\]
This is the Juggler map recorded in OEIS A094683 [1]. The conjecture
that every positive orbit reaches  \(1\)  remains open. The question
studied here is more limited: which distribution estimates for finite
itineraries would imply that many starting values eventually fall below
their initial value?

Single-floor parity estimates follow from classical exponential-sum
methods [2, 3]. Composing floors creates an additional difficulty. For
\(m=\lfloor n^{3/2}\rfloor\)  and  \(\theta=\{n^{3/2}\}\),
\[
m^{3/2}=n^{9/4}-\tfrac32\theta n^{3/4}+O(n^{-3/4}).
\]
The coefficient of the fractional part grows with  \(n\). A theorem for
the smooth phase  \(n^{9/4}\)  therefore does not by itself estimate the
nested phase. Nor does a parity estimate over consecutive starting
values automatically apply to a sparse set of orbit images.

The main result is the five-step certificate count in Theorem 5.4.
The proof distinguishes finite word classification from the analytic
estimates needed to count those words. Sections 4.2--4.3 establish
the four-step estimate and the  \(OOEOE\)  split. Section 4.4 and
Appendices A--C establish the remaining  \(OOOEE\)  mixed-mode bound.
All signs, zero coordinates, Fourier coefficient weights, and
interval boundaries are included.

The single-floor estimate and the conditional all-depth counting
argument use standard methods. The latter is in the spirit of
stopping-time arguments for the Collatz map, such as Terras [4];
no theorem about Collatz is transferred to the Juggler map.
The general  \(95/96\)  kernel target and arbitrary short-interval
extensions from earlier drafts remain unproved. The weaker
\(127/128\)  exponent proved here suffices for the five-step count.

This preprint supersedes the earlier conditional and  \(27/32\)
versions. The proofs have been developed and checked with AI
assistance and exact-arithmetic controls. No independent mathematical
review or complete Lean verification is claimed.

The proof can be read in the following order.

| Part | Role |
|---|---|
| Sections 2--3 | Formal words, exact certificates, and single-floor counts |
| Sections 4.2--4.3 | Four-step estimate and the  \(OOEOE\)  split |
| Section 4.4 and Appendix C | The precise  \(OOOEE\)  mixed-mode theorem |
| Appendix A | Floor exceptions, positive Fourier errors, and exact carries |
| Appendix B | The wave-bearing estimate used in Appendix C |
| Sections 5--6 | Five-step density and the conditional all-depth implication |

## 2. Exact itineraries and the power envelope

Throughout, \(e(t)=\exp(2\pi i t)\), \(\{t\}=t-\lfloor t\rfloor\),
and \(\|t\|\) is the distance from \(t\) to the nearest integer. Define
\[
\psi(t)=(-1)^{\lfloor t\rfloor}
=1-2\mathbf 1_{[1/2,1)}(\{t/2\}).
\]
Thus \(\psi\) equals \(+1\) at an even floor and \(-1\) at an odd
floor, including at integer endpoints. Implied constants are independent
of the scale and of modes in the stated ranges; fixed comparison
constants and any displayed \(\varepsilon\) may enter them.

Let  \(w=w_1\cdots w_d\)  be a word in  \(\{E,O\}\). The itinerary
\(\operatorname{word}_d(n)\)  records the parities of
\(n,J(n),\ldots,J^{d-1}(n)\). It contains  \(d\)  letters and specifies
the  \(d\)  operations that produce  \(J^d(n)\). Write  \(o(w)\)  for the
number of its odd letters.

**Proposition 2.1 (power envelope).** If  \(w\)  is realized at  \(n\), then
\[
\bigl(J^d(n)\bigr)^{2^d}\le n^{3^{o(w)}}.
\]
Consequently, if  \(n\ge2\)  and  \(3^{o(w)}<2^d\), then  \(J^d(n)<n\).

*Proof.* At any positive integer  \(x\), the even operation satisfies
\(J(x)^2\le x\), and the odd operation satisfies  \(J(x)^2\le x^3\).
Suppose a prefix of length  \(r\)  with  \(o\)  odd letters ends at  \(x\)
and obeys  \(x^{2^r}\le n^{3^o}\). An even operation preserves the
right-hand exponent after raising  \(J(x)^2\le x\)  to  \(2^r\); an
odd operation replaces it by  \(3^{o+1}\). Induction starts at the empty
prefix. If  \(3^{o(w)}<2^d\)  and  \(n>1\), the bound is strictly less
than  \(n^{2^d}\), proving descent.  \(\square\)

A word satisfying  \(3^{o(w)}<2^{|w|}\)  is called *contracting*. A
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
\(\mathcal C_d\)  need not equal the set of all starts that descend
within  \(d\)  steps.

For an odd-rooted target word  \(w\), define its *formal chain* for
every odd  \(n\), regardless of whether  \(n\)  realizes  \(w\):
\[
x_1^w(n)=n,\qquad
\xi_t^w(n)=\bigl(x_t^w(n)\bigr)^{p_t},\qquad
x_{t+1}^w(n)=\lfloor\xi_t^w(n)\rfloor\quad(1\le t<d),
\]
where  \(p_t=3/2\)  for  \(w_t=O\)  and  \(p_t=1/2\)  for  \(w_t=E\).
Set  \(s_t^w(n)=\psi(\xi_t^w(n))\), and put  \(\epsilon_t=1\)  for
\(w_{t+1}=E\),  \(\epsilon_t=-1\)  for  \(w_{t+1}=O\).

**Lemma 2.2 (parity and branch indicators).** For real  \(x\),
\(\lfloor x\rfloor\)  is odd exactly when  \(\{x/2\}\in[1/2,1)\).
For every odd  \(n\)  and odd-rooted word  \(w\),
\[
\mathbf1_{\operatorname{word}_d(n)=w}
=2^{-(d-1)}\prod_{t=1}^{d-1}(1+\epsilon_t s_t^w(n)).
\tag{2.1}
\]

*Proof.* Writing  \(x=\lfloor x\rfloor+\{x\}\)  proves the first
assertion, including the half-open endpoints. Each factor divided by
two tests the parity of  \(x_{t+1}^w\). Until the first failed test, the
formal chain agrees with the true orbit, by induction on  \(t\). A
failed test makes the product zero and prevents realization of  \(w\).
If all tests pass, the chains agree through the required letters and
the product is one. The empty product covers  \(d=1\).  \(\square\)

The use of formal chains is essential: the product is defined on every
odd input before any correlation or Fourier expansion is made.

## 3. An unconditional certificate density

Let  \(M(N)=\#\{n\le N:n\text{ odd}\}=N/2+O(1)\), and set
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

*Proof.* Write  \(n=2r+1\)  and  \(g(r)=\tfrac12(2r+1)^{3/2}\).
Then  \(g''(r)=\tfrac32(2r+1)^{-1/2}\). On a dyadic block with
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
Taking  \(H=\lfloor Q^{1/6}\rfloor\)  for sufficiently large  \(Q\)
gives  \(O(Q^{5/6})\). Lemma 2.2 identifies parity with membership in
\([1/2,1)\); summing the dyadic bounds proves the first assertion.
Since  \(S_O=M-2\#OO\), it also proves the count of  \(OO\).

The only minimal contracting words of length at most two are  \(E\)
and  \(OE\). The first class has count  \(\lfloor N/2\rfloor\), and
the second has count  \(M-\#OO=N/4+O(N^{5/6})\). They are disjoint,
and Proposition 2.1 proves the stated certificate count.  \(\square\)

This argument estimates starting values in an interval. It makes no
independence assertion about successive orbit parities.

**Proposition 3.2 (the OE third letter).** One has
\[
\#\{n\le N:\operatorname{word}_3(n)=w\}
=N/8+O(N^{5/6}\log(2N)),
\qquad w\in\{OEE,OEO\}.
\]

*Proof.* For every real  \(x\ge0\),
\[
\lfloor\sqrt{\lfloor x\rfloor}\rfloor=\lfloor\sqrt x\rfloor:
\]
for an integer  \(r\ge0\), the inequalities  \(r^2\le\lfloor x\rfloor\)
and  \(r^2\le x\)  are equivalent. Consequently, with
\(m=\lfloor n^{3/2}\rfloor\), one has
\(\psi(m^{1/2})=\psi(n^{3/4})\)  exactly.

On a dyadic block apply the two-dimensional Erdős--Turán--Koksma
inequality to  \((\{n^{3/2}/2\},\{n^{3/4}/2\})\)  at odd  \(n\),
with cutoff  \(H=\lfloor P^{1/6}\rfloor\). For a nonzero integer
mode  \((i,l)\)  in this range, the second-derivative estimate gives
\[
\left|\sum e\bigl(\tfrac i2n^{3/2}+\tfrac l2n^{3/4}\bigr)\right|
\ll
\begin{cases}
|i|^{1/2}P^{3/4}+|i|^{-1/2}P^{1/4},&i\ne0,\\
|l|^{1/2}P^{3/8}+|l|^{-1/2}P^{5/8},&i=0.
\end{cases}
\]
For  \(i\ne0\), dominance follows from
\(|l/i|P^{-3/4}\le P^{-7/12}\).
Using the product weights of Proposition 4.2, the discrepancy is
\[
O\bigl(P/H+H^{1/2}P^{3/4}\log(2H)+P^{5/8}\log(2H)\bigr),
\]
hence  \(O(P^{5/6}\log P)\). The two boxes selecting even  \(m\)
and either parity of  \(\lfloor n^{3/4}\rfloor\)  have area  \(1/4\).
Each therefore counts  \(P/8\)  odd starts on the block, with the
stated error. Sum dyadically.  \(\square\)

## 4. Correlation criteria and proved cases

For a fixed odd-rooted word  \(w\)  of length  \(d\)  and nonempty
\(A\subseteq\{1,\ldots,d-1\}\), define
\[
R_{w,A}(N)=\sum_{\substack{n\le N\\n\ \mathrm{odd}}}
\prod_{t\in A}s_t^w(n).
\]

**Hypothesis  \(\mathrm H(w;\delta)\).** For some fixed
\(0<\delta<1\), every nonempty  \(A\)  satisfies
\(R_{w,A}(N)=O_{w,A}(N^{1-\delta})\)  as  \(N\to\infty\).

**Hypothesis  \(\mathrm H_0(w)\).** The same correlations satisfy
\(R_{w,A}(N)=o(N)\), without a prescribed rate.

These are assertions about the formal chains, not assumptions that the
true orbit is a sequence of independent coin tosses. Hypothesis
\(\mathrm H(w;\delta)\)  implies  \(\mathrm H_0(w)\).

**Proposition 4.1 (conditional word count).** Under
\(\mathrm H(w;\delta)\),
\[
\#\{n\le N:\operatorname{word}_d(n)=w\}
=2^{-d}N+O_w(N^{1-\delta}).
\tag{4.1}
\]
Under  \(\mathrm H_0(w)\), the error is  \(o(N)\).

*Proof.* Expand (2.1) and sum. The empty subset contributes
\(2^{-(d-1)}M(N)=2^{-d}N+O(1)\). The other  \(2^{d-1}-1\)  terms
are fixed signed multiples of  \(R_{w,A}\), and there are finitely
many for fixed  \(w\).  \(\square\)

For example,  \(\mathrm H(OOEE;\delta)\)  concerns the seven nonempty
products of
\[
\psi(n^{3/2}),\qquad \psi(m^{3/2}),\qquad \psi(v^{1/2}),
\quad m=\lfloor n^{3/2}\rfloor,\quad v=\lfloor m^{3/2}\rfloor.
\]
Proposition 4.1 then gives the count  \(N/16+O(N^{1-\delta})\)
needed for four-step certificates. Theorem 3.1 establishes the
first estimate. Corollary 4.6 below establishes all seven for every
\(0<\delta<1/24\).

### 4.1 A sufficient Fourier criterion

For  \(\mathbf k=(k_1,\ldots,k_{d-1})\in\mathbb Z^{d-1}\), let
\[
S_{w,\mathbf k}(N)=\sum_{\substack{n\le N\\n\ \mathrm{odd}}}
e\left(\frac12\sum_{t=1}^{d-1}k_t\xi_t^w(n)\right).
\]

**Proposition 4.2 (conditional Fourier-to-parity transfer).** Fix
\(d\ge2\),  \(w\), and  \(0<\eta,\sigma<1\). Suppose, uniformly
over all nonzero integer vectors with
\(\|\mathbf k\|_\infty\le\lfloor N^\eta\rfloor\), that
\[
|S_{w,\mathbf k}(N)|\ll_w N^{1-\sigma}.
\tag{4.2}
\]
Then  \(\mathrm H(w;\delta)\)  holds for every
\(0<\delta<\min(\eta,\sigma)\). The constants may depend on these
fixed parameters.

*Proof.* Apply the multidimensional Erdős--Turán--Koksma inequality
[3, Chapter 2, p. 116] to the points
\(\mathbf y_n=(\{\xi_1^w(n)/2\},\ldots,\{\xi_{d-1}^w(n)/2\})\).
For any half-open axis-parallel box  \(B\subseteq[0,1)^{d-1}\), its
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
The weight sum is  \(O_d((1+\log H)^{d-1})\). With
\(H=\lfloor N^\eta\rfloor\), (4.2) gives box discrepancy
\(O_w(N^{1-\eta}+N^{1-\sigma}(1+\log N)^{d-1})\).
Each nonempty sign product is constant, with value  \(1\)  or  \(-1\),
on the  \(2^{d-1}\)  boxes obtained by splitting each coordinate at
\(1/2\). Its integral over the unit cube is zero. Summing their
discrepancies therefore bounds  \(R_{w,A}\); absorbing the fixed
logarithmic power proves the assertion.  \(\square\)

The criterion needs every indicated mixed mode, including vectors
with zero coordinates and mixed signs. A bound for one undecorated
kernel is not a substitute for (4.2). Qualitatively, cancellation
\(S_{w,\mathbf k}(N)=o(N)\)  for each fixed nonzero  \(\mathbf k\)
also implies  \(\mathrm H_0(w)\): keep  \(H\)  fixed in the displayed
inequality, let  \(N\to\infty\), and then let  \(H\to\infty\).

### 4.2 A nested estimate sufficient for four-step descent

The general decorated kernel is not needed for four-step certificates.
We prove the smaller mixed family directly. Constants in this subsection
may depend on a fixed  \(C\ge1\), but are uniform in all integer modes
in their stated ranges.

**Lemma 4.3 (a truncated carry expansion).** Put
\[
b(t)=\{t\}-\tfrac12,\qquad
b_R(t)=-\sum_{1\le |r|\le R}\frac{e(rt)}{2\pi i r},\qquad
E_R(t)=\min\left(1,\frac1{R\|t\|}\right),
\]
where  \(\|t\|\)  denotes distance to the nearest integer,
\(E_R(t)=1\)  at integers, and  \(R\ge2\)  is integral. Then
\(b(t)=b_R(t)+O(E_R(t))\), including at integers. For
\(X(x)=x^{3/2}\), any interval  \(I\subseteq[P,3P]\)  satisfies
\[
\sum_{\substack{n\in I\\n\ \mathrm{odd}}}E_R(X(n))
\ll \frac{P\log(2R)}R+P^{5/6}.
\tag{4.3}
\]

*Proof.* Away from integers, the Fourier series of  \(b\)  is the
displayed series with infinite range. Summation by parts bounds its
tail by  \(O((R\|t\|)^{-1})\). If  \(\|t\|\le R^{-1}\), pairing
the modes  \(r\)  and  \(-r\)  and using
\(|\sin(2\pi rt)|\le2\pi r\|t\|\)  bounds the finite sum by an
absolute constant. At an integer the finite sum is zero and
\(b(t)=-1/2\), so the asserted bound remains valid.

The proof of Theorem 3.1, with phase  \((2r+1)^{3/2}\), gives interval
discrepancy  \(O(P^{5/6})\)  for the fractional parts  \(\{X(n)\}\)
with odd  \(n\in I\). In particular the number within distance
\(z\le1/2\)  of an integer is  \(O(Pz+P^{5/6})\). Split these
distances at  \(R^{-1},2R^{-1},4R^{-1},\ldots\). Each resulting
weighted count contributes  \(O(P/R+2^{-j}P^{5/6})\), proving
(4.3). This is a bound in terms of the ambient scale  \(P\); it does
not rescale a global exceptional set by the length of  \(I\).
\(\square\)

**Lemma 4.4 (small-shift nested sum).** Write
\(m(n)=\lfloor n^{3/2}\rfloor\),  \(Y(n)=m(n)^{3/2}\), and
\(\Delta_h f(n)=f(n+2h)-f(n)\). If
\[
1\le h\le P^{1/12},\qquad
1\le |j|\le CP^{1/24},\qquad |i|,|k|\le CP^{1/24},
\]
where  \(i,j,k,h\)  are integers, then
\[
\left|\sum_{\substack{P<n\le2P-2h\\n\ \mathrm{odd}}}
e\left(\tfrac i2\Delta_hX(n)+\tfrac j2\Delta_hY(n)
+\tfrac k2\Delta_h(n^{9/8})\right)\right|
\ll_C P^{7/8}(1+h^{1/2}).
\tag{4.4}
\]

*Proof.* Conjugate the whole sum if necessary and put  \(u=j/2>0\).
Thus  \(u\ge1/2\); integrality of  \(u\)  is not required. Set
\(\theta=\{X(n)\}\),  \(\delta=\Delta_hX(n)\), and
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
For the derivative assertion, write  \(A_h(x)=x^{9/4}a(2h/x)\), where
\(a(z)=\tfrac32((1+z)^{3/4}-1)-\tfrac12((1+z)^{9/4}-1)\).
The identities  \(a(0)=a'(0)=0\)  and bounded derivatives of
\(a(z)/z^2\)  near zero give the estimate. No floor is differentiated.

Deleting the last two terms of (4.5) from the phase costs
\[
O(uhP^{3/4}+uP^{1/4}),
\tag{4.6}
\]
because  \(\Delta_h(x^{3/4})=O(hP^{-1/4})\),
\(E(x)=O(P^{-3/4})\), and  \(|e(t)-1|\le2\pi|t|\).

Partition the interval into level sets of  \(G=\lfloor\delta\rfloor\).
Since  \(\delta'(x)\asymp hP^{-1/2}\), there are
\(O(1+hP^{1/2})\)  cells; their total length is at most  \(P\).
On a cell put  \(z=\delta-G\). It is monotone in  \([0,1)\), and exactly
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
Apply Lemma 4.3 with  \(R=\lfloor P^{1/4}\rfloor\)  to the two
sawtooths. Their total error after the partition is
\(O(P^{5/6}+P^{3/4}\log P)\): the cells partition the same input
set, and the multiplying difference of exponentials has modulus
at most two.

On every cell  \(G+\epsilon\asymp hP^{1/2}\), and
\[
F_{G,\epsilon}''(x)
=-\tfrac9{32}u(G+\epsilon)(x+2h)^{-5/4}
+O(uh^2P^{-7/4}+|i|hP^{-3/2}+|k|hP^{-15/8}).
\tag{4.9}
\]
The error is  \(o(uhP^{-3/4})\), uniformly in the stated ranges.
The second-derivative estimate [2, Theorem 2.2] has scale
\(\lambda\asymp uhP^{-3/4}\)  and a bounded curvature ratio.
After  \(n=2r+1\)  it has the same form for odd integers, with
implicit constants. Summing over all cells, and using partial
summation for the monotone weights  \(z\)  and  \(1-z\), gives
\[
\ll (uh)^{1/2}P^{5/8}+(h/u)^{1/2}P^{7/8}.
\tag{4.10}
\]
Each nonzero Fourier mode adds either  \(rX(x)\)  or  \(rX(x+2h)\)
to one of the phases  \(F_{G,\epsilon}\). Its curvature has size
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
The Fourier weights are  \(O(1/|r|)\), so their total is
\(O(R^{1/2}P^{3/4}+hP^{3/4})\). Collecting the costs gives
\[
\begin{split}
\ll_C {}&(uh)^{1/2}P^{5/8}+(h/u)^{1/2}P^{7/8}
+P^{7/8}+hP^{3/4}\\
&+uhP^{3/4}+uP^{1/4}+P^{5/6}+P^{3/4}\log P.
\end{split}
\]
Here  \(uh\ll_C P^{1/8}\)  and  \(u\ge1/2\). Every term is
\(O_C(P^{7/8}(1+h^{1/2}))\). Endpoint cells are included;
no estimate is extended across their boundaries.  \(\square\)

**Theorem 4.5 (restricted mixed exponential sums).** For every fixed
\(C\ge1\), uniformly over nonzero integer triples  \((i,j,k)\)  with
\(\max(|i|,|j|,|k|)\le CP^{1/24}\), one has
\[
\left|\sum_{\substack{P<n\le2P\\n\ \mathrm{odd}}}
e\left(\tfrac i2 n^{3/2}+\tfrac j2m(n)^{3/2}
+\tfrac k2n^{9/8}\right)\right|\ll_C P^{23/24}.
\tag{4.11}
\]

*Proof.* If  \(j\ne0\), apply the van der Corput differencing
inequality [2] to the sequence indexed by odd integers, with
\(H=\lfloor P^{1/12}\rfloor\). Writing  \(T_h\)  for (4.4), it gives
\[
|S|^2\ll \frac{P^2}{H}+\frac P H\sum_{1\le h<H}|T_h|
\ll_C \frac{P^2}H+P^{15/8}H^{1/2}
\ll_C P^{23/12}.
\]
If  \(j=0\), the phase is smooth. For  \(i\ne0\), its curvature
is  \(\asymp |i|P^{-1/2}\), because
\(|k/i|P^{-3/8}\ll_C P^{-1/3}\). The bound is
\(O_C(P^{37/48}+P^{1/4})\). For  \(i=0\), one has  \(k\ne0\),
curvature  \(\asymp |k|P^{-7/8}\), and bound
\(O_C(P^{7/12}+P^{7/16})\). Both are smaller than (4.11).
\(\square\)

**Corollary 4.6 (three formal signs).** Put
\(v=\lfloor m^{3/2}\rfloor\). Every sign class of
\[
\bigl(\psi(n^{3/2}),\psi(m^{3/2}),\psi(v^{1/2})\bigr)
\]
on odd  \(n\le N\)  has count
\[
\frac N{16}+O\bigl(N^{23/24}(\log(2N))^3\bigr).
\tag{4.12}
\]
In particular,  \(\mathrm H(OOEE;\delta)\)  holds for every
\(0<\delta<1/24\).

*Proof.* On a dyadic block,
\[
|v^{1/2}-n^{9/8}|
\le |v^{1/2}-m^{3/4}|+|m^{3/4}-X^{3/4}|
\ll P^{-9/8}+P^{-3/8}.
\]
Replacing the third phase coordinate in (4.11) by  \(v^{1/2}\)
costs  \(O_C(|k|P^{5/8})=O_C(P^{2/3})\). Apply the
three-dimensional Erdős--Turán--Koksma inequality, as in Proposition
4.2, to the points
\[
\bigl(\{X/2\},\{Y/2\},\{v^{1/2}/2\}\bigr),
\]
with cutoff  \(\lfloor P^{1/24}\rfloor\)  on this block. Its box
discrepancy is  \(O(P^{23/24}(\log(2P))^3)\).
The eight half-cube boxes encode
the three signs exactly. Summing over dyadic blocks proves
(4.12) and bounds all seven nonempty sign products by the same error.
The cutoff is chosen separately on each block; no uniformity
from a large block is assumed on smaller ones.  \(\square\)

This establishes the hypothesis used for four-step certificates.
It does not estimate the expanding third-level coordinate  \(v^{3/2}\)
or every formal chain required at length five. The next subsection
handles the  \(OOEOE\)  chain.

### 4.3 The fifth-letter split of OOEO

Write
\[
X=n^{3/2},\quad m=\lfloor X\rfloor,\quad Y=m^{3/2},
\quad v=\lfloor Y\rfloor,\quad U=v^{1/2},\quad
w=\lfloor U\rfloor,\quad W=w^{3/2}.
\]
The four formal coordinates for  \(OOEOE\)  are  \(X,Y,U,W\).
The new floor is handled by centering its Fourier expansion at the
integer part of a smooth coefficient. This introduces many intervals;
the next two lemmas keep their boundary cost explicit.

**Lemma 4.7 (a centered Fourier expansion).** For  \(0\le\beta\le1\), put
\[
a_r(\beta)=\int_0^1e(-(\beta+r)t)\,dt .
\]
For integral  \(T\ge2\), uniformly in real  \(t\)  and  \(\beta\),
\[
e(-\beta\{t\})=\sum_{|r|\le T}a_r(\beta)e(rt)+O(E_T(t)),
\qquad
|a_r(\beta)|+|a_r'(\beta)|\ll(1+|r|)^{-1}.
\tag{4.13}
\]
Here  \(E_T\)  is as in Lemma 4.3. If  \(B=N+\beta\),  \(N\in\mathbb Z\),
then  \(e(-B\{t\})=e(-Nt)e(-\beta\{t\})\)  exactly.
On an interval where  \(N=\lfloor B(x)\rfloor\)  is fixed and
\(\beta(x)\)  is monotone, the sum over  \(|r|\le T\)  of the
supremum norms and total variations of  \(a_r(\beta(x))\)
is  \(O(\log(2T))\).

*Proof.* The integral defines the coefficients also at the removable
singularities of
\[
a_r(\beta)=\frac{1-e(-\beta)}{2\pi i(r+\beta)}.
\]
Integration by parts gives the asserted bounds for  \(|r|\ge2\),
including for the derivative with respect to  \(\beta\); the remaining
coefficients and their derivatives are bounded by their integrals.
For  \(|r|\ge2\), the coefficient is
\((1-e(-\beta))/(2\pi ir)+O(r^{-2})\), uniformly in  \(\beta\).
The tail of the first series is bounded by the argument of Lemma 4.3,
and the absolutely convergent remainder has tail  \(O(T^{-1})\).
Near an integer the paired  \(r,-r\)  terms are bounded as in that lemma.
At the integer itself both sides are bounded and  \(E_T=1\).
This proves (4.13) at every point. Finally the variation of \(\beta\) on one interval is at most one,
and summing the coefficient bounds gives the logarithm. \(\square\)

**Bounded-residual extension.** The same expansion holds for every
real \(\beta\) with \(|\beta|\le B_0\), where \(B_0\) is fixed, with
constants depending only on \(B_0\). Moreover, for a real function
\(\beta(x)\) on an interval \(I\), the condition
\(\|\beta\|_{\infty,I}+\operatorname{TV}_I(\beta)\le B_0\) implies
\[
\sum_{|r|\le T}\left(\|a_r(\beta)\|_{\infty,I}
+\operatorname{TV}_I(a_r\circ\beta)\right)
\ll_{B_0}\log(2T).
\]
Monotonicity is not required for this extension.

*Proof.* For \(|r|>2B_0+2\), the integral formula gives
\(a_r(\beta)=(1-e(-\beta))/(2\pi i r)+O_{B_0}(r^{-2})\),
and \(|a_r|+|a_r'|\ll_{B_0}(1+|r|)^{-1}\). The remaining finitely
many coefficients and derivatives are bounded directly by their
integrals, including at \(r+\beta=0\). The same paired-tail argument
proves the pointwise remainder; bounded cutoffs can be absorbed in
the constant since \(E_T(t)\ge\min(1,2/T)\). Finally
\(\operatorname{TV}_I(a_r\circ\beta)
\le\sup_{|v|\le B_0}|a_r'(v)|\operatorname{TV}_I(\beta)\).
Sum the harmonic bounds. Complex conjugation gives the expansion
with the opposite sign in the exponent. \(\square\)

**Lemma 4.8 (mixed sums over the frequency intervals).** Set
\[
J_0=P^{1/48},\qquad H=\lfloor P^{1/12}\rfloor .
\]
Let  \(1\le |k|\le J_0\),  \(1/2\le u\le J_0/2\), and  \(|i|\le J_0\).
Partition a subinterval of  \([P,2P]\)  into  \(D\)  intervals  \(I\), with
\[
D\ll |k|P^{9/16},\qquad |I|\ll L:=P^{7/16}/|k|.
\]
For a fixed constant  \(C\), define
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

*Proof.* Fix a shift  \(1\le h<H\). The exact carry argument of
Lemma 4.4 applies on every  \(I\). The additional smooth part has
differenced second derivative
\[
O\bigl(|i|hP^{-3/2}+|k|hP^{-21/16}
+|R|hP^{-15/8}\bigr)
=O_C\bigl(J_0hP^{-3/2}+|k|hP^{-21/16}\bigr).
\]
This is  \(o(uhP^{-3/4})\). Thus the zero-mode curvature and the
dominance of every nonzero carry mode are unchanged.

Intersecting the frequency intervals with the gap cells produces
\(O(D+hP^{1/2})\)  cells in total: on an interval of length  \(\ell\),
the gap function has variation  \(O(hP^{-1/2}\ell)\).
Retaining these boundaries, the zero carry modes cost
\[
\ll (uh)^{1/2}P^{5/8}
+(h/u)^{1/2}P^{7/8}
+D(uh)^{-1/2}P^{3/8}.
\]
With carry cutoff  \(R_0=\lfloor P^{1/4}\rfloor\), the nonzero modes cost
\[
\ll R_0^{1/2}P^{3/4}+hP^{3/4}+DP^{1/4}.
\]
These follow by applying the second-derivative estimate on every
intersection, exactly as in (4.10). The weights  \(z,1-z\)  in the
carry identity have uniformly bounded variation on each intersection.

The discarded floor terms cost  \(O(uhP^{3/4}+uP^{1/4})\).
The truncated carry error costs  \(O(P^{5/6}+P^{3/4}\log P)\)
over the whole partition. For each local sum, its two endpoints
\(n,n+2h\)  lie in the same  \(I\), so this error is bounded by a fixed
multiple of  \(\sum_{n\in I}E_{R_0}(X(n))\). The disjoint intervals
therefore charge (4.3) only once. The same bounds hold after taking
the suprema over  \(R\)  and subintervals, because their local bounds
use only  \(|I|\), its gap-cell count, and this nonnegative error sum.

If  \(B_h\)  denotes the sum over  \(I\)  of those supremum bounds for
the differenced sums, the collected costs imply
\[
B_h\ll_C P^{7/8}(1+h^{1/2})
+|k|P^{15/16}h^{-1/2}.
\tag{4.15}
\]
Indeed  \(uh\le P^{5/48}/2\),  \(u\ge1/2\), and
\(DP^{1/4}\ll |k|P^{13/16}\le P^{5/6}\).

Apply van der Corput's inequality to each local sum, padding by zero
inside an interval of length  \(O(L)\)  when taking a subinterval.
Since  \(H\ll L\), its squared bound is
\[
O\left(\frac LH\left(\#I+\sum_{h<H}|T_{I,h}|\right)\right),
\]
where  \(\#I\)  counts odd integers and endpoint constants are harmless.
Cauchy--Schwarz over the  \(D\)  intervals, together with  \(DL\ll P\),
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
\(2-1/12\),  \(15/8+1/24\), and  \(1/48+31/16-1/24\),
all equal to  \(23/12\). This proves (4.14), including partial
endpoint intervals.  \(\square\)

**Theorem 4.9 (four formal coordinates).** Uniformly over nonzero
integer quadruples with  \(\max(|i|,|j|,|\ell|,|k|)\le P^{1/48}\),
\[
\left|\sum_{\substack{P<n\le2P\\n\ \mathrm{odd}}}
e\left(\tfrac i2X+\tfrac j2Y+\tfrac\ell2U+\tfrac k2W\right)\right|
\ll P^{23/24}\log(2P).
\tag{4.16}
\]

*Proof.* We first bound the error in (4.13) along  \(U(n)\).
The comparison  \(U=n^{9/8}+O(P^{-3/8})\)  from Corollary 4.6 gives,
for positive integer  \(q\),
\[
\left|\sum e(qU)\right|
\ll q^{1/2}P^{9/16}+q^{-1/2}P^{7/16}+qP^{5/8}.
\]
Erdős--Turán with cutoff  \(\lfloor P^{1/8}\rfloor\)  gives interval
discrepancy  \(O(P^{7/8})\)  for  \(\{U(n)\}\). The distance-strip
argument of Lemma 4.3 therefore gives
\[
\sum E_T(U(n))\ll P\log(2T)/T+P^{7/8}.
\tag{4.17}
\]
All sums here are over the same odd-input block.

When  \(k=0\), Theorem 4.5 and the comparison for  \(U\)  prove (4.16).
Suppose  \(k\ne0\), and put  \(\theta=\{X\}\),  \(\xi=\{U\}\).
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
For clarity,  \(U=m^{3/4}+O(P^{-9/8})\).
Also  \(W=v^{3/4}-(3/2)v^{1/4}\xi+O(P^{-9/16})\),
\(v^{3/4}=m^{9/8}+O(P^{-9/16})\), and
\(v^{1/4}=n^{9/16}+O(P^{-15/16})\); expanding  \(m=X-\theta\)
proves both displayed formulas.

Set
\[
B(x)=\tfrac{3k}{4}x^{9/16},\qquad
C(x)=\tfrac{9k}{16}x^{3/16},\qquad T=\lfloor P^{1/8}\rfloor.
\]
Partition by  \(N=\lfloor B(x)\rfloor\), and put  \(\beta=B-N\).
Since  \(|B'|\asymp |k|P^{-7/16}\), this partition has
\(D\ll |k|P^{9/16}\)  intervals, each of length
\(O(P^{7/16}/|k|)\). The two endpoint intervals can be shorter.
The total variation of  \(\beta\)  on any one interval is at most one.

Use (4.18), then expand  \(e(-B\{U\})\)  by Lemma 4.7. Formula
(4.17) bounds its total truncation error by  \(O(P^{7/8}\log P)\);
the initial Taylor error is  \(O(|k|P^{7/16})\).
On a fixed interval and for  \(|r|\le T\), set
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
Its absolute value is  \(O((T+P^{1/48})P^{-3/8})\), so the
remaining  \(\theta\) -term can be deleted. Since
\(|R|\ll |k|P^{9/16}\), all these replacements, summed with the
coefficient masses, cost
\[
O\bigl((|k|P^{7/16}+P^{5/8}(T+P^{1/48}))\log P\bigr)
\ll P^{3/4}\log P.
\]
Thus it remains to estimate the smooth-frequency phases in Lemma 4.8.
If  \(j\ne0\), conjugation if needed makes  \(u=|j|/2\ge1/2\).
Partial summation for the coefficients  \(a_r(\beta)\), whose summed
supremum norms and variations are  \(O(\log P)\)  on each interval,
and (4.14) give  \(O(P^{23/24}\log P)\).

If  \(j=0\), differentiate with  \(R\)  fixed. The remaining phase
\(\Phi=iX/2+kn^{27/16}/2+Rn^{9/8}\)  satisfies
\[
\begin{split}
\Phi''(x)&=\tfrac{3i}{8}x^{-1/2}
+\tfrac{297k}{512}x^{-5/16}
+\tfrac{9R}{64}x^{-7/8}\\
&=\tfrac{243k}{512}x^{-5/16}
+O\bigl(|i|P^{-1/2}+(T+|\ell|+1)P^{-7/8}\bigr).
\end{split}
\]
The last equality substitutes  \(R=-B(x)+(r+\beta(x)+\ell/2)\)
only after differentiation. The error is  \(o(|k|P^{-5/16})\).
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
sign classes of  \((\psi(X),\psi(Y),\psi(U),\psi(W))\)  over odd
\(n\le N\)  has count
\[
N/32+O(N^{47/48}).
\tag{4.20}
\]
In particular, for each  \(a\in\{OOEOE,OOEOO\}\),
\[
\#\{n\le N:\operatorname{word}_5(n)=a\}
=N/32+O(N^{47/48}).
\]
The hypothesis  \(\mathrm H(OOEOE;1/48)\)  holds.

*Proof.* Apply four-dimensional Erdős--Turán--Koksma on each dyadic
block with cutoff  \(\lfloor P^{1/48}\rfloor\). Theorem 4.9 bounds
its box discrepancy by
\[
O\bigl(P^{47/48}+P^{23/24}(\log(2P))^5\bigr)
=O(P^{47/48}).
\]
The sixteen half-cubes have volume  \(1/16\); the number of odd
inputs is  \(P/2+O(1)\). Summing dyadically proves (4.20).
All fifteen nonempty sign products are bounded by summing these
discrepancies. The signs  \((-1,+1,-1,\pm1)\)  select the two
actual words by Lemma 2.2. This does not count the formal chain
through the expanding third-level coordinate  \(v^{3/2}\).
\(\square\)

### 4.4 The OOOEE mixed-mode estimate

For this subsection the formal coordinates are
\[
X=n^{3/2},\quad m=\lfloor X\rfloor,\quad Y=m^{3/2},\quad
v=\lfloor Y\rfloor,\quad Z=v^{3/2},\quad w=\lfloor Z\rfloor,\quad U=\sqrt w.
\]
They differ from the chain in Section 4.3.

**Theorem 4.11 (OOOEE mixed modes).** For every fixed  \(C\ge1\)
and every  \(\varepsilon>0\), uniformly over nonzero integer
quadruples with  \(\max(|i|,|j|,|k|,|l|)\le CP^{1/24}\),
\[
\left|\sum_{\substack{P<n\le2P\\n\ \mathrm{odd}}}
e\left(\tfrac12(iX+jY+kZ+lU)\right)\right|
\ll_{C,\varepsilon}P^{127/128+\varepsilon}.
\tag{4.21}
\]

*Proof.* Appendix C provides the full argument using Lemmas A.1--A.4
and Theorem B.1. The cases with  \(k=0\)  are treated directly.
For  \(k\ne0\), two differencings use half-shift cutoffs
\(P^{1/48}\)  and  \(P^{1/24}\). The complete second correlation
has exponent  \(31/32\), including all positive errors. The two
outer inequalities give exponents  \(63/64\)  and  \(127/128\);
their diagonal terms are smaller.  \(\square\)

**Corollary 4.12 (the OOOE split).** Every formal parity-sign class
of  \((X,Y,Z,U)\)  on odd  \(n\le N\)  has count
\[
N/32+O_\varepsilon(N^{127/128+\varepsilon}).
\tag{4.22}
\]
In particular  \(OOOEE\)  and  \(OOOEO\)  each have that count, and
\(\mathrm H(OOOEE;\delta)\)  holds for every  \(0<\delta<1/128\).

*Proof.* On each dyadic block apply Erdős--Turán--Koksma at cutoff
\(\lfloor P^{1/24}\rfloor\)  to the four coordinates divided by two,
as in Proposition 4.2. The sixteen half-cubes all have volume
\(1/16\), and there are  \(P/2+O(1)\)  odd inputs. Absorb the fixed
logarithmic weights in (4.21) into epsilon, then sum dyadically
with each block's own cutoff. The signs  \((-1,-1,+1,\pm1)\)
select the stated actual words. Summing the sixteen discrepancies
also controls every nonempty sign product. The end of Appendix C
gives the endpoint conventions and full dyadic argument.  \(\square\)

## 5. Finite-depth descent densities

**Lemma 5.1 (minimal certificates through length five).** The contracting
words of length at most five with no proper contracting prefix are
exactly
\[
E,\qquad OE,\qquad OOEE,\qquad OOOEE,\qquad OOEOE.
\tag{5.1}
\]

*Proof.* An  \(E\) -rooted word already contracts at its first letter,
and an  \(OE\) -rooted word contracts at its second. Every remaining
word begins with  \(OO\). At length three, even two odd letters
give  \(3^2>2^3\), so no new certificate appears. At length four,
contraction requires at most two odd letters, giving only  \(OOEE\).
After excluding that prefix, the possible fourth-level prefixes are
\(OOEO\),  \(OOOE\), and  \(OOOO\). At length five, contraction
requires at most three odd letters because  \(3^3<2^5<3^4\).
The first two prefixes must therefore end with  \(E\), and the third
cannot contract. This proves (5.1).  \(\square\)

**Theorem 5.2 (unconditional four-step density).** One has
\[
\#(\mathcal C_4\cap[1,N])
=\frac{13N}{16}+O\bigl(N^{23/24}(\log(2N))^3\bigr).
\]

*Proof.* Lemma 5.1 gives the disjoint prefix classes  \(E\),  \(OE\),
and  \(OOEE\). Theorem 3.1 supplies the first two counts. The
\(OOEE\)  class is the sign class  \((-1,+1,+1)\)  in Corollary 4.6,
so has count  \(N/16+O(N^{23/24}(\log(2N))^3)\).
Their densities add to  \(1/2+1/4+1/16=13/16\).  \(\square\)

**Theorem 5.3 (a five-step subfamily of density  \(27/32\) ).** Let
\[
\mathcal D_5=\mathcal C_4\ \cup\
\{n\ge2:\operatorname{word}_5(n)=OOEOE\}.
\]
Then  \(\mathcal D_5\subseteq\mathcal C_5\)  and
\[
\#(\mathcal D_5\cap[1,N])=27N/32+O(N^{47/48}).
\]
In particular the lower natural density of  \(\mathcal C_5\)  is at
least  \(27/32\).

*Proof.* The added prefix is disjoint from  \(E,OE,OOEE\), and
\(3^3<2^5\)  certifies its contraction. Add Corollary 4.10 to
Theorem 5.2, absorbing the smaller four-step error. The main terms
sum to  \(13/16+1/32=27/32\). This does not assert that
\(\mathcal D_5\)  exhausts  \(\mathcal C_5\).  \(\square\)

**Theorem 5.4 (full five-step certificate density).** For every
\(\varepsilon>0\),
\[
\#(\mathcal C_5\cap[1,N])
=\frac{7N}{8}+O_\varepsilon(N^{127/128+\varepsilon}).
\]
In particular  \(\mathcal C_5\)  has natural density  \(7/8\).
This counts the power-envelope certificate class, not every start
that may happen to descend within five operations.

*Proof.* By Lemma 5.1,  \(\mathcal C_5\)  is the disjoint union of
\(\mathcal D_5\)  and the  \(OOOEE\)  class. Add Theorem 5.3 and
Corollary 4.12. Their main terms are  \(27N/32+N/32=7N/8\);
the former error  \(O(N^{47/48})\)  is smaller.  \(\square\)

The exact fractions and their analytic requirements can be read together:

| Certificate family | Minimal prefixes added | Density | Status |
|---|---|---|---|
|  \(\mathcal C_1\)  |  \(E\)  |  \(1/2\)  | Unconditional |
|  \(\mathcal C_2\)  |  \(OE\)  |  \(3/4\)  | Theorem 3.1 |
|  \(\mathcal C_4\)  |  \(OOEE\)  |  \(13/16\)  | Theorem 5.2 |
|  \(\mathcal D_5\subseteq\mathcal C_5\)  |  \(OOEOE\)  |  \(27/32\)  | Theorem 5.3 |
|  \(\mathcal C_5\)  |  \(OOOEE\)  |  \(7/8\)  | Theorem 5.4 |

The formal  \(OOOEE\)  chain in Section 4.4 uses the expanding
third-level coordinate  \(v^{3/2}\); the  \(OOEOE\)  chain in Section 4.3
uses  \(v^{1/2}\)  at that level. The proofs therefore concern distinct
families. Neither proof asserts fair-share counts for every actual
itinerary at every depth.

## 6. The fixed-depth reduction to density-one certificates

**Hypothesis  \(\mathrm{FD}\).** For every fixed  \(d\ge1\)  and every
odd-rooted word  \(w\)  of length  \(d\),
\[
\#\{n\le N:\operatorname{word}_d(n)=w\}=2^{-d}N+o_w(N).
\]
No common error rate in  \(d\)  is assumed. The family
\(\mathrm H_0(w)\)  over all such words implies  \(\mathrm{FD}\).

**Theorem 6.1 (conditional density-one certificate theorem).** Under
\(\mathrm{FD}\),  \(\mathcal C_\infty\)  has natural density one.

*Proof.* Put  \(p=\log2/\log3>1/2\). A word with no contracting
prefix through length  \(d\)  must in particular have at least  \(pd\)
odd letters at length  \(d\). All such words begin with  \(O\).
For a uniformly chosen odd-rooted word of length  \(d\), the number
of odd letters is distributed as  \(1+B_{d-1}\), where
\(B_{d-1}\)  is a binomial random variable with parameters
\((d-1,1/2)\). This is an auxiliary count on words, not a stochastic
model asserted for the Juggler orbit.

Choose  \(q=(p+1/2)/2\), so  \(1/2<q<p\). For all sufficiently
large fixed  \(d\),  \(pd-1\ge q(d-1)\). For  \(t>0\), the
exponential Markov inequality and the binomial generating function give
\[
\Pr(B_{d-1}\ge q(d-1))
\le\left(\frac{1+e^t}{2e^{qt}}\right)^{d-1}.
\]
The logarithm of the expression in parentheses is zero at  \(t=0\)
and has derivative  \(1/2-q<0\)  there. Hence some fixed  \(t>0\)
makes it a number  \(\vartheta<1\).

For fixed  \(d\),  \(\mathrm{FD}\)  and a finite sum over surviving
words show that the natural density of  \(\mathbb N\setminus\mathcal C_d\)
is their number divided by  \(2^d\). It is at most
\(\tfrac12\vartheta^{d-1}\)  for sufficiently large  \(d\).
Since  \(\mathcal C_d\subseteq\mathcal C_\infty\),
\[
\overline{\operatorname{dens}}(\mathbb N\setminus\mathcal C_\infty)
\le\tfrac12\vartheta^{d-1}.
\]
Letting  \(d\to\infty\)  proves the assertion. In this argument
\(N\to\infty\)  is taken first, with  \(d\)  fixed.  \(\square\)

The conclusion concerns descent below the initial value. It does not
prove that a descended value reaches  \(1\), or that subsequent orbit
samples avoid an exceptional set. Even a density-zero exceptional set
can contain a nontrivial cycle. No interchange of the two limits, and
no assertion of finite stopping time for every start, follows from
Theorem 6.1.

## 7. Exact floor defects and separate analytic questions

For  \(n\ge3\), write
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

*Proof.* Let  \(a=\sqrt m\),  \(b=\sqrt X\). Direct factorization gives
\[
E=a^3-\tfrac32a^2b+\tfrac12b^3
=\tfrac12(a-b)^2(2a+b)\ge0.
\]
Moreover  \(\theta=b^2-a^2\), and  \(Ea\le\tfrac38\theta^2\)
follows from
\(4a(2a+b)\le3(a+b)^2\), equivalent to
\((5a+3b)(a-b)\le0\). Thus
\(E\le\tfrac38m^{-1/2}\), which is at most
\(\tfrac38(X-1)^{-1/2}\). Finally
\((X-1)^{-1/2}\le\tfrac43X^{-1/2}\)  for  \(n\ge3\).
\(\square\)

**Lemma 7.2 (gap and carry).** For an integer  \(h\ge1\), set
\(\Delta_hX(n)=X(n+2h)-X(n)\). Then
\[
m(n+2h)-m(n)=\lfloor\Delta_hX(n)\rfloor+\kappa_h(n),
\quad
\kappa_h(n)=\mathbf1_{\{X(n)\}+\{\Delta_hX(n)\}\ge1}\in\{0,1\}.
\]

*Proof.* Expand  \(X(n)+\Delta_hX(n)\)  into integer and fractional
parts, and take its floor. The sum of the two fractional parts lies
in  \([0,2)\).  \(\square\)

For  \(1\le h\le P/4\)  and  \(n\in(P,2P]\), differentiation gives
\((\Delta_hX)'(n)\asymp hP^{-1/2}\). The level sets of
\(\lfloor\Delta_hX\rfloor\)  consequently form  \(O(1+hP^{1/2})\)
intervals. Full intervals have length  \(\asymp P^{1/2}/h\); the
two endpoint intervals can be shorter. A coefficient involving this
floor is frozen only on these intervals. A derivative estimate
proved there must be summed over the partition, or replaced by a
separate global argument with controlled errors.

**Lemma 7.3 (next-level defect).** One has
\[
v^{3/2}=m^{9/4}-\tfrac32v^{1/2}\theta_2-\mathcal R,
\qquad 0\le\mathcal R\le\tfrac38v^{-1/2}\theta_2^2.
\]

*Proof.* Apply Taylor's theorem to  \(x^{3/2}\)  between  \(v\)  and
\(v+\theta_2=Y\). Its second derivative is
\(\tfrac34x^{-1/2}\le\tfrac34v^{-1/2}\)  on that interval, and is
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
now follows from Theorem 4.5 with  \(k=0\)  and  \(C=2\).
The stronger general kernel target, with  \(c_k(n)=\tfrac{3k}{4}n^{9/8}\), is
\[
K_k(P)=\sum_{\substack{P<n\le2P\\n\ \mathrm{odd}}}
e(c_k(n)\theta_2(n)),
\qquad |K_k(P)|\ll_\varepsilon P^{95/96+\varepsilon},
\quad1\le k\le P^{1/24}.
\tag{7.2}
\]
The indices  \(i,j,k\)  are integers. Estimate (7.1) is unconditional
in this revision; (7.2), with its printed uniformity, remains an
**open target**. A bare-kernel bound does not imply a mixed-mode
estimate by itself. The exact families needed here are instead
proved in Theorems 4.9 and 4.11.
Lemma 4.4 handles half-integer coefficients  \(j/2\)  directly.
This does not extend the frequency domain of the earlier general
decorated lemma, whose separate applications remain unproved.

Short-interval variants require separate estimates. A bound for a
transition set  \(\Omega\subset(P,2P]\)  of the form
\(|\Omega|\ll P^a\)  implies only
\(|\Omega\cap I|\le\min(|I|,O(P^a))\). It does not imply a bound
proportional to  \(|I|/P\). Therefore the earlier localized-kernel
threshold  \(|I|\ge P^{29/48+\delta}\)  is not asserted here.

### 7.1 An unconditional estimate averaged over a shift

**Proposition 7.4 (shift average).** Let  \(L\ge1\), let
\(A_1<\cdots<A_L\)  obey
\(|A_t-A_s|\ge a|t-s|\)  with  \(a>0\), and let  \(x_1,\ldots,x_L\)
be real. For
\(S_\lambda=\sum_{t=1}^{L}e(A_t\{x_t+\lambda\})\),
\[
\left|\int_0^1|S_\lambda|^2\,d\lambda-L\right|
\le\frac4\pi\frac La(1+\log L).
\tag{7.3}
\]
For every  \(0<\eta<1\), outside a set of shifts of measure at most
\(\eta\),
\[
|S_\lambda|\le
\left[\frac L\eta\left(1+\frac4{\pi a}(1+\log L)\right)\right]^{1/2}.
\]

*Proof.* Expanding the square gives the diagonal term  \(L\).
For  \(t\ne s\), the integrand
\(e(A_t\{x_t+\lambda\}-A_s\{x_s+\lambda\})\)  is periodic in
\(\lambda\). Integrate over a period starting at one of its two
fractional-part breakpoints. There is at most one other interior
breakpoint, giving at most two intervals on which the phase is
affine with slope  \(A_t-A_s\). On each interval the integral has
modulus at most  \(1/(\pi|A_t-A_s|)\). Hence the off-diagonal
contribution is bounded by
\[
\frac{2}{\pi a}\sum_{t\ne s}\frac1{|t-s|}
=\frac4{\pi a}\sum_{r=1}^{L-1}\frac{L-r}{r}
\le\frac4\pi\frac La(1+\log L).
\]
For  \(L=1\)  the off-diagonal sum is empty. Markov's inequality
applied to  \(|S_\lambda|^2\)  gives the second assertion.
\(\square\)

The estimate allows a small exceptional set of shifts. It gives no
bound for a specified shift, including  \(\lambda=0\)  in (7.2).

### 7.2 Counting the gap cells in a collision estimate

The following lemma repairs the cell-counting problem for a fixed
curvature model. It does not assert that every decorated phase in the
earlier kernel proof meets its hypotheses.

**Lemma 7.5 (curvature estimates over a partition).** Partition an
interval of length at most  \(P\)  into interval cells, so that every subinterval
of length  \(L\)  meets  \(O(1+\nu L)\)  cells. On each cell let  \(f\)
be a real  \(C^2\)  function; its values and derivatives may jump at
cell boundaries. Suppose that a continuous reference function
\(\Lambda\)  satisfies  \(|\Lambda|\ll M\), and that, for  \(0<s\le1\),
both sets
\[
\{|\Lambda|\le sM\},\qquad \{sM<|\Lambda|\le2sM\}
\]
are unions of  \(O(1)\)  intervals, each set of total length  \(O(Ps)\).
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
\(\tau=\max(4\rho,(MP^2)^{-1/3})\). If  \(\tau\)  is bounded below
by a positive absolute constant, the terms  \(P\rho+(P/M)^{1/3}\)
already give the trivial bound  \(O(P)\). Otherwise discard
\(\{|\Lambda|\le\tau M\}\), containing  \(O(P\tau+1)\)  integers.
Split the remainder into dyadic bands  \(|\Lambda|\asymp sM\),
with  \(\tau\ll s\ll1\), and the outer set  \(|\Lambda|>M\)  if necessary.
Each band has total length  \(O(Ps)\)  and meets
\(O(1+\nu Ps)\)  cells. On its intersection with a cell the
curvature has one sign and size  \(\asymp sM\).

Apply the second-derivative estimate on every such intersection.
The resulting costs at scale  \(s\)  are
\[
O\bigl(PM^{1/2}s^{3/2}
+M^{-1/2}s^{-1/2}+\nu P M^{-1/2}s^{1/2}\bigr).
\]
The geometric sum over bands is
\(O(PM^{1/2}+M^{-1/2}\tau^{-1/2}+\nu PM^{-1/2})\).
Our choice gives
\(M^{-1/2}\tau^{-1/2}\le(P/M)^{1/3}\)  and
\(P\tau\ll P\rho+(P/M)^{1/3}\), proving (7.4).
One may assign boundary integers to either adjacent cell and
estimate that cell up to its endpoint.  \(\square\)

**Proposition 7.6 (the basic frozen-gap collision model).** Let
\(u\ge1/2\),  \(1\le h\le P^{1/8}\),  \(uh\le P^{1/2}\), and
let  \(w>0\)  satisfy
\(c_1uhP^{-1/4}\le w\le c_2uhP^{-1/4}\), for fixed
\(0<c_1<c_2\). With  \(A_h\)  as in Lemma 4.4 and
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
\(G(x)=3h\sqrt x+O(1+h^2P^{-1/2})\)  and
\(A_h''=O(h^2P^{-7/4})\)  show, as a comparison of values,
\[
|f''-\Lambda|\ll M\bigl(h/P+(hP^{1/2})^{-1}\bigr).
\]
This does not differentiate  \(G\). The gap-cell partition has
density parameter  \(\nu\asymp hP^{-1/2}\).

To verify the sublevel conditions, factor
\(\Lambda(x)=\tfrac34x^{-3/4}(wx^{1/4}-9uh/8)\).
The expression in parentheses is strictly increasing, with
derivative  \(\asymp uh/P\)  in the stated collision range.
Hence  \(|\Lambda|\le sM\)  occupies length  \(O(Ps)\).
Moreover  \(\Lambda'\)  has at most one zero, so the sublevel
sets and dyadic bands have a bounded number of components.
Apply Lemma 7.5 with
\(\rho=O(h/P+(hP^{1/2})^{-1})=o(1)\).
Its terms give (7.5); the extra  \(M^{-1/2}\)  is absorbed by
\((h/u)^{1/2}P^{7/8}\).  \(\square\)

For integer  \(w\)  in the collision range,  \(w\ge1\)  implies
\(uh\gg P^{1/4}\). Formula (7.5) is then  \(O(P^{7/8})\):
its second term is  \(h(uh)^{-1/2}P^{7/8}\ll P^{7/8}\),
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
| Certificate density  \(3/4\)  | Classical analytic proof in Theorem 3.1 |
| Correlation-to-count and Fourier-to-parity implications | Proofs in Propositions 4.1 and 4.2 |
| Certificate density  \(13/16\)  | Unconditional: Corollary 4.6 and Theorem 5.2 |
| Certificate subfamily density  \(27/32\)  | Unconditional: Corollary 4.10 and Theorem 5.3 |
| Full five-step certificate density  \(7/8\)  | Unconditional: Corollary 4.12, Theorem 5.4, and Appendices A--C |
| Density-one finite certificates | Conditional on  \(\mathrm{FD}\); no depth uniformity assumed |
| Restricted mixed sums | Theorems 4.5, 4.9, and 4.11 |
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
the four-step repairs. Further exact scripts check the fifth-letter centering identity,
the D2 floor reduction, the signed-wave and master inventories,
the mixed curvature coefficients, and all displayed exponent budgets.
The source package includes these scripts and their results.
Those checks support reproducibility;
they are not proofs of asymptotic cancellation.

Earlier repository audits and Lean modules concern identities,
inequalities, and arithmetic from the previous draft. This version
claims no Lean formalization of its analytic hypotheses or of the
complete manuscript. Earlier theorem numbers are superseded
and should not be used as citations to unconditional nested estimates.
Companion texts that rely on those estimates require their own review.

The full five-step certificate class proved here has density  \(7/8\).
The argument does not extend its error estimates proportionally
to an arbitrary short interval, and it supplies no universal
termination conclusion. A proof of all fixed-depth fair-share
counts would imply density-one certificates by Theorem 6.1;
that additional hypothesis remains open.

## Appendix A. Floor reductions and the carry inventory

We collect the estimates used by the OOOEE argument. All counts of
exceptional integers use the original gap runs, before any later
frequency partition. Constants may depend on fixed comparability
constants. Every displayed estimate is uniform for sufficiently
large P; bounded smaller P is absorbed into the implied constants.

### A.1 A reduction for a differenced floor factor

**Lemma A.1 (fixed-label floor reduction).** The definitions below lead to (A.9), with the stated error and coefficient variation bounds.

In Appendices A--C, a subscript on \(\Delta\) denotes the actual
translation: \(\Delta_d f(x)=f(x+d)-f(x)\). Thus a half-shift \(h\)
uses \(\Delta_{2h}\). This differs from the local half-shift convention
\(\Delta_h f(x)=f(x+2h)-f(x)\) in Section 4.2.
All constants below are absolute, or depend on fixed constants in
comparability bounds. Let P tend to infinity,
with integer parameters
\[
1\le k,h_1,h_2\le P^{1/24},\qquad 1\le h\le P^{1/8}.
\]
Put X(x)= \(x^{3/2}\), m(n)=floor(X(n)), and c(x)=3k  \(x^{9/8}\) /4.
Work on (P,2P], extending the definitions to (P,3P] to accommodate
shifts. Fixed positive multiples of the upper parameter bounds are allowed,
with constants depending on those multiples. All estimates also
hold after restriction to odd integers.

Partition by the integer parts of
\[
X(x+2h_1)-X(x),\quad X(x+2h_2)-X(x),\quad
X(x+2h_1+2h_2)-X(x).
\] There are
\[
D\ll (h_1+h_2)P^{1/2}
\]
runs, and an interval of length L meets
\(O(1+(h_1+h_2)L P^{-1/2})\)  runs.

On each run freeze a carry label and its integer offsets
\(\beta_1\),  \(\beta_2\),  \(\beta_{12}\). Assume
\(\beta_i\)  is comparable to  \(h_i\)   \(P^{1/2}\), for i=1,2, and
j= \(\beta_{12}\) - \(\beta_1\) - \(\beta_2\)  is a bounded integer, with |j| \(\le\) 2
for the admissible branches used here. Define, on that run,
\[
\begin{split}
F(t)&=(t+\beta_1+\beta_2+j)^{3/2}
-(t+\beta_1)^{3/2}-(t+\beta_2)^{3/2}+t^{3/2},\\
G(x)&=F(X(x)),\qquad A(n)=\lfloor F(m(n))\rfloor.
\end{split}
\]
The offsets may change between runs. The theorem treats any such
piecewise extension; no derivative crosses a run boundary.
There are only finitely many carry labels, so bounds for their
positive error terms can be summed. Reassembling oscillatory sums
with the actual carry indicators is a further step, not an assumption
that a branch extension is the physical orbit everywhere.


On an interval I of length L, suppose G is  \(C^{1}\)  and
a \(\le\) |G'| \(\le\) C a, with 0<a \(\le\) 1. Its derivative has constant sign.
For 0< \(\delta\)  \(\le\) 1/2, the number of integer n in I with
distance(G(n),Z) \(\le\)  \(\delta\)  is
\[
\ll \delta(L+a^{-1})+aL+1. \tag{A.1}
\]
Indeed G(I) meets  \(O(aL+1)\)  integer neighborhoods. Each inverse image
is an interval of length  \(O(\delta/a)\), containing  \(O(\delta/a+1)\)
integers. This includes endpoints and exact integer values.

Let
\[
E_Q(t)=\min(1,(Q\|t\|)^{-1}),\qquad E_Q(t)=1\quad(t\in\mathbb Z).
\]
Splitting the distances to Z into dyadic bands gives
\[
\sum_{n\in I}E_Q(G(n))
\ll {L+a^{-1}\over Q}\log(2Q)+aL+1. \tag{A.2}
\]
The additive lattice-count cost is multiplied by a convergent
geometric sum, not by the number of bands.

Over D disjoint runs with a common comparable derivative scale,
these become
\[
\begin{split}
\#\{\|G(n)\|\le\delta\}
&\ll \delta(P+D/a)+Pa+D,\\
\sum E_Q(G(n))
&\ll {(P+D/a)\log(2Q)\over Q}+Pa+D.
\end{split}\tag{A.3}
\]
Runs of different offset types are bounded separately. No
equidistribution assumption, random model, or rescaling of a global
exceptional set is used.


Set p= \(h_1\)   \(h_2\). The zero-offset part has the exact integral
representation
\[
F_0(t)={3\over4}\int_0^{\beta_1}\int_0^{\beta_2}
(t+s+r)^{-1/2}\,dr\,ds.
\]
Consequently, with the  \(\beta\)  values fixed when differentiating,
\[
\begin{split}
G_0'(x)&=-{9\over16}\beta_1\beta_2 x^{-7/4}(1+o(1)),\\
G_0''(x)&={63\over64}\beta_1\beta_2 x^{-11/4}(1+o(1)).
\end{split}
\]
The errors are uniform because ( \(\beta_1\) + \(\beta_2\) )/X=o(1).

The offset contribution is
\[
{3j\over2}\int_0^1
(t+\beta_1+\beta_2+s j)^{1/2}\,ds.
\]
After composition with X its first derivative is
(9j/8) \(x^{-1/4}\) (1+o(1)). For j nonzero it dominates the zero-offset
derivative, since p  \(P^{-1/2}\) =o(1). Thus, on every run,
\[
|G'|\asymp
\begin{cases}
pP^{-3/4},&j=0,\\
P^{-1/4},&j\ne0,
\end{cases}
\qquad
|G''|\ll |j|P^{-5/4}+pP^{-7/4}. \tag{A.4}
\]
Also |G| is  \(O(|j|P^{3/4}+pP^{1/4})\).
These are derivatives of frozen-offset functions, not derivatives
of the approximations  \(\beta_i\)  approximately 3h_i  \(\sqrt{x}\).

Take Q=floor( \(P^{5/16}\) ). For j=0, the potentially largest term in
(A.3) is
\[
{D\over Qa}\ll {h_1+h_2\over h_1h_2}P^{15/16}
\ll P^{15/16}.
\]
The other terms are  \(P^{11/16}\), \(pP^{1/4}\), and D.
For j nonzero, (A.3) is  \(O(P^{3/4} \log P)\).
It follows that, summed over all runs of either type,
\[
\sum E_Q(G(n))\ll P^{15/16}\log P. \tag{A.5}
\]

The replacement of m by X is used only inside the floor, after
counting its exceptional set. The mean value theorem gives
\[
|F(m(n))-G(n)|
\ll |j|P^{-3/4}+pP^{-5/4}=:\delta.
\]
A floor mismatch requires G(n) to lie within  \(\delta\)  of an integer.
For either derivative scale in (A.4),  \(\delta\) /a= \(O(P^{-1/2})\).
The first line of (A.3) therefore proves
\[
\#\{n:A(n)\ne\lfloor G(n)\rfloor\}\ll P^{3/4}. \tag{A.6}
\]
This remains useful when c is large: changing a unit exponential
costs at most two on the exceptional set. A large coefficient is
never multiplied by an uncontrolled pointwise floor error.


Exclude for the moment n whose interval from n to n+2h crosses
an original run boundary. There are  \(O(hD)\)  such integers.

Within a run, G is monotone. If
floor(G(n+2h)) differs from floor(G(n)), this interval contains an
integer-level crossing of G. There are  \(O(aL+1)\)  levels on a run of
length L, and any crossing belongs to at most  \(O(h)\)  such integer
starting intervals. Including the original run boundaries gives
\[
\#\{\hbox{floor change or run crossing}\}
\ll h(Pa+D)\ll P^{7/8}. \tag{A.7}
\]
For zero offset the bound is even smaller; the uniform largest term
is \(hP^{3/4}\) from nonzero offsets.

Write B(x)=c(x+2h)-c(x). Using (A.6) at both endpoints and then
(A.7), we obtain the following statement in the sum of absolute
errors:
\[
e\bigl(-\Delta_{2h}(cA)(n)\bigr)
=e\bigl(-B(n)\lfloor G(n)\rfloor\bigr)+\mathcal E_n,
\qquad
\sum|\mathcal E_n|\ll P^{7/8}. \tag{A.8}
\]
Both expressions in this comparison are unimodular. The second
expression is defined on every run, including the exceptional
starting points; no irregularly punctured domain is passed to a
derivative test.

The floor-crossing argument also explains why a small drift is insufficient by itself. For comparison, on
zero-offset runs |Delta G| is  \(O(hpP^{-3/4})\); at the carry
cutoff J=floor( \(P^{1/8}\) ), J|Delta G|=o(1). Therefore the distance
majorant  \(E_J\) (Delta G) equals one for sufficiently large P.
The standard sawtooth Fourier approximation has an order-one
endpoint error there as well. Small drift alone cannot justify the
\(O(P/J)\)  charge for this individual layer. The exact carry
combination may cancel; (A.7) preserves that cancellation by counting
the floor change before expansion.


The coefficient B is increasing, with
\[
B\asymp khP^{1/8},\quad
B'\asymp khP^{-7/8},\quad
|B''|\ll khP^{-15/8}.
\]
Refine the original runs by N=floor(B), and put  \(\beta\) =B-N.
The extra number of cuts is  \(O(1+khP^{1/8})\).
The exact identity
\[
e(B\{G\})=e(NG)e(\beta\{G\})
\]
centers the frequency before truncation.

For 0 \(\le\)  \(\beta\)  \(\le\) 1 let
\[
a_r(\beta)=\int_0^1 e((\beta-r)t)\,dt.
\]
By Lemma 4.7, or its
complex conjugate,
\[
e(\beta\{G\})
=\sum_{|r|\le Q}a_r(\beta)e(rG)+O(E_Q(G)).
\]
The integral definition includes the removable singularity.
Both | \(a_r\) | and | \(a_r\) '| are  \(O(1/(1+|r|))\). On each refined interval,
\(\beta\)  is monotone and has variation at most one, so
\[
\sum_{|r|\le Q}
\left(\|a_r(\beta)\|_\infty+\operatorname{TV}(a_r(\beta))\right)
\ll\log(2Q).
\]

Combining this expansion with (A.5) and (A.8) proves the fixed-label floor reduction:
\[
\begin{split}
e\bigl(-\Delta_{2h}(cA)(n)\bigr)
&=\sum_{|r|\le Q}a_r(\beta(n))e(\Phi_r(n))+\mathcal R_n,\\
\Phi_r(x)&=(N+r-B(x))G(x),\\
\sum_{P<n\le2P}|\mathcal R_n|&\ll P^{15/16}\log P.
\end{split}\tag{A.9}
\]
N and all offsets are fixed only within the refined interval.
The error sum is charged once on the original runs; it is not
multiplied by the number of frequency windows. This is valid with
any additional weight of modulus at most one. A fixed number of
such floor factors can be expanded by telescoping, at a fixed extra power
of log P and with the same power saving.

This replacement uses the bounded residual  \(\beta\), so it has no
unaccounted continuous-part tail between Q and  \(P^{1/2}\).


Differentiate with N and r fixed:
\[
\Phi_r''=(N+r-B)G''-2B'G'-B''G.
\]
Since N+r-B=r- \(\beta\), (A.4) yields
\[
|\Phi_r''|\ll
(Q+1)(|j|P^{-5/4}+pP^{-7/4})
+kh(|j|P^{-9/8}+pP^{-13/8}). \tag{A.10}
\]
For an undisturbed wave curvature \(M=uhP^{-3/4}\), u \(\ge\) 1/2,
the four exponent bounds for this ratio are respectively
\[
P^{-3/16},\quad P^{-29/48},\quad
P^{-1/3},\quad P^{-3/4}.
\]
Thus \(|\Phi_r^{\prime\prime}|\)= \(O(P^{-3/16}M)\), uniformly.

Where a total phase already has curvature comparable to M, the
extra endpoint cost in the second-derivative estimate is
\[
\begin{split}
(D+1+khP^{1/8})M^{-1/2}
\ll{}&(h_1+h_2)(uh)^{-1/2}P^{7/8}\\
&+k(h/u)^{1/2}P^{1/2}+(uh)^{-1/2}P^{3/8}.
\end{split} \tag{A.11}
\]
Its largest uniform exponent is 11/12, below 15/16.
Partial summation uses the coefficient-variation bound proved above.

This comparison is not a declaration that an arbitrary sum of
signed waves has curvature comparable to M. At a curvature
cancellation, the reference-function and sublevel hypotheses must
still be verified for the complete phase.


### A.2 Joint first-floor carries

**Lemma A.2 (carry arcs and global positive errors).**
Let  \(1\le h\le P^{1/12}\), and let the number of shifts below be
bounded by a fixed constant.

There are finitely many first-floor evaluations in the main wave
and the D1 terms. All have the form m(n+s), with s an even
nonnegative integer  \(O_{C,M}(h+P^{1/24})\). Use the single variable
\(\theta\) ={X(n)} and
\[
m(n+s)-m(n)=b_s+
{\bf1}_{\,\theta\ge 1-\delta_s},\qquad
b_s=\lfloor X(n+s)-X(n)\rfloor,\quad
\delta_s=\{X(n+s)-X(n)\}.
\]
The convention when  \(\delta_s\) =0 is that this indicator is zero
for 0 \(\le\)  \(\theta\) <1.

Partition by the integer gaps  \(b_s\)  and any input or coefficient
windows already required by the argument. There are
\(O(1+\sum_s s \sqrt{P})\)  original gap runs. Their local count in an
interval of length L is  \(O(1+\sum_s s L P^{-1/2})\).
On each gap run each  \(\delta_s\)  is monotone and varies by at most one.
Sort their endpoints 1- \(\delta_s\); two distinct endpoints cross at most
once on such a run, because the difference of the corresponding
real gaps is monotone. Equal shifts give identical endpoints.
This adds only  \(O_{C,M}(1)\)  cuts per cell.

A joint carry pattern is now a fixed finite union of intervals of
\(\theta\), with endpoints 0,1, or 1- \(\delta_s\). Its Fourier expansion
truncated at R=floor( \(P^{1/4}\) ) has:
- a zero-mode coefficient with sup norm plus variation  \(O_{C,M}(1)\);
- endpoint modes with coefficients  \(O_{C,M}(1/|v|)\), 0<|v| \(\le\) R,
multiplying e(vX(n+s)) for one of the allowed s (s=0 included);
- an absolute remainder bounded by a constant times the sum of
\(E_R\) (X(n+s)) over these finitely many endpoints, where
\(E_R\) (z)=min(1,1/(R||z||)), with value one at integers.

This is the usual interval Fourier expansion: a moving endpoint
u=1- \(\delta_s\)  supplies e(-v u), and, since  \(b_s\)  is integer,
e(vX(n))e(-v(1- \(\delta_s\) ))=e(vX(n+s)). Thus the moving
endpoint belongs in the phase, not in an unbounded-variation
coefficient. Zero-length intervals and points at endpoints are
covered by the positive remainder.

Here is the global bound needed for that remainder:
\[
\sum_{P<n\le2P}E_R(X(n+s))\ll_{C,M}P^{5/6}\log(2P). \tag{A.12}
\]
It holds also over odd integers or a subinterval. To verify it,
the second-derivative test for vX(x+s) gives
\(O(|v|^{1/2}P^{3/4}+|v|^{-1/2}P^{1/4})\).
The interval-discrepancy inequality with auxiliary cutoff
K=floor( \(P^{1/6}\) ) then gives discrepancy  \(O(P^{5/6})\).
Dyadic bands for the distance to an integer give
\(O(P \log(2R)/R+P^{5/6})\), which implies (A.12).
The remainder is charged once over the common input interval.
It is not multiplied by the cell count. Products with the other finite Fourier expansions
introduce at most a fixed logarithmic factor.


### A.3 Positive errors for the second-level inventory

Let  \(X=x^{3/2}\),  \(m=\lfloor X\rfloor\),  \(Y=m^{3/2}\), and put
\(d_i=2h_i\),  \(W_i=\Delta_iY\),  \(D=\Delta_1\Delta_2Y\),
where  \(1\le h_1\le P^{1/48}\),  \(1\le h_2\le P^{1/24}\), and
\(p=h_1h_2\). Here  \(\Delta_i f(x)=f(x+d_i)-f(x)\).
Even translations by  \(O(P^{1/24})\)  are allowed.
**Lemma A.3 (positive inventory errors).**

Set  \(J=\lfloor P^{1/24}\rfloor\), and use
\(E_J(z)=\min(1,(J\|z\|)^{-1})\), with value one at integers.
For every argument occurring in the carry expansion below,
\[
\sum_{P<n\le2P,\ n\ {\rm odd}} E_J(Z(n))
\ll P^{23/24}(\log(2P))^C, \tag{A.13}
\]
where
\[
Z\in\{Y(n),Y(n+d_1),Y(n+d_2),Y(n+d_1+d_2),
W_1(n),W_2(n),W_1(n+d_2),D(n)\}.
\]
The constant C is absolute. This is an unweighted positive bound;
it does not assume that an anchor is still present.

For Y at any of these even translations, Theorem 4.5, with modes  \((i,j,k)=(0,2q,0)\), gives  \(O(P^{23/24})\)  for 1 \(\le\) |q| \(\le\) J.
The discrepancy inequality at cutoff J, followed by dyadic distance
bands, proves (A.13). The same argument for W uses Lemma 4.4 with
i=k=0 and j=2q. Its bound is
\(O(P^{7/8}(1+h_i^{1/2}))\) = \(O(P^{43/48})\), which also fits (A.13).
The proofs of those results work on any subinterval of [P,3P]:
their length, gap-cell, and positive-error bounds are all in the
ambient scale P. No proportional rescaling of an exceptional set
is used for the translated intervals here.

For D, a separate elementary argument is needed. Put
\[
j(n)=\Delta_1\Delta_2m(n),\qquad -1\le j(n)\le2.
\]
The exact frozen-branch integral formulas imply the global
value approximation
\[
D(n)=g_{j(n)}(n)+O((h_1+h_2)P^{-1/4}),\qquad
g_j(x)=\tfrac32j x^{3/4}+\tfrac{27}{4}p x^{1/4}. \tag{A.14}
\]
To verify the error, the first-floor offsets satisfy
\(\beta_i\) =3h_i  \(\sqrt{n}\) + \(O(1)\), hence
\(\beta_1\)   \(\beta_2\) =9pn+ \(O((h_1+h_2)\sqrt{P}+1)\).
In the zero-offset integral, replacing its argument by  \(n^{3/2}\)
has relative error  \(O((h_1+h_2)/P)\); in the offset integral the
corresponding absolute error is  \(O((h_1+h_2)P^{-1/4})\).
The resulting extra zero-offset error
\(O(p(h_1+h_2)P^{-3/4})\)  is smaller than the displayed error.
This is a comparison of values, not of frozen derivatives.

The error in (A.14) is  \(O(P^{-5/24})\), so J times that error tends to zero.
For |u-v| \(\le\) 1/(2J), one has  \(E_J\) (u) \(\le\) 2E_J(v).
On a branch j=0,  \(g_j\)  has derivative comparable to \(pP^{-3/4}\).
On a nonzero branch it has derivative comparable to  \(P^{-1/4}\),
of the sign of j. Both are monotone slow variables on the whole
dyadic block. The monotone counting lemma (A.2) in
Appendix A.1 gives
\[
\sum E_J(g_j(n))
\ll (P+a_j^{-1})\log(2J)/J+Pa_j+1,
\quad
a_0\asymp pP^{-3/4},\quad a_j\asymp P^{-1/4}\ (j\ne0).
\]
Every term is  \(O(P^{23/24} \log P)\). Bound a branch-restricted positive
sum by this full-block sum and add the four possible j values.
This proves (A.13) for D without multiplying a floor-error estimate
by the number of original gap runs.


### A.4 Exact centered master inventory

Let  \(c(x)=3kx^{9/8}/4\),  \(c_{11}(x)=c(x+d_1+d_2)\),
\(\vartheta=\{Y\}\), and  \(1\le k\le CP^{1/24}\).
**Lemma A.4 (master identity and coefficient mass).**

Define the binary carry  \(C(A,B)=\{A\}+\{B\}-\{A+B\}\), and set
\[
\kappa_1=C(Y,W_1),\quad \kappa_2=C(Y,W_2),\quad
\kappa_1^+=C(Y(n+d_2),W_1(n+d_2)),\quad
\kappa_*=C(W_1,D).
\]
Let
\[
B_2(x)=\Delta_2c(x+d_1),\qquad
B_1(x)=\Delta_1c(x+d_2),\qquad N_i(x)=\lfloor B_i(x)\rfloor .
\]
The product rule and the exact carry identity give
\[
\begin{split}
\Delta_1\Delta_2(c\vartheta)
={}&(\Delta_1\Delta_2c)\vartheta
+B_2(\{W_1\}-\kappa_1)+B_1(\{W_2\}-\kappa_2)\\
&+c_{11}(\{D\}-\kappa_*-\kappa_1^++\kappa_1).
\end{split} \tag{A.15}
\]
With  \(\Pi=kh_1h_2\), the first term has total deletion cost
\(O(\Pi P^{1/8})\) = \(O(P^{11/48})\).

For each factor e( \(B_i\) {W}), center at the integer  \(N_i\):
\[
e(B_i\{W\})=e(N_iW)e(\beta_i\{W\}),\qquad
\beta_i=B_i-N_i\in[0,1).
\]
Here  \(\beta_i\)  denotes a coefficient residual only; it is not a
first-floor offset used in a branch formula.
Expand the last factor at the short cutoff J:
\[
e(\beta_i\{W\})=\sum_{|r|\le J}a_r(\beta_i)e(rW)+O(E_J(W)),
\quad a_r(\beta)=\int_0^1e((\beta-r)y)\,dy. \tag{A.16}
\]
Its coefficients satisfy
| \(a_r\) |+| \(a_r\) '|<<1/(1+|r|), including removable singularities.
The error is covered by (A.13), independently of the large center  \(N_i\).
There is no uncentered large-coefficient tail to discard.

For each of the five carry exponentials in (A.15), use exactly
\[
e(g\kappa)=1+\kappa(e(g)-1).
\]
Expand the factor e(g)-1 into two terms and move e(g) into the
smooth phase. Expand kappa additively using its three unit
fractional parts, each at cutoff J by Lemma 4.3.
The only arguments are those in (A.13), because
\[
Y+W_i=Y(n+d_i),\quad W_1+D=W_1(n+d_2),\quad
Y(n+d_2)+W_1(n+d_2)=Y(n+d_1+d_2).
\]
The smooth phases introduced this way are bounded integer
combinations of  \(B_1\), \(B_2\), \(c_{11}\).

There are two centered Fourier layers and at most five carry layers.
Their total coefficient mass is  \(O((\log(2P))^7)\); a larger fixed
logarithmic power covers all errors. Indeed, pointwise truncated
factors have  \(O(\log P)\)  bounds, so telescoping products multiplies
each error in (A.13) only by a fixed logarithmic power.

The  \(N_i\)  windows are retained globally as functions of x.
Both  \(B_i\)  are increasing, with
\[
B_i\asymp kh_iP^{1/8},\quad B_i'\asymp kh_iP^{-7/8}.
\]
Their common partition has local count
\(O(1+k(h_1+h_2)LP^{-7/8})\)  and total count  \(O(P^{5/24})\).
On each cell the residuals  \(\beta_i\)  are monotone in [0,1), so
the same logarithmic bound holds for summed coefficient
sup norms plus variations.

For arbitrary four corner coefficients, the exact identity is
\[
\sum_{d\in\{0,d_1,d_2,d_1+d_2\}}q_dY(n+d)
=tY+(q_{d_1}+q_{d_1+d_2})W_1
+(q_{d_2}+q_{d_1+d_2})W_2+q_{d_1+d_2}D,
\quad t=\sum_dq_d. \tag{A.17}
\]
Use also  \(W_1\) (n+ \(d_2\) )= \(W_1\) +D.

Consequently (A.15)--(A.16) reduce the sum with phase  \(Delta_1\)   \(Delta_2\) (c  \(\vartheta\) ), with absolute error
\(O(P^{23/24} \log^C(P))\), to a finite weighted family with phases
\[
c_{11}\{D\}+tY+(N_2+u)W_1+(N_1+v)W_2+qD+\phi . \tag{A.18}
\]
Here t,u,v,q are fixed integers for each Fourier multi-index,
\[
|t|,|u|,|v|,|q|\le6J,
\]
and  \(\phi\)  is a bounded integer combination of  \(B_1\), \(B_2\), \(c_{11}\).
In particular
\[
|\phi''|\ll kP^{-7/8},\qquad |\phi'''|\ll kP^{-15/8}. \tag{A.19}
\]
The two centered residual frequencies account for the extra unit
in the bound 6J; each carry layer contributes at most one mode.
All signs and zero coordinates are included.

More precisely there are nonnegative numbers  \(\rho_\nu\), one for each
multi-index, with sum  \(\rho_\nu\) = \(O(\log^7(P))\), such that its amplitude
divided by  \(\rho_\nu\)  has bounded sup norm plus variation on each
\(N_1\), \(N_2\)  cell. This follows by multiplying the harmonic coefficient
bounds above and applying the product variation inequality.
Thus it suffices to prove a uniform bound for each normalized
amplitude; no estimate is multiplied by the number of frequency
windows.

The first-difference coefficients satisfy
\[
|(N_2+u)h_1|+|(N_1+v)h_2|
\ll \Pi P^{1/8}+J(h_1+h_2)\ll P^{11/48}, \tag{A.20}
\]
well within the widened  \(P^{1/2}\)  budget.


## Appendix B. A wave-bearing estimate

The following estimate is used only for the family that its statement
specifies. In Appendix C the total Y frequency is a nonzero integer.
Allowing half-integer frequencies here also covers the elementary
main-wave argument.

**Theorem B.1 (nonzero total frequency).**

Let \(e(v)=\exp(2\pi i v)\), and put
\[
X(x)=x^{3/2},\quad m(n)=\lfloor X(n)\rfloor,\quad
Y(n)=m(n)^{3/2},\quad \Delta_d f(x)=f(x+d)-f(x).
\]
All functions are defined on [P,3P], with harmless further extension
at its upper endpoint if needed. Constants C and M are fixed.
All estimates concern sufficiently large P depending only on them.
Let t be real and fixed throughout the sum, with
\[
\tfrac12\le |t|\le CP^{1/24}.
\]
There are at most M first-difference terms, with even shifts  \(e_j\)  \(\ge\) 0
and positive integer half-shifts  \(r_j\)  satisfying
\[
e_j\le CP^{1/24},\qquad 1\le r_j\le CP^{1/24},
\qquad |a_j(x)|r_j\le CP^{1/2}. \tag{B.1}
\]
The real coefficients  \(a_j\)  are constant separately on the cells of an
interval partition  \(\mathcal P\). Any interval of length L meets at
most C(1+L  \(P^{-11/24}\) ) cells of this partition. In particular, its
total cell count is  \(O_C(P^{13/24})\). The real function  \(\phi\)  is  \(C^{3}\)
on each cell and satisfies
\[
|\phi'''(x)|\le CP^{-13/12}. \tag{B.2}
\]
No continuity across cell boundaries is required. The complex
amplitude  \(\eta\)  satisfies
\[
\|\eta\|_{\infty,I}+\operatorname{TV}_I(\eta)\le C
\]
on each cell I. Endpoint values are assigned consistently; their
possible exceptional contribution is covered by the cell count.

We also allow at most M terms  \(-\sigma_\ell c_\ell A_\ell\), where
\(\sigma\)  belongs to {-1,0,1}. These are the fixed-label D2 objects of
the Appendix A.1, with
\[
1\le k_\ell,h_{\ell,1},h_{\ell,2}\le CP^{1/24},
\qquad c_\ell(x)=\tfrac34 k_\ell(x+v_\ell)^{9/8}.
\]
The integers k and h are positive. The base shift  \(s_\ell\)  and the
coefficient shift  \(v_\ell\)  are nonnegative even integers  \(O_C(P^{1/24})\).
To specify the object unambiguously, partition by the integer parts of
\[
X(x+s_\ell+2h_{\ell,i})-X(x+s_\ell),\qquad
X(x+s_\ell+2h_{\ell,1}+2h_{\ell,2})-X(x+s_\ell).
\]
On every such original run choose fixed admissible carry offsets
\(\beta_1\), \(\beta_2\), \(\beta_{12}\), with  \(\beta_i\)  comparable to  \(h_i\)   \(\sqrt{P}\)  and
j= \(\beta_{12}\) - \(\beta_1\) - \(\beta_2\)  a bounded integer (|j| \(\le\) 2 suffices). Set
\[
\begin{split}
F_\ell(z)&=(z+\beta_1+\beta_2+j)^{3/2}
-(z+\beta_1)^{3/2}-(z+\beta_2)^{3/2}+z^{3/2},\\
G_\ell(x)&=F_\ell(X(x+s_\ell)),\\
A_\ell(n)&=\lfloor F_\ell(m(n+s_\ell))\rfloor.
\end{split}
\]
The version  \(A_\ell(n)=\lfloor G_\ell(n)\rfloor\)  is also allowed.

The partition  \(\mathcal P\)  refines these original runs. Further
refinement does not change their chosen labels: it cannot introduce
new arbitrary jumps in  \(F_\ell\)  or  \(G_\ell\). All D2 counting errors below
are evaluated on the original runs. These floors are not first
partitioned into their integer level sets.

Under these hypotheses the theorem is
\[
\begin{split}
U(P)=\sum_{\substack{P<n\le2P\\n\ {\rm odd}}}\eta(n)e\Big(
tY(n)+\sum_j a_j(n)\Delta_{2r_j}Y(n+e_j)
-\sum_\ell\sigma_\ell c_\ell(n)A_\ell(n)+\phi(n)\Big),\\
|U(P)|\ll_{C,M,\varepsilon}P^{31/32+\varepsilon}.
\end{split}\tag{B.3}
\]
The hypotheses on the partition and  \(\phi\)  must be verified in any
application; they do not permit arbitrary additional floor factors
or a smooth twist that cancels the main wave.

### B.1 The widened D1 linearization

Fix an A-process half-shift  \(1\le h\le P^{1/12}\). On an actual
carry branch for z=n+e, put
\[
m(z+2h)=m(z)+\beta_1,\quad
m(z+2r)=m(z)+\beta_2,\quad
m(z+2h+2r)=m(z)+\beta_1+\beta_2+j.
\]
Then
\[
\Delta_{2h}\Delta_{2r}Y(z)=F_j(m(z)),
\]
where  \(F_j\)  has the same four-term form as  \(F_\ell\)  above. Uniformly,
\(\beta_1\)  is comparable to h  \(\sqrt{P}\),  \(\beta_2\)  to r  \(\sqrt{P}\), and |j| \(\le\) 2.
The latter follows because the corresponding real mixed difference
of X is  \(O(hr P^{-1/2})\) =o(1).

The exact integral formulas, with the  \(\beta\)  values frozen, are
\[
\begin{split}
F_0(v)&=\tfrac34\int_0^{\beta_1}\int_0^{\beta_2}
(v+b+c)^{-1/2}\,dc\,db,\\
F_j(v)-F_0(v)&=\tfrac{3j}{2}\int_0^1
(v+\beta_1+\beta_2+\tau j)^{1/2}\,d\tau .
\end{split} \tag{B.4}
\]
They hold for both signs of j. Differentiating with respect to v gives
\[
|F_j'(v)|\ll |j|P^{-3/4}+hrP^{-5/4},\qquad v\asymp P^{3/2}. \tag{B.5}
\]
Since 0 \(\le\) X(z)-m(z)<1, replacing  \(F_j\) (m(z)) by  \(F_j\) (X(z)) in
the exponential costs at most a constant times |a| times (B.5).
The error summed over all integers in the dyadic interval is
\[
\ll |a|P^{1/4}+|a|hrP^{-1/4}
\ll_C P^{3/4}/r+hP^{1/4}
\ll_C P^{3/4}. \tag{B.6}
\]
This is one global charge; it is not paid again on each branch.

A second differentiation after composition gives
\[
|(F_j\circ X)''|\ll |j|P^{-5/4}+hrP^{-7/4}.
\]
Consequently the retained D1 curvature is at most
\[
C\big(P^{-3/4}/r+hP^{-5/4}\big). \tag{B.7}
\]
The leading frozen coefficients provide a useful check:
\[
\begin{array}{c|cc}
& F_j'(v) & (F_j\circ X)''(x)\\ \hline
\text{offset part} & (3j/4)v^{-1/2} & -(9j/32)x^{-5/4}\\
\text{zero-offset part} & -(3\beta_1\beta_2/8)v^{-3/2}
& (63\beta_1\beta_2/64)x^{-11/4}.
\end{array}
\]
These are leading terms with uniform smaller remainders, not exact
equalities for finite  \(\beta\). One must not differentiate the moving
approximation  \(\beta_i\)  approximately 3h_i  \(\sqrt{x}\).

No large Fourier expansion of this D1 floor error is needed.

### B.2 Differencing and the nonzero main wave

Choose  \(H=\lfloor P^{1/12}\rfloor\). Apply van der Corput differencing
to the sequence indexed by the odd integers, using shifts 2h:
\[
|U|^2\ll_C P^2/H+(P/H)\sum_{1\le h<H}|V_h|. \tag{B.8}
\]
Here  \(V_h\)  is the correlation on the overlap of the original interval
and its translate. At most  \(O_C(h P^{13/24})\)  starting points cross
a cell boundary of  \(\mathcal P\). Their contribution is
\(O_C(P^{5/8})\)  for each h. On each remaining stable interval
I intersect (I-2h), all  \(a_j\)  are constant, the product of the two
amplitudes has bounded variation  \(O_C(1)\), and
\[
|(\Delta_{2h}\phi)''|\le 2h\sup_I|\phi'''|
\ll_C hP^{-13/12}. \tag{B.9}
\]
We apply all derivative tests to these intervals, never to a
domain punctured by individual exceptional integers.

Let  \(\theta\) (n)={X(n)}. Taylor's theorem gives
\[
Y(n)=n^{9/4}-\tfrac32\theta(n)n^{3/4}+E(n),
\qquad |E(n)|\ll P^{-3/4}.
\]
On a fixed main carry branch write  \(\beta\) =m(n+2h)-m(n), and put
\[
A_h(x)=\Delta_{2h}(x^{9/4})
-\tfrac32\Delta_{2h}X(x)(x+2h)^{3/4}.
\]
The exact resulting decomposition is
\[
\Delta_{2h}Y(n)= A_h(n)+\tfrac32\beta(n+2h)^{3/4}
-\tfrac32\theta(n)\Delta_{2h}(n^{3/4})+\Delta_{2h}E(n). \tag{B.10}
\]
The  \(\theta\)  term and E term cost, over the full correlation,
\[
O(|t|hP^{3/4}+|t|P^{1/4})=O_C(P^{7/8}). \tag{B.11}
\]
Taylor expansion of the smooth  \(A_h\), with derivatives, gives
\[
A_h''=O(h^2P^{-7/4}).
\]
On each branch  \(\beta\) =3h  \(\sqrt{x}\) + \(O(1+h^2P^{-1/2})\)  as a
comparison of values. Holding  \(\beta\)  fixed in differentiation, the
main retained phase therefore has
\[
\left(tA_h+\tfrac{3t}{2}\beta(x+2h)^{3/4}\right)''
=-\tfrac{27}{32}thx^{-3/4}(1+o(1)). \tag{B.12}
\]
The o(1) is uniform for 1 \(\le\) h \(\le\) H and for all admissible branches.

Write  \(M_h=|t|hP^{-3/4}\). The ratio of the combined D1 curvature
in (B.7) to  \(M_h\)  is
\[
O_{C,M}\big((|t|h)^{-1}+P^{-1/2}/|t|\big).
\]
Choose a sufficiently large constant  \(h_0\) = \(h_0\) (C,M), independent
of P. For h \(\ge\)  \(h_0\)  this ratio is smaller than a fixed fraction of
the lower constant in (B.12). The twist ratio in (B.9) is
\(O_C(P^{-1/3}/|t|)\). Thus all these terms preserve the one-signed
main curvature. This argument permits arbitrary signs and mutual
cancellation among the D1 coefficients.

There are only O_{C,M}(1) shifts h< \(h_0\). The trivial bound | \(V_h\) | \(\le\) C P
for these shifts contributes O_{C,M}(P^2/H) to (B.8).
Small values of P for which H< \(h_0\)  are covered by the implied constant.

### B.3 Insert the D2 reduction on its original runs

Use (A.9) of Appendix A.1 at this h, with Q=floor( \(P^{5/16}\) ).
Translations of the base and coefficient by  \(O_C(P^{1/24})\)  preserve
all derivative comparisons and run counts in that proof. Conjugation
handles  \(\sigma\) =-1, and  \(\sigma\) =0 contributes the constant factor one.

For each factor, outside an error whose sum of absolute values is
\(O_C(P^{15/16} \log P)\), the retained modes are
\[
e(\Phi_{\ell,q}),\qquad
\Phi_{\ell,q}=(N_\ell+q-B_\ell)G_\ell,\quad
B_\ell=\Delta_{2h}c_\ell,\quad N_\ell=\lfloor B_\ell\rfloor ,
\]
or their conjugates. Here |q| \(\le\) Q and on each coefficient window
the total coefficient sup norms plus variations are  \(O(\log P)\).
For a fixed number of factors these become a fixed power of log P.

Every such mode has
\[
|\Phi_{\ell,q}''|\ll_C P^{-15/16}. \tag{B.13}
\]
The ratio to  \(M_h\)  is  \(O_C(P^{-3/16}/(|t|h))\), and so preserves (B.12).
The additional coefficient-window count is
\[
O_C(1+k_\ell hP^{1/8})=O_C(P^{1/4});
\]
the original D2 run count is  \(O_C(P^{13/24})\). Both are retained
in the common partition below.

For clarity, the  \(P^{15/16}\)  error includes floor mismatches and
floor-crossing events. Those are compared in absolute value with
unimodular expressions and then replaced on full intervals. Their
counts are taken on the original D2 runs before any extra refinement.
Allowing fresh D2 labels on every added input cell would not be
justified by that count and is explicitly excluded in Theorem B.1.

### B.4 Reassemble the actual first-level carries

Apply Lemma A.2 to the finitely many first-floor evaluations in
the main wave and first-difference terms. Their even shifts are
\(O(h+P^{1/24})\). Intersect the resulting gap runs with the stable
input cells and the coefficient windows from Lemma A.1.
The full number of cells is
\[
D_h\ll_{C,M}(h+P^{1/24})P^{1/2}. \tag{B.14}
\]
The input partition contributes  \(O(P^{13/24})\)  cells; each floor-factor
coefficient contributes  \(O(P^{1/4})\)  additional windows.
Endpoint-order cuts multiply this number by a fixed constant.

At carry cutoff R=floor( \(P^{1/4}\) ), Lemma A.2 supplies the zero
coefficients with bounded variation, nonzero endpoint modes with
weights  \(O(1/|v|)\)  and phases vX(x+s), and total positive error
\(O(P^{5/6} \log P)\). This error is charged once over the common input
interval, multiplied only by the logarithmic coefficient masses
from the earlier expansions.

### B.5 Sum every retained mode and every cell

After the preceding replacements, the zero carry mode has
one-signed curvature comparable to  \(M_h\), uniformly in the D2 indices.
On a cell of length L the second-derivative test gives
\(O(L \sqrt{M_h}+M_h^{-1/2})\), also for any subinterval and the odd lattice.
Partial summation applies to  \(\eta\)  and all Fourier coefficients.
Their total sup norms plus variations on each cell are at most
a fixed power of log P. Summing lengths and all  \(D_h\)  endpoints gives
\[
\begin{split}
P\sqrt{M_h}+D_h M_h^{-1/2}
\ll_{C,M}{}&
(|t|h)^{1/2}P^{5/8}\\
&+\left(\sqrt{h/|t|}
+P^{1/24}(|t|h)^{-1/2}\right)P^{7/8}.
\end{split} \tag{B.16}
\]
For  \(h_0\)  \(\le\) h \(\le\)  \(P^{1/12}\)  and the stated t range this is
\(O_{C,M}(P^{11/12})\), before logarithmic losses.

For a nonzero carry Fourier mode v, its extra curvature is
vX''(x+s), of size |v| \(P^{-1/2}\). All other curvatures together
are  \(O_{C,M}(M_h)\), and
\[
\frac{M_h}{|v|P^{-1/2}}
\ll_{C,M}P^{-1/8}.
\]
Thus these modes also have one-signed curvature of the claimed size.
Summing their 1/|v| weights and all cell endpoints gives
\[
R^{1/2}P^{3/4}+D_h P^{1/4}
\ll_{C,M}P^{7/8}+(h+P^{1/24})P^{3/4}. \tag{B.17}
\]
This is  \(O_{C,M}(P^{7/8})\)  in the full range. A common reference
curvature and uniform cell count make this bound valid after summing
the coefficient masses of every D2 mode; no factor Q or  \(D_h\)  is
hidden in that mass.

Combining the absolute errors (B.6), (B.11), (A.12), the D2 error,
the coarse-boundary cost, and (B.16)--(B.17), for every h \(\ge\)  \(h_0\),
\[
|V_h|\ll_{C,M}P^{15/16}(\log(2P))^{B}, \tag{B.18}
\]
where B depends only on M. The largest cost is the D2 error.
Substitution in (B.8), with the finitely many small shifts treated
as in Appendix B.2, yields
\[
|U|^2\ll_{C,M}
P^{23/12}+P^{31/16}(\log(2P))^{B}.
\]
Since 23/12<31/16, this proves (B.3), absorbing logarithms into
an arbitrarily small positive power of P.


## Appendix C. Proof of the OOOEE mixed-mode theorem

Put
\[
\begin{gathered}
X(n)=n^{3/2},\quad m(n)=\lfloor X(n)\rfloor,\quad Y(n)=m(n)^{3/2},\\
v(n)=\lfloor Y(n)\rfloor,\quad Z(n)=v(n)^{3/2},\\
w(n)=\lfloor Z(n)\rfloor,\quad U(n)=\sqrt{w(n)}.
\end{gathered}
\]
For every fixed  \(C\ge1\)  and every  \(\varepsilon>0\), uniformly over
nonzero integer quadruples with
\(\max(|i|,|j|,|k|,|l|)\le CP^{1/24}\),
\[
\left|\sum_{\substack{P<n\le2P\\n\ {\rm odd}}}
e\left(\frac{iX(n)+jY(n)+kZ(n)+lU(n)}2\right)\right|
\ll_{C,\varepsilon}P^{127/128+\varepsilon}. \tag{C.1}
\]
Here \(e(x)=\exp(2\pi i x)\). These coordinates form a formal chain for
every odd n; they coincide with the Juggler trajectory on the
specified OOOEE sign class.

The counting consequences are
\[
\#\{n\le N:\operatorname{word}_5(n)=OOOEE\}
=\frac N{32}+O_\varepsilon(N^{127/128+\varepsilon}), \tag{C.2}
\]
and the class  \(\mathcal C_5\)  of starts with a power-envelope
contraction certificate of length at most five satisfies
\[
\#(\mathcal C_5\cap[1,N])
=\frac{7N}{8}+O_\varepsilon(N^{127/128+\varepsilon}). \tag{C.3}
\]
This is a certificate-class density, not the exact density of all
starts that happen to descend within five steps.

### C.1 The full phase

The proof uses Lemmas A.1--A.4 and Theorem B.1. The elementary
small-shift argument is Lemma 4.4. The fractional-floor exception
counts needed below are derived from (A.3)--(A.4) on original runs.
The exact centered master identity supplies the signed inventory.

The bare kernel bound alone is insufficient. Writing
\(\theta=\{X\}\)  and  \(\vartheta=\{Y\}\), Taylor's theorem gives
\[
\begin{split}
Z&=m^{9/4}-\tfrac32m^{3/4}\vartheta+O(P^{-9/8}),\\
m^{3/4}&=n^{9/8}+O(P^{-3/8}),\\
U&=m^{9/8}+O(P^{-9/16}).
\end{split}\tag{C.4}
\]
For the last assertion,
\(\sqrt{\lfloor Z\rfloor}=v^{3/4}+O(P^{-27/16})\)  and
\(v^{3/4}=Y^{3/4}+O(P^{-9/16})\).
All comparisons are uniform for n in [P,3P].

Let  \(c(x)=3kx^{9/8}/4\). Replacing the original phase by
\[
F(n)=\tfrac i2X(n)+\tfrac j2Y(n)+\tfrac k2m(n)^{9/4}
+\tfrac l2m(n)^{9/8}-c(n)\vartheta(n) \tag{C.5}
\]
costs in the whole exponential sum at most
\[
O_C\bigl(|k|P^{5/8}+|k|P^{-1/8}+|l|P^{7/16}\bigr)
=O_C(P^{2/3}). \tag{C.6}
\]
We keep both powers of m in (C.5) until after differencing. In
particular, the fifth-coordinate term is not expanded initially
into a Fourier series with a growing coefficient.

### C.2 The cases k=0, including every zero coordinate

In these cases (C.4) leaves the phase
\(iX/2+jY/2+l m^{9/8}/2\), with error already covered by (C.6).

If j is nonzero, apply one A-process with
\(H=\lfloor P^{1/12}\rfloor\). On a first-floor gap cell and
carry branch let  \(g=m(n+2h)-m(n)\), with g fixed and comparable
to  \(h\sqrt P\). For
\[
V_g(z)=(z+g)^{9/8}-z^{9/8}
\]
the exact integral formula gives
\[
|V_g'(X)|\ll hP^{-13/16},\qquad
|(V_g\circ X)''|\ll hP^{-21/16}. \tag{C.7}
\]
Replace  \(lV_g(m)/2\)  by  \(lV_g(X)/2\)  at the global cost
\(O(|l|hP^{3/16})\le O_C(P^{5/16})\).
In the proof of Lemma 4.4, add this last smooth term separately
to each of the two g branches. No new gap cell or carry is needed.
Its curvature relative to the main one
\(|j|hP^{-3/4}\)  is
\[
O(|l/j|P^{-9/16})=O_C(P^{-25/48}).
\]
The exact carry interpolation (4.8), global positive Fourier errors,
and domination of the nonzero first-floor Fourier modes therefore
remain valid. Both signs of j are handled by conjugating the whole
phase. The correlation is
\(O_C(P^{7/8}(1+\sqrt h))\); the A-process gives
\(O_C(P^{23/24})\).

If j=0 and l is nonzero, expand once:
\[
\tfrac l2m^{9/8}
=\tfrac l2n^{27/16}-B(n)\theta+O(|l|P^{-21/16}),
\quad B(x)=\tfrac{9l}{16}x^{3/16}. \tag{C.8}
\]
Set  \(N_B=\lfloor B\rfloor\)  and expand the bounded residual
\(B-N_B\)  at cutoff  \(T=\lfloor P^{1/8}\rfloor\).
The retained phases are
\[
f_r(x)=\tfrac l2x^{27/16}+(i/2+r-N_B)x^{3/2},\qquad |r|\le T.
\]
Freeze  \(N_B\)  when differentiating. Substituting its value only
after differentiation gives
\[
f_r''=\tfrac{81l}{512}x^{-5/16}
+O((|i|+T+1)P^{-1/2}). \tag{C.9}
\]
The coefficient is
\((1/2)(27/16)(11/16)-(9/16)(3/4)=81/512\).
The error relative to the leading term is
\(O_C(P^{-7/48}+P^{-1/16})\).
There are  \(O(1+|l|P^{3/16})\)  center windows; the Fourier
coefficient mass and variation on each are  \(O(\log P)\).
The summed second-derivative bound is
\[
O\left(|l|^{1/2}P^{27/32}
+(1+|l|P^{3/16})|l|^{-1/2}P^{5/32}\right)\log^C(2P)
\ll_C P^{83/96}\log^C(2P).
\]
The positive Fourier error totals  \(O(P^{7/8}\log P)\).
For example (A.12)'s distance-band proof gives
\(O(P\log(2T)/T+P^{5/6}\log(2P))\)  at this cutoff.
Thus this case is  \(O_C(P^{7/8}\log^C P)\).

Finally j=l=0 forces i nonzero. The smooth phase  \(iX/2\)
has curvature comparable to  \(|i|P^{-1/2}\)  and sum
\(O_C(P^{37/48}+P^{1/4})\). This covers every k=0 mode
without using (C.1).

### C.3 The twice-differenced inventory when k is nonzero

Conjugate all four frequencies if necessary to assume k \(\ge\) 1.
Use the ranges in Appendix A.3
\[
H_1=\lfloor P^{1/48}\rfloor,\quad H_2=\lfloor P^{1/24}\rfloor,
\quad 1\le h_a<H_a,\quad d_a=2h_a,\quad
p=h_1h_2,\quad \Pi=kp\ll_C P^{5/48}. \tag{C.10}
\]
Write  \(\Delta_a f(x)=f(x+d_a)-f(x)\),
\(W_a=\Delta_aY\),  \(D=\Delta_1\Delta_2Y\), and
\(c_{11}(x)=c(x+d_1+d_2)\).
The double difference of (C.5) is exactly
\[
\tfrac k2\Delta_1\Delta_2(m^{9/4})
+\tfrac l2\Delta_1\Delta_2(m^{9/8})
+\tfrac i2\Delta_1\Delta_2X+\tfrac j2D
-\Delta_1\Delta_2(c\vartheta). \tag{C.11}
\]

Apply the conjugate of the master expansion (A.15)--(A.18) to the
last term, with  \(J=\lfloor P^{1/24}\rfloor\). Set
\[
B_2=\Delta_2c(x+d_1),\quad B_1=\Delta_1c(x+d_2),
\quad N_a=\lfloor B_a\rfloor .
\]
The retained modes have phase
\[
\begin{split}
&\tfrac k2\Delta_1\Delta_2(m^{9/4})
+\tfrac l2\Delta_1\Delta_2(m^{9/8})-c_{11}\{D\}\\
&\hspace{8mm}+tY+a_1W_1+a_2W_2+qD+\phi_0,\qquad
a_1=-N_2+u,\quad a_2=-N_1+v.
\end{split}\tag{C.12}
\]
Here t,u,v are integers of absolute value  \(O_C(J)\);
\(q\in\frac12\mathbb Z\)  of absolute value  \(O_C(J)\), including
the original j/2. The function  \(\phi_0\)  is  \(i\Delta_1\Delta_2X/2\)
plus a bounded integer combination of  \(B_1,B_2,c_{11}\).
In particular
\[
\begin{split}
|a_1|h_1+|a_2|h_2
&\ll_C \Pi P^{1/8}+J(h_1+h_2)\ll_C P^{11/48},\\
|\phi_0''|&\ll_C kP^{-7/8}+|i|pP^{-5/2}.
\end{split}\tag{C.13}
\]
All signs of i,j,l,u,v,q are permitted.
The original jY/2 contributes only jD/2 after two differences,
so t remains an integer.

The full coefficient mass is  \(O(\log^7(2P))\). Each multi-index
has a fixed harmonic envelope under which its normalized
coefficient has bounded sup norm plus variation on the  \(N_1\), \(N_2\)
cells. The centers have local density  \(O_C(P^{-19/24})\).
These are exactly the centering and five binary-carry operations
in the master-inventory argument, with signs reversed. The deleted first
master term costs  \(O_C(P^{11/48})\), and all positive errors cost
\(O_C(P^{23/24}\log^C P)\). Their arguments are the same Y corners,
\(W_1\), \(W_2\),the shifted  \(W_1\), and D. The new factors in (C.11) have
modulus one, so the positive bounds (A.13) are unchanged. In
particular no OOOEE discrepancy has been assumed to control them.

### C.4 Frozen branches and the extra powers

Partition first into the original gap runs determined by the floors
of  \(\Delta_1X,\Delta_2X,\Delta_{d_1+d_2}X\).
Their total count is  \(O_C(P^{13/24})\), their local count in
length L is  \(O_C(1+LP^{-11/24})\), and their lengths are
\(O_C(\sqrt P)\). On a carry pattern let
\[
m(n+d_a)=m(n)+\beta_a,\quad
m(n+d_1+d_2)=m(n)+\beta_1+\beta_2+b .
\]
Then  \(-1\le b\le2\), since the real mixed difference of X is
positive and o(1). The  \(\beta\)  values and b are fixed on the branch;
\(\beta_a=3h_a\sqrt x+O(1+h_a^2P^{-1/2})\)  only as values.

For any exponent a define
\[
F_a(z)=(z+\beta_1+\beta_2+b)^a
-(z+\beta_1)^a-(z+\beta_2)^a+z^a .
\]
The formulas used for every derivative are
\[
\begin{split}
F_{a,0}(z)&=a(a-1)\int_0^{\beta_1}\int_0^{\beta_2}
(z+s+t)^{a-2}\,dt\,ds,\\
F_a(z)-F_{a,0}(z)&=ab\int_0^1
(z+\beta_1+\beta_2+\tau b)^{a-1}\,d\tau .
\end{split}\tag{C.14}
\]
They apply also when b<0. The notation  \(F_{a,0}\)  means b=0.
Put  \(G=F_{3/2}(X)\)  and  \(A=\lfloor F_{3/2}(m)\rfloor\).
The exact identity  \(\Delta_1\Delta_2(m^a)=F_a(m)\)
holds on its actual carry pattern.

The fifth-coordinate term can now be replaced directly by
\(lF_{9/8}(X)/2\). The relevant bounds are
\[
\begin{split}
|F_{9/8}'(X)|&\ll |b|P^{-21/16}+pP^{-29/16},\\
|(F_{9/8}\circ X)''|&\ll |b|P^{-29/16}+pP^{-37/16},\\
|(F_{9/8}\circ X)'''|&\ll |b|P^{-45/16}+pP^{-53/16}.
\end{split}\tag{C.15}
\]
The total replacement error is
\(O(|l|P^{-5/16}+|l|pP^{-13/16})=O_C(1)\).
Replacing qD by qG costs  \(O_C(P^{7/24})\), by (A.4) and the mean value theorem;
integrality of q is irrelevant for that comparison.

Combine the two large terms before expanding in  \(\theta\):
\[
H(z,x)=\tfrac k2F_{9/4}(z)-c_{11}(x)F_{3/2}(z),\qquad
B_{\rm core}(x)=\partial_zH(X(x),x).
\]
Since  \(-c_{11}\{D\}=-c_{11}F_{3/2}(m)+c_{11}A\), the
core of (C.12) is H(m,x)+ \(c_{11}\)  A. Taylor expansion gives
\[
H(m,x)=H(X,x)-B_{\rm core}\theta
+O_C(k|b|P^{-9/8}+\Pi P^{-13/8}), \tag{C.16}
\]
so its total error is bounded. The growing coefficient is
\[
B_{\rm core}
=\tfrac{27}{32}kb x^{3/8}
+O_C\bigl(\Pi P^{-1/8}+k(h_1+h_2)P^{-5/8}\bigr). \tag{C.17}
\]
The leading coefficient is  \(45/32-9/16=27/32\).
The remainder after subtracting \((27/32)kb x^{3/8}\) is bounded
in (C.10). Its derivative on each original run is
\(O_C(P^{-3/4})\), by (C.14) with the offsets fixed. Each such run
has length \(O_C(P^{1/2})\), so this remainder has bounded variation
there. The leading term itself has derivative \(O_C(kP^{-5/8})\);
it is not included in the smaller remainder-derivative bound.

All carry patterns are retained. As in (A.12), their indicators are
finite unions of arcs in  \(\theta\). Endpoint-order cuts add only a
fixed multiple of the run count. At cutoff  \(R_c=P^{1/4}\),
each nonzero endpoint mode has weight  \(O(1/|s|)\)  and phase
sX(x+d), for an allowed shift d; the zero coefficient has bounded
variation. Their global positive errors are  \(O(P^{5/6}\log P)\).
We use  \(R=P^{5/16}\)  for the bounded  \(\theta\)  coefficients below;
their global errors have the same bound. No error is charged
again on each gap run or frequency window.

### C.5 Nonzero total Y frequency

Suppose t is nonzero in (C.12). Keep the first differences
\(a_1W_1+a_2W_2\)  unexpanded and keep the floor A on its original
fixed-label runs. In particular do not cut into A's integer levels.

Center the growing term (C.17) at
\[
N_*=\left\lfloor\tfrac{27}{32}kb x^{3/8}\right\rfloor .
\]
On the intersections of original runs and \(N_*\) windows,
\(B_{\rm core}-N_*\) has bounded size and variation: the leading
fractional part is monotone with variation at most one, and the
remainder has the variation bound just proved. This residual need
not lie in \([0,1]\). For \(b=0\) use \(N_*=0\). Expand it at \(R\)
using the bounded-residual extension of Lemma 4.7.
After the first-floor carry expansion the smooth part is
\[
\Phi=H(X,x)+\tfrac l2F_{9/8}(X)+qG+\phi_0
+(r-N_*)X+sX(x+d).
\]
Its third derivative satisfies
\[
|\Phi'''|\ll_C
kP^{-9/8}+\Pi P^{-13/8}
+(R+|N_*|+R_c)P^{-3/2}
+|l|(P^{-45/16}+pP^{-53/16})
\ll_C P^{-13/12}. \tag{C.18}
\]
The q and  \(\phi_0\)  terms are smaller;  \(|N_*|\ll_C P^{5/12}\).

The common coarse partition consists of original runs,  \(N_1\), \(N_2\)
windows, N_* windows, and endpoint-order cuts. Its local count
remains  \(O_C(1+LP^{-11/24})\), since N_* has local density
\(O_C(kP^{-5/8})=O_C(P^{-7/12})\). Fixed b on each original
run permits this assertion even though b changes between runs.
The assigned D2 labels do not change at extra refinements.
An empty carry pattern is extended using an admissible fixed
label on that original run and zero amplitude there.

Every normalized retained term now satisfies (B.3): the nonzero
integer t is in its allowed range; (C.13) fits its widened
first-difference budget; (C.18) fits its twist budget; and the
single floor term is + \(c_{11}\)  A, namely  \(\sigma\) =-1 in (B.3).
The sum of all these weighted terms is
\[
O_{C,\varepsilon}(P^{31/32+\varepsilon}). \tag{C.19}
\]
The D2 reduction is invoked inside (B.3), after that theorem's
additional A-process, rather than on an arbitrary undifferenced
floor.

### C.6 Zero total Y frequency: shared reductions

Now t=0. Replace A by  \(J_F=\lfloor G\rfloor\).
For b nonzero, (A.3)--(A.4), at derivative scale
\(P^{-1/4}\)  and distance  \(O(P^{-3/4}+pP^{-5/4})\), give
\(O_C(P^{3/4})\)  exceptions on all original runs.
For b=0 the scale is \(pP^{-3/4}\), the distance is  \(O(pP^{-5/4})\),
and the same count is
\(O_C(pP^{1/4}+(h_1+h_2)P^{1/2})\) = \(O_C(P^{13/24})\). Each changed exponential costs at most two. The
coefficient  \(c_{11}\)  is not multiplied by the size of a floor error.

For  \(V_a(z)=(z+\beta_a)^{3/2}-z^{3/2}\), expand
\[
a_aV_a(m)=a_aV_a(X)-a_aV_a'(X)\theta
+O(|a_a|h_aP^{-7/4}).
\]
By (C.13) the global error is  \(O_C(P^{-25/48})\).
The smooth part and  \(\theta\)  coefficient are consequently
\[
\begin{split}
F_{\rm sm}&=\tfrac k2F_{9/4}(X)-c_{11}(G-J_F)
+a_1V_1(X)+a_2V_2(X)+\tfrac l2F_{9/8}(X)+qG+\phi_0,\\
B&=B_{\rm core}+a_1V_1'(X)+a_2V_2'(X).
\end{split}\tag{C.20}
\]
The wave contribution to B is bounded:
\[
\left|\sum a_aV_a'(X)\right|
\ll_C \Pi P^{-1/8}+J(h_1+h_2)P^{-1/4}\ll_C1.
\]
Its derivative on a frozen cell is bounded by
\(O_C(\Pi P^{-9/8}+J(h_1+h_2)P^{-5/4})\).
Multiplying the derivative bound by the original-run length
\(O_C(P^{1/2})\) proves bounded variation on every frozen cell;
refining a cell cannot increase this bound. Together with the
remainder bound following (C.17), this verifies the hypotheses of
the bounded-residual extension of Lemma 4.7 in both offset cases.
All integer levels of \(J_F\) are now included in the derivative-test
partition.

### C.7 Nonzero b: recompute the mixed curvature

For b nonzero, center B at the same N_* as in Appendix C.5;
its bounded residual has bounded variation. Retained phases are
\(f=F_{\rm sm}+(r-N_*)X+sX(x+d)\).

Freeze  \(\beta_a,b,J_F,N_*,N_a\)  before differentiation.
The three leading contributions, in units of  \(kb x^{-1/8}\),
are
\[
\begin{array}{c|c}
\text{term} & \text{coefficient}\\ \hline
(kF_{9/4}(X)/2)'' & 945/512\\
(-c_{11}(G-J_F))'' & -864/512\\
-N_*X'' & -324/512
\end{array}
\]
Their sum is
\[
-\tfrac{243}{512}. \tag{C.21}
\]
For the middle row use
\(-2c_{11}'G'-c_{11}G''-c_{11}''(G-J_F)\).
The last factor  \(G-J_F\)  is bounded, so its curvature term is
only  \(O(kP^{-7/8})\). Dropping the integer-floor contribution
would give the wrong leading coefficient.

Uniformly for every retained index,
\[
f''=-\tfrac{243}{512}kb x^{-1/8}+O_C(P^{-3/16}). \tag{C.22}
\]
For clarity, the error terms include
\[
\begin{split}
&\Pi P^{-5/8}+k(h_1+h_2)P^{-9/8}+kP^{-7/8}\\
&+(|a_1|h_1+|a_2|h_2)P^{-3/4}
+(R+R_c+1)P^{-1/2}+R_c(h_1+h_2)P^{-3/2}\\
&+|q|(P^{-5/4}+pP^{-7/4})
+|l|(P^{-29/16}+pP^{-37/16})+|\phi_0''|.
\end{split}
\]
Every term fits (C.22) under (C.10),(C.13). Both signs of b are
allowed. The error is smaller than the leading curvature by
\(O_C(P^{-1/16}/k)\).

The full number of intervals is  \(O_C(P^{3/4})\).
The G-levels add at most  \(O_C(P^{3/4}+P^{13/24})\);
the original gaps, moving centers, and arc-order cuts are smaller.
Summing lengths and every endpoint in the second-derivative
estimate, with coefficient masses and variation, gives
\[
O_C\left(\sqrt{k}P^{15/16}
+k^{-1/2}P^{13/16}\right)\log^C(2P)
\ll_C P^{23/24}\log^C(2P). \tag{C.23}
\]
The positive errors and floor exceptions are smaller. This
proves the nonzero-offset part for the actual mixed family.

### C.8 Zero b: the actual negative moving centers

When b=0, (C.20) has  \(|B|\ll_C1\)  and bounded variation on every
original run intersected with the  \(N_a\)  windows. Expand it directly
at R, without a new  \(\theta\)  center. After the carry expansion put
\(\ell_F=r+s\), an integer, and
\(\alpha_0=uh_1+vh_2\).
For fixed  \(\ell_F\), the coefficient sup norms plus variations
sum to  \(O(\log(2P)/(1+|\ell_F|))\). Indeed the convolution of the two coefficient envelopes satisfies
\[
\sum_{r+s=\ell_F}\frac1{(1+|r|)(1+|s|)}
\ll\frac{\log(2P)}{1+|\ell_F|}.
\]
Split at |r| \(\ge\) | \(\ell_F\) |/2 or |s| \(\ge\) | \(\ell_F\) |/2 to verify this bound.
The same estimate holds for the coefficient variations by the
product variation inequality; the phases for different r,s need not
be identical.

The pure  \(kF_{9/4}(X)/2\)  curvature has leading coefficient
\(-6075/2048\)  in units of  \(\Pi x^{-5/8}\).
The negative fractional anchor contributes
\(243/128=3888/2048\), so their subtotal is  \(-2187/2048\).
The centers in this problem have negative signs:
\[
h_1a_1+h_2a_2
=-\tfrac{27}{8}\Pi x^{1/8}+\alpha_0
+O_C(h_1+h_2+\Pi(h_1+h_2)P^{-7/8}). \tag{C.24}
\]
The frozen wave curvature is
\(-27(h_1a_1+h_2a_2)x^{-3/4}/32\), up to smaller terms.
It adds  \(729/256=5832/2048\)  to the subtotal. Thus
\[
f''=-\tfrac{27}{32}\alpha_0x^{-3/4}
+\tfrac{3645}{2048}\Pi x^{-5/8}
+\tfrac34\ell_Fx^{-1/2}
+O_C(\Pi P^{-3/4}). \tag{C.25}
\]
This is the coefficient for the complete mixed phase (C.12),
including the pure power and both moving centers.

The errors in (C.25) include
\[
\begin{split}
&(h_1+h_2)P^{-3/4}
+( |a_1|+|a_2| )P^{-5/4}
+( |a_1|h_1^2+|a_2|h_2^2 )P^{-7/4}\\
&+k(h_1+h_2)P^{-9/8}
+\Pi(h_1+h_2)P^{-13/8}
+kP^{-7/8}+|q|pP^{-7/4}\\
&+P^{-29/24}+|l|pP^{-37/16}+|\phi_0''|.
\end{split}
\]
Use  \(h_1+h_2\le2p\le2\Pi\), before inserting independent shift
caps, for the leading rounding error. All terms have the claimed
bound. The fifth-coordinate term is particularly small here.

There is a strict frequency gap:
\[
\frac{|\alpha_0|P^{-3/4}}{\Pi P^{-5/8}}
\ll_C JP^{-1/8}=O_C(P^{-1/12}),\qquad
\frac{\Pi P^{-5/8}}{P^{-1/2}}\ll_C P^{-1/48}. \tag{C.26}
\]
Consequently  \(\ell_F=0\)  has one-signed curvature comparable
to  \(\Pi P^{-5/8}\); every nonzero integer  \(\ell_F\)  has
one-signed curvature comparable to  \(|\ell_F|P^{-1/2}\).
No hypothesis on the largest individual signed wave is used.

The common partition has  \(O_C(P^{13/24})\)  cells, including
\(O_C(pP^{1/4}+P^{13/24})\)  zero-offset G-level cuts.
For  \(\ell_F=0\), summing all lengths and endpoints costs
\[
O_C\left(\Pi^{1/2}P^{11/16}
+\Pi^{-1/2}P^{41/48}\right)\log^C(2P).
\]
For nonzero  \(\ell_F\), sum the harmonic weights as well:
\[
O_C\left(R^{1/2}P^{3/4}+P^{13/24+1/4}\right)\log^C(2P)
=O_C(P^{29/32}\log^C(2P)). \tag{C.27}
\]
The zero mode and positive errors are smaller. This directly estimates the moving coefficients in (C.12), with every window endpoint included.

### C.9 Assembly and the dyadic count

For the double correlation of (C.5), the accounting is:

| Contribution | Exponent, apart from fixed logarithmic powers |
|---|---|
| Deleted master term | 11/48 |
| Positive short-Fourier errors | 23/24 |
| Extra-power Taylor errors and slow D replacement | at most 7/24 |
| Nonzero t, via (B.3) | 31/32 |
| t=0, nonzero b | 23/24 |
| t=0, b=0 | 29/32 |

The first-floor Fourier errors and floor mismatches are included
in the last three estimates. Thus the double correlation is
\(O_{C,\varepsilon}(P^{31/32+\varepsilon})\).
For the sum  \(S_F\)  and its first and second correlations,
van der Corput differencing on the odd lattice gives
\[
|S_F|^2\ll P^2/H_1+(P/H_1)\sum_{h_1<H_1}|T_1(h_1)|,
\]
\[
|T_1(h_1)|^2\ll P^2/H_2+(P/H_2)\sum_{h_2<H_2}|T_2(h_1,h_2)|.
\]
Substitution gives
\[
|T_1|^2\ll_C P^{47/24}+P^{63/32+\varepsilon},
\qquad |T_1|\ll_{C,\varepsilon}P^{63/64+\varepsilon},
\]
and
\[
|S_F|^2\ll_C P^{95/48}+P^{127/64+\varepsilon},
\qquad |S_F|\ll_{C,\varepsilon}P^{127/128+\varepsilon}.
\]
Overlap endpoints cost  \(O(h_1+h_2)\)  and fit these estimates.
Arbitrarily small epsilon losses may be relabeled after each step.
Together with Appendices C.1--C.2 this proves (C.1).

Apply the four-dimensional Erdős--Turán--Koksma inequality to
\[
(\{X/2\},\{Y/2\},\{Z/2\},\{U/2\})
\]
on the odd integers in a single dyadic block. Use cutoff
\(\lfloor P^{1/24}\rfloor\). Its diagonal error is  \(O(P^{23/24})\);
the weighted nonzero modes in (C.1) cost
\(O_\varepsilon(P^{127/128+\varepsilon})\), absorbing the
four harmonic sums. All sixteen half-boxes have volume 1/16.
Since there are P/2+ \(O(1)\)  odd inputs, each formal sign class has
count
\[
P/32+O_\varepsilon(P^{127/128+\varepsilon})
\]
on this block. A half-box records exactly the parity of the floor:
even for a coordinate in [0,1/2), odd for one in [1/2,1).

Use this discrepancy argument separately on each dyadic block
in a decomposition of [1,N], with that block's own frequency
cutoff. Then sum the counts and errors. One must not impose
the largest block's cutoff on all smaller blocks. Taking a small
epsilon first, the error series is geometric; the remaining
bounded initial interval contributes  \(O(1)\). The class with
m,v odd and w,floor(U) even is exactly OOOEE for odd n.
This proves (C.2), including endpoint conventions. All fifteen
nonempty products of its four parity signs also have this
error bound, by summing the sixteen sign classes. In the
manuscript's notation, H(OOOEE; \(\delta\) ) follows for every
\(0<\delta<1/128\).

Finally Lemma 5.1 and Theorem 5.3 of the manuscript give the
disjoint union of its 27/32 class and OOOEE. The former error
\(O(N^{47/48})\)  is smaller. Their densities add to
\(27/32+1/32=7/8\), proving (C.3).
This proves Corollary 4.12 and Theorem 5.4.


## Acknowledgments and AI assistance

Large language models were used throughout the development of the
earlier draft and this revision, including the formulation and review
of proof arguments, drafting, programming, and discussion of Lean
formalizations. The September 2026 review with OpenAI Codex identified
unresolved analytic steps and assisted with the conditional revision,
the four-step and fifth-letter repairs, the D2 reduction, the signed
mixed-mode proofs, their consolidation into this version, and the
release materials. AI assistance and automated
checks are not independent mathematical validation. The author is
responsible for the statements, proofs, code, and final approval of
the preprint. The models are not authors.

## References

1. OEIS Foundation Inc., "Juggler sequence: if n mod 2 = 0 then
floor( \(\sqrt{n}\) ) else floor( \(n^{3/2}\) )," *The On-Line Encyclopedia of
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
