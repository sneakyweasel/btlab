---
title: "Fate contagion for the Juggler map: every fate class has logarithmic counting function at least (log x)^{0.40}"
author: Philippe Cochin
date: 3 September 2026
subtitle: Laboratory note. Not a paper claim; not a termination theorem.
---

## 0. What this note is and is not

The Juggler map \(J(n)=\lfloor\sqrt n\rfloor\) (\(n\) even),
\(\lfloor n^{3/2}\rfloor\) (\(n\) odd) gives every start exactly one of
three fates (Paper A, Lemma 1.1; Lean `fate_trichotomy`): it reaches
\(1\), it enters a nontrivial cycle, or its orbit is unbounded. This
note proves that the fates are **contagious**: whichever fate occurs
at all occurs on a set whose *logarithmic* counting function grows
at least like a fixed power of \(\log x\),
\[
\sum_{\substack{n\le x\\ \mathrm{fate}(n)=\varphi}}\frac1n
\;\ge\; c_\varphi\,(\log x)^{\lambda}
\qquad(\lambda<\lambda^{**}=0.405\ldots),
\]
whereas the full set of integers has \(\sum_{n\le x}1/n\sim\log x\).
The mechanism is that the one-step preimages of the Juggler map are
*large and structured*: the even preimages of \(m\) fill the whole
interval \([m^2,(m+1)^2)\), and the two-step preimages through an
even middle state fill a positive proportion of the fiber
\(\lfloor n^{3/4}\rfloor=m\), on which \(\lfloor n^{3/2}\rfloor\)
sweeps its parity. Because the argument is a *lower-bound recursion*,
it needs only positive proportions on fibers, not equidistribution,
and it therefore bypasses the short-interval wall that stops
Paper B's equidistribution machinery.

Consequences. (i) The set \(R\) of starts that reach \(1\) has
\(\sum_{n\in R,\,n\le x}1/n\gg(\log x)^{\lambda}\). (ii) If a single
start fails to reach \(1\), the failures have the same lower bound,
and on infinitely many dyadic blocks they have natural density
\(\gg(\log y)^{\lambda-1}\). (iii) **The Juggler conjecture is
equivalent to a Tao-type almost-all statement with a mild rate**: if
the starts whose orbit never drops into the certified interval
\([1,3.5\cdot 10^8]\) have logarithmic count \(o((\log x)^{0.40})\),
then every start reaches \(1\). For the Collatz map the analogous
implication is unavailable, because Collatz backward trees are thin
(\(x^{0.84}\), Krasikov--Lagarias); for the Juggler map the even
preimage interval makes them fat.

This note excludes no fate. It does not prove termination, it does
not exclude cycles, and it does not exclude divergent orbits. Its
content is the quantitative shape of the trichotomy.

Lean: the exact combinatorial layer (backward closure of the fate
classes, the even block, the OE fiber, the fourth-power cell identity,
the trichotomy with basins named, mutual exclusion of the fates) is
`formal/Problems/Juggler/FateContagion.lean`, no `sorry`. The
analytic counting (Sections 3--4) is a human proof; its two inputs
are checked numerically in
`data/research/juggler/fate_contagion/summary.json`.

## 1. Setting

\(\mathbb N=\{1,2,\dots\}\). For \(A\subseteq\mathbb N\) and
\(0\le u<v\) write
\[
\ell_A(u,v]=\sum_{\substack{n\in A\\ u<n\le v}}\frac1n,\qquad
L_A(x)=\ell_A(0,x],\qquad
g_A(t)=\ell_A\bigl(e^{t/2},e^{t}\bigr].
\]
For \(A=\mathbb N\), \(g(t)=t/2+O(e^{-t/2})\).

**Definition.** \(A\) is *backward-closed* if \(J(n)\in A\) implies
\(n\in A\); *forward-closed* if \(n\in A\) implies \(J(n)\in A\).

**Lemma 1.1 (fate classes).** Let \(R=\{n:\exists k,\ J^k(n)=1\}\),
\(F=\mathbb N\setminus R\), \(B(m)=\{n:\exists k,\ J^k(n)=m\}\) for
any \(m\), and \(D=\{n:\forall B\ \exists k,\ J^k(n)>B\}\). Each of
\(R,F,B(m),D\) is backward-closed; \(R,F,D\) are also forward-closed.
Every \(n\ge 1\) lies in \(R\), or in \(B(m)\) for some \(m\ge 2\) on a
cycle, or in \(D\), and these possibilities exclude one another.

*Proof.* Backward closure is the definition of each set (for \(D\):
\(J^k(J(n))=J^{k+1}(n)\)). Forward closure of \(R\): if
\(J^k(n)=1\) then \(J^{k-1}(J(n))=1\) for \(k\ge 1\), and
\(J(1)=1\). Forward closure of \(D\): given \(B\), pick \(k\) with
\(J^k(n)>\max(B,n)\); then \(k\ge 1\) and \(J^{k-1}(J(n))>B\). The
trichotomy is Lemma 1.1 of Paper A: a bounded orbit repeats, a
repeat is a cycle, a cycle through \(1\) is the fate \(R\). Exclusion:
an orbit that reaches \(1\) or enters a cycle is bounded; an orbit
that reaches \(1\) and passes through a cycle state \(m\ge 2\) would
force \(m=J^{qL}(m)=1\). Lean: `reachesOne_backwardClosed`,
`not_reachesOne_backwardClosed`, `ancestor_backwardClosed`,
`escapes_backwardClosed`, `reachesOne_floorPower`,
`escapes_floorPower`, `fate_trichotomy`, `reachesOne_not_escapes`,
`cycle_basin_not_escapes`, `reachesOne_not_cycle_basin`. \(\square\)

Throughout, \(A\) is a nonempty backward-closed set. Every statement
below applies to each fate class that is realized by at least one
start.

## 2. The two productions

**Lemma 2.1 (even block).** Let \(m\in A\). Every even \(n\) with
\(m^2\le n<(m+1)^2\) lies in \(A\). Write
\(E(m)\) for this set. Then \(|E(m)|\ge m\) and
\[
\sum_{n\in E(m)}\frac1n\ \ge\ \frac{m}{(m+1)^2}\ \ge\ \frac1m\Bigl(1-\frac2m\Bigr).
\]

*Proof.* \(J(n)=\lfloor\sqrt n\rfloor=m\) exactly on that interval
(`Nat.eq_sqrt`), so \(n\in A\). The interval has \(2m+1\) integers,
at least \(m\) of them even. Each is below \((m+1)^2\). Lean:
`even_block_mem`, `even_block_card`. \(\square\)

**Lemma 2.2 (OE fiber).** Let \(m\in A\) and let
\[
\Phi(m)=\{n\ \text{odd}:\ m^4\le n^3<(m+1)^4\}
=\{n\ \text{odd}:\ m^{4/3}\le n<(m+1)^{4/3}\}.
\]
If \(n\in\Phi(m)\) and \(\lfloor n^{3/2}\rfloor\) is even, then
\(J(J(n))=m\), hence \(n\in A\). Moreover
\[
H_m:=|\Phi(m)|\in\Bigl[\tfrac23m^{1/3}-1,\ \tfrac23(m+1)^{1/3}+1\Bigr],
\]
and the fibers of distinct \(m\) are disjoint.

*Proof.* \(J(n)=\lfloor\sqrt{n^3}\rfloor=:k\); if \(k\) is even then
\(J(k)=\lfloor\sqrt k\rfloor\), and
\(\lfloor\sqrt{\lfloor\sqrt N\rfloor}\rfloor=m\iff m^4\le N<(m+1)^4\)
(`sqrt_sqrt_eq_iff`; this is the exact form of the transparent
nesting \(\lfloor\sqrt{\lfloor n^{3/2}\rfloor}\rfloor=\lfloor n^{3/4}\rfloor\)).
The interval \([m^{4/3},(m+1)^{4/3})\) has length between
\(\tfrac43m^{1/3}\) and \(\tfrac43(m+1)^{1/3}\) by the mean value
theorem, and a half-open interval of length \(\ell\) contains
between \(\ell/2-1\) and \(\ell/2+1\) odd integers. Disjointness is
the cell identity. Lean: `oe_fiber_mem`, `floorPower_oe_fiber`,
`oe_fiber_disjoint`. \(\square\)

Write \(G_m=\#\{n\in\Phi(m):\lfloor n^{3/2}\rfloor\ \text{even}\}\).
The whole note rests on lower bounds for \(G_m\): one elementary
bound valid on every fiber outside a thin exceptional set
(Section 3.1), and one classical average over an even block of
\(m\)'s (Section 3.2).

## 3. Parity on a fiber

### 3.1 The sweep lemma

On the fiber \(\Phi(m)\) the quantity \(x=n^{3/2}/2\) has
\(\lfloor n^{3/2}\rfloor\) even iff \(\{x\}<\tfrac12\). Consecutive
odd \(n\) advance \(x\) by \(\approx\tfrac32 n^{1/2}\approx\tfrac32m^{2/3}\),
and over the whole fiber this step drifts by less than one unit of
\(1/H_m\). So mod \(1\) the fiber is an arithmetic progression with
a nearly constant step \(\alpha\), of length \(H_m\). Such a
progression cannot avoid a half-circle unless its step is within
\(O(1/H_m)\) of \(0\) (or its two-step is, i.e. \(\alpha\approx\tfrac12\)
with the wrong phase). This is the sweep lemma.

**Lemma 3.1 (sweep).** Let \(x_1<x_2<\dots<x_H\) be real numbers with
\(x_{j+1}-x_j\in[a,b]\) for all \(j\), where \(0<a\le b\le\tfrac12\),
\(b\le\tfrac{21}{20}a\) and \((H-1)a\ge 12\). Then
\[
\#\{j:\{x_j\}<\tfrac12\}\ \ge\ \tfrac H7
\qquad\text{and}\qquad
\#\{j:\{x_j\}\ge\tfrac12\}\ \ge\ \tfrac H7 .
\]
The same holds with the cells \((k/2,(k+1)/2]\) in place of
\([k/2,(k+1)/2)\), i.e. with the representative in \((0,1]\) in place
of the fractional part.

*Proof.* Cut \(\mathbb R\) into cells \(C_k=[k/2,(k+1)/2)\),
\(k\in\mathbb Z\); even \(k\) are the *good* cells (\(\{x\}<\tfrac12\)),
odd \(k\) the *bad* cells. Call \(C_k\) *traversed* if
\(x_1\le k/2\) and \((k+1)/2\le x_H\).

(i) *A traversed cell contains at least \(g:=\lfloor 1/(2b)\rfloor\ge 1\)
and at most \(G:=\lfloor 1/(2a)\rfloor+1\) of the points.* Let
\(j_0\) be the least index with \(x_{j_0}\ge k/2\). Then
\(x_{j_0}<k/2+b\) (either \(j_0=1\) and \(x_1=k/2\), or
\(x_{j_0-1}<k/2\)). Since every step is at most \(b\),
\(x_{j_0+i}<k/2+(i+1)b\le(k+1)/2\) for all \(i\le 1/(2b)-1\), and
these indices exist because \((k+1)/2\le x_H\). That gives at least
\(\lfloor 1/(2b)\rfloor\) points in \(C_k\). Since every step is at
least \(a\), the points in \(C_k\) are \(x_{j_0+i}\) with
\(k/2+ia\le x_{j_0+i}<(k+1)/2\), so \(i<1/(2a)\) and there are at
most \(\lfloor 1/(2a)\rfloor+1\) of them. The same count holds for
*any* cell (traversed or not) as an upper bound.

(ii) *Counting cells.* The traversed cells are consecutive, and
their number \(T\) is at least \(2(x_H-x_1)-2\ge 2(H-1)a-2\ge 22\).
Good and bad traversed cells alternate, so their numbers \(T_g,T_b\)
differ by at most one and \(T_g,T_b\ge 10\). Every point outside the
traversed cells lies in the cell of \(x_1\) or the cell of \(x_H\).

(iii) *The ratio.* Hence
\(\mathrm{Good}\ge gT_g\) and
\(H\le G(T_g+T_b+2)\le G(2T_g+3)\), so
\[
\frac{\mathrm{Good}}H\ \ge\ \frac gG\cdot\frac{T_g}{2T_g+3}\ \ge\ \frac gG\cdot\frac{10}{23}.
\]
Put \(X=1/(2a)\ge 1\), so \(G=\lfloor X\rfloor+1\) and, from
\(b\le\tfrac{21}{20}a\), \(g\ge\lfloor\tfrac{20}{21}X\rfloor\). If
\(X<2\): \(g\ge 1,G\le 2\). If \(2\le X<3\): \(g\ge 1,G=3\). If
\(3\le X<4\): \(g\ge 2,G=4\). If \(4\le X<5\): \(g\ge 3,G=5\). If
\(X\ge 5\): \(g/G\ge(\tfrac{20}{21}X-1)/(X+1)\ge 0.62\). In all cases
\(g/G\ge\tfrac13\), so \(\mathrm{Good}/H\ge\tfrac{10}{69}>\tfrac17\).
The bad count is symmetric. For left-open cells the same proof
applies verbatim (the first point in a cell \((c,c+\tfrac12]\) after
a point \(\le c\) is \(\le c+b\le c+\tfrac12\)). \(\square\)

**Lemma 3.2 (fiber parity).** For \(m\ge 10^6\) put
\(\alpha_m=\{\tfrac32m^{2/3}\}\) and call \(m\) *good* if
\[
\|\alpha_m\|\ \ge\ 22\,m^{-1/3}
\qquad\text{and}\qquad
\|\alpha_m-\tfrac12\|\ \ge\ 2\,m^{-1/3},
\]
where \(\|\cdot\|\) is the distance to the nearest integer. If \(m\)
is good then
\[
G_m\ \ge\ \tfrac17H_m
\qquad\text{and}\qquad
H_m-G_m\ \ge\ \tfrac17H_m .
\]

*Proof.* Let \(n_1<\dots<n_H\) be the odd integers of \(\Phi(m)\),
\(n_{j+1}=n_j+2\), and \(x_j=n_j^{3/2}/2\). Then
\(\lfloor n_j^{3/2}\rfloor\) is even iff \(\{x_j\}<\tfrac12\). The
steps are
\[
\delta_j=x_{j+1}-x_j=\int_{n_j}^{n_j+2}\tfrac34t^{1/2}\,dt
\in\bigl[\tfrac32n_j^{1/2},\ \tfrac32(n_j+2)^{1/2}\bigr]
\subseteq[A_m,B_m],
\]
with \(A_m=\tfrac32m^{2/3}\) and
\(B_m=\tfrac32\bigl((m+1)^{4/3}+2\bigr)^{1/2}\). Using
\(\sqrt u-\sqrt v\le(u-v)/(2\sqrt v)\) and
\((m+1)^{4/3}-m^{4/3}\le\tfrac43(m+1)^{1/3}\),
\[
\eta_m:=B_m-A_m\le\frac{(m+1)^{1/3}+\tfrac32}{m^{2/3}}
\le m^{-1/3}\Bigl(1+\frac1{3m}+\frac32m^{-1/3}\Bigr)\le 1.02\,m^{-1/3}.
\]
Also \(H_m-1\ge\tfrac23m^{1/3}-2\ge 0.646\,m^{1/3}\).

*Case 1: \(\alpha_m\le\tfrac12-2m^{-1/3}\).* Put \(N=\lfloor A_m\rfloor\)
and \(y_j=x_j-jN\); then \(\{y_j\}=\{x_j\}\) and the steps of \(y\)
lie in \([a,b]=[\alpha_m,\alpha_m+\eta_m]\subseteq[22m^{-1/3},\tfrac12]\).
Now \(b/a\le 1+1.02/22<\tfrac{21}{20}\) and
\((H-1)a\ge 0.646\cdot 22>12\). Lemma 3.1 applies.

*Case 2: \(\alpha_m\ge\tfrac12+2m^{-1/3}\).* Put
\(z_j=j(N+1)-x_j\), increasing with steps
\((N+1)-\delta_j\in[1-\alpha_m-\eta_m,\ 1-\alpha_m]
\subseteq[20.98\,m^{-1/3},\ \tfrac12]\); again
\(b/a\le 1+1.02/20.98<\tfrac{21}{20}\) and \((H-1)a\ge 0.646\cdot 20.98>12\).
Write \(\langle z\rangle\in(0,1]\) for the representative of \(z\)
modulo \(1\) in \((0,1]\). Then \(\langle z_j\rangle=1-\{x_j\}\) for
every \(j\), so \(\{x_j\}<\tfrac12\iff\langle z_j\rangle\in(\tfrac12,1]\).
Lemma 3.1 in its left-open form gives both counts.

The middle range \(|\alpha_m-\tfrac12|<2m^{-1/3}\) and the range
\(\|\alpha_m\|<22m^{-1/3}\) are excluded by goodness. \(\square\)

**Lemma 3.3 (bad fibers are thin).** For \(u\ge 10^6\),
\[
\#\{m\in(u,2u]:\ m\ \text{bad}\}\le 63\,u^{2/3},
\qquad
\sum_{\substack{m>U\\ m\ \text{bad}}}\frac1m\le 306\,U^{-1/3}\quad(U\ge 10^6).
\]

*Proof.* \(\varphi(m)=\tfrac32m^{2/3}\) increases with
\(\varphi(m+1)-\varphi(m)\in[(m+1)^{-1/3},m^{-1/3}]\subseteq[(3u)^{-1/3},u^{-1/3}]\)
on \((u,2u]\). Badness means \(\{\varphi(m)\}\) lies in one of two
arcs of the circle, of total length at most \(48\,u^{-1/3}\). As
\(m\) runs over \((u,2u]\), \(\varphi\) increases by
\(\tfrac32u^{2/3}(2^{2/3}-1)<0.882\,u^{2/3}\), so it passes each arc
at most \(0.882u^{2/3}+2\) times, and each pass through an arc of
length \(w\) takes at most \(w(3u)^{1/3}+1\) values of \(m\). Hence
the count is at most
\((0.882u^{2/3}+2)(48\cdot 3^{1/3}+2)\le 63\,u^{2/3}\) for
\(u\ge 10^6\). Summing \(63\,(2^iU)^{-1/3}\) over \(i\ge 0\) gives
\(63U^{-1/3}/(1-2^{-1/3})\le 306\,U^{-1/3}\). \(\square\)

### 3.2 The block average

The elementary bound \(G_m\ge H_m/7\) is far from the truth
(\(G_m/H_m\) has mean \(\tfrac12\) and is at least \(\approx\tfrac13\)
on every good fiber in the census). When the members of \(A\) come
in even blocks — as the \(E\)-produced part of \(A\) always does —
the fibers can be averaged over the block, and the average is
exactly \(\tfrac12\) by a classical exponential-sum estimate.

**Proposition 3.4 (block average).** For \(m'\ge 2\) let
\(I(m')=[m'^{8/3},(m'+1)^{8/3})\) and
\[
U(m')=\{n\ \text{odd in}\ I(m'):\ \lfloor n^{3/4}\rfloor\ \text{even},\ \lfloor n^{3/2}\rfloor\ \text{even}\}
=\bigsqcup_{\substack{m\in E(m')}}\{n\in\Phi(m):\lfloor n^{3/2}\rfloor\ \text{even}\}.
\]
There is an absolute constant \(C_0\) with
\[
|U(m')|\ \ge\ \tfrac14\,\#\{n\ \text{odd in}\ I(m')\}-C_0\,m'^{11/9}\log(m'+1).
\]
Since \(\#\{n\ \text{odd in}\ I(m')\}\ge\tfrac43m'^{5/3}-1\), this
reads \(|U(m')|\ge\tfrac13m'^{5/3}\bigl(1-\varepsilon_B(m')\bigr)\)
with \(\varepsilon_B(m')=\tfrac34m'^{-5/3}+3C_0m'^{-4/9}\log(m'+1)\to 0\).

*Proof.* Write \(\psi(y)=(-1)^{\lfloor y\rfloor}\), so that
\([\lfloor y\rfloor\ \text{even}]=\tfrac12(1+\psi(y))\), and
\[
|U(m')|=\tfrac14\sum_{n}\bigl(1+\psi(n^{3/4})+\psi(n^{3/2})+\psi(n^{3/4})\psi(n^{3/2})\bigr),
\]
the sum over odd \(n\in I(m')\). Four terms.

*Term 1* is the main term.

*Term 2.* \(\lfloor n^{3/4}\rfloor=m\) is constant on each fiber, so
\(\sum\psi(n^{3/4})=\sum_{m'^2\le m<(m'+1)^2}(-1)^mH_m\). Since
\(H_m\) is within \(1\) of half the length of the fiber and
consecutive fiber lengths differ by at most \(1\),
\(|H_{m+1}-H_m|\le 3\); pairing consecutive \(m\) gives
\(|\text{Term 2}|\le 3m'+\max H_m\ll m'\).

*Term 3.* Expand \(\psi\) by Vaaler's theorem (Paper B, Lemma 3.5):
\(\psi(y)=V_J(y/2)+O(\Delta_J(y/2))\), where
\(V_J(t)=\sum_{0<|q|\le J}a_qe(qt)\) with \(|a_q|\ll 1/|q|\) and
\(\Delta_J\ge 0\) is a trigonometric polynomial of degree \(J\) with
constant term and coefficients \(\le 1/(J+1)\). Reindex \(n=2r+1\).
For \(q\ne 0\) the phase \(f(r)=q(2r+1)^{3/2}/2\) has
\(f''(r)=\tfrac32q\,n^{-1/2}\), which on \(I(m')\) lies between
\(\lambda_q=\tfrac32|q|(m'+1)^{-4/3}\) and \(2^{4/3}\lambda_q\). The
second-derivative test (Paper B, Lemma 3.3) with interval length
\(M\le\tfrac43(m'+1)^{5/3}+1\) gives
\[
\Bigl|\sum_r e(f(r))\Bigr|\ll M\lambda_q^{1/2}+\lambda_q^{-1/2}
\ll |q|^{1/2}m'+|q|^{-1/2}m'^{2/3}.
\]
Summing against \(|a_q|\ll 1/|q|\) over \(0<|q|\le J\) gives
\(\ll J^{1/2}m'+m'^{2/3}\). The \(\Delta_J\) error contributes
\(\ll M/J+J^{-1}\sum_{0<|q|\le J}|\sum_re(f)|\ll m'^{5/3}/J+J^{1/2}m'\).
With \(J=m'^{4/9}\) both are \(\ll m'^{11/9}\).

*Term 4.* Expand both factors. The main part is
\(\sum_{q_1,q_2\ne 0}a_{q_1}a_{q_2}\sum_re\bigl(f_{q_1,q_2}(r)\bigr)\) with
\(f_{q_1,q_2}(r)=\tfrac12\bigl(q_1(2r+1)^{3/4}+q_2(2r+1)^{3/2}\bigr)\) and
\[
f''_{q_1,q_2}(r)=\tfrac32q_2n^{-1/2}\Bigl(1-\frac{q_1}{4q_2}\,n^{-3/4}\Bigr).
\]
For \(|q_1|\le J=m'^{4/9}\) and \(n\ge m'^{8/3}\) the correction is
\(\le\tfrac14m'^{4/9-2}\), so \(|f''|\) is again between
\(\lambda_{q_2}\) and \(2^{4/3}\lambda_{q_2}\) up to a factor
\(1+o(1)\), uniformly in \(q_1\); the second-derivative test gives the
same bound as in Term 3, and the double sum against
\(|a_{q_1}a_{q_2}|\ll 1/(|q_1||q_2|)\) is
\(\ll(\log J)(J^{1/2}m'+m'^{2/3})\). Three error terms remain.
\(\sum\Delta_J(n^{3/2}/2)\) is bounded as in Term 3. For
\(\sum\Delta_J(n^{3/4}/2)\) the constant term gives \(M/(J+1)\) and
each mode \(0<|q_1|\le J\) gives \((J+1)^{-1}|\sum_re(q_1(2r+1)^{3/4}/2)|\);
here the phase has derivative \(\tfrac34q_1n^{-1/4}\), monotone and
of size between \(\tfrac34|q_1|(m'+1)^{-2/3}\) and
\(\tfrac34m'^{4/9-2/3}<\tfrac12\), so the Kusmin--Landau first-derivative
test bounds the sum by \(\ll m'^{2/3}/|q_1|\); the modes contribute
\(\ll m'^{2/3}\log J/J\) in total. The product error
\(\sum\Delta_J\Delta_J\) is at most \(\sup\Delta_J\le 2\) times either
of the two previous sums. Altogether Term 4 is
\(\ll m'^{11/9}\log m'\).

Collecting, \(|U(m')|=\tfrac14\#\{n\ \text{odd in}\ I(m')\}+O(m'^{11/9}\log(m'+1))\).
\(\square\)

*Numerical check.* On the census \(m'\in[20,60)\cup[200,230)\cup[1000,1010)\cup\{3000,5000\}\)
the deviation from the main term is at most \(0.9\sqrt{|I(m')_{\rm odd}|}\),
i.e. square-root scale, and at most \(0.078\,m'^{11/9}\log m'\)
(`block_census` in `summary.json`). The proposition is not sharp; it
is all the recursion needs.

## 4. The recursion and the theorem

### 4.1 Three sources of members of \(A\) in \((\sqrt x,x]\)

Let \(x\ge 2\) and \(t=\log x\). Three families of members of
\(A\cap(\sqrt x,x]\) are pairwise disjoint:

1. **\(E\)-images.** For \(m\in A\cap(x^{1/4},\sqrt x-1]\),
   \(E(m)\subseteq(\sqrt x,x]\) (as \(m^2>\sqrt x\) and
   \((m+1)^2\le x\)). Distinct \(m\) give disjoint blocks. By
   Lemma 2.1 the log-mass is at least
   \(\sum_m\frac1m(1-\frac2m)\ge(1-2x^{-1/4})\,\ell_A(x^{1/4},\sqrt x-1]\),
   and \(\ell_A(x^{1/4},\sqrt x-1]\ge g_A(t/2)-2x^{-1/2}\) (at most one
   integer lies in \((\sqrt x-1,\sqrt x]\)).

2. **\(OE\)-images of \(E\)-blocks.** For \(m'\in A\cap(x^{3/16},x^{3/8}-1]\),
   \(U(m')\subseteq A\cap(\sqrt x,x]\) (Lemma 2.2 applied to the even
   \(m\in E(m')\subseteq A\); \(I(m')\subseteq(\sqrt x,x]\) as
   \(m'^{8/3}>\sqrt x\) and \((m'+1)^{8/3}\le x\)). Distinct \(m'\)
   give disjoint \(I(m')\). Each \(n\in U(m')\) has
   \(1/n>(m'+1)^{-8/3}\), so by Proposition 3.4 the log-mass of
   \(U(m')\) is at least
   \(\tfrac13m'^{5/3}(1-\varepsilon_B(m'))(m'+1)^{-8/3}\ge\frac1{3m'}\bigl(1-\varepsilon_B(m')-\tfrac8{3m'}\bigr)\),
   and summing,
   \(\ge\tfrac13(1-\varepsilon'(x))\bigl(g_A(3t/8)-2x^{-3/8}\bigr)\) with
   \(\varepsilon'(x)=\sup_{m'>x^{3/16}}(\varepsilon_B(m')+\tfrac8{3m'})\to 0\).

3. **\(OE\)-images of the rest.** Let
   \(A^{E}_x=\bigcup_{m''\in A}E(m'')\cap(x^{3/8},x^{3/4}]\) be the
   \(E\)-produced part of \(A\cap(x^{3/8},x^{3/4}]\) and
   \(A^{\rm rest}_x\) its complement in \(A\cap(x^{3/8},x^{3/4}]\).
   The blocks meeting \((x^{3/8},x^{3/4}]\) come from
   \(m''\in[x^{3/16}-1,x^{3/8}]\), so
   \(\ell(A^E_x)\le\sum_{m''}\frac{m''+1}{m''^2}\le(1+2x^{-3/16})\bigl(g_A(3t/8)+2x^{-3/16}\bigr)\)
   and
   \(\ell(A^{\rm rest}_x)\ge g_A(3t/4)-(1+2x^{-3/16})\bigl(g_A(3t/8)+2x^{-3/16}\bigr)\).
   For \(m\in A^{\rm rest}_x\) with \(m\le x^{3/4}-1\) (this drops
   at most one element, of log-mass \(\le 2x^{-3/4}\)),
   \(\Phi(m)\subseteq(\sqrt x,x]\); the fibers are disjoint from each
   other and from those of item 2 (different \(m\)), and for good
   \(m\ge 10^6\) Lemma 3.2 and Lemma 2.2 give log-mass at least
   \(\tfrac17\bigl(\tfrac23m^{1/3}-1\bigr)(m+1)^{-4/3}\ge\frac2{21m}(1-2m^{-1/3})\).
   Bad \(m>x^{3/8}\) carry log-mass at most \(306x^{-1/8}\)
   (Lemma 3.3). Hence item 3 contributes at least
   \(\tfrac2{21}(1-2x^{-1/8})\bigl[\ell(A^{\rm rest}_x)-306x^{-1/8}-2x^{-3/4}\bigr]_+\).

The images in item 1 are even, those in items 2--3 odd, so the three
families are disjoint, and all lie in \((\sqrt x,x]\).

### 4.2 The functional inequalities

Adding items 1 and 2:
\[
g_A(t)\ \ge\ (1-\varepsilon_1(t))\,g_A(t/2)+\tfrac13(1-\varepsilon_2(t))\,g_A(3t/8)-\varepsilon_3(t),
\tag{4.1}
\]
with \(\varepsilon_1=2e^{-t/4}\), \(\varepsilon_2=\varepsilon'(e^t)\),
\(\varepsilon_3=2e^{-t/2}+e^{-3t/8}\), all tending to \(0\). Adding
item 3 as well, and noting that the coefficient of the *actual*
value \(g_A(3t/8)\) is
\(\tfrac13(1-\varepsilon_2)-\tfrac2{21}(1+2e^{-3t/16})\to\tfrac5{21}>0\):
\[
g_A(t)\ \ge\ (1-\varepsilon_1)\,g_A(t/2)+\bigl(\tfrac5{21}-\varepsilon_4\bigr)g_A(3t/8)+\bigl(\tfrac2{21}-\varepsilon_5\bigr)g_A(3t/4)-\varepsilon_6(t),
\tag{4.2}
\]
with \(\varepsilon_4,\varepsilon_5,\varepsilon_6\to 0\) (for \(t\) so
large that \(x^{3/8}\ge 10^6\); the bracket \([\cdot]_+\) may be
dropped because the right side of (4.2) is a lower bound for it).
Every coefficient of a \(g_A\)-value on the right is nonnegative for
large \(t\), so lower bounds for \(g_A\) at \(t/2\), \(3t/8\), \(3t/4\)
transfer.

### 4.3 The seed

**Lemma 4.1 (seed).** Every nonempty backward-closed \(A\) contains
an integer \(m\ge 3\), and for any such \(m\),
\[
g_A(t)\ \ge\ c_A:=\Bigl(1-\frac2{m^4}\Bigr)\Bigl(\frac{0.375}{m+1}-\frac1{(m+1)^2-1}\Bigr)>0
\qquad\text{for all}\ t\ge 4\log(m+1).
\]

*Proof.* If \(A\ni a\le 2\) then \(E(a)\subseteq A\) contains \(2\) or
\(4\), and \(E(2)\ni 4\), so \(A\ni 4\). Fix \(m\ge 3\) in \(A\) and
let \(S_1=E(m)\), \(S_{k+1}=\bigcup_{m''\in S_k}E(m'')\). Then
\(S_k\subseteq A\cap[m^{2^k},(m+1)^{2^k})\) and, by Lemma 2.1,
\(\ell(S_{k+1})\ge(1-2m^{-2^k})\ell(S_k)\), so
\(\ell(S_k)\ge\ell(S_1)\prod_{j\ge 1}(1-2m^{-2^j})\ge 0.75\,\ell(S_1)\ge\frac{0.375}{m+1}\)
for \(m\ge 3\). Let \(y\ge(m+1)^4\) and choose \(k\ge 2\) with
\((m+1)^{2^k}\le y<(m+1)^{2^{k+1}}\). Then
\(S_k\subseteq(y^{1/4},y]\) (as \(y<m^{2^{k+2}}\)). The members of
\(S_k\) above \(\sqrt y\) lie in \((\sqrt y,y]\); the members in
\((y^{1/4},\sqrt y-1]\) have their \(E\)-images in \((\sqrt y,y]\), with
log-mass at least \((1-2m^{-2^k})\) times their own; at most one
member lies in \((\sqrt y-1,\sqrt y]\), with \(1/n\le 1/((m+1)^2-1)\).
Hence \(g_A(\log y)\ge(1-2m^{-4})\bigl(\ell(S_k)-1/((m+1)^2-1)\bigr)\ge c_A\),
and \(c_A>0\) because \(0.375(m+1)\ge 1+0.375/(m+1)\) for \(m\ge 3\). \(\square\)

### 4.4 The theorem

Let \(\lambda^*\) and \(\lambda^{**}\) be the roots in \((0,1)\) of
\[
2^{-\lambda}+\tfrac13\bigl(\tfrac38\bigr)^{\lambda}=1,
\qquad
2^{-\lambda}+\tfrac5{21}\bigl(\tfrac38\bigr)^{\lambda}+\tfrac2{21}\bigl(\tfrac34\bigr)^{\lambda}=1 .
\]
Numerically \(\lambda^*=0.3774\ldots\) and \(\lambda^{**}=0.4050\ldots\).
(For comparison: the elementary sweep alone, without Proposition 3.4,
gives \(2^{-\lambda}+\tfrac2{21}(\tfrac34)^\lambda=1\), root \(0.138\ldots\);
perfect fiber equidistribution at this depth would give
\(2^{-\lambda}+\tfrac13(\tfrac34)^\lambda=1\), root \(0.4927\ldots\).)

**Theorem 4.2 (logarithmic density of a fate class).** Let
\(A\subseteq\mathbb N\) be nonempty and backward-closed, and let
\(0<\lambda<\lambda^{**}\). There are \(c>0\) and \(x_0\), depending on
\(A\) and \(\lambda\), such that
\[
\sum_{\substack{n\in A\\ n\le x}}\frac1n\ \ge\ c\,(\log x)^{\lambda}
\qquad\text{for all}\ x\ge x_0 .
\]
The same conclusion for \(\lambda<\lambda^*\) uses only Proposition 3.4
(no sweep lemma).

*Proof.* Set \(\zeta=2^{-\lambda}+\tfrac5{21}(\tfrac38)^\lambda+\tfrac2{21}(\tfrac34)^\lambda-1>0\).
By Lemma 4.1 and the decay of the \(\varepsilon_i\), choose \(t_1\)
with \(\tfrac38t_1\ge 4\log(m+1)\) such that for all \(t\ge t_1\)
\[
\varepsilon_1(t)2^{-\lambda}+\varepsilon_4(t)\bigl(\tfrac38\bigr)^\lambda+\varepsilon_5(t)\bigl(\tfrac34\bigr)^\lambda\le\tfrac\zeta3,
\qquad
\varepsilon_6(t)\le\tfrac{2\zeta}3\,c_A ,
\]
and all coefficients in (4.2) are nonnegative. Put \(K=c_At_1^{-\lambda}\).
Claim: \(g_A(t)\ge Kt^\lambda\) for all \(t\ge\tfrac38t_1\). For
\(t\in[\tfrac38t_1,t_1]\) this is Lemma 4.1 (\(Kt^\lambda\le c_A\)).
Suppose it holds on \([\tfrac38t_1,T]\) with \(T\ge t_1\) and let
\(t\in(T,\tfrac83T]\). Then \(t/2,\ 3t/8,\ 3t/4\in[\tfrac38t_1,T]\),
so by (4.2)
\[
g_A(t)\ \ge\ Kt^\lambda\Bigl[(1+\zeta)-\tfrac\zeta3\Bigr]-\varepsilon_6(t)
\ \ge\ Kt^\lambda\Bigl(1+\tfrac{2\zeta}3\Bigr)-\tfrac{2\zeta}3c_A\ \ge\ Kt^\lambda ,
\]
using \(Kt^\lambda\ge Kt_1^\lambda=c_A\). Induction on the intervals
\((\tfrac83)^NT\) covers all \(t\ge\tfrac38t_1\). Finally
\(L_A(x)\ge g_A(\log x)\). For \(\lambda<\lambda^*\) run the same
argument with (4.1). \(\square\)

**Corollary 4.3 (natural density, infinitely often).** For every
\(\lambda<\lambda^{**}\) there is \(c>0\) such that for every
\(X\ge x_0\) some \(y\in(\sqrt X,X]\) satisfies
\[
\#\bigl(A\cap(y/2,y]\bigr)\ \ge\ c\,y\,(\log y)^{\lambda-1}.
\]

*Proof.* \(\ell_A(\sqrt X,X]=g_A(\log X)\ge K(\log X)^\lambda\) is
spread over at most \(\tfrac12\log_2X+2\) dyadic blocks
\((y/2,y]\subseteq(\sqrt X,2X]\); one of them has
\(\ell_A(y/2,y]\ge K'(\log X)^{\lambda-1}\), hence
\(\#(A\cap(y/2,y])\ge\tfrac y2\,\ell_A(y/2,y]\ge\tfrac{K'}2\,y\,(2\log y)^{\lambda-1}\),
because \(\log X\le 2\log y\) and \(\lambda-1<0\). \(\square\)

### 4.5 Fate contagion

**Corollary 4.4 (contagion).** Let \(\varphi\) be a fate that is
realized by at least one start: the trivial cycle, a particular
nontrivial cycle \(C\), or divergence. Then the class
\(\{n:\mathrm{fate}(n)=\varphi\}\) satisfies Theorem 4.2 and
Corollary 4.3. In particular:

1. \(\displaystyle\sum_{n\in R,\ n\le x}\frac1n\gg(\log x)^{\lambda}\)
   for every \(\lambda<\lambda^{**}\).
2. If some start does not reach \(1\), then
   \(\displaystyle\sum_{n\notin R,\ n\le x}\frac1n\gg(\log x)^{\lambda}\),
   and on infinitely many dyadic blocks the failures have natural
   density \(\gg(\log y)^{\lambda-1}\).
3. If a nontrivial cycle exists, the set of starts that enter it has
   the same lower bounds; if a divergent orbit exists, so does the set
   of divergent starts.

*Proof.* Lemma 1.1 and Theorem 4.2. \(\square\)

**Corollary 4.5 (the conjecture as an almost-all statement).** Fix
any \(N_0\) with \([1,N_0]\subseteq R\) (Lean: \(N_0=260\),
`reachesOne_of_lt_two_hundred_sixty_one`; certified computation:
\(N_0=3.5\cdot 10^8\)). The following are equivalent.

1. Every \(n\ge 1\) reaches \(1\).
2. For some \(\lambda<\lambda^{**}\),
   \(\displaystyle\sum_{n\le x,\ n\notin R}\frac1n=o\bigl((\log x)^{\lambda}\bigr)\).
3. For some \(\lambda<\lambda^{**}\), the starts \(n\le x\) whose orbit
   never enters \([1,N_0]\) have logarithmic count
   \(o\bigl((\log x)^{\lambda}\bigr)\).

*Proof.* (1)\(\Rightarrow\)(3): the set is empty. (3)\(\Rightarrow\)(2):
an orbit that enters \([1,N_0]\) reaches \(1\), so \(F\) is contained
in the set of (3). (2)\(\Rightarrow\)(1): \(F\) is backward-closed;
if it were nonempty, Theorem 4.2 would contradict (2). \(\square\)

In natural-density language, (3) asks that all but
\(O\bigl(x(\log x)^{-0.6}\bigr)\) starts below \(x\) eventually fall
below \(3.5\cdot 10^8\) — a Tao-type "almost all orbits attain a
bounded value" statement with a mild logarithmic rate. For the
Collatz map, Tao's theorem gives almost-bounded values in
logarithmic density without a usable rate, and even a strong rate
would not imply the Collatz conjecture, because the preimage tree of
a hypothetical failure is thin (Krasikov--Lagarias: at least
\(x^{0.84}\), and nothing forces more). For the Juggler map the
implication is a theorem.

## 5. Remarks, limits, and what is not claimed

**5.1 The certified subset of \(R\).** Let \(\mathcal C\) be the
closure of the Lean-verified seed \([1,260]\) under the productions
\(E\) and \(OE\). Every member of \(\mathcal C\) reaches \(1\)
(Lean: `even_block_mem`, `oe_fiber_mem` with
`reachesOne_backwardClosed`). Computed exactly up to \(10^9\)
(`certified_closure`): \(\mathcal C\) has density between \(0.45\) and
\(0.49\) on every dyadic block \((2^k,2^{k+1}]\) with
\(16\le k\le 29\), against \(0.25\) for the \(E\)-only closure. At
\(x=10^9\) the log-mass of \(\mathcal C\cap(\sqrt x,x]\) splits as
\(3.785\) (even) \(+1.547\) (odd), and the realised recursion
coefficients are \(0.9998\) for \(E\) (theory \(1\)) and \(0.3332\)
for \(OE\) against the source mass \(\ell_{\mathcal C}(x^{3/8},x^{3/4}]\)
(heuristic \(\tfrac13\); proved \(\tfrac13\) on \(E\)-blocks and
\(\tfrac2{21}\) elsewhere). The recursion is exactly what the closure
does; only the fiber constants are conservative.

**5.2 Why the exponent is not \(1\).** Positive logarithmic density
(\(\lambda=1\)) would need the productions to account for all of the
mass: in the ideal recursion
\(g(t)\ge g(t/2)+\sum_w c_w\,g(e_wt)\) over descent certificates \(w\)
with ideal exponents \(e_w\), linear growth requires
\(\tfrac12+\sum_wc_we_w=\tfrac12\), i.e. the certificate classes must
carry the full odd mass. Depth two (\(E\), \(OE\)) carries \(\tfrac34\)
of the integers and gives at best \(\lambda=0.4927\); Paper B's
depth-five classes (\(\tfrac78\)) would give \(\approx 0.75\); the
\(OO\)-rooted classes send their mass to *larger* scales
(\(x^{3/2}\)), which a downward induction cannot use until a later
descent certificate returns it. Positive density of \(R\) is therefore
as hard as the full almost-all-descent statement with a rate, and is
not claimed. Deeper certificates would require the nested-floor
parities on the sub-dyadic intervals \(I(m')\) (length \(x^{5/8}\)),
which is Paper B's machinery on shorter intervals; the OE fiber is the
one place where the nesting is transparent
(\(\lfloor\sqrt{\lfloor n^{3/2}\rfloor}\rfloor=\lfloor n^{3/4}\rfloor\)),
which is why depth two closes by elementary means.

**5.3 Pointwise natural density.** Theorem 4.2 is a logarithmic
statement and Corollary 4.3 holds infinitely often, not for every
\(x\). A pointwise bound \(\#(A\cap[1,x])\gg x(\log x)^{\lambda-1}\)
cannot be inducted through fixed-ratio intervals — the \(E\)-preimage
of a ratio-\(r\) interval has ratio \(\sqrt r\) — and for a
backward-closed set generated by a single seed it is false: the
\(E\)-tree of one integer is lacunary at the dyadic scale. For
\(R\) itself the \(E\)-tree of the full interval \([1,N_0]\) is
uniform on dyadic blocks as long as \(2^k\ll N_0\) at level \(k\),
i.e. for \(\log x\ll N_0\log N_0\), which covers every \(x\) below
\(10^{10^9}\); the density there is at least
\(2^{-k}\approx\log N_0/(2\log x)\) from \(E\) alone, and the
closure numerics of 5.1 show what \(OE\) adds. The asymptotic
statement is the logarithmic one.

**5.4 What is excluded.** Nothing. Corollary 4.4 does not say that a
cycle or a divergent orbit is impossible; it says that either would
be common. Corollary 4.5 does not prove the conjecture; it converts
it into an almost-all statement whose Collatz analogue is Tao's
theorem strengthened to a bounded target with a rate. No estimate in
this laboratory or in Paper B controls the orbits of almost all
starts down to a fixed bound.

**5.5 Sharpness of the constants.** The census
(`fiber_census` in `summary.json`; \(m<10^5\), spot ranges at
\(10^6\) and \(10^7\)) finds mean \(G_m/H_m=0.5000\), minimum on good
fibers \(0.328\) at \(m=1\,003\,635\) (\(\alpha_m\approx\tfrac13\), the
three-cluster case), and every fiber with \(G_m/H_m<\tfrac17\) flagged
bad by the \(\alpha\)-criterion. The truth on good fibers is
\(\approx\tfrac13\); the proof gives \(\tfrac17\). Replacing \(\tfrac17\)
by \(\tfrac13\) would move \(\lambda^{**}\) from \(0.405\) to
\(0.448\); the ceiling of the depth-two method is \(0.4927\).

## Appendix. Lean names

| Statement | Lean (`FateContagion.lean`) |
|---|---|
| backward closure | `BackwardClosed`, `backwardClosed_iterate` |
| Lemma 1.1, fate classes closed | `reachesOne_backwardClosed`, `not_reachesOne_backwardClosed`, `ancestor_backwardClosed`, `escapes_backwardClosed`, `reachesOne_floorPower`, `escapes_floorPower` |
| Lemma 1.1, trichotomy | `Periodic`, `periodic_of_repeat`, `fate_trichotomy` (from `cycles_or_escapes`) |
| Lemma 1.1, exclusion | `reachesOne_bounded`, `reachesOne_not_escapes`, `cycle_basin_bounded`, `cycle_basin_not_escapes`, `reachesOne_not_cycle_basin`, `periodic_iterate_mod` |
| Lemma 2.1 | `floorPower_even_block`, `even_block_mem`, `even_block_card` |
| Lemma 2.2 | `sqrt_sqrt_eq_iff`, `floorPower_oe_fiber`, `oe_fiber_mem`, `oe_fiber_disjoint` |
| Lemmas 3.1--3.3, Proposition 3.4, Theorem 4.2 | human proof; censuses in `data/research/juggler/fate_contagion/summary.json` |
