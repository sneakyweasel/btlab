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
(Section 7 raises the exponent to \(\lambda^{***}=0.4922\ldots\) by
localizing Paper B's triple parity discrepancy to sub-dyadic intervals
and adding the \(OOEEE\) production; every statement below holds with
\(\lambda^{***}\) in place of \(\lambda^{**}\).)
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

*Naming.* The three fates are the three Moirai: **Atropos** cuts the
thread — the orbit is absorbed at \(1\) (the class \(R\));
**Lachesis** measures out an allotted length — the orbit is eventually
periodic on a nontrivial cycle (the basins \(B(C)\)); **Clotho** spins
without end — the orbit is unbounded (the class \(D\)). Only Atropos
is known to act; contagion says that whichever sister acts at all acts
on a set of positive \((\log x)^{\lambda}\)-mass.

*Sequel.* The Tao-type reformulation that Corollary 4.5 suggests is
worked out in
[juggler_tao_reduction_note.md](juggler_tao_reduction_note.md): a
Tao-type almost-all theorem with the bounded target \([1,N_0]\) and
rate \((\log y)^{-e}\), \(e>1-\lambda^{**}\), implies the conjecture,
and such a theorem follows from parity equidistribution at depth
\(O(\log\log y)\) because the Juggler descent is by powers.

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

## 6. The termination problem after contagion: an exact map

This section records what the fate-contagion viewpoint says the
termination problem *is*, exactly, and where Paper A and Paper B sit
relative to it. Everything here is either a Lean-verified identity, a
consequence of Sections 2–5, or an explicitly labelled open statement.

### 6.1 Odd generation

Write \(S=\{\lfloor m^{3/2}\rfloor:\ m\ \text{odd}\}\) for the image
of the odd integers.

**Theorem 6.1 (odd generation; Lean).** Let \(A\) be forward- and
backward-closed with \(1\notin A\). Then:

1. every \(n\in A\) descends by even steps only to an odd member
   \(m\ge 3\) of \(A\) (`exists_odd_ancestor_ge_three`);
2. for odd \(n\), \(n\in A\iff\lfloor n^{3/2}\rfloor\in A\)
   (`odd_mem_iff`), so the odd members of \(A\) are exactly the odd
   preimages of \(A\cap S\);
3. \(A\ne\emptyset\iff A\cap S\ne\emptyset\), i.e. \(A\) contains
   the image of some odd \(m\ge 3\) (`nonempty_iff_odd_image_mem`).

Applied to the failure set \(F\): **every positive integer reaches
\(1\) iff no image \(\lfloor m^{3/2}\rfloor\) of an odd \(m\) fails to
reach \(1\)** — and \(F\) is the \(E\)-forest over the odd preimages
of \(F\cap S\). The whole class is generated by the sparse set
\(F\cap S\) (the image set \(S\) has density \(\asymp z^{-1/3}\) at
scale \(z\)).

### 6.2 The exact first-letter decomposition and the free term

Let \(A\) be forward- and backward-closed. On \((\sqrt x,x]\) its
members split by first letters into three exact pieces:

- the **even** members, \(=\bigsqcup_{m\in A}E(m)\cap(\sqrt x,x]\),
  of log-mass \(\ell_A(x^{1/4},\sqrt x]+O(x^{-1/4})\) (Lemma 2.1);
- the **\(OE\)-type** odd members (\(\lfloor n^{3/2}\rfloor\) even),
  \(=\bigsqcup_{m\in A}\{n\in\Phi(m):\lfloor n^{3/2}\rfloor\ \text{even}\}\)
  (Lemma 2.2), of log-mass between \(\tfrac2{21}\) and \(\tfrac47\)
  of \(\ell_A(x^{3/8},x^{3/4}]\) on good fibers (two-sided sweep,
  Lemma 3.2) and exactly \(\tfrac13(1+o(1))\) of it on \(E\)-blocks
  (Proposition 3.4);
- the **\(OO\)-type** odd members (\(\lfloor n^{3/2}\rfloor\) odd),
  \(=\) the odd preimages of \(A\cap S_{\rm odd}\cap(x^{3/4},x^{3/2}]\),
  of log-mass \(\sum_{m\in A\cap S_{\rm odd}}1/n(m)\), where \(n(m)\)
  is the unique odd preimage.

In log-density form, with \(\varphi_A(t)=\ell_A(e^{t/2},e^t]/(t/2)\)
and \(\psi_A(t)\) the log-weighted fraction of \(OO\)-type odd
\(n\in(\sqrt x,x]\) whose image lies in \(A\):
\[
\varphi_A(t)=\tfrac12\varphi_A(t/2)+\tfrac14\,\varphi^{\rm fib}_A(3t/4)+\tfrac14\,\psi_A(t)+O(e^{-t/4}/t),
\tag{6.1}
\]
where \(\varphi^{\rm fib}_A\) is the fiber-weighted density (equal to
\(\varphi_A\) on \(E\)-blocks). For \(A=\mathbb N\) every term is
\(1\). For \(A=F\) the boundary condition is \(\varphi_F(t)=0\) for
\(t\le\log N_0\). **The single free term is \(\psi_F\)**: if
\(\psi_F(t)\le\varphi_F(3t/2)+o(1)\) — the failures are *not
over-represented* among the odd images \(S_{\rm odd}\) — then (6.1)
is the harmonic equation of a random walk on \(\log t\) with steps
\(\log\tfrac12,\ \log\tfrac34,\ \log\tfrac32\) of probabilities
\(\tfrac12,\tfrac14,\tfrac14\), whose drift \(-0.317\) is negative,
and the boundary condition forces \(\varphi_F\equiv 0\): the
conjecture. Conversely \(\psi_F\equiv 1\) (every \(OO\)-type odd
number above the floor fails) is consistent with (6.1). So:

> **The Juggler conjecture is equivalent to the \(S\)-fairness of the
> failure set: \(F\ne\emptyset\) forces the failures to be
> over-represented among \(\{\lfloor m^{3/2}\rfloor:m\ \text{odd}\}\)
> at some scales.**

*What the free term is (sequel note §11).* For odd \(n\), \(n\in F\)
iff its orbit never enters \([1,N_0]\), so \(\psi_F(t)\) is the
infinite-depth *live mass* of the depth-two cylinder \(OO\) at scale
\(e^t\): \(\psi_F(t)=\lim_d\mathbb P^{\log}(\tau>d\mid OO)\). The
Tao-type hypotheses of the sequel note bound exactly this quantity
(\(\psi_F(t)\ll(t/\log N_0)^{-e}\) under any of them). The two halves
of (6.1) are the two theorems of this note: \(\psi\ge0\) is the ideal
depth-two contagion recursion (lower bound, \(\lambda_{\rm ideal}=0.4927\)),
\(\psi\le1\) the upper recursion for the failure density, whose
homogeneous decay exponent \(1-\lambda_{\rm ideal}=0.5073\) is the
Tao-type rate threshold up to the fiber-constant gap. The exact map
therefore cannot replace contagion (a small free term gives
\(\varphi_F\ll t^{-0.507}\), not \(\varphi_F\equiv0\)); the frontier is
one quantity, the live mass of odd-heavy words at depth
\(\asymp\log\log x\).

A quantitative form (the amount of bias forced by contagion) is
vacuous with the present constants: contagion's constant for \(F\) is
\(\asymp 1/\min F\le 1/N_0\), below the boundary slop of (6.1); the
block-aligned identity \(W_A((M+1)^2-1)=W_A(M)+W_{A,\rm odd}((M+1)^2-1)\)
with the invariant weight \(w\) (each \(E\)-block carries exactly the
weight of its root) removes the slop at \(E\)-steps but not at
\(O\)-steps. We record the qualitative statement only.

*Numerical illustration.* The certified closure \(\mathcal C\) of
\([1,260]\) under \(E\) and \(OE\) is a backward-closed set whose
\(OO\)-production was deliberately omitted. Its first-letter
decomposition (`first_letter_decomposition` in `summary.json`) shows
the mechanism: the \(OE\)-type share of members equals the fair share
(\(0.7288\) vs \(0.7305\) at \(x=10^6\); \(0.7997\) vs \(0.8036\) at
\(10^5\); \(0.9009\) vs \(0.9031\) at \(10^4\)) — fiber fairness holds
to three digits — while the \(OO\)-type share is \(0\) against a fair
share of \(0.30\): the free term is exactly the omitted production.

### 6.3 Where Paper A and Paper B sit

*Paper A* concerns the fate Lachesis from the inside: finance and the
walk charge bound the *states* of a hypothetical cycle
(\(\min>3.5\cdot 10^8\), period \(\ge 780239\)). Contagion concerns
the basin: if the cycle exists, its basin is a two-way closed class
with the cycle's states as seeds and has log-count
\(\gg(\log x)^{0.405}\) (Corollary 4.4). The two do not meet: finance
constrains the seed, contagion the growth from the seed, and no
inequality bounds a basin from above. The floor-free gap transfer
(Theorem 4.10) and the finance table are exactly the internal
constraints; the basin's size is governed by the same free term
\(\psi\).

*Paper B* controls the descending branches of (6.1) — the fairness
of the landing distributions of \(E\), \(OE\) and, with its depth-4
and depth-5 theorems, of \(OOEE\), \(OOOEE\), \(OOEOE\) — on dyadic
blocks. Entering (6.1) with those deeper certificates needs them on
the unions of fibers over \(E\)-blocks of landing points, which are
intervals of length \(x^{23/32}\) at scale \(x\) (for \(OOEE\)). Paper
B's Theorem 4.4 is stated for dyadic blocks with error
\(P^{23/24+\varepsilon}\); its proof (Weyl differencing, exact
linearization, cell decomposition, second-derivative test) appears to
localize to sub-intervals of length \(Y\ge P^{1/2+\varepsilon}\) with
the *relative* saving \(P^{-1/24+\varepsilon}\), because every term of
the estimate scales with the interval length. **This is not
verified here.** If it holds, and likewise for Theorem 4.7, the
\(OOEE\) production enters the contagion recursion with coefficient
\(\tfrac19\) at argument \(\tfrac9{16}t\), and
\(2^{-\lambda}+\tfrac5{21}(\tfrac38)^\lambda+\tfrac2{21}(\tfrac34)^\lambda+\tfrac19(\tfrac9{16})^\lambda=1\)
gives \(\lambda^{**}\approx 0.527\), lowering the Tao-type rate
requirement of the sequel note from \(0.595\) to \(0.473\). Depth
five would add \(\tfrac2{27}\) at \(\tfrac{27}{32}t\). None of this
touches the free term: the ascending branch \(OO\) sends mass to
\(x^{3/2}\), and its return is the nested-floor parity at all depths
— the \(K_3\) wall (Paper B Conjecture 7.3 and its iterates).

### 6.4 What a proof must do

Every route in this laboratory — finance, walk charge, kernel
equidistribution, contagion — bounds a side of (6.1) that does not
contain \(\psi_F\). A proof of termination must show that a
\(J\)-invariant set cannot be over-represented among the odd images
\(S_{\rm odd}\): a per-set, all-depth parity statement. The three
conditional theorems of the sequel note
([juggler_tao_reduction_note.md](juggler_tao_reduction_note.md)) are
the honest boundary: parity equidistribution — or merely a one-sided
odd-share bound \(q<\log 2/\log 3\) — on cylinders of depth
\(O(\log\log y)\) implies the conjecture; the weakest form is the live
pressure / no-momentum hypothesis (sequel note §10), and the free term
\(\psi_F\) is the infinite-depth live mass it controls (sequel note
§11): one frontier statement, not two. Nothing unconditional is
claimed beyond Theorem 4.2 and Theorem 6.1.

## 7. Localizing Paper B: the \(OOEEE\) production and \(\lambda^{***}=0.4922\)

Section 6.3 asked whether Paper B's depth-\(\le 4\) theorems localize to
the sub-dyadic intervals that the contagion recursion needs. They do,
for the Weyl-differencing skeleton of Theorems 4.4 and 4.7: every
estimate in that proof scales with the length of the summation
interval, and the few that do not are tiny. This section records the
localized statement with its proof as a modification list, the
resulting production, and the improved exponent.

### 7.1 The localized triple parity discrepancy

Notation as in Paper B: for odd \(n\), \(m=\lfloor n^{3/2}\rfloor\),
\(v=\lfloor m^{3/2}\rfloor\), \(\psi_1=\psi(n^{3/2})\),
\(\psi_2=\psi(m^{3/2})\), \(\psi_3=\psi(v^{1/2})\), with
\(\psi(y)=(-1)^{\lfloor y\rfloor}\).

**Proposition 7.1 (Paper B Theorem 4.7 on sub-dyadic intervals).**
For every \(\varepsilon>0\) there is \(P_0\) such that for all
\(P\ge P_0\), every interval \(I\subseteq(P,2P]\) of length
\(Y\ge P^{1/2}\), and every \((a,b,c)\in\{0,1\}^3\setminus\{0\}\),
\[
\Bigl|\sum_{n\in I,\ n\ \mathrm{odd}}\psi_1^{a}\psi_2^{b}\psi_3^{c}\Bigr|
\ \le\ Y\,P^{-1/24+\varepsilon}.
\]

*Proof.* Run the seven steps of the proof of Paper B Theorem 4.4 (and
the passenger argument of Theorem 4.7) over \(I\) instead of
\((P,2P]\), with the same truncations \(J_1=J_2=J_3=P^{1/24}\),
\(H=P^{1/12}\), \(R=P^{1/4}\). Every displayed bound is of one of
two kinds: a bound proportional to the number of summands, which
becomes proportional to \(Y\); or a bound independent of the number
of summands, which is unchanged and is \(\le P^{7/16}\).

*Step 1 (wave expansion).* The majorant layers cost their constant
terms \(\le Y/(2(J+1))\le YP^{-1/24}\) and mode sums
\(\sum_{0<r\le 2J}(J+1)^{-1}|\sum_{n\in I}e(\tfrac r2n^{3/2})|\);
Lemma 3.3 on \(I\) gives each inner sum
\(\le 1.4\,r^{1/2}YP^{-1/4}+2P^{1/4}\), total
\(\le 2.4\,J^{1/2}YP^{-1/4}+2P^{1/4}\le 3YP^{-11/48}+2P^{1/4}\).

*Step 2 (linearization).* The phase change is \(\le\tfrac j4n^{-3/4}\)
per summand, hence \(\le 2jYP^{-3/4}\) in total; the passenger
\(\tfrac k2v^{1/2}\to\tfrac k2n^{9/8}\) (Lemma 4.6) costs
\(\le 5|k|YP^{-3/8}\).

*Step 3 (Weyl differencing).* For a sum of \(M=Y/2\) unimodular
terms and \(H\le M\), the classical inequality reads
\(|S|^2\le Y^2/(2H)+(2Y/H)\sum_{1\le h<H}|T_h|\), with \(T_h\) the
differenced sum over \(n,n+2h\in I\).

*Step 4 (differenced phase).* Exact identity, pointwise; discarding
the sawtooth term costs \(\le 7.1\,jhP^{-1/4}\) per summand, i.e.
\(\le 3.6\,jhYP^{-1/4}\).

*Step 5 (cells).* The level sets of \(\lfloor\delta\rfloor\) cut
\(I\) into at most \(1.5hYP^{-1/2}+2\) cells, all but the two end
cells of length in \([\tfrac23,0.95]P^{1/2}/h\). The Vaaler layer for
\(\kappa\) costs \(Y/(R+1)\le YP^{-1/4}\) plus mode sums bounded per
cell by Lemma 3.3 and summed: \(\le 5.2R^{1/2}YP^{-1/4}+3hYP^{-3/8}\le 6YP^{-1/8}\).
The exact shift device and the Abel summation per cell are unchanged.

*Step 6 (second-derivative test per cell).* For \(r=0\):
\(\sum_{\rm cells}(\ell_{\rm cell}\lambda^{1/2}+\lambda^{-1/2})
\le 0.83(jh)^{1/2}YP^{-3/8}+3.9(h/j)^{1/2}YP^{-1/8}+5.2(jh)^{-1/2}P^{3/8}\),
the last term from the two end cells. For \(r\ne 0\): the same
per-cell bounds with the mode curvature, summed against the
\(1/|r|\) weights, give \(\le 6YP^{-1/8}+13hYP^{-1/4}+7P^{1/4}\). All
sign-dominance checks are pointwise and unchanged.

*Step 7 (assembly).* \(|T_h|\le C\,YP^{-1/8}(1+h^{1/2})\log P+C'P^{3/8}\),
so
\(|S|^2\le Y^2/(2H)+(2Y/H)\sum_{h<H}\bigl(CYP^{-1/8}(1+h^{1/2})\log P+C'P^{3/8}\bigr)
\le Y^2P^{-1/12}\bigl(\tfrac12+3C\log P\bigr)+2C'YP^{3/8}\).
For \(Y\ge P^{1/2}\) the last term is \(\le 2C'Y^2P^{-1/8}\), and
\(|S|\ll Y P^{-1/24}\log^{1/2}P\). The mode weights contribute
\(O(\log^2P)\); the \(j=0\) sums are single smooth exponential sums on
\(I\) bounded by \(Yi^{1/2}P^{-1/4}+P^{1/4}\) (\(i\ne 0\)) or
\(Yk^{1/2}P^{-7/16}+k^{-1/2}P^{7/16}\) (\(i=0\)), both
\(\le YP^{-1/24}\) for \(Y\ge P^{1/2}\). \(\square\)

The threshold \(Y\ge P^{1/2}\) is where the two end cells
(\(P^{3/8}\)) and the pure passenger term (\(P^{7/16}\)) fall below
the main saving \(YP^{-1/24}\); nothing in the argument uses the
dyadic length except through the number of summands.

### 7.2 The \(OOEEE\) production on even blocks

For \(m'\ge 2\) let \(I(m')=[m'^{32/9},(m'+1)^{32/9})\), an interval
of length \((32/9)m'^{23/9}(1+O(1/m'))\) at scale
\(P=m'^{32/9}\): so \(|I(m')|\asymp P^{23/32}\ge P^{1/2}\).

**Proposition 7.2.** Let
\(\mathcal O(m')=\{n\ \text{odd}\in I(m'):\ \mathrm{word}_5(n)=OOEEE,\ J^5(n)=m'\}\).
Every \(n\in\mathcal O(m')\) has \(J^4(n)\in E(m')\), and
\[
|\mathcal O(m')|
=\tfrac1{16}\#\{n\ \text{odd}\in I(m')\}+O_\varepsilon\bigl(|I(m')|\,m'^{-4/27+\varepsilon}\bigr).
\]
Consequently, for a backward-closed \(A\) and \(m'\in A\),
\(\mathcal O(m')\subseteq A\), with log-mass at least
\(\frac1{9m'}\bigl(1-O(m'^{-4/27+\varepsilon})\bigr)\).

*Proof.* Along \(OOEEE\) the states \(J^0(n),\dots,J^4(n)\) are
\(n\) (odd), \(m\) (odd), \(v\) (even), \(\lfloor v^{1/2}\rfloor\)
(even), \(\lfloor v^{1/4}\rfloor\) (even), and
\(J^5(n)=\lfloor\sqrt{J^4(n)}\rfloor\). If \(J^5(n)=m'\) then
\(J^4(n)\in[m'^2,(m'+1)^2)\) and is even: \(J^4(n)\in E(m')\), and
membership in \(A\) follows from Lemma 2.1 and backward closure. For
the count, the transparent nesting gives
\(\lfloor v^{1/4}\rfloor=\lfloor n^{9/16}\rfloor\) except when
\(\{n^{9/16}\}<n^{-15/16}\) (Lemma 4.6 pattern:
\(v^{1/4}=n^{9/16}-D''\), \(0\le D''\le n^{-15/16}\)); off that
exceptional set, \(n\in I(m')\) forces
\(\lfloor n^{9/16}\rfloor\in[m'^2,(m'+1)^2)\), hence \(J^5(n)=m'\)
automatically, so \(|\mathcal O(m')|\) differs from
\(\#\{n\ \text{odd}\in I(m'):\mathrm{word}_5(n)=OOEEE\}\) by at most
the size of the exceptional set, which is \(\ll YP^{-1/24}+P^{7/16}\)
(Erdős–Turán for \(\{n^{9/16}\}\) at resolution \(P^{-15/16}\), with
the Kusmin–Landau bounds below).
The indicator of \(OOEEE\) on odd \(n\) is
\(\tfrac1{16}(1-\psi_1)(1+\psi_2)(1+\psi_3)(1+\psi_4)\) with
\(\psi_4=\psi(v^{1/4})\). Expanding, the main term is
\(\tfrac1{16}|I_{\rm odd}|\) and the fifteen sign sums split into
those without \(\psi_4\) — Proposition 7.1 with \(Y=|I(m')|\ge P^{1/2}\)
— and those with \(\psi_4\). For the latter, replace \(v^{1/4}\) by
\(n^{9/16}\) (cost \(\le 2\pi\sum_{n\in I}D''\ll YP^{-15/16}\)) and
Vaaler-expand \(\psi(n^{9/16})\) at truncation \(J_4=P^{1/24}\): its
modes \(e(\tfrac\ell2n^{9/16})\) have second derivative
\(\ll\ell P^{-23/16}\), far below every curvature retained in Steps 5–6
of Proposition 7.1 and below the \(n^{9/8}\) passenger, so they ride
along unchanged; the pure sums \(\sum_{n\in I}e(\tfrac\ell2n^{9/16})\)
have monotone derivative in \((0,\tfrac12)\) and are
\(\ll P^{7/16}/\ell\) by the Kusmin–Landau test; the majorant costs
\(Y/J_4+P^{7/16}\log J_4\). Every error is
\(\ll YP^{-1/24+\varepsilon}=Y m'^{-4/27+\varepsilon}\). The log-mass
bound follows from \(1/n\ge(m'+1)^{-32/9}\) and
\(\tfrac1{16}\cdot\tfrac12\cdot\tfrac{32}9m'^{23/9}=\tfrac19m'^{23/9}\). \(\square\)

### 7.3 The improved exponent

**Theorem 7.3.** Theorem 4.2 holds for every
\(\lambda<\lambda^{***}=0.4922\ldots\), the root of
\[
2^{-\lambda}+\tfrac5{21}\bigl(\tfrac38\bigr)^{\lambda}+\tfrac2{21}\bigl(\tfrac34\bigr)^{\lambda}+\tfrac19\bigl(\tfrac9{32}\bigr)^{\lambda}=1 .
\]

*Proof.* Add to the three families of §4.1 a fourth: for
\(m'\in A\cap(x^{9/64},x^{9/32}-1]\), the \(OOEEE\)-starts of
\(I(m')\subseteq(\sqrt x,x]\). They are odd with odd \(\lfloor n^{3/2}\rfloor\),
hence disjoint from the even members and from the \(OE\)-type
members of the first three families, and distinct \(m'\) give
disjoint \(I(m')\). By Proposition 7.2 their log-mass is at least
\(\tfrac19(1-\varepsilon_7(x))\bigl(g_A(9t/32)-2x^{-9/32}\bigr)\), and (4.2)
gains the term \((\tfrac19-\varepsilon_7)g_A(9t/32)\). The induction of
§4.4 runs verbatim with the new root. \(\square\)

Downstream: the rate requirement of the sequel note becomes
\(e>1-\lambda^{***}=0.5077\ldots\); the least depth constants are
\(C=19\) for the fair Chernoff bound (\(e(19)=0.527\)), and in the
biased-split form \(C(0.5)=19\), \(C(0.55)=41\), \(C(0.60)=223\),
\(C(0.62)=1587\). The depth-two ceiling of the method is \(0.4927\)
(perfect fiber equidistribution *without* deeper certificates); the
\(OOEEE\) production has carried the elementary exponent from
\(0.405\) to within \(0.0005\) of it by a different route. Further
gains would come from \(OOOEE\) and \(OOEOE\) on even blocks
(Paper B Theorem 6.3 through the kernel theorem — its localization is
not examined here) and from sharper fiber constants.

*What is unchanged.* Proposition 7.1 is a statement about consecutive
odd starts in an interval; it says nothing about the odd images
\(S_{\rm odd}\) of §6, and the free term \(\psi_F\) of (6.1) is
untouched. The improvement is quantitative.

### 7.4 The kernel theorem: assessment, not a proof

The next two productions on even blocks would be \(OOOEE\) and
\(OOEOE\) (Paper B Theorem 6.1, the \(OOO*\) splits), each with
coefficient \((1/32)/(27/32)=1/27\) at the root scale \(27t/64\).
Their recursion root is \(\lambda=0.5561\ldots\), the rate threshold
would drop to \(0.4439\), and the least depth constants to \(C=18\)
(fair and \(q=\tfrac12\)) and \(C(0.55)=38\)
(`hypothetical_kernel_localized` in the probe). Theorem 6.1 rests on
the kernel theorem (Paper B Theorem 5.3, \(K_c(P)\ll P^{1-1/96+\varepsilon}\)),
whose proof is a double Weyl differencing (\(H_1=P^{1/48}\),
\(H_2=P^{1/24}\)) over an exact carry-branch decomposition, with the
doubly differenced phase split by a master identity into four
bounded pieces, each expanded by Lemma 3.7 on frozen windows and
estimated per window by Lemmas 3.3, 3.8, 3.9 (Steps 1–6, some 430
lines). We read the proof for the same question as in
Proposition 7.1 — does every displayed cost scale with the number
of summands or stay below the target? — and found the same
architecture: the additive costs are per-point (flat term
\(8(1+|B|)/T\), majorant \(1/(J+1)\), \(M_1\) deletion
\(2.7kh_1h_2P^{-7/8}\), window residuals \(6.3P^{-1/8}\)) times the
number of summands, or per-window absolute costs (\(M^{-1/2}\),
\((P/M)^{1/3}\le P^{3/8}\), \(\lambda_a^{-1/2}\le P^{1/16}\)) times
window counts that are themselves proportional to the length plus
\(O(1)\); the leading term \(\sum_w|I_w|M^{1/2}\le2.5(k|j|)^{1/2}P^{15/16}\)
is length times \(\lambda_a^{1/2}\) and scales. On an interval
\(I\subseteq(P,2P]\) of length \(Y\) the differencing gives
\(|K_c(I)|^2\le2Y^2/H_1+(4Y/H_1)\sum|T_1|\), and the balance
\(|T_2|\ll YP^{-1/24+\varepsilon}\Rightarrow|K_c(I)|\ll YP^{-1/96+\varepsilon}\)
needs every absolute leftover below \(YP^{-1/24}=P^{0.677}\) at
\(Y=P^{23/32}\); the block proof's absolute terms are at most
\(P^{7/16}\). So localization to \(Y\ge P^{23/32}\) is plausible and
the check is mechanical. It is **not done here**: it requires
re-deriving each of the roughly forty displayed estimates of
Steps 3–5 with \(Y\) in place of \(P\) where it belongs, and the
resonant, collision-band and anchor-class pieces have window
hypotheses (Lemma 5.2's decorations) that must be re-verified on
partial windows. The gain is one unit of \(C\) and \(0.064\) in the
exponent; the free term \(\psi_F\) is untouched either way. Decision:
PARK, with the precise falsifier "an absolute cost in Steps 3–5 of
Paper B §5 exceeding \(P^{0.677}\)".

## 8. What the certified floor and the period bound say here

The laboratory's two large computations enter this note in three
places; none is a threshold, and it is worth saying exactly why.

*The floor \(N_0=3.5\cdot10^8\) stratifies the failure set.* By
backward closure and Theorem 6.1, if \(F=\mathbb N_{\ge1}\setminus R\)
is nonempty then: \(\min F\) is odd with odd image (an \(OO\)-start,
descent-free, exactly as the minimum of a cycle in Paper A);
every odd failure with even image exceeds \(N_0^{4/3}=2.4\cdot10^{11}\)
(its image's square root is a smaller failure); every even failure
exceeds \(N_0^{2}=1.2\cdot10^{17}\); and every failure that is an odd
image exceeds \(N_0^{3/2}=6.5\cdot10^{12}\) (its odd preimage is a
smaller failure), so \(F\cap S\subseteq(6.5\cdot10^{12},\infty)\). In
the Tao-type reduction the floor enters only through
\(L(y)=\log_2(\log 2y/\log N_0)\): against the Lean floor \(260\) it
lowers \(L\) by \(\log_2(19.67/5.56)=1.82\), i.e. the required depth
by \(35\)–\(38\) letters at every scale. That is all the floor does
for the asymptotics.

*The floor makes the aggregate hypothesis testable.* Because every
\(n\le N_0\) reaches \(1\), the statistic "\(J^t(n)\le N_0\) for some
\(t\le d\)" is a finite computation on exact big integers, and its
complement is exactly the bad set of the sequel note's Theorem B. The
census there (\(y=10^{12}\) to \(10^{50}\), depth \(40\)) finds the
survival fraction equal to the odd-start fair-coin value within
\(3\%\) for \(d\ge10\). The aggregate odd share along surviving
prefixes — which is what \(\mathrm H_q(C,A)\) is about — is
\(\tfrac12\) in every tested regime. This is the strongest evidence
the laboratory has that the hypothesis is true in aggregate; it is no
evidence at all about individual cylinders, which is where a proof
must work.

*The period bound places cycles at the critical share.* A cycle of
period \(L\) with \(o\) odd states has \(3^{o}/2^{L}=1+\Lambda\) with
\(\Lambda\) tiny (Paper A), so its word — an infinite bad word in the
sense of §2 of the sequel note — has odd share
\(o/L=\log 2/\log 3+O(\Lambda/L)\): exactly the critical share
\(q^{*}=0.6309\) of the biased-split hypothesis, at which the exponent
walk has zero drift. The surviving periods (\(176251\), \(301994\),
\(478245\), \(780239\)) are denominators of convergents and
semiconvergents of \(q^*\) (\(111202/176251\), \(190537/301994\),
and their mediants), because a periodic bad word must realize \(q^*\)
to within \(O(\Lambda/L)\) and Paper A's finance forces \(\Lambda\)
small enough that only those denominators survive. So the
finance/walk-charge program and
the biased-split hypothesis are two views of one boundary: cycles
must sit *on* the critical share, the Tao-type hypothesis asks that
no cylinder be pushed *toward* it, and \(L\ge780239\) at
\(n\ge3.5\cdot10^8\) is the statement that the boundary carries no
short periodic word below that floor. A cycle's basin is nonetheless
consistent with \(\mathrm H(C,A)\) at every finite scale — its
cylinders carry one state each, far below their fair share
\(y/2^{d}\) — which is why the conditional theorem must pass
through contagion (the basin's \((\log x)^{\lambda}\) log-count
against the bad set's \((\log x)^{1-e}\)). The exponent gap that
closes the argument at \(C=19\) is \(e(19)-0.5078=0.5269-0.5078=0.019\);
it is a choice, not a coincidence — \(C=25\) gives \(0.81\), \(C=30\)
gives \(1.05\) — but the depth \(C\log_2\log y\) is the price.

## Appendix. Lean names

| Statement | Lean (`FateContagion.lean`) |
|---|---|
| backward closure | `BackwardClosed`, `backwardClosed_iterate` |
| Lemma 1.1, fate classes closed | `reachesOne_backwardClosed`, `not_reachesOne_backwardClosed`, `ancestor_backwardClosed`, `escapes_backwardClosed`, `reachesOne_floorPower`, `escapes_floorPower` |
| Lemma 1.1, trichotomy | `Periodic`, `periodic_of_repeat`, `fate_trichotomy` (from `cycles_or_escapes`) |
| Lemma 1.1, exclusion | `reachesOne_bounded`, `reachesOne_not_escapes`, `cycle_basin_bounded`, `cycle_basin_not_escapes`, `reachesOne_not_cycle_basin`, `periodic_iterate_mod` |
| Lemma 2.1 | `floorPower_even_block`, `even_block_mem`, `even_block_card` |
| Lemma 2.2 | `sqrt_sqrt_eq_iff`, `floorPower_oe_fiber`, `oe_fiber_mem`, `oe_fiber_disjoint` |
| Theorem 6.1 (odd generation) | `ForwardClosed`, `reachesOne_forwardClosed`, `not_reachesOne_forwardClosed`, `escapes_forwardClosed`, `mem_iff_floorPower_mem`, `exists_odd_ancestor`, `exists_odd_ancestor_ge_three`, `nonempty_iff_odd_image_mem`, `odd_mem_iff` |
| envelope descent into the floor (sequel note) | `iterate_le_of_envelope`, `mem_of_envelope_floor`, `reachesOne_of_itinerary_envelope` |
| Lemmas 3.1--3.3, Proposition 3.4, Theorem 4.2 | human proof; censuses in `data/research/juggler/fate_contagion/summary.json` |
