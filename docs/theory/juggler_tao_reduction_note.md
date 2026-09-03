---
title: "The Juggler conjecture as an almost-all statement: a Tao-type reduction at depth O(log log y)"
author: Philippe Cochin
date: 3 September 2026
subtitle: Laboratory note. Conditional theorems; the hypothesis is a conjecture. Not a termination theorem.
---

## 0. The question and the answer

Fate contagion ([juggler_fate_contagion_note.md](juggler_fate_contagion_note.md),
Corollary 4.5) turned the Juggler conjecture into an almost-all
statement: every start reaches \(1\) **iff** the starts whose orbit
never enters a certified interval \([1,N_0]\) have logarithmic count
\(o((\log x)^{\lambda})\) for some \(\lambda<\lambda^{**}=0.4480\ldots\).
The question left open was whether a Tao-type theorem — "almost all
orbits attain almost bounded values" — with the *bounded* target
\([1,N_0]\) and the rate \((\log x)^{-0.6}\) is available for the
Juggler map.

The answer has two parts.

1. **Unconditionally, no such theorem is available**: by Corollary 4.5
   it *is* the Juggler conjecture. Nothing in the laboratory or in
   Paper B proves it.
2. **Conditionally, the required Tao-type statement follows from parity
   equidistribution at depth \(O(\log\log y)\)** (Theorem B below): if
   no cylinder of depth \(d(y)=\lceil C\log_2(\log 2y/\log N_0)\rceil\)
   is over-represented among odd starts in \((y,2y]\) by more than a
   vanishing relative error, then all but \(O(y(\log y)^{-e(C)})\)
   of those starts enter \([1,N_0]\) within \(d(y)\) steps, with
   \(e(21)=0.621>1-\lambda^{**}\). Contagion then closes the loop
   (Theorem A): **the Juggler conjecture follows from the
   log-log-depth cylinder bound** (Corollary C).

The mechanism is specific to the Juggler map. Its descent is by
*powers* — one contracting certificate sends \(n\) to
\(n^{e}\), \(e<1\) — so the exponent walk has to travel only
\(\log_2\log y\) units to bring a start of size \(y\) below a fixed
\(N_0\), and the parity word needed is \(O(\log\log y)\) letters long,
far inside the range where cylinders are large (\(y/2^{d}\gg 1\)).
For the Collatz map the descent is by constant factors, the walk
needs \(\Theta(\log y)\) steps, cylinders of that depth have single
elements, and Tao's renewal machinery with a *growing* target
\(f(N)\to\infty\) is forced; moreover, thin Collatz preimage trees
(Krasikov–Lagarias, \(x^{0.84}\)) mean that even a bounded-target
almost-all theorem would not imply the Collatz conjecture. For the
Juggler map both obstacles disappear: one-shot Terras counting at
depth \(O(\log\log y)\) reaches the bounded target, and contagion
converts the almost-all statement into the full conjecture.

What this note does **not** do: it does not prove the hypothesis.
Paper B proves parity equidistribution to depth four (with power
savings on dyadic blocks) and two depth-five words; the hypothesis
here asks for depth \(\to\infty\) like \(\log\log y\). Section 10
identifies the weakest form the argument can use — a single
exponential moment of the odd count on *live* starts (the "pressure"
form, Theorem B‴) — and shows that it is insensitive to any
\(o(\log\log y)\) initial depths and tolerates tower cylinders
\(O^t\) biased up to odd share \(0.84\):
the obstruction is the bulk behaviour of typical odd-heavy parity
words at depth \(\asymp\log\log y\), not the \(K_3\) split, and no
bounded-depth cylinder statement can close the reduction. The
reduction shows what stands behind that wall: not merely density-one
descent (Paper B, Proposition 7.1), but the conjecture itself.

Lean: the exact envelope-descent step is
`iterate_le_of_envelope`, `mem_of_envelope_floor`,
`reachesOne_of_itinerary_envelope` in `FateContagion.lean`. The
Chernoff count and the assembly are human proofs; the constants are
computed in `research.juggler_sequence.tao_reduction`.

## 1. Notation

\(J\) is the Juggler map, \(R\) the set of starts that reach \(1\),
\(F=\mathbb N\setminus R\). Fix \(N_0\ge 2\) with \([1,N_0]\subseteq R\)
(Lean: \(N_0=260\); certified computation: \(N_0=3.5\cdot 10^8\)).
For a word \(w\in\{O,E\}^d\) and \(t\le d\) write \(o_t(w)\) for the
number of odd letters among the first \(t\) and
\[
u_t(w)=o_t(w)\log_2 3-t
\]
for the exponent walk, so that the ideal image after \(t\) letters
is \(n^{2^{u_t}}\). For \(y\ge 1\) put
\[
L(y)=\log_2\frac{\log 2y}{\log N_0},
\qquad
d(y)=\lceil C\,L(y)\rceil ,
\]
with a constant \(C\ge 5\) fixed below. A word \(w\) of length \(d\)
is \(L\)-*bad* if \(u_t(w)>-L\) for every \(1\le t\le d\) (its walk
never descends to \(-L\)). \(\mathrm{word}_d(n)\) is the realized
itinerary of the first \(d\) steps of \(n\).

## 2. Envelope descent

**Lemma 2.1.** Let \(n\in(y,2y]\) and \(d\ge 1\). If
\(\mathrm{word}_d(n)\) is not \(L(y)\)-bad, then \(n\in R\).

*Proof.* Some \(t\le d\) has \(u_t\le -L(y)\), i.e.
\(3^{o_t}/2^t\le\log N_0/\log 2y\le\log N_0/\log n\), i.e.
\(n^{3^{o_t}}\le N_0^{2^t}\) as integers. The power envelope
\(J^t(n)^{2^t}\le n^{3^{o_t}}\) (Paper A Theorem 2.2,
`power_bound_word`) gives \(J^t(n)\le N_0\), so \(J^t(n)\in R\) and
\(n\in R\) by backward closure. Lean: `iterate_le_of_envelope`,
`reachesOne_of_itinerary_envelope`. \(\square\)

## 3. Bad words are rare

**Lemma 3.1 (Chernoff).** For \(C\ge 5\) put
\[
p_C=\frac{1-1/C}{\log_2 3},
\qquad
e(C)=\frac{C\,D(p_C\,\|\,\tfrac12)}{\ln 2},
\qquad
D(p\|\tfrac12)=p\ln(2p)+(1-p)\ln(2(1-p)).
\]
For \(L>0\) and \(d\ge CL\), the number of \(L\)-bad words of length
\(d\) is at most \(2^d\cdot 2^{-e(C)L}\). Moreover, for every
\(\varepsilon>0\) there is \(L_0\) such that for \(L\ge L_0\) and
\(d=\lceil CL\rceil\) the number of \(L\)-bad words of length \(d\)
*beginning with \(O\)* is at most \(2^{d-1}\cdot 2^{-(e(C)-\varepsilon)L}\).

*Proof.* An \(L\)-bad word has \(u_d>-L\), i.e.
\(o_d>(d-L)/\log_2 3\ge p_Cd\) (as \(L/d\le 1/C\)). For a fair coin,
\(\Pr[\mathrm{Bin}(d,\tfrac12)\ge pd]\le e^{-dD(p\|1/2)}\) for
\(p\ge\tfrac12\), and \(D(\cdot\|\tfrac12)\) is increasing on
\([\tfrac12,1]\); \(p_C\ge\tfrac12\) for \(C\ge 5\). Hence the count
is at most \(2^d e^{-dD(p_C\|1/2)}\le 2^de^{-CL\,D(p_C\|1/2)}=2^d2^{-e(C)L}\).
For the \(O\)-rooted count, the remaining \(d-1\) letters contain
\(o_d-1>(d-L)/\log_2 3-1=p'(d-1)\) odd letters with
\(p'=p_C-O(1/L)\); the same Chernoff bound with \(d-1\) trials gives
\(2^{d-1}e^{-(d-1)D(p'\|1/2)}\), and \((d-1)D(p'\|1/2)\ge(e(C)-\varepsilon)L\ln 2\)
for \(L\) large. \(\square\)

Odd starts have first letter \(O\) deterministically; the fair share
of an \(O\)-rooted cylinder of depth \(d\) among the \(y/2\) odd
starts of \((y,2y]\) is therefore \(2^{-(d-1)}\cdot y/2\), and the
relevant walk model conditions on \(u_1=\log_2 3-1\). Asymptotically
in \(L\) this changes nothing (the exponent \(e(C)\) is unchanged);
at finite depth it doubles the bad probability, as the census of
Section 6 confirms.

Numerically \(e(20)=0.574\), \(e(21)=0.621\), \(e(22)=0.668\),
\(e(25)=0.812\), \(e(30)=1.054\), \(e(40)=1.544\); \(e(C)\sim 0.0488\,C\).
The Chernoff bound is loose: the exact fair-coin probability that a
walk of length \(21L\) never reaches \(-L\) is \(4\)–\(20\) times
smaller on the range of the table in Section 6.

## 4. The hypothesis and the Tao-type bound

**Hypothesis \(\mathrm H(C,A)\) (log-log-depth cylinder bound).** For
all sufficiently large \(y\), with \(d=d(y)=\lceil C L(y)\rceil\),
every word \(w\in\{O,E\}^{d}\) beginning with \(O\) satisfies
\[
\#\{n\ \text{odd},\ y<n\le 2y:\ \mathrm{word}_d(n)=w\}
\ \le\ 2^{-(d-1)}\cdot\frac y2+\frac{y}{(\log y)^{A}} .
\]

Only an *upper* bound is asked, only at one depth per scale, and (as
the proof shows) only for the \(L(y)\)-bad words. Since
\(2^{-(d-1)}y/2\asymp y(\log y)^{-C}\) up to constants, \(\mathrm H(C,A)\)
with \(A>C\) says that no \(O\)-rooted cylinder of depth \(d(y)\)
exceeds its fair share among odd starts by more than a relative
\(O((\log y)^{C-A})\).

**Theorem B (Tao-type bound).** Assume \(\mathrm H(C,A)\) with
\(C\ge 5\) and \(A>C+e(C)\). Then for every \(\varepsilon>0\) and all
sufficiently large \(y\),
\[
\#\{n\ \text{odd},\ y<n\le 2y:\ n\notin R\}
\ \le\ \#\{n\ \text{odd in }(y,2y]:\ J^t(n)>N_0\ \forall t\le d(y)\}
\ \le\ \frac y2\Bigl(\frac{\log 2y}{\log N_0}\Bigr)^{-(e(C)-\varepsilon)} .
\]
In words: all but \(O(y(\log y)^{-e(C)+\varepsilon})\) odd starts in
\((y,2y]\) enter \([1,N_0]\) within \(d(y)=O(\log\log y)\) steps.

*Proof.* The first inequality is Lemma 2.1 applied with \(d=d(y)\)
(a start whose word is not bad enters \([1,N_0]\) within \(d\)
steps). Every odd start has an \(O\)-rooted word; by Lemma 3.1 the
\(O\)-rooted bad words number at most \(2^{d-1}2^{-(e(C)-\varepsilon)L(y)}\),
and by \(\mathrm H(C,A)\) each carries at most
\(2^{-(d-1)}y/2+y(\log y)^{-A}\) odd starts. Hence the count is at most
\[
\frac y2\,2^{-(e(C)-\varepsilon)L(y)}+2^{d-1}\,\frac{y}{(\log y)^A}
\ \le\ \frac y2\Bigl(\frac{\log 2y}{\log N_0}\Bigr)^{-(e(C)-\varepsilon)}
+\Bigl(\frac{\log 2y}{\log N_0}\Bigr)^{C}\frac{y}{(\log y)^{A}},
\]
using \(2^{d-1}\le 2^{CL}\). The second term is
\(O(y(\log y)^{C-A})=o(y(\log y)^{-e(C)})\) because \(A>C+e(C)\).
\(\square\)

## 5. Contagion closes the loop

**Theorem A (Tao-type bound with rate implies the conjecture).**
Suppose that for some \(e>1-\lambda^{**}=0.5520\ldots\) and all
sufficiently large \(y\),
\[
\#\{n\ \text{odd},\ y<n\le 2y:\ n\notin R\}\ \le\ \frac{y}{(\log y)^{e}} .
\]
Then \(R=\mathbb N\).

*Proof.* Suppose \(F\ne\emptyset\). Every \(n\in F\) lies in the
\(E\)-tree of an odd member of \(F\): if \(n\) is even then
\(\lfloor\sqrt n\rfloor\in F\) (forward closure, Lemma 1.1 of the
fate note), and the chain \(n\to\lfloor\sqrt n\rfloor\to\cdots\)
strictly decreases until it meets an odd integer, which is in \(F\)
(it cannot reach \(1\in R\)). For an odd \(n_0\in F\) the level-\(j\)
set \(S_j(n_0)\) of its \(E\)-tree has log-mass at most
\(\prod_{i<j}(1+n_0^{-2^i})/n_0\le 2/n_0\) (Lemma 2.1 of the fate
note gives \(\sum_{n\in E(m)}1/n\le(m+1)/m^2\)), and only levels with
\(n_0^{2^j}\le x\), i.e. \(j\le\log_2\log x\), meet \([1,x]\). Hence
\[
\sum_{\substack{n\in F\\ n\le x}}\frac1n
\ \le\ 2\,(1+\log_2\log x)\sum_{\substack{n_0\in F\ \text{odd}\\ n_0\le x}}\frac1{n_0}
\ \le\ 2\,(1+\log_2\log x)\Bigl(\sum_{k\ge k_0}\frac{2^k(k\ln 2)^{-e}}{2^k}+O(1)\Bigr)
\ \ll\ (\log x)^{1-e}\log\log x .
\]
By fate contagion (Theorem 4.2 of the fate note) the left side is
\(\ge K(\log x)^{\lambda}\) for every \(\lambda<\lambda^{**}\) and
all large \(x\). Choosing \(\lambda\in(1-e,\lambda^{**})\) gives a
contradiction for large \(x\). \(\square\)

The same conclusion holds if the hypothesis is stated for all
\(n\in(y,2y]\) (both parities) — then the \(E\)-tree bookkeeping is
unnecessary — or in logarithmic form
\(\sum_{n\le x,\,n\notin R}1/n=o((\log x)^{\lambda})\) for some
\(\lambda<\lambda^{**}\) (Corollary 4.5 of the fate note).

**Corollary C (the conjecture from a cylinder bound).** If
\(\mathrm H(C,A)\) holds for some \(C\ge 20\) and \(A>C+e(C)\), then
every positive integer reaches \(1\).

*Proof.* Theorem B gives Theorem A's hypothesis with
\(e=e(C)\ge e(20)=0.574>0.5520\). \(\square\)

The rate requirement is exactly the complement of the contagion
exponent. If \(\lambda^{**}\) is improved toward the depth-two ceiling
\(0.4927\) (uniform fiber share \(1/2\)), then \(e>0.5073\) suffices and
the remaining gap is \(1/3\) versus \(1/2\); \(\lambda^{**}\to 1\) would make any positive rate
suffice, but that improvement requires all descent certificates and is
circular here.

## 6. Constants and depth

With the certified floor \(N_0=3.5\cdot 10^8\) and \(C=21\)
(\(C=20\) now suffices; the table is a conservative illustration):

| \(y\) | \(L(y)\) | \(d(y)=\lceil 21L\rceil\) | Chernoff bound | exact bad probability | \((\log y)^{-0.6}\) | least depth for rate \(0.6\) (exact walk) |
|---|---|---|---|---|---|---|
| \(10^{20}\) | \(1.25\) | \(27\) | \(0.58\) | \(0.052\) | \(0.100\) | \(19\) |
| \(10^{100}\) | \(3.55\) | \(75\) | \(0.22\) | \(0.014\) | \(0.038\) | \(56\) |
| \(10^{1000}\) | \(6.87\) | \(145\) | \(0.052\) | \(0.0028\) | \(0.0096\) | \(117\) |
| \(10^{10000}\) | \(10.19\) | \(215\) | \(0.012\) | \(0.00057\) | \(0.0024\) | \(180\) |

The "exact bad probability" is the fair-coin probability that a walk
of length \(d(y)\) never reaches \(-L(y)\), by dynamic programming
(unconditioned first letter; for odd starts condition on
\(u_1=\log_2 3-1\), which roughly doubles the finite-depth values —
\(0.087\) in place of \(0.052\) at \((10^{20},27)\) — and leaves the
exponent unchanged); the last column is the least depth at which
that probability drops below \((\log y)^{-0.6}\) — about
\(17\,L(y)\), so the hypothesis could be stated at depth
\(\approx 17\log_2\log y\) with the exact walk count in place of
Chernoff. With the Lean floor \(N_0=260\) the depths grow by about
\(38\) letters. Source:
`data/research/juggler/tao_reduction/summary.json`.

**The census the certified floor makes possible.** Because every
\(n\le N_0=3.5\cdot 10^8\) is known to reach \(1\), the Tao-type
statistic "the orbit of \(n\) enters \([1,N_0]\) within \(d\) steps"
is a finite computation on exact big-integer orbits, and it is
exactly the aggregate form of \(\mathrm H_q(C,A)\): its complement is
the bad set of Theorem B. For random odd starts in \((y,2y]\) at
\(y=10^{12},10^{15},10^{20},10^{30},10^{50}\) (\(40000\), \(40000\),
\(40000\), \(20000\), \(20000\) samples), the fraction of orbits
still above \(N_0\) after \(d\) steps, \(d\le 40\), agrees with the
odd-start fair-coin probability
\(\Pr[u_t>-L(y)\ \forall t\le d\mid u_1=\log_2 3-1]\) to within
\(3\%\) for \(d\ge 10\) at every scale (ratios \(0.92\)–\(1.05\); at
\(10^{12}\), \(d=40\): \(0.0215\) against \(0.0219\); at \(10^{50}\),
\(d=40\): \(0.087\) against \(0.084\)). The only systematic deviation
is at depth \(\le 8\) for \(L(y)\) just below an integer (\(10^{15}\),
\(10^{20}\)), where the floors in \(J^t(n)\le n^{2^{u_t}}\) make real
orbits descend one step *earlier* than the continuous threshold —
in the favourable direction. Source:
`data/research/juggler/tao_reduction/summary.json` (`tao_census`).
So the exponent walk to the certified floor is fair-coin to depth
\(40\) at scales up to \(10^{50}\): the aggregate odd share along
surviving prefixes is \(\tfrac12\), not \(0.55\), far from the
critical \(0.6309\). This is evidence about the *aggregate* over
cylinders; the hypothesis asks for every cylinder, which no sample
can test.

For comparison, Paper B controls depth \(4\) (all words) and two
words of depth \(5\), with relative error \(y^{-1/96}\) on dyadic
blocks; the first open case is the \(OOOO*\) split (Conjecture 7.3).
The hypothesis \(\mathrm H(C,A)\) asks for depth \(d(y)\to\infty\) at
the rate \(C\log_2\log y\) with relative error \(o(1)\) — weaker in
rate than power savings, unbounded in depth. It is the natural
quantitative strengthening of the rate-free conjecture
`juggler_tower_rate_free_equidistribution` (fixed depth, no rate,
which yields density-one descent) to the regime where the descent
reaches a fixed floor.

## 7. What is and is not claimed

- Theorems A and B and Corollary C are proved (human proofs on top
  of the Lean envelope step and the fate-contagion theorem).
- Hypothesis \(\mathrm H(C,A)\) is not proved; it is recorded as the
  conjecture `juggler_loglog_depth_cylinder_bound`. Its depth-\(\le 4\)
  analogue is Paper B; its depth-\(5\) analogue is the \(K_3\) wall.
- No fate is excluded and no orbit is shown to terminate beyond the
  certified floor. The content is the identification of the exact
  almost-all statement that is equivalent to the conjecture, and the
  proof that it follows from a depth-\(O(\log\log y)\) equidistribution
  hypothesis — a reduction that has no Collatz analogue.

## 8. The biased-split form: one-sided odd-share control suffices

Equidistribution is more than the argument uses. The exponent walk
only has to *drift down*; a one-sided bound on the conditional
probability of the letter \(O\), uniformly over cylinders, is enough,
and the constant may be any \(q\) below \(\log 2/\log 3=0.6309\ldots\)
— the same threshold as the laboratory's node-wise \(E\)-share
\(\beta^*=1-\log 2/\log 3\) (`J-rate-free-density-one` (B)), now at
depth \(O(\log\log y)\) and with the conjecture as conclusion.

For odd \(n\in(y,2y]\) and \(t\ge 0\) write \([w]_y\) for the
cylinder \(\{n\ \text{odd}\in(y,2y]:\mathrm{word}_t(n)=w\}\),
\(w\in\{O,E\}^t\).

**Hypothesis \(\mathrm H_q(C,A)\) (log-log-depth odd-share bound).**
For all sufficiently large \(y\), every \(1\le t<d(y)=\lceil CL(y)\rceil\)
and every \(w\in\{O,E\}^t\),
\[
\#\{n\in[w]_y:\ \mathrm{word}_{t+1}(n)=wO\}\ \le\ q\,\#[w]_y+\frac{y}{(\log y)^{A}} .
\]
(The depth-\(0\) cylinder is all odd starts, whose next letter is
\(O\) with share \(1\); the hypothesis starts at depth \(1\).)

**Theorem B′ (biased-split Tao-type bound).** Let
\(q<\log 2/\log 3\), \(\mu=1-q\log_2 3>0\), \(C>1/\mu\), and put
\[
e_q(C)=\frac{2\,(C\mu-1)^2}{C\,(\log_2 3)^2\ln 2}
=1.1486\ldots\cdot\frac{(C\mu-1)^2}{C}.
\]
Assume \(\mathrm H_q(C,A)\) with \(A>C+1\). Then for every
\(\varepsilon>0\) and all sufficiently large \(y\),
\[
\#\{n\ \text{odd}\in(y,2y]:\ n\notin R\}
\ \le\ \frac y2\Bigl(\frac{\log 2y}{\log N_0}\Bigr)^{-(e_q(C)-\varepsilon)} .
\]
Consequently, if \(e_q(C)>1-\lambda^{**}\), Theorem A gives
\(R=\mathbb N\).

*Proof.* Let \(n\) be uniform on the odd integers of \((y,2y]\),
\(\mathcal F_t\) the σ-algebra of the depth-\(t\) cylinders,
\(X_t=\mathbf 1[\mathrm{word}_{t+1}(n)=\mathrm{word}_t(n)O]\) for
\(t\ge 1\), and \(u_t=(\log_2 3-1)+\sum_{1\le s<t}(X_s\log_2 3-1)\) the
exponent walk (the first letter is \(O\)). Put
\(\eta_t=\max\bigl(0,\ \mathbb P(X_t=1\mid\mathcal F_t)-q\bigr)\) for
\(t\ge 1\). On a cylinder \([w]\) of depth \(t\), \(\mathrm H_q\)
gives \(\eta_t\le y(\log y)^{-A}/\#[w]\), so
\(\mathbb E[\eta_t]\le\sum_w\frac{\#[w]}{y/2}\cdot\frac{y(\log y)^{-A}}{\#[w]}\le 2^{t+1}(\log y)^{-A}\)
and \(\mathbb E\bigl[\sum_{1\le t<d}\eta_t\bigr]\le 2^{d+1}(\log y)^{-A}\le 4(\log 2y/\log N_0)^{C}(\log y)^{-A}\).
Since \(\mathbb E[u_{t+1}-u_t\mid\mathcal F_t]\le-\mu+\eta_t\log_2 3\)
for \(t\ge 1\), the process
\(M_t=u_t-u_1-\sum_{1\le s<t}\mathbb E[u_{s+1}-u_s\mid\mathcal F_s]\)
is a martingale with increments in an interval of length
\(\log_2 3\), and
\(u_d\le u_1+M_d-(d-1)\mu+\log_2 3\sum_{1\le s<d}\eta_s\). Fix
\(\kappa\in(0,1)\). If \(n\notin R\) then by Lemma 2.1 the walk never
reaches \(-L\), so \(u_d>-L\), hence either
\(\log_2 3\sum_s\eta_s>\kappa(d-1)\mu\) or
\(M_d>-L-u_1+(1-\kappa)(d-1)\mu\). By Markov and the bound on
\(\mathbb E[\sum\eta_s]\), the first event has probability
\(\le\frac{4\log_2 3}{\kappa(d-1)\mu}(\log 2y/\log N_0)^{C}(\log y)^{-A}=O((\log y)^{C-A})\),
negligible for \(A>C+1\). By Azuma–Hoeffding, with
\(a=(1-\kappa)(d-1)\mu-L-u_1\ge L\bigl((1-\kappa)C\mu-1\bigr)-\log_2 3\),
\[
\mathbb P(M_d>a)\le\exp\Bigl(-\frac{2a^2}{(d-1)(\log_2 3)^2}\Bigr)
\le 2^{-L\,(e_q^{(\kappa)}(C)-o(1))},
\qquad
e^{(\kappa)}_q(C)=\frac{2((1-\kappa)C\mu-1)^2}{C(\log_2 3)^2\ln 2},
\]
and \(e^{(\kappa)}_q(C)\to e_q(C)\) as \(\kappa\to 0\). \(\square\)

The least \(C\) with \(e_q(C)>1-\lambda^{**}\) (`least_C_biased`):

| \(q\) | \(\mu\) | least \(C\) | \(e_q(C)\) |
|---|---|---|---|
| \(0.50\) | \(0.2075\) | \(20\) | \(0.570\) |
| \(0.55\) | \(0.1283\) | \(44\) | \(0.563\) |
| \(0.60\) | \(0.0490\) | \(240\) | \(0.555\) |
| \(0.62\) | \(0.0173\) | \(1715\) | \(0.552\) |

So: **if no cylinder of depth below \(44\log_2(\log 2y/\log N_0)\)
sends more than \(55\%\) of its members to an odd next state, every
positive integer reaches \(1\).** At \(q=\tfrac12\) the one-sided
hypothesis reproduces the constant \(C=20\) of the two-sided
Chernoff argument; as \(q\to\log 2/\log 3\), \(C\to\infty\).

## 9. Anatomy of the bad words, and why the wall is unavoidable

Two computations locate the hypothesis precisely
(`data/research/juggler/tao_reduction/summary.json`).

*Long odd runs are essential.* Among fair-coin words of length
\(d(y)\) whose walk never reaches \(-L(y)\) (\(N_0=3.5\cdot 10^8\),
\(C=21\)), the fraction containing an odd run of length \(\ge 4\) is
\(0.967\) at \(y=10^{20}\), \(0.9999\) at \(10^{100}\) and
\(1-10^{-6}\) at \(10^{300}\); the fraction with a run \(\ge 5\) is
\(0.80\), \(0.988\), \(0.998\). A bad word is odd-heavy
(\(o\ge 0.63d\) minus a little), and odd-heavy words have long odd
runs. Odd runs of length one are transparent
(\(\lfloor\sqrt{\lfloor n^{3/2}\rfloor}\rfloor=\lfloor n^{3/4}\rfloor\)),
runs of length two and three are Paper B's Theorems 4.4 and 6.1, but
the cylinders that carry the bad mass are exactly those with runs
\(\ge 4\), i.e. the \(O^4\!\to O^5\) split (Conjecture 7.3, the
\(K_3\) kernel) and its deeper iterates. Controlling odd runs of
bounded length, however uniformly in depth, would not touch the
hypothesis; there is no way around the nested-floor tower.

*The hardest cylinders look fair.* On the odd starts of
\((10^6,2\cdot 10^6]\) the cylinders \(O^t\) (all-odd prefix) have
odd-share \(0.500,\ 0.499,\ 0.498,\ 0.502,\ 0.504,\ 0.497,\ 0.488,\ 0.499,\ 0.513,\ 0.539,\ 0.490,\ 0.504,\ 0.531,\ 0.478\)
for \(t=1,\dots,14\), on \(500000,\ 250114,\ \dots,\ 130,\ 69\)
members — binomial noise around \(\tfrac12\), far below the \(0.55\)
of the \(q=0.55\) row. This is consistent with \(\mathrm H_q(C,A)\)
and is not evidence for it in the required range (depth
\(\approx 46\,L(y)\) at astronomically large \(y\)).

*Update (fate note §7).* Paper B's Weyl-differencing skeleton
(Theorems 4.4 and 4.7) localizes to sub-dyadic intervals of length
\(\ge P^{1/2}\) with the same relative saving \(P^{-1/24}\); the
resulting \(OOEEE\) production on even blocks raises the contagion
exponent to \(\lambda^{***}=0.5392\ldots\). Every requirement in this
note improves accordingly: the rate threshold becomes
\(e>1-\lambda^{***}=0.4608\ldots\); the least depth constants are
\(C=18\) for the fair bound (\(e(18)=0.480\)) and, in the biased-split
form, \(C(0.5)=18\), \(C(0.55)=39\), \(C(0.60)=206\), \(C(0.62)=1451\).
The structure of the hypothesis (odd-share control at depth
\(O(\log\log y)\), carried by odd runs \(\ge 4\)) is unchanged.

*Can Paper B's kernel method be made uniform in the depth?* Not by
any route known to the laboratory. The rated methods (power savings
per depth) are blocked at depth five by the BB/GG/JJ ladder; a
rate-free method would give no uniformity in the depth; the
transparent-nesting structure disposes only of odd runs of length
one. The question is recorded as PARK behind the \(K_3\) program
(`docs/problems/juggler_tao_almost_bounded.md`), not reopened. What
the reduction adds is the size of the prize: uniform odd-share control
at depth \(O(\log\log y)\) — one-sided, with any constant below
\(0.6309\) — is the whole Juggler conjecture.

*Update (Section 10).* The uniform per-cylinder form is not what the
argument needs. The pressure form of Section 10 is one-sided,
aggregated over cylinders with exponential weights, tolerant of tower
cylinders \(O^t\) biased up to \(0.84\) and of any \(o(\log\log y)\)
initial depths;
what it needs is the *aggregate* split of typical odd-heavy live
words at depth \(\asymp\log\log y\). The statements "the hypothesis is
the \(O^t\to O^{t+1}\) split" and "long odd runs are essential" above
are correct for \(\mathrm H_q\) and for the shape of bad words; they
do not describe the weakest hypothesis. See §10.4.

## 10. The weakest form: live pressure and the no-momentum hypothesis

The question this section answers: what is the weakest hypothesis on
Juggler parity words from which the exponent-walk argument still
yields the Tao-type bound? Theorems B and B′ condition on the past
letter by letter; the concentration step actually needs one number
per scale.

### 10.1 Live starts and the stopped walk

Let \(N=y/2\) count the odd starts of \((y,2y]\), let
\(\tau(n)=\min\{t\ge 1:\ J^t(n)\le N_0\}\) be the entrance time into
the certified floor, and call \(n\) *live at depth \(t\)* if
\(\tau(n)>t\). Write \(o_t(n)\) for the number of odd letters among
\(n,J(n),\dots,J^{t-1}(n)\). By Lemma 2.1, \(\tau(n)>t\) implies
\(u_t(n)=o_t\log_2 3-t>-L(y)\).

The stopping is essential and not a technicality: \(J(1)=1\) is odd,
so after entering \([1,N_0]\) an orbit that reaches \(1\) has an
all-\(O\) tail, and the unstopped odd count of *every* start grows
linearly. Every statement below is about live starts.

### 10.2 The pressure form

For \(\theta>0\) put \(a_\theta=\tfrac12(1+e^{\theta})\), the fair-coin
value of \(\mathbb E[e^{\theta X}]\) for one letter.

**Hypothesis \(\mathrm P_\theta(C)\) (live pressure).** For all
sufficiently large \(y\), with \(d=d(y)=\lceil CL(y)\rceil\),
\[
\frac1N\sum_{\substack{n\ \mathrm{odd}\in(y,2y]\\ \tau(n)>d}}e^{\theta\,o_d(n)}
\ \le\ a_\theta^{\,d}\,e^{o(d)} .
\]

**Theorem B‴ (pressure form).** Assume \(\mathrm P_\theta(C)\) with
\(C\ge 5\) and \(\theta=\theta_C=\log\bigl(p_C/(1-p_C)\bigr)\). Then for
every \(\varepsilon>0\) and all large \(y\),
\[
\#\{n\ \mathrm{odd}\in(y,2y]:\ \tau(n)>d(y)\}
\ \le\ \frac y2\Bigl(\frac{\log 2y}{\log N_0}\Bigr)^{-(e(C)-\varepsilon)},
\]
the bound of Theorem B; hence \(\mathrm P_{\theta_C}(C)\) with
\(C\ge 19\) implies the Juggler conjecture (Theorem A with
\(\lambda^{***}\)).

*Proof.* If \(\tau(n)>d\) then \(u_d>-L\), i.e.
\(o_d>(d-L)/\log_2 3\ge p_Cd\). Hence
\[
\#\{\tau>d\}\le\#\{\tau>d,\ o_d\ge p_Cd\}
\le e^{-\theta p_Cd}\sum_{\tau(n)>d}e^{\theta o_d(n)}
\le N\,e^{-\theta p_Cd}a_\theta^{\,d}e^{o(d)} .
\]
At \(\theta=\theta_C\), \(\theta p_C-\log a_\theta=D(p_C\|\tfrac12)\),
so the count is \(\le N\exp(-dD(p_C\|\tfrac12)(1-o(1)))\le N2^{-(e(C)-\varepsilon)L}\).
\(\square\)

### 10.3 The tilted share: no momentum

For \(1\le t<d\) let \(\mu_{\theta,t}\) be the probability measure on
the starts live at depth \(t\) with density proportional to
\(e^{\theta o_t(n)}\), and let
\[
s_\theta(t)=\mu_{\theta,t}\bigl(J^t(n)\ \text{odd}\bigr)
\]
be the *tilted odd share*: the probability that the next letter is
\(O\) when odd-heavy live prefixes are up-weighted exponentially.

**Hypothesis \(\mathrm M_{\theta,q}(C)\) (no momentum).** For all large
\(y\),
\(\sum_{t=1}^{d(y)-1}\bigl(s_\theta(t)-q\bigr)^+=o(d(y))\).

**Proposition 10.1.** \(\mathrm M_{\theta,1/2}(C)\) implies
\(\mathrm P_\theta(C)\). More generally \(\mathrm M_{\theta,q}(C)\)
with \(q<p_C\) gives
\(\#\{\tau>d\}\le N\exp(-d\,D(p_C\|q)(1-o(1)))\), i.e. the exponent
\(e_q^{\rm Ch}(C)=C\,D(p_C\|q)/\ln 2\), which is at least the Azuma
exponent of Theorem B′ (least \(C\): \(19\) at \(q=\tfrac12\), \(41\)
at \(0.55\), \(214\) at \(0.60\), \(1497\) at \(0.62\)).

*Proof.* Dropping the condition \(\tau>t+1\) in favour of \(\tau>t\)
only enlarges the sum, so
\[
\sum_{\tau>t+1}e^{\theta o_{t+1}}\le\sum_{\tau>t}e^{\theta o_{t+1}}
=\Bigl(\sum_{\tau>t}e^{\theta o_t}\Bigr)\bigl(1+(e^{\theta}-1)s_\theta(t)\bigr).
\]
With \(a_{\theta,q}=1+(e^\theta-1)q\) and \(c_\theta=(e^\theta-1)/a_{\theta,q}\),
\(1+(e^\theta-1)s\le a_{\theta,q}\exp\bigl(c_\theta(s-q)^+\bigr)\).
Telescoping from \(t=1\) (\(\sum_{\tau>1}e^{\theta o_1}\le Ne^\theta\))
gives
\(\sum_{\tau>d}e^{\theta o_d}\le Ne^{\theta}a_{\theta,q}^{\,d-1}\exp\bigl(c_\theta\sum_{t<d}(s_\theta(t)-q)^+\bigr)\),
which is \(\mathrm P_\theta\) at \(q=\tfrac12\); the Chernoff step of
Theorem B‴ with \(a_{\theta,q}\) in place of \(a_\theta\) and
\(\theta=\log\frac{p_C(1-q)}{q(1-p_C)}\) gives \(D(p_C\|q)\).
\(\square\)

### 10.4 What the pressure form does not need

Each of the following is a consequence of the form of
\(\mathrm P_\theta\); together they relocate the wall.

**(a) Any \(o(\log\log y)\) initial depths are free.** A letter
contributes a factor at most \(e^\theta\) to the moment, so bias —
however extreme — at any set of depths of size \(o(d(y))\) is absorbed
by the \(e^{o(d)}\). In particular the depth-\(5\) split (\(K_3\),
Paper B Conjecture 7.3) and every split to any fixed depth, or to depth
\(s_0(y)\) for any \(s_0=o(\log\log y)\), is irrelevant to the
reduction.

**(b) The tower cylinders are nearly free.** A cylinder \(w\) of depth
\(t\) enters \(\mathrm P_\theta\) only through \(\#[w]e^{\theta o(w)}\),
against a fair total \(Ne^{\theta}a_\theta^{\,t-1}\). If the tower
\(O^t\) splits with odd share \(\beta\) at every level,
\(\#[O^t]=N\beta^{t-1}\) and its tilted weight relative to the fair
total is \((\beta e^{\theta}/a_\theta)^{t-1}\), which decays
geometrically iff \(\beta<a_\theta e^{-\theta}=\tfrac12(1+e^{-\theta})\)
— \(0.836\) at \(\theta_{19}=0.396\). So a tower biased anywhere below
\(0.836\) contributes a bounded total to \(\sum_t(s_\theta(t)-\tfrac12)^+\)
when the rest of the population is fair, hence \(o(d)\); the uniform
hypothesis \(\mathrm H_q\) needs the same tower to split below
\(q<0.6309\), and the Tao-type *conclusion* itself only fails once
\(\beta>2^{-e(C)/C}=0.981\). The same accounting holds for any family
of cylinders whose tilted weights sum to \(o(d)\) over depths: a single
cylinder of depth \(t\) matters only if it is over-populated by an
exponential factor \((2a_\theta e^{-\theta})^{t}=(1.67)^t\) relative to
its fair share. The iterated \(O^t\to O^{t+1}\) splits of Section 9 —
the "hardest cylinders" — are therefore not what the weakest hypothesis
is about; it is about the tilted average over all live cylinders.

**(c) One-sidedness and aggregation.** \(\mathrm M_{\theta,q}\) bounds
one weighted average per depth from above; under-populated odd
continuations anywhere, and over-populated ones on cylinders of small
tilted weight, cost nothing. In Walsh terms, \(e^{\theta X_s}=a_\theta+b_\theta(-1)^{J^s(n)}\)
with \(b_\theta/a_\theta=-\tanh(\theta/2)\), so
\[
\frac1N\sum_ne^{\theta o_d(n)}=a_\theta^{\,d}\Bigl(1+\sum_{\emptyset\ne T}(-\tanh\tfrac\theta2)^{|T|}\frac{W_T}{N}\Bigr),
\qquad W_T=\sum_n\prod_{s\in T}(-1)^{J^s(n)} :
\]
the Walsh sums of high order are exponentially down-weighted
(\(\tanh(0.198)=0.196\) per letter), whereas the uniform cylinder
hypothesis needs all \(2^{d}\) of them with equal weight. (The live
restriction adds the indicator of \(\{u_t>-L\ \forall t\}\); the
identity is stated for the unstopped moment to show the weights.)

**(d) The intermediate forms are reparameterizations.** Between
\(\mathrm H(C,A)\) and \(\mathrm P_\theta\) sit the "almost all
cylinders" form (odd-share \(\le q\) on all but a set of cylinders of
total mass \(\le N(\log y)^{-B}\) per depth, \(B>e_q(C)\); the Markov
step of Theorem B′ absorbs it) and its second-moment version. With
\(D(w)=\#[wO]-\tfrac12\#[w]\) and the collision count
\(\mathcal C_t=\sum_{|w|=t}\#[w]^2\), Parseval gives
\(\sum_wD(w)^2=2^{-t-2}\sum_{S\subseteq[0,t)}|W_{S\cup\{t\}}|^2=\tfrac12\mathcal C_{t+1}-\tfrac14\mathcal C_t\),
so the almost-all form follows from the pair-correlation asymptotic
\(\mathcal C_t\le(N^2/2^{t-1})(1+(\log y)^{-A'})\), \(A'>C+2\) — a
two-point statement — but by Walsh inversion any such two-sided
bound is equivalent, up to the exponent, to polylogarithmic savings on
every Walsh sum to depth \(d(y)\), i.e. to \(\mathrm H(C,A)\) with a
different \(A\). They are recorded as `REPARAMETERIZATION`; the
pressure form is the one that is weaker in substance.

**(e) No bounded-depth cylinder statement can close the reduction.**
Fix \(k\). The probability measure on parity words that is fair to
depth \(k\) and all-\(O\) afterwards satisfies every cylinder-count
statement of depth \(\le k\) exactly, and under it a positive
proportion of starts is live for ever. An argument for the Tao-type
bound that used only depth-\(\le k\) cylinder statistics of the
Juggler map and the walk logic would prove the same bound for that
measure. Hence every proof of the Tao-type bound — in any of the
forms of this note — must use information about the parity words at
depth \(\to\infty\); Paper B's program at any fixed depth is neither
necessary (by (a)) nor sufficient (by (e)) for it.

### 10.5 Where the wall is, in this language

\(\mathrm P_\theta(C)\) says that the exponentially tilted distribution
of live parity words of length \(d\asymp\log_2\log y\) has the fair
pressure \(\log a_\theta\): odd-heavy live words — those with about
\(e^\theta/(1+e^\theta)\approx 60\%\) odd letters, the words the tilt
selects — are not over-populated at an exponential rate in \(d\).
Typical such words contain odd runs of length \(\ge 4\) (so the nested
towers of height \(\ge 4\) that block Paper B at depth five sit inside
almost every relevant cylinder), but no individual cylinder is
required to split fairly: only the tilted average over the
\(\approx 2^{0.97d}\) typical cylinders at each depth. This is a
statement about *averaging over cylinders at unbounded depth*, of a
kind (mean over characters, not sup) for which analytic number theory
sometimes has tools where pointwise bounds fail; the laboratory knows
no such tool for nested-floor parities, and records the question,
not an approach. The two frontier statements of the termination
problem — the free term \(\psi_F\) of the exact map (fate note §6.2)
and \(\mathrm P_\theta(C)\) here — are both bulk-depth parity
statements; neither is approached by fixed-depth equidistribution.

### 10.6 Census

`pressure_census` (`data/research/juggler/tao_reduction/summary.json`)
computes the tilted odd share \(s_\theta(t)\) on live starts from
exact orbits: \(40000\) random odd starts in \((y,2y]\) for
\(y=10^{12},10^{20},10^{30},10^{50}\), target \(N_0=3.5\cdot 10^8\),
depths \(t=1,\dots,40\), \(\theta\in\{0.396,0.6\}\). Live populations
at depth \(40\): \(858\), \(1534\), \(2069\), \(3408\). Results:
\(s_\theta(t)\in[0.44,0.56]\) at every depth and scale, within the
binomial noise of the effective tilted sample; the cumulative excess
\(\sum_{t<40}(s_\theta(t)-\tfrac12)^+\) is \(0.14\)–\(0.19\) at
\(\theta=0.396\) and \(0.19\)–\(0.26\) at \(\theta=0.6\), exactly the
expected positive-part noise (\(\approx 0.4\sigma_t\) per depth); the
live moment \(\frac1N\sum_{\tau>d}e^{\theta o_d}\) divided by its
fair-coin DP value is \(0.95\)–\(1.08\) for \(d=10,20,30,40\). No
momentum is detectable to depth \(40\) at any scale up to \(10^{50}\).
This is an OBSERVATION about the aggregate statistic of
\(\mathrm M_{\theta,1/2}\) in the accessible range; the hypothesis is
about \(d(y)\to\infty\).

## 11. One frontier statement: the free term is the live mass

The fate note leaves the termination problem with two frontier
statements: the free term \(\psi_F\) of the exact first-letter
decomposition (fate note (6.1)) and the hypothesis of this note. This
section shows they are the same object, records the exact duality
between the two halves of (6.1), and derives from it what "uniform in
depth" has to mean quantitatively for any analytic route.

### 11.1 The free term as infinite-depth live mass

Recall (fate note §6.2): with \(x=e^t\), \(\ell_A(a,b]=\sum_{n\in A\cap(a,b]}1/n\),
\(\varphi_A(t)=\ell_A(e^{t/2},e^t]/(t/2)\), and \(\psi_A(t)\) the
log-weighted fraction of the \(OO\)-type odd \(n\in(\sqrt x,x]\)
(odd with odd \(\lfloor n^{3/2}\rfloor\)) whose image lies in \(A\),
\[
\varphi_A(t)=\tfrac12\varphi_A(t/2)+\tfrac14\varphi^{\rm fib}_A(3t/4)+\tfrac14\psi_A(t)+O(e^{-t/4}/t).
\tag{6.1}
\]
For \(A=F=\mathbb N_{\ge1}\setminus R\) and odd \(n\), \(n\in F\iff\lfloor n^{3/2}\rfloor\in F\)
(odd generation), and \(n\in F\iff\tau(n)=\infty\) since
\([1,N_0]\subseteq R\). Hence, with \(\mathbb P^{\log}_x\) the
\(1/n\)-weighted measure on the odd \(n\in(\sqrt x,x]\),

**Proposition 11.1.** \(\psi_F(t)=\lim_{d\to\infty}\mathbb P^{\log}_x\bigl(\tau(n)>d\ \big|\ \mathrm{word}_2(n)=OO\bigr)\),
a decreasing limit, and under \(\mathrm P_\theta(C)\) (equivalently
under any hypothesis of Sections 4, 8, 10),
\[
\psi_F(t)\ \le\ 2\,(1+o(1))\Bigl(\frac{t}{2\log N_0}\Bigr)^{-(e(C)-\varepsilon)} .
\]

*Proof.* The first claim is the definition of \(\psi_F\) together with
\(F\cap\{\text{odd}\}=\{\tau=\infty\}\cap\{\text{odd}\}=\bigcap_d\{\tau>d\}\).
For the bound, cover \((\sqrt x,x]\) by dyadic blocks \((y,2y]\); the
\(OO\)-type odd starts of a block number \(\tfrac y4(1+O(y^{-\delta}))\)
(Paper B, depth two, unconditional, with a power saving), the live starts at depth
\(d(y)\) number at most \(\tfrac y2(\log 2y/\log N_0)^{-(e(C)-\varepsilon)}\)
by Theorem B‴, and \(\{\tau>d\}\) decreases in \(d\). The
\(1/n\)-weighting only averages the block ratios. \(\square\)

So the free term of the exact map is the infinite-depth live mass of
the depth-two cylinder \(OO\), and the hypothesis of this note bounds
it. There are not two frontier statements but one quantity — the
live mass of odd-heavy parity words at depth \(\asymp\log\log x\) —
seen once as a limit (exact map) and once at finite depth with a rate
(Tao-type bound). The pressure form is the weakest condition on the
concentration route that controls it.

### 11.2 Exact map = contagion + free term, and the critical exponent

The two halves of (6.1) are the two theorems of the fate note.
Dropping \(\psi\ge0\) gives the *lower* recursion
\(\varphi_F(t)\ge\tfrac12\varphi_F(t/2)+\tfrac14\varphi^{\rm fib}_F(3t/4)\),
which in log-mass form \(g=(t/2)\varphi\) is
\(g(t)\ge g(t/2)+\tfrac13g^{\rm fib}(3t/4)\): the ideal depth-two
contagion recursion (fate note §4.2 with perfect fibers; the proved
constants \(\tfrac19,\tfrac29\) and the \(OOEEE\) term give
\(\lambda^{***}=0.5392\), above the ideal depth-two ceiling \(0.4927\)
because \(OOEEE\) is an extra production). Dropping
\(\psi\le1\) instead gives the *upper* recursion for the failure
density. Its homogeneous solutions \(\varphi=t^{-e}\) satisfy
\(\tfrac12 2^{e}+c\,(4/3)^{e}=1\) with \(c=\tfrac14\) for ideal fibers
and \(c=\tfrac13\) with the two-sided pairing constant \(\tfrac23\):
\[
e_{\rm crit}=1-\lambda_{\rm ideal}=0.5073\quad(\text{ideal}),\qquad
e_{\rm crit}=0.3391\quad(\text{pairing}).
\]
The Tao-type rate threshold \(e>1-\lambda^{***}=0.4608\) is therefore
the homogeneous decay exponent of the exact map up to the
fiber-constant gap: contagion's growth rate and the exact map's decay
rate are the same number because they are the same recursion.

**Corollary 11.2 (the exact map cannot replace contagion).** Suppose
\(\psi_F(t)\le t^{-e}\) with \(e\) as large as one likes. The upper
recursion then gives \(\varphi_F(t)\ll t^{-\min(e,e_{\rm crit})}\) and
nothing more: with honest constants \(\varphi_F\ll t^{-0.339}\), ideally
\(\varphi_F\ll t^{-0.507}\), never \(\varphi_F\equiv0\). Contagion gives
\(\varphi_F\gg t^{-0.4608}\) if \(F\ne\emptyset\) under Appendix C.
The two bounds do not
cross. What does cross contagion is the *direct* inclusion
\(F\cap(y,2y]\subseteq\{\tau>d(y)\}\) applied to all starts — Theorem
A — not the recursion. Conversely, if \(F\ne\emptyset\) and \(\psi_F\)
decayed faster than the critical rate, the sandwich would force
\(\varphi_F(t)\asymp t^{-0.507}\): a nonempty failure set with a small
free term would have log-count exactly of the order
\((\log x)^{0.4927}\).

### 11.3 The depth-uniformity budget

Section 10.4(e) says that a proof of the Tao-type bound must use
information at depth \(\to\infty\). The exact form of the bound says
how uniform that information must be. Suppose an analytic method
proves cylinder equidistribution at depth \(d\) with a power saving,
\(\#[w]_y=2^{-(d-1)}\tfrac y2+O(y^{1-\delta_d})\), where the saving
exponent loses a factor \(2^{c}\) per depth: \(\delta_d=\delta_0 2^{-cd}\)
(Weyl differencing loses \(c\ge1\); Paper B's chain \(\tfrac1{24}\to\tfrac1{96}\)
from depth three to four is \(c=2\)). Theorem B needs the error to be
\(o(y(\log y)^{-e(C)})\) at \(d=C\log_2\log y\), i.e.
\(2^{-cd}\log y\ge e(C)\log\log y\), i.e. \((\log y)^{1-cC}\gtrsim\log\log y\):
\[
cC<1,\qquad\text{so the per-depth loss factor must be below }2^{1/C}=1.035\ (C=20),\ 1.016\ (C=44).
\]
Any method losing more than about \(4\%\) of its saving exponent per
depth is structurally excluded from the Tao depth, whatever it does at
depth five; Weyl differencing, at \(c\ge1\), reaches at most depth
\(\approx\log_2\log y\) — one unit of \(L(y)\), enough for the all-\(E\)
word to reach the floor, not for the Chernoff tail, which needs
\(C\ge5\) units. (A polylogarithmic *relative* saving at every depth,
as in \(\mathrm H(C,A)\), would suffice; what is excluded is
power-saving machinery whose exponent decays exponentially in the
depth.) This is the quantitative content of "uniform in depth": the
saving may decay at most like \(2^{-d/C}\).

### 11.4 What is closed

The termination frontier of the laboratory is a single statement —
the live mass of odd starts at scale \(y\) at depth \(C\log_2\log y\)
decays like \((\log y)^{-e}\), \(e>1-\lambda^{***}\) — with the
pressure/no-momentum form its weakest sufficient condition, the free
term \(\psi_F\) its \(OO\)-restriction at infinite depth, contagion the
mechanism that turns it into the conjecture, and the exact map the
identity that shows nothing else is free. No new hypothesis arises;
the unification is a `REPARAMETERIZATION` and the question is closed.
Nothing unconditional is claimed.
