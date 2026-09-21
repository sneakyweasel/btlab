---
title: "No m-cycles of the 3n−1 map for m ≤ 49"
subtitle: "The Simons–de Weger template on the negative side, from a verification floor of 2^44"
author: Philippe Cochin
date: 21 September 2026
keywords:
  - 3n-1 map
  - Collatz cycles
  - m-cycles
  - linear forms in logarithms
  - verification floor
header-includes:
  - \usepackage{amsmath,amssymb}
  - \AtBeginDocument{\author{Philippe Cochin \\ \texttt{philippe@cochin.fr}}}
---

**Laboratory manuscript, first draft of 21 September 2026.** Not a review object. One
external input, Rhin's effective measure for linear forms in \(\log2\) and \(\log3\); one
computational input, the laboratory's own verification floor; everything else is proved
below or is exact arithmetic recorded with its margins. Simons–de Weger 2005 and Rhin 1987
were read in full on the day of this draft, and the constants below are compared with theirs
where the comparison is informative.

## Abstract

Let \(g(y)=y/2\) for even \(y\) and \(g(y)=(3y-1)/2\) for odd \(y\), the \(3n-1\) map on the
positive integers, equivalently the shortcut \(3n+1\) map on the negative integers. Its known
cycles are \(1\), \((5,7,10)\) and the eleven-element cycle at \(17\), and every start below
\(2^{44}\) reaches one of them. An \(m\)-cycle is a cycle with \(m\) maximal runs of odd
elements. We transpose the template of Simons and de Weger for \(3n+1\) \(m\)-cycles to this
map, deriving its constants on this side rather than borrowing them: the odd step subtracts,
so in the variable \(u=y-1\) an odd run is exact multiplication by \(3/2\), a run of \(a\) odd
steps starts at \(y\ge2^a+1\), the cycle equation bounds the linear form
\(\Lambda=o\log3-K\log2\) by \(m/(x_{\min}-1)\) with constant one, and successive local
minima obey \(u_{i+1}<u_i^{\log_23}/2\). With Rhin's bound this gives: the \(3n-1\) map has
no \(m\)-cycle with \(1\le m\le49\) other than the two known ones. For \(m\le43\) no
admissible cycle length lies below Rhin's ceiling; for \(44\le m\le49\) the admissible lengths
are excluded by the chaining, the closest by \(1.4\) bits. At \(m=50\) four lengths remain,
the input for lattice reduction. The same tables give \(m\le44\) from \(2^{40}\), \(m\le68\)
from \(2^{60}\) and \(m\le82\) from \(2^{68}\). No published verification floor and no
\(m\)-cycle theorem with \(m\ge3\) existed for this map.

## 1. The map, the cycles, and what is known

Write \(g\) for the shortcut \(3n-1\) map above. Its orbits on the positive integers are the
orbits of the shortcut Collatz map \(T(x)=x/2\), \((3x+1)/2\) on the negative integers under
\(x=-y\): \((3(-y)+1)/2=-(3y-1)/2\). Three cycles are known,
\[
(1),\qquad(5,7,10),\qquad(17,25,37,55,82,41,61,91,136,68,34),
\]
with \((K,o)=(1,1),(3,2),(11,7)\) steps and odd steps. Whether these are all the cycles, and
whether every orbit is bounded, are the \(3x-1\) questions of Lagarias's bibliographies, open.

**The floor.** Every \(1\le y<2^{44}\) reaches one of the three cycles. This is the
laboratory's own computation (19–20 September 2026), ninety-six chunks of \(5\cdot2^{35}\)
starts, \(8246337208320\) odd starts counted exactly, no failure, no new cycle, greatest step
count \(704\); the verifier source, the chunk reports and the coverage check are archived
with the branch `negative_floor_3x1`. No published floor exists: the only statement in print
is an unattributed comment on OEIS A037084, "up to at least 100000000". The certificate is a
computation and is labelled as one throughout.

**\(m\)-cycles.** A cycle with at least one even step splits into \(m\ge1\) maximal runs of
odd elements alternating with runs of even elements. The first element of an odd run is a
local minimum, the element after its last odd step a local maximum. The two known cycles
with an even step have \(m=1\) and \(m=2\). Simons [S07] proves that \(g\) has exactly one
nontrivial \(2\)-cycle, at \(17\), and does so without any floor, by de Weger's bounds on
\(0<3^K-2^{K+L}<3^{0.89K}\), Steiner's \(1\)-cycle theorem and an extremal inequality; he
states that the floor-free route stops at \(m\ge3\). For \(3n+1\), Simons [Si05] excludes
\(2\)-cycles, Simons and de Weger [SdW] exclude \(m\)-cycles for \(m\le68\) from the floor
of November 2004, \(X_0=301\cdot2^{50}>3.3889\cdot10^{17}\), and Hercher [H23] reaches
\(m\le91\) from \(695\cdot2^{60}\) with the arrangement of the valleys. The template of
[SdW] has five steps: a floor; a bound on \(\Lambda\) from the cycle equation (their Lemma 4
and Corollary 5); a chaining of the local minima (Lemmas 6, 7); Crandall's lemma generalized
for a lower bound on the length (Lemma 10, Corollary 11) against Rhin's bound for an upper one
(Lemmas 12, 14), sharpened through the partial quotients of \(\log_23\) (Lemma 16); and de
Weger's approximation lattice where a window remains (Lemma 18). At their floor the three
stages give \(m\le57\), \(m\le63\) and \(m\le68\). Nobody has run any of it on \(3n-1\),
because the first step was missing; [S08], which extends the template to \(3x+q\), \(px+q\)
and Guy's permutation, skips the map. This note runs the first four steps with the constants
of this side, replaces the partial-quotient stage by an exact enumeration of the admissible
lengths, and leaves the lattice as its open list.

## 2. Notation

Throughout \(x=\log2/\log3\), \(\delta=\log_23=1/x\). For a cycle \(C\) of \(g\) with \(K\)
steps and \(o\) odd steps put
\[
\Lambda(C)=o\log3-K\log2 .
\]
For odd \(y\) put \(u=y-1\). The local minima of an \(m\)-cycle are \(y_1,\dots,y_m\) in
cyclic order, \(u_i=y_i-1\), the run from \(y_i\) has \(a_i\) odd steps, and \(r_i\ge1\)
halvings follow it. \(x_{\min}\) is the least element of \(C\). The floor is
\(X_0=2^{44}\).

## 3. Four lemmas on the negative side

**Lemma 1 (odd runs).** Let \(y\ge3\) be odd, \(u=y-1\), \(a=v_2(u)\). Then
\[
g^k(y)-1=\Bigl(\tfrac32\Bigr)^k(y-1)\qquad(0\le k\le a),
\]
\(g^k(y)\) is odd for \(k<a\) and \(g^a(y)\) is even. Consequently a run of \(a\) odd steps
starts at \(y\ge2^a+1\), and its local maximum \(M=g^a(y)\) satisfies \(M\le u^{\delta}+1\).

*Proof.* For odd \(y\), \(g(y)-1=(3y-1)/2-1=\tfrac32(y-1)\). While the iterates stay odd
this repeats, so \(g^k(y)=1+3^ku/2^k\) as long as \(g^j(y)\) is odd for \(j<k\); and
\(1+3^ku/2^k\) is an odd integer exactly when \(2^{k+1}\mid u\), since \(3^k\) is odd. Hence
the first \(a=v_2(u)\) iterates are odd and the next is even. Then \(u\ge2^a\) gives
\(y\ge2^a+1\), and \((3/2)^a\le(3/2)^{\log_2u}=u^{\log_2(3/2)}=u^{\delta-1}\) gives
\(M=1+(3/2)^au\le1+u^{\delta}\). \(\square\)

This is Hercher's Lemma 8 [H23] with \(y\equiv1\pmod{2^a}\) in place of \(y\equiv-1\): the
floor \(2^a+1\) is larger by two, and it is attained at \(5\) (\(a=2\)) and \(17\) (\(a=4\)).

**Lemma 2 (cycle equation).** On a cycle \(C\) with at least one even step,
\[
\Lambda(C)=-\sum_{y\in C\ \mathrm{odd}}\log\Bigl(1-\frac1{3y}\Bigr)>0,
\qquad\text{so}\qquad 3^o>2^K,
\]
and \(\Lambda(C)<\sum_{y\in C\ \mathrm{odd}}\dfrac1{3y-1}\). The run from a local minimum
\(y\) contributes less than \(1/(y-1)\). Hence, for an \(m\)-cycle,
\[
\Lambda(C)<\sum_{i=1}^m\frac1{y_i-1}\le\frac m{x_{\min}-1}.
\]

*Proof.* An odd step multiplies by \(\tfrac32(1-\tfrac1{3y})\) and an even step by
\(\tfrac12\); around the cycle the product is \(1\), so
\(3^o2^{-K}\prod_{\mathrm{odd}}(1-1/(3y))=1\), which is the displayed identity, and the
product is below \(1\). The bound \(-\log(1-t)\le t/(1-t)\) at \(t=1/(3y)\) gives
\(1/(3y-1)\). Along the run from \(y\), Lemma 1 gives \(3g^k(y)-1=3(3/2)^ku+2>3(3/2)^ku\), so
the run contributes less than \(\tfrac1{3u}\sum_{k\ge0}(2/3)^k=1/u\). Finally the least
element of \(C\) is odd (an even least element would halve to something smaller) and its
predecessor is even (an odd predecessor \(y'\) would have \(y'<(3y'-1)/2=x_{\min}\)), so
\(x_{\min}\) is a local minimum and every \(y_i\ge x_{\min}\). \(\square\)

This is [SdW] Lemma 4 and Corollary 5 with the sign flipped. The corresponding bound on the
positive side, Hercher's Corollary 17, carries the constant \(97/54\), and [SdW] Lemma 4 has
\(\sum1/x_i\) over the minima themselves. Here it is \(1/(y_i-1)\): the odd step subtracts, so
the run's elements sit at or above the geometric progression rather than below it.

**Lemma 3 (chaining).** For consecutive local minima, \(u_{i+1}<u_i^{\delta}/2\). Hence,
with \(B(m)=(\delta^m-1)/(\delta-1)\),
\[
o=\sum_{i=1}^ma_i\ \le\ B(m)\log_2u_1-\frac{B(m)-m}{\delta-1},
\qquad K<\delta\,o,
\]
and therefore, taking \(y_1=x_{\min}\),
\[
\log_2(x_{\min}-1)\ >\ L_{\min}(K,m):=\frac1{B(m)}\Bigl(\frac K\delta+\frac{B(m)-m}{\delta-1}\Bigr).
\]

*Proof.* \(y_{i+1}=M_i/2^{r_i}\) with \(r_i\ge1\) and \(M_i\le u_i^{\delta}+1\) (Lemma 1), so
\(u_{i+1}=M_i/2^{r_i}-1\le(u_i^{\delta}+1)/2-1<u_i^{\delta}/2\). Taking logarithms,
\(\log_2u_{i+1}<\delta\log_2u_i-1\), and by induction
\(\log_2u_i\le\delta^{i-1}\log_2u_1-(\delta^{i-1}-1)/(\delta-1)\). Summing over \(i\) and
using \(a_i=v_2(u_i)\le\log_2u_i\) gives the bound on \(o\); \(K\log2<o\log3\) is
\(\Lambda>0\). Solving for \(\log_2u_1\) gives \(L_{\min}\). \(\square\)

The chaining is tight on the \(17\)-cycle: \(u_1=16\), \(u_2=40\), and \(16^{\delta}/2=40.5\).
It is [SdW] Lemma 6 in the variable \(u\): their \(x_{i+1}<b^{\delta}x_i^{\delta}\) with
\(b=(1+X_0^{-1})/2^{1/\delta}\) becomes exact here, with no \(X_0\) in the constant, because
\(u=y-1\) is the conjugated variable itself. The bound on \(o\) is their Lemma 7 read as a
lower bound on the least element rather than as an upper bound on \(\Lambda\).

**Lemma 4 (admissible lengths).** If an \(m\)-cycle has \(x_{\min}\ge X_0\), then
\(0<\Lambda<m/(X_0-1)<\log3\), so \(o=\lceil Kx\rceil\) and
\[
\Lambda(K)=\log3\,\bigl(1-\{Kx\}\bigr)<\frac m{X_0-1}.
\]
The lengths \(K\) satisfying this are exactly those with \(1-\{Kx\}<m/((X_0-1)\log3)\), and
below any bound they are enumerated exactly by the three-gap walk: from the two least
returns \(q_1,q_2\) of \(\{Kx\}\) into the two windows, found among the convergents and
semiconvergents of \(x\), every further member is the previous one plus \(q_1\), \(q_2\) or
\(q_1+q_2\). The least member is Crandall's lower bound on the length.

*Proof.* Lemma 2 and \(x_{\min}\ge X_0\). The walk is the classical three-distance structure
of \(\{Kx\}\) and is the laboratory's `three_gap_walk`, checked against a direct scan at
coarse thresholds. \(\square\)

[SdW] reach the same set from above and below: Lemma 10 and Corollary 11 give the least
convergent denominator the floor admits, and Lemma 16 caps the length through the largest
partial quotient below that index. The exact enumeration replaces both, and, at their floor,
lands exactly on their Lemma 17 (Section 5).

## 4. Rhin's ceiling

**Proposition 5.** Rhin's Proposition [R87, p. 160, (7)] states that for integers
\(u_0,u_1,u_2\) with \(H=\max(|u_1|,|u_2|)\ge2\),
\[
|u_0+u_1\log2+u_2\log3|\ \ge\ H^{-13.3},
\]
with no further constant. For an \(m\)-cycle of length \(K\ge2\) with an even step,
\((u_0,u_1,u_2)=(0,-K,o)\) and \(H=K\), so
\[
2^{L_{\min}(K,m)}\ <\ x_{\min}-1\ <\ \frac m{\Lambda}\ \le\ m\,K^{13.3}.
\]
Let \(K_3(m)\) be the least integer such that \(2^{L_{\min}(K,m)}\ge2m\,K^{13.3}\) for every
\(K\ge K_3(m)\). Then every \(m\)-cycle has \(K<K_3(m)\).

*Proof.* Lemmas 2 and 3 with Rhin's bound. The function
\(K\mapsto L_{\min}(K,m)-13.3\log_2K-\log_2(2m)\) is convex, negative at \(K=2\), and has a
larger root; beyond it the function increases, so \(K_3(m)\) is well defined, and the doubled
constant covers \(m/\Lambda+1\). \(\square\)

Rhin's bound is the one external input of this note. It is a theorem, not a hypothesis; it
is external in the sense that nothing here re-proves it and no Lean statement carries it.
[SdW] Lemma 12 states it as \(\Lambda>e^{-13.3(0.46057+\log K)}\) in their odd count \(K\),
which is (7) at \(H=K+L<1.000001\,\delta K\) with \(0.46057=\log\delta\); the laboratory's
Paper A and its cycle-gap branch carried that form, weaker by the factor \(\delta^{13.3}=457\)
when \(H\) is the length itself, and it is (7) that is used here. The general two-logarithm
bound of Laurent–Mignotte–Nesterenko [LMN] would replace \(13.3\) by an exponent in the
thousands at these heights and is not competitive; Rhin's constant is specific to \(\log2\)
and \(\log3\).

## 5. The theorem

**Theorem 6.** Let \(X_0=2^{44}\). For every \(1\le m\le49\) and every length \(K<K_3(m)\)
with \(\Lambda(K)<m/(X_0-1)\),
\[
2^{L_{\min}(K,m)}\ \ge\ \frac m{\Lambda(K)} .
\]
Consequently, with Rhin's bound, the \(3n-1\) map has no \(m\)-cycle with \(1\le m\le49\)
whose least element is at least \(2^{44}\), and by the floor no \(m\)-cycle with \(m\le49\)
other than \((5,7,10)\) and the cycle at \(17\).

*Proof.* An \(m\)-cycle above the floor has \(K<K_3(m)\) by Proposition 5, its length is
admissible by Lemma 4, and Lemmas 2 and 3 give \(2^{L_{\min}(K,m)}<x_{\min}-1\le m/\Lambda(K)\),
contradicting the display. The display is a finite exact computation: for each \(m\) the
admissible lengths below \(K_3(m)\) are enumerated by Lemma 4 and each is tested at eighty
digits. For \(m\le43\) there is no admissible length below \(K_3(m)\) at all, so the
conclusion there rests on Lemmas 2 and 4 and Proposition 5 alone. For \(44\le m\le49\) the
admissible lengths exist and fail the display by the margins of Table 1. \(\square\)

**Table 1.** Rows at the floor \(2^{44}\). "Margin" is
\(\max\log_2\bigl(m/(\Lambda(K)\,2^{L_{\min}})\bigr)\) over the admissible \(K<K_3(m)\), negative
when every admissible length is excluded.

| \(m\) | \(m/(X_0-1)\) | \(K_3(m)\) | admissible \(K<K_3\) | least admissible | margin (bits) |
|---|---|---|---|---|---|
| 1 | \(5.7\cdot10^{-14}\) | 156 | 0 | — | — |
| 2 | \(1.1\cdot10^{-13}\) | 496 | 0 | — | — |
| 5 | \(2.8\cdot10^{-13}\) | 3927 | 0 | — | — |
| 10 | \(5.7\cdot10^{-13}\) | 57130 | 0 | — | — |
| 20 | \(1.1\cdot10^{-12}\) | 8393108 | 0 | — | — |
| 30 | \(1.7\cdot10^{-12}\) | 1094917646 | 0 | — | — |
| 40 | \(2.3\cdot10^{-12}\) | 134716197552 | 0 | — | — |
| 44 | \(2.5\cdot10^{-12}\) | 913288455198 | 1 | 757698850864 | \(-399.7\) |
| 45 | \(2.6\cdot10^{-12}\) | 1472498495288 | 3 | 757698850864 | \(-236.4\) |
| 47 | \(2.7\cdot10^{-12}\) | 3824399289666 | 9 | 757698850864 | \(-68.3\) |
| 48 | \(2.7\cdot10^{-12}\) | 6160750059302 | 15 | 757698850864 | \(-27.3\) |
| 49 | \(2.8\cdot10^{-12}\) | 9921719447061 | 25 | 757698850864 | \(-1.4\) |
| 50 | \(2.8\cdot10^{-12}\) | 15974496522786 | 41 | 539722056247 | \(+22.4\) |

The exclusion at \(m=49\) hangs on \(1.4\) bits at \(K=757698850864\); any weakening of the
constants, in Rhin's form or in the chaining, would move the theorem to \(m\le48\). At
\(m=50\) the template leaves four lengths,
\[
539722056247,\quad757698850864,\quad975675645481,\quad1193652440098,
\]
with \(22.4\), \(15.0\), \(7.8\) and \(2.9\) bits of room; they are the near-convergent
lengths of \(x\) on the expanding side, and they are the input for the fifth step of the
template, lattice reduction on the \(m\) local minima, which this note does not perform.

**Table 2.** What each floor buys, by the same tables.

| floor | \(m\) excluded through | first open \(m\) | lengths left at the first open \(m\) |
|---|---|---|---|
| \(2^{40}\) | 44 | 45 | 72448885240, 82888745831, 93328606422, 103768467013 |
| \(2^{44}\) | 49 | 50 | 539722056247, 757698850864, 975675645481, 1193652440098 |
| \(2^{48}\) | 49 | 50 | 1193652440098 |
| \(301\cdot2^{50}\) ([SdW]'s floor) | 63 | 64 | 766512153894657 |
| \(2^{60}\) | 68 | 69 | 9881527843552324 |
| \(2^{68}\) | 82 | 83 | 6094436882695943503, 6724555128221608268 |

Two comparisons calibrate the method, on the other sign and so as plausibility checks rather
than reproductions. At [SdW]'s own floor, \(301\cdot2^{50}\), their three stages give
\(m\le57\) by the tables, \(m\le63\) after the continued-fraction reduction and \(m\le68\)
after the lattice; the exact enumeration here gives \(63\) at that floor, which is their
Lemma 17 exactly, so the lattice stage is worth five values of \(m\) there and would be worth
a comparable amount at \(2^{44}\). Hercher's \(91\) at \(695\cdot2^{60}\) against the plain
template's \(82\) at \(2^{68}\) prices his valley arrangement at about nine values of \(m\),
which is therefore the second refinement to transpose. The floor enters only through the
admissibility threshold, in steps: \(2^{48}\) buys nothing over \(2^{44}\) except one
survivor fewer at \(m=50\).

## 6. The cycles that exist pass the same test

The inequalities were checked where they must not exclude. With the floor set at \(17\) and
\(m=2\), the admissible lengths include \(11\) and it survives the display; with the floor
at \(5\) and \(m=1\), length \(3\) survives; with the floor at \(18\), length \(11\) no
longer appears, since the \(17\)-cycle's least element is below it. The cycle equation of
Lemma 2 is verified in exact rationals on all three cycles, and Lemma 1's run length and
identity on every odd \(y<4000\).

## 7. What this note does not do

It excludes no Juggler cycle. The Juggler's cycle words are, letter for letter, the words of
the negative Collatz cycles (Paper A, Section 5.9, and `CollatzBridge.lean`), but a word
shape does not transport a realization, so a \(3n-1\) \(m\)-cycle theorem constrains Juggler
cycle words and nothing more. It does not settle the \(3n-1\) cycle question, \(m\) being
bounded, and it says nothing about divergence on either map. Its fifth step, lattice
reduction at \(m=50\) and beyond, is not done; Hercher's refinement is not transposed; the
Eliahou-type lattice of admissible periods on this side is not written. Lemmas 1–3 are
elementary and are not yet in Lean; the negative-side finance and word shape that surround
them are (`neg_cycle_finance`, `neg_prefix_noncontracting`, `neg_cycle_expanding`).

## 8. Verification

`python -m research.juggler_sequence.negative_m_cycles` recomputes both tables in a few
seconds and writes `data/research/juggler/negative_m_cycles/summary.json`;
`tests/research/juggler_sequence/test_negative_m_cycles.py` checks Lemma 1 on every odd
\(y<4000\), the cycle equation on the three cycles, the tightness of Lemmas 1 and 3 at \(17\),
that the known cycles pass, that \(K_3\) is a ceiling, that the three-gap walk agrees with a
direct scan, and that the archived tables reproduce. The floor's certificate is with the
branch `negative_floor_3x1`.

## References

- [H23] C. Hercher, "There are no Collatz m-cycles with m ≤ 91," *J. Integer Seq.* 26 (2023),
  Article 23.3.5. arXiv:2201.00406.
- [S07] J. L. Simons, "A simple (inductive) proof for the non-existence of 2-cycles of the
  3x+1 problem," *J. Number Theory* 123 (2007), 10–17. Section 6 treats \(3x-1\).
- [S08] J. L. Simons, "On the (non-)existence of m-cycles for generalized Syracuse
  sequences," *Acta Arith.* 131 (2008), 217–254.
- [SdW] J. L. Simons and B. M. M. de Weger, "Theoretical and computational bounds for
  m-cycles of the 3n+1-problem," *Acta Arith.* 117 (2005), 51–70.
- [Si05] J. L. Simons, "On the nonexistence of 2-cycles for the 3x+1 problem," *Math. Comp.*
  74 (2005), 1565–1572.
- [R87] G. Rhin, "Approximants de Padé et mesures effectives d'irrationalité," *Séminaire de
  Théorie des Nombres, Paris 1985–86*, Progress in Mathematics 71, Birkhäuser, 1987,
  155–164.
- [LMN] M. Laurent, M. Mignotte and Y. Nesterenko, "Formes linéaires en deux logarithmes et
  déterminants d'interpolation," *J. Number Theory* 55 (1995), 285–321.
- [Si03] M. K. Sinisalo, "On the minimal cycle lengths of the Collatz sequences," preprint,
  University of Oulu, 2003.
- [E93] S. Eliahou, "The 3x+1 problem: new lower bounds on nontrivial cycle lengths,"
  *Discrete Math.* 118 (1993), 45–56.
- [St77] R. P. Steiner, "A theorem on the Syracuse problem," *Proc. 7th Manitoba Conf.
  Numerical Math.* (1977), 553–559.
- [L85] J. C. Lagarias, "The 3x+1 problem and its generalizations," *Amer. Math. Monthly* 92
  (1985), 3–23; and the annotated bibliographies, arXiv:math/0309224 and math/0608208.
- [A] P. Cochin, "Lower Bounds for Cycle Lengths in the Juggler Map" (Paper A), Section 5.9,
  and `formal/Problems/Juggler/CollatzBridge.lean`, in the repository
  https://github.com/sneakyweasel/btlab/.
- OEIS A037084, comment on the \(3x-1\) verification to \(10^8\).
