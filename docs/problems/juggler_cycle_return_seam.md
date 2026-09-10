# The initialized return seam survives exact integer guards

Status: **CLOSE** the finite initialized-seam obstruction.
Completed 10 September 2026. This dossier is the canonical written source
for this gate. No actual cycle or new cycle bound is obtained.

## Problem

Does the complete initialized return-seam rectangle remove the two-sign
mixed-cell configurations that survived the exact-predecessor gate?

## Exact statement

Use \(O(n)=\lfloor n^{3/2}\rfloor\), \(E(n)=\lfloor\sqrt n\rfloor\),
and the chronological words \(A=OOE\), \(B=OE\). The new theorem constructs,
for every integer \(u\ge2^{32}\) with \(u\equiv65\pmod {2048}\), the
four actual guarded return equations

\[
 A(a)=t,\qquad B(b_\pm)=m,\qquad A(m)=z,\qquad B(t)=w.
\]

Both alternatives share the same \(m,M,t,q,w,z\), have odd \(w<z\),
lie in the same numerical cubic band, satisfy the established scalar
seam and DC/LR gap inequalities, and retain opposite mixed-loss signs.
They do not supply complete rank adjacency, selected C/W transfer arrays,
counts satisfying all cycle finance and grid restrictions, or a cycle.

## Current literature

**PROJECT-SPECIFIC internal extension; no external priority claim.**
The exact predecessor condition and earlier two-face family are in
[the preceding dossier](juggler_cycle_cut_predecessors.md). The return
machinery and actual-cycle bounds are recorded in
[Paper A](../theory/juggler_finite_dynamics_note.md),
[direction changes](juggler_cycle_direction_change.md),
[later returns](juggler_cycle_later_returns.md), and
[negative knowledge](../negative_knowledge.md). The construction below
closes the next finite local obstruction; it does not strengthen those
actual-cycle theorems. No external theorem or parity heuristic is used.

## Branch budget

- **Target:** the entire initialized guarded return rectangle, with its
  known scalar constraints, on the existing two-face family.
- **Novelty hypothesis:** the two missing OE passages impose incompatible
  absolute cells or parity requirements.
- **Falsifier:** one symbolic infinite congruence subfamily supplies all
  missing guards and still permits both mixed-loss signs.
- **Already killed by?:** predecessor-only signs, independent local cells,
  fixed-modulus summaries and relaxed real-cell averages are closed. This
  gate imposes the entire initialized rectangle instead.
- **Existing machinery:** exact square cells, OOE/OE return geometry,
  integer polynomial congruences and transported floor-loss estimates.
- **Maximum Phase-0 scope:** one polynomial parameter refinement and the
  three fixed controls \(u=2^{32}+65,2^{40}+65,2^{64}+65\); no source,
  orbit, rank, floor, or residue census.
- **Promotion criterion:** a new necessary obstruction for actual cycles.
- **Stop criterion:** CLOSE this finite rectangle as a sign obstruction if
  it survives. Do not automatically append another local word.

## Balanced-ternary formulation

All parameters, state values, square remainders, polynomial coefficients
and rational bounds have exact balanced-ternary representations.

## Why BT may be relevant

No representation advantage is used or claimed.

## Candidate operations / invariants

The lift \(r=u^4+2\) turns the four missing floor expressions into rational
polynomials plus small residual terms. Exact square inequalities certify
the floors; a single polynomial congruence class certifies their parities.

The one registered theorem is **J-cycle-return-seam-family**, labelled
**EXACT — HUMAN PROOF**. This repository tier describes an AI-assisted
written proof, cross-checked by other AI agents. It does not mean
independent human review or Lean verification.

## Experiments

The [runner](../../src/research/juggler_sequence/cycle_return_seam.py),
[tests](../../tests/research/juggler_sequence/test_cycle_return_seam.py),
and [record](../../data/research/juggler/cycle_return_seam/summary.json)
use exactly \(u=2^{32}+65,2^{40}+65,2^{64}+65\). They check twelve distinct
actual edges across the two alternative faces, exact polynomial output
formulas, parities, full numerical order, seam inequalities and the
inherited height margins. All three minima exceed both DC/LR cutoffs.

    python -m research.juggler_sequence.cycle_return_seam

The fifteen new coefficient certificates (eight cell margins and seven
ordering differences) establish positivity on the infinite ray
\(u\ge2^{32}\); the three fixed evaluations are implementation controls,
not the proof of the infinite family.

## Conjectures

No new conjecture file. The actual no-cycle problem remains open.

## Counterexamples

The theorem refutes a universal mixed-loss sign derived from the displayed
initialized rectangle, even with its exact integer predecessors, every
shown source guard and the current scalar bounds. The two faces are
alternative finite configurations; their union is not asserted to be a
cycle or part of one cycle. The fixed regressions are linked above.

## Formalization

No new Lean theorem is claimed. Existing actual-cycle results retain their
coverage in [Paper A's formalization map](../theory/juggler_finite_dynamics_formalization.md).
The new polynomial family and its quantitative compatibility are written
proofs only.

## Results

**Theorem (J-cycle-return-seam-family).** The family defined in Results
1–2 has the exact guarded edges and order proved in Results 3–4,
the initialized rectangle and scalar compatibility in Results 5–6,
and both inherited mixed-loss signs. Its scope is finite local
compatibility; Result 7 identifies the missing global matching.

### 1. Parameter and inherited family

Take any integer

\[
u\ge2^{32},\qquad u\equiv65\pmod {2048},\qquad r=u^4+2.
\]

Then \(r\ge67\), \(r\equiv3\pmod {16}\). Define

\[
\begin{aligned}
a&=r^8+8,&h&=r^{12}+12r^4,\\
M&=r^{18}+18r^{10}+54r^2-1,&t&=r^9+9r-1,\\
b_-&=r^8+4r^4-4r^2+2,&b_+&=b_-+2,\\
m&=r^6+3r^2-3,&q&=(8r^9+36r^5-36r^3+27r-1)/8,\\
s_-&=m^2+6r^2-1,&s_+&=s_-+3r^4+5.
\end{aligned}
\]

The [cut-predecessor dossier](juggler_cycle_cut_predecessors.md) proves all eight distinct actual edges in

\[
a\xrightarrow O h\xrightarrow O M\xrightarrow E t,
\qquad b_\pm\xrightarrow O s_\pm\xrightarrow E m\xrightarrow O q.
\]

It also proves

\[
m<a<b_-<b_+<t<q<h<m^2<s_-<s_+<M<m^3,
\quad m^3-M>2m^2,
\]

and, with \(\Delta(h,s)=s^{3/4}-h^{3/4}-(q-t)\),

\[
\Delta(h,s_-)<-3/4,\qquad\Delta(h,s_+)>2r-1>r.
\]

The refinement below changes none of these states or claims. Both earlier large-minimum cutoffs hold throughout the new domain: \(m>u^{24}\ge2^{768}\).

### 2. Four explicit integer polynomial outputs

Define integer polynomials

\[
N_t(u)=\sum_{j=0}^{13}c_{t,j}u^{54-4j},\quad
N_q(u)=\sum_{j=0}^{13}c_{q,j}u^{54-4j},
\]

\[
N_w(u)=\sum_{j=0}^{6}c_{w,j}u^{27-4j},\quad
N_z(u)=\sum_{j=0}^{6}c_{z,j}u^{27-4j},
\]

with the following complete coefficients. Blank cells indicate terms absent from the shorter polynomials.

| \(j\) | \(c_{t,j}\) | \(c_{q,j}\) | \(c_{w,j}\) | \(c_{z,j}\) |
|---:|---:|---:|---:|---:|
| 0 | 1024 | 1024 | 1024 | 1024 |
| 1 | 27648 | 27648 | 13824 | 13824 |
| 2 | 345600 | 345600 | 79488 | 79488 |
| 3 | 2649600 | 2649600 | 251712 | 251712 |
| 4 | 13910400 | 13917312 | 471960 | 475416 |
| 5 | 52859520 | 52990848 | 519156 | 538164 |
| 6 | 149768640 | 150878016 | 302841 | 332649 |
| 7 | 320932800 | 326410560 | | |
| 8 | 521529624 | 538994520 | | |
| 9 | 637558728 | 674986824 | | |
| 10 | 574337844 | 628592724 | | |
| 11 | 366609348 | 418520196 | | |
| 12 | 154023975 | 184637853 | | |
| 13 | 36239049 | 45676467 | | |

Set

\[
H_t=(N_t-840)/1024,\qquad H_q=(N_q-584)/1024,
\]

\[
w=(N_w-517)/1024,\qquad z=(N_z-565)/1024.
\]

All four are integers, with \(H_t,H_q\) even and \(w,z\) odd. Indeed, the exact modular data are

| Numerator | \(N(1)\bmod2048\) | \(N'(1)\bmod32\) | \(N(65)\bmod2048\) |
|---|---:|---:|---:|
| \(N_t\) | 1096 | 28 | 840 |
| \(N_q\) | 1352 | 20 | 584 |
| \(N_w\) | 1605 | 31 | 1541 |
| \(N_z\) | 629 | 15 | 1589 |

For any integer polynomial,
\(N(1+64)\equiv N(1)+64N'(1)\pmod {2048}\), since \(64^2\) is divisible by 2048. This derives the successful lift directly. Polynomial congruence then gives the same residues for every \(u\equiv65\pmod {2048}\). Subtracting the four displayed shifts gives respectively residues \(0,0,1024,1024\) modulo 2048, proving the assertions.

### 3. Exact cells without an asymptotic error assumption

The four new edges are

\[
\boxed{t\xrightarrow O H_t\xrightarrow E w,
\qquad q\xrightarrow O H_q\xrightarrow E z.}
\]

Here is an explicit coefficient-dominance proof. Expand the indicated rational polynomials using the coefficient table. In the table below, \(A\) and \(d\) mean that the leading term is \(Au^d\); \(k\) bounds the degree of every negative term; \(S\) bounds the sum of the absolute values of all negative coefficients. All nonleading positive terms can be discarded in a lower bound.

| Polynomial | \(d\) | \(A\) | Negative terms |
|---|---:|---:|---|
| \(t^3-H_t^2\) | 54 | \(105/64\) | none |
| \((H_t+1)^2-t^3\) | 54 | \(23/64\) | \(k\le52,\ S<2^{35}\) |
| \(q^3-H_q^2\) | 54 | \(73/64\) | none |
| \((H_q+1)^2-q^3\) | 54 | \(55/64\) | \(k\le52,\ S<2^{35}\) |
| \(H_t-w^2\) | 27 | \(517/512\) | only a constant of magnitude less than 2 |
| \((w+1)^2-H_t\) | 27 | \(507/512\) | \(k\le26,\ S<2^{18}\) |
| \(H_q-z^2\) | 27 | \(565/512\) | only a constant of magnitude less than 1 |
| \((z+1)^2-H_q\) | 27 | \(459/512\) | \(k\le26,\ S<2^{18}\) |

For \(u\ge2^{32}\), the O upper margins divided by \(u^{54}\) exceed
\(23/64-2^{35}/u^2\ge23/64-2^{-29}>0\).
The E upper margins divided by \(u^{27}\) exceed
\(459/512-2^{18}/u\ge459/512-2^{-14}>0\).
The other four margins are positive immediately from their table entries. Thus every indicated lower and upper square inequality is strict.

The definitions in Result 2, and these finite rational polynomial computations, constitute the proof; the motivating Laurent expansions are not assumed to have a particular error sign or magnitude. The canonical probe expands these eight margins exactly from the displayed numerator coefficients and records the coefficient budgets. It checks a weighted negative-coefficient bound at \(u=2^{32}\), valid uniformly on the whole ray. The proof needs only the displayed elementary bounds.

Since \(t,q\) are odd by the inherited family, \(H_t,H_q\) are even by the modular calculation, and \(w,z\) are odd, all four new source guards and both retained endpoint parities are genuine.

### 4. Position of the new states

The same exact expansion certifies

\[
\boxed{m<w<z<a,\qquad m^2<H_t<H_q<M.}
\]

For completeness the seven difference polynomials have the following leading terms:

| Difference | Leading term |
|---|---|
| \(w-m\) | \(u^{27}\) |
| \(z-w\) | \((27/8)u^{11}\) |
| \(a-z\) | \(u^{32}\) |
| \(H_t-m^2\) | \(u^{54}\) |
| \(H_t-s_+\) | \(u^{54}\) |
| \(H_q-H_t\) | \((27/4)u^{38}\) |
| \(M-H_q\) | \(u^{72}\) |

In each row the total absolute value of the negative coefficients is less than \(2^{22}\), and their degrees are at least three below the leading degree. Consequently its normalized negative part is less than \(2^{22}/u^3\le2^{-74}\), proving positivity. These seven full expansions are also in the exact certificate record.

In fact the retained gap has the especially short exact expression

\[
\boxed{d=z-w=(216u^{11}+1188u^7+1863u^3-3)/64.}
\]

Thus it is positive, even, and grows as \((27/8)u^{11}\). The expression and the parity proof concern the same integer outputs; no rounding interval is substituted for an actual endpoint.


### 5. The complete rectangle and scalar inequalities

The four new cells join the inherited eight distinct cells to give

\[
\begin{gathered}
a\xrightarrow O h\xrightarrow O M\xrightarrow E t
 \xrightarrow O H_t\xrightarrow E w,\\
b_\pm\xrightarrow O s_\pm\xrightarrow E m
 \xrightarrow O q\xrightarrow O H_q\xrightarrow E z.
\end{gathered}
\]

Thus all guards of \(A(a)=t\), \(B(b_\pm)=m\), \(A(m)=z\), and
\(B(t)=w\) hold. There are twelve distinct actual edges when both
alternative faces are retained. Both alternatives share the same
\(m,M,t,q,w,z\) and retain the opposite signed losses from Result 1.

The order can be sharpened to include both new peaks:

\[
\boxed{m<w<z<a<b_-<b_+<t<q<h<m^2<s_-<s_+<H_t<H_q<M<m^3.}
\tag{RS1}
\]

Indeed \(t>r^9\) gives
\(H_t>r^{27/2}-1>4r^{12}>(m+1)^2>s_+\) for \(r\ge67\).
The other new insertions follow from Result 4. All displayed lower states
are odd and all displayed upper states \(s_-,s_+,H_t,H_q,M\) are even.
This establishes numerical order, not selected rank adjacency.

The elementary identity \(\lfloor\sqrt{\lfloor x\rfloor}\rfloor
=\lfloor\sqrt{x}\rfloor\) for \(x\ge0\) gives
\(w=\lfloor t^{3/4}\rfloor\) and \(z=\lfloor q^{3/4}\rfloor\)
from the exact new cells.

For clarity, the following quantitative bounds hold for every parameter
of the preceding family \(r\ge67\), \(r\equiv3\pmod {16}\), when
\(w=\lfloor t^{3/4}\rfloor\), \(z=\lfloor q^{3/4}\rfloor\),
whether or not its new guards hold:

\[
2r^{11/4}<d=z-w<4r^{11/4},\qquad d>m^{11/24}.
\tag{RS2}
\]

To prove them, use the exact formula bounds

\[
r^6<m<2r^6,\quad t>r^9,\quad
4r^5<q-t<\tfrac92r^5,\quad q<\tfrac32r^9.
\]

For the lower gap comparison,
\(8(q-t-4r^5)=4r^5-36r^3-45r+7>0\).
Since \((3/2)^{1/4}<9/8\), the decreasing derivative of \(x^{3/4}\)
gives

\[
\tfrac83r^{11/4}<q^{3/4}-t^{3/4}<\tfrac{27}{8}r^{11/4}.
\]

Two floors alter the difference by less than one. Both allowances fit
strictly inside (RS2) for \(r\ge2\). Finally
\(m^{11/24}<2^{11/24}r^{11/4}<2r^{11/4}<d\).

In particular \(d>8\). Put
\(\gamma=243/256\), \(\rho=3^{41}/2^{65}\),
\(\sigma=13/128+1-\rho\). The exact comparisons

\[
\tfrac{26240}{59049}<1,\qquad
\tfrac{13}{128}<\tfrac{11}{24},\qquad
0<\sigma<\tfrac18<\tfrac{11}{24}
\]

show that (RS2) exceeds the established DC/LR lower bounds

\[
d>\tfrac{26240}{59049}m^{13/128},\qquad d>\tfrac25m^\sigma.
\tag{RS3}
\]

Here \(\sigma<1/8\) follows from \(3^{41}>125\cdot2^{58}\).
The sharper DC expression
\((57344/59049)m^{13/128}-(32/27)m^{13/256}\) is less than
\(m^{13/128}\), hence is also below \(d\). Even the unreduced LR
coefficient \(7609/(20480\gamma^2\rho)\) is less than one, using
\(\gamma>3/4\), \(\rho>125/128\), and \(11250>7609\).
The even positive gap meets the discrete requirements \(d\ge6,8\).
All scale restrictions hold throughout the selected subfamily.

For either face the mixed AB/BA upper comparison also has room. Set
\(\kappa(m)=(27/32)m^{-5/32}\). Then

\[
b_\pm-a>3r^4,\qquad m^{-5/32}>\tfrac12r^{-15/16}.
\]

For \(r\ge64\), \(r^{5/16}\ge2^{15/8}>7/2\), with the last
comparison equivalent to \(2^{23}>7^8\). Therefore

\[
\kappa(m)(b_\pm-a)
>\tfrac{81}{64}r^{49/16}
>\tfrac{567}{128}r^{11/4}>4r^{11/4}>d.
\tag{RS4}
\]

This is stronger than the required upper bound with additive \(9/8\).
There is also the more precise, compatible consequence of the existing
word estimate:

\[
d<\tfrac{27}{32}a^{-5/32}(b_\pm-a)
   +1+\tfrac{35}{16}a^{-1/4}.
\tag{RS5}
\]

For its proof, every proper state of the AB trace from \(a\), namely
\(h,M,t,H_t\), is at least \(a\). Its proper tail exponents are
\(9/16,3/8,3/4,1/2\), summing to \(35/16\), so the established
one-sided loss bound gives the displayed error. The upper trace is
\(BA(b_\pm)=z\); it has the same exponent \(27/32\) and needs only
its unconditional ideal-power upper bound. Thus the proof does not
assume that AB and BA are the same word.

### 6. Exact seam cells and height compatibility

The genuine new guards imply the stronger integer cells used in the
existing cycle-height deductions:

\[
t^3+2\le[w(w+2)]^2,\qquad
M+2\le(t+1)^2,\qquad z^8\le m^9.
\tag{RS6}
\]

For the first, odd \(t\) and even \(H_t\) give
\(t^3+2\le(H_t+1)^2\). Even \(H_t\), odd \(w\), and its upper
E cell give \(H_t\le(w+1)^2-2\), hence \(H_t+1\le w(w+2)\).
The second follows in the same way from even \(M\) and odd \(t\).
For the last, the lower cells give
\(q^2\le m^3\), \(H_q^2\le q^3\), \(z^2\le H_q\), so
\(z^8\le H_q^4\le q^6\le m^9\).

The inherited deficit \(m^3-M>2m^2\) exceeds the previously excluded
upper-strip deficits \(m^{15/8}\), \(\tfrac12m^{253/128}\), and
\(\tfrac12m^\theta\), where
\(\theta=381/128-3^{41}/2^{65}<2\). By (RS1), adding the four new
states changes neither numerical extremum. These are scalar
compatibility statements; they do not construct the actual C/W
transfer arrays used to derive the cycle bounds.

### 7. The global matching that the rectangle does not supply

The terminal suffix begins with OE: it starts as OE and every suffix
update appends a word on the right. The two new OE traces therefore
complete the original retained seam, rather than an arbitrary extra
local word. In a hypothetical actual cycle the five pairs

\[
(a,b)\xrightarrow O(h,s)
\xrightarrow{OE/EO}(t,q)
\xrightarrow O(H_t,H_q)\xrightarrow E(w,z)
\]

must be adjacent in the same sorted cycle. Their numerical order and
exact cells establish none of those full-cycle adjacency assertions.
In particular the two alternative faces in this construction are not
asserted to coexist in one selected cycle.

Let \(Y\) denote the hypothetical retained odd set in \([m,t]\).
Complete periodic placement requires simultaneous ordered, fully guarded
bijections

\[
A:Y\cap[m,a]\longrightarrow Y\cap[z,t],\qquad
B:Y\cap[b,t]\longrightarrow Y\cap[m,w].
\tag{RS7}
\]

There must be no retained states in \((a,b)\) or \((w,z)\). The source
sets partition the same \(Y\), as do their image sets. The A source and
target intervals overlap because \(z<a\); their interior selections
cannot be made independently. Every return must keep its interior
states in the same cubic band and outside the retained section until
its final E, and the complete matching must have the primitive rotation.
The finite family supplies no such \(Y\), no compatible rank counts,
and no global finance or grid certificate.

Providing all that data would construct an actual cycle by expanding
the return words. Merely restating existence or nonexistence of \(Y\)
is consequently a reformulation of the problem, not a new obstruction.
No matching enumeration or capacity search is performed here.

## Open questions

The complete selected integer P/OE/EO/Q passage and actual cyclic
matching remain open. Positive or negative mixed loss at the finite
rectangle does not control the remaining prefix amplification and suffix
contraction. The regime \(M\ge m^3\) is outside this gate.

## Decision

**CLOSE** the finite initialized-seam obstruction. A single symbolic
congruence refinement supplies every displayed actual guard and both
mixed-loss signs, while satisfying the existing scalar inequalities.
It proves no new actual cycle, height, period, descent, or no-cycle result.
No further local word is appended after this result.

Exactly one best next question: **can the common retained-set matching
force an interval's required population to exceed its exact guarded
integer preimage capacity, beyond the existing spacing and grid bounds?**
For example, any actual \(Y\) and interval \(J\subseteq[m,w]\) must obey

\[
\#(Y\cap J)\le
\#\{x\in[b,t]\cap(2\mathbb Z+1):
 x\text{ follows B},\ B(x)\in J,\ O(x)\le M\}.
\]

A useful result must obtain a strict deficit from the simultaneous
cycle constraints, rather than recover that necessary counting identity.
Its feasibility is unproved. No capacity computation or new gate is
opened by this decision.

## Publication assessment

Status: **STRUCTURAL**. One exact scoped infinite-family theorem, with
AI-assisted written proofs and three fixed controls. Independent human
review and Lean verification remain outstanding. This Phase-0 gate
updates no Paper A or release copy. The certified floor \(350000000\)
and period lower bound \(780239\) are unchanged.


## Capacity follow-up

The next bounded test is recorded in the canonical
[preimage-capacity dossier](juggler_cycle_preimage_capacity.md).
It distinguishes raw predecessor multiplicity from distinct supported
targets, derives the shared-set capacities, and closes ordinary Hall or
guard-free counting as an additional obstruction. No strict deficit in
the exact shared support is proved; the global matching question remains
open. The infinite seam family above is neither promoted to a cycle nor
claimed to satisfy all these additional shared-set capacities.
