# The \(OEOEE\) production, and the elementary \((OE)^{k-1}OEE\) family

Status: **reduction complete, constants pending** (4 September 2026).
The word \(OEOEE\) was listed in
[juggler_contagion_exponent_calculus.md](juggler_contagion_exponent_calculus.md)
as "needs localized Paper B depth 2". That label is **wrong**: the
nesting in \(OEOEE\) is removable exactly, and the whole count reduces
to classical one-variable exponential sums. No Paper B estimate, no
localization of Theorems 4.4/4.7, and — unlike Appendix C's \(OOEEE\)
— no exceptional-set argument are needed.

Consequence, if the two half-estimates are written out with constants:
\(\lambda^{**}\) rises from \(0.4480\) to \(0.4801\)
**unconditionally**, and \(\lambda^{***}\) from \(0.5392\) to
\(0.5665\). Section 8 iterates the same construction into a family
\(V_k=(OE)^{k-1}OEE\) whose geometry does not degrade with \(k\) and
whose terms telescope **exactly** to the ideal depth-two recursion,
root \(0.4927\) — closing the whole gap the fate note records as a
dynamical averaging problem. It also shows why \(OEOEOE\) is *not* the
next word: its binding layer has relative length \(\tfrac14\), where
the phase is essentially linear and the measured worst-case
cancellation is nil. Verification and census:
[`tests/research/juggler_sequence/test_oeoee_production.py`](../../tests/research/juggler_sequence/test_oeoee_production.py).

## 1. The exact chain

**Lemma 1 (EXACT — HUMAN PROOF).** Let \(n\) be odd with
\(\mathrm{word}_5(n)=OEOEE\), and put \(w=\lfloor n^{3/4}\rfloor\).
Then

\[
J^2(n)=w,\qquad J^3(n)=\lfloor w^{3/2}\rfloor,\qquad
J^4(n)=\lfloor w^{3/4}\rfloor,\qquad J^5(n)=\lfloor w^{3/8}\rfloor,
\]

and consequently, for \(m'\ge 1\),

\[
J^5(n)=m'\iff w\in[m'^{8/3},(m'+1)^{8/3})
\iff n\in J(m'):=[m'^{32/9},(m'+1)^{32/9}) .
\]

*Proof.* \(J(n)=\lfloor n^{3/2}\rfloor\) is even, so
\(J^2(n)=\lfloor\sqrt{\lfloor n^{3/2}\rfloor}\rfloor=\lfloor n^{3/4}\rfloor=w\)
by the transparent nesting \(\lfloor\sqrt{\lfloor y\rfloor}\rfloor=\lfloor\sqrt y\rfloor\)
(fate note Lemma 2.2, Lean `sqrt_sqrt_eq_iff`). \(w\) is odd, so
\(J^3(n)=\lfloor w^{3/2}\rfloor\); it is even, so
\(J^4(n)=\lfloor\sqrt{\lfloor w^{3/2}\rfloor}\rfloor=\lfloor w^{3/4}\rfloor\)
by the same identity; it is even, so
\(J^5(n)=\lfloor\sqrt{\lfloor w^{3/4}\rfloor}\rfloor=\lfloor w^{3/8}\rfloor\).
The fiber statement is \(\lfloor w^{3/8}\rfloor=m'\iff m'^{8/3}\le w<(m'+1)^{8/3}\),
and \(\lfloor n^{3/4}\rfloor\) lies in that window exactly when \(n\)
lies in its \(4/3\)-power. \(\square\)

Two things are worth noting. First, **the fiber is exact** — there is
no exceptional set, in contrast with Appendix C's \(OOEEE\), where
\(\lfloor v^{1/4}\rfloor=\lfloor n^{9/16}\rfloor\) fails on a set that
must be bounded by Erdős–Turán. Second, at scale \(P=n\),

\[
|J(m')|=\tfrac{32}9m'^{23/9}\bigl(1+O(1/m')\bigr)\asymp P^{23/32},
\qquad \rho_{OEOEE}=\tfrac9{32},
\]

the same fiber length as \(OOEEE\), so the criterion
\(\rho_w\le\tfrac12\) of the calculus note is met with room.

## 2. The block decomposition

**Lemma 2 (EXACT — HUMAN PROOF).** Write
\(\psi(y)=(-1)^{\lfloor y\rfloor}\), \(w=w(n)=\lfloor n^{3/4}\rfloor\),
and
\[
\Lambda_1(w)=(-1)^{w},\qquad
\Lambda_2(w)=\psi(w^{3/2}),\qquad
\Lambda_3(w)=\psi(w^{3/4}),\qquad
\psi_1(n)=\psi(n^{3/2}).
\]
Then for odd \(n\),
\[
16\cdot\mathbf 1[\mathrm{word}_5(n)=OEOEE]
=(1+\psi_1)(1-\Lambda_1)(1+\Lambda_2)(1+\Lambda_3).
\]
Moreover \(\Lambda_1,\Lambda_2,\Lambda_3\) are functions of \(w\)
alone, hence **constant on each level set**
\(I_w=\{n:\lfloor n^{3/4}\rfloor=w\}=[w^{4/3},(w+1)^{4/3})\cap\mathbb Z\),
an interval with
\(|I_w|=\tfrac43w^{1/3}(1+O(1/w))\asymp P^{1/4}\). Only \(\psi_1\)
varies inside a block.

*Proof.* By Lemma 1 the four parity conditions of the word are
\(J(n)\) even, \(w\) odd, \(\lfloor w^{3/2}\rfloor\) even,
\(\lfloor w^{3/4}\rfloor\) even, whose indicators are
\((1+\psi_1)/2\), \((1-\Lambda_1)/2\), \((1+\Lambda_2)/2\),
\((1+\Lambda_3)/2\). The level sets are the stated intervals because
\(\lfloor n^{3/4}\rfloor=w\iff w^{4/3}\le n<(w+1)^{4/3}\). \(\square\)

**This is where the nesting goes.** The word's two \(O\)-steps are
separated by an \(E\)-step, and the \(E\)-step's transparent nesting
turns \(J^2\) into the *exact* function \(\lfloor n^{3/4}\rfloor\) of
\(n\). Everything downstream is then a function of the single integer
variable \(w\), in which \(\Lambda_2=\psi(w^{3/2})\) and
\(\Lambda_3=\psi(w^{3/4})\) are \(\psi\) of **smooth monomials**, not
of nested floors. A word with two consecutive \(O\)'s — \(OOEEE\) —
has no such change of variable: there
\(\lfloor\lfloor n^{3/2}\rfloor^{3/2}\rfloor\) is genuinely nested and
Paper B is unavoidable.

## 3. The count

**Proposition 3.** Let \(\mathcal O(m')=\{n\ \text{odd}\in J(m'):\
\mathrm{word}_5(n)=OEOEE\}\). Then
\[
|\mathcal O(m')|=\tfrac1{16}\#\{n\ \text{odd}\in J(m')\}
+O\bigl(|J(m')|\,P^{-1/8+\varepsilon}\bigr),
\qquad P=m'^{32/9}.
\]

*Reduction.* Expand Lemma 2. The main term is
\(\tfrac1{16}\#\{n\ \text{odd}\in J(m')\}\); the other fifteen sign
sums split by whether \(\psi_1\) occurs. Write \(Y=|J(m')|\asymp P^{23/32}\),
\(H=|I_w|\asymp P^{1/4}\), so the number of blocks is
\(\mathcal N=Y/H\asymp P^{15/32}\), and \(w\) ranges over an interval
\(K\) of length \(L=\mathcal N\asymp W^{5/8}\) at scale
\(W=m'^{8/3}=P^{3/4}\).

*Half A — the eight terms without \(\psi_1\).* These are
\(\sum_{w\in K}\omega(w)\Lambda_1^{b}\Lambda_2^{c}\Lambda_3^{d}\) with
\(\omega(w)=\#\{n\ \text{odd}\in I_w\}\asymp W^{1/3}\) smooth and
monotone, and \((b,c,d)\ne 0\). Partial summation against \(\omega\)
reduces to the unweighted partial sums. Then:

- \(c=1\): Vaaler-expand \(\Lambda_2,\Lambda_3\) at truncation
  \(S=U=W^{1/8}\). The modes have phase
  \(g(w)=\tfrac s2w^{3/2}+\tfrac u2w^{3/4}+\tfrac b2w\) with
  \(g''\asymp sW^{-1/2}\), and the second-derivative test gives
  \(Ls^{1/2}W^{-1/4}+s^{-1/2}W^{1/4}\); summing against \(1/s\) and
  adding the truncation error \(L/S\) gives \(\ll LW^{-1/8+\varepsilon}\).
- \(c=0,d=1,b=0\): \(\sum_{w\in K}\psi(w^{3/4})=\sum_v(-1)^v|K_v|\)
  over the level sets \(K_v\) of \(\lfloor w^{3/4}\rfloor\), whose
  lengths \(\asymp W^{1/4}\) differ by \(O(1)\) between consecutive
  \(v\); pairing consecutive \(v\) gives \(\ll LW^{-1/4}+W^{1/4}\).
  (This is the "Term 2" pairing of fate note Proposition 3.4.)
- \(c=0,d=1,b=1\): \(f'=\tfrac12+\tfrac{3u}8w^{-1/4}\) stays at
  distance \(\ge\tfrac14\) from \(\mathbb Z\) for \(u\le W^{1/4}/8\),
  so Kusmin–Landau gives \(O(1)\); larger \(u\) falls to the
  second-derivative test as above.
- \(c=d=0,b=1\): \(\sum_{w\in K}(-1)^w=O(1)\).

With the truncation balanced instead of fixed (Section 11.4) Half A
saves \(W^{-1/6+\varepsilon}=P^{-1/8+\varepsilon}\); the fixed choice
\(S=U=W^{1/8}\) above gives only \(W^{-1/8}=P^{-3/32}\).

*Half B — the eight terms with \(\psi_1\).* Each is
\(\sum_w\Lambda_1^b\Lambda_2^c\Lambda_3^d\,T(w)\) with
\(T(w)=\sum_{n\ \text{odd}\in I_w}\psi_1(n)\), so it is at most
\(\sum_w|T(w)|\). Vaaler-expand \(\psi_1\) at truncation \(R\); with
\(S_q(w)=\sum_{n\ \text{odd}\in I_w}e(\tfrac q2n^{3/2})\), the phase has
\(f'\asymp qP^{1/2}\) varying by only \(\asymp qP^{-1/4}\) across a
block, so Kusmin–Landau gives
\(|S_q(w)|\ll\min\bigl(H,\|\alpha_q(w)\|^{-1}\bigr)\) with
\(\alpha_q(w)=\tfrac{3q}2w^{2/3}\) monotone in \(w\), stepping by
\(\asymp qP^{-1/4}\ll1\), of total variation \(\asymp qP^{7/32}\gg1\).
Summing \(|S_q|\) **directly** — not through Cauchy–Schwarz, which is
lossy here — gives \(\sum_w|S_q(w)|\ll qL+L\log P\), and the Vaaler
weights \(2/q\) cancel the \(q\): \(\sum_w|T(w)|\ll LR+Y/R\), balanced
at \(R\asymp(Y/L)^{1/2}\), i.e. \(\sum_w|T(w)|\ll(LY)^{1/2}\log P\).
Against \(Y\) this saves \(P^{-1/8+\varepsilon}\). \(\square\)

The needed saving is any fixed power; both halves clear it, and they
**tie** at \(P^{-1/8}\) (Section 11).

**Status.** Lemmas 1 and 2 are exact and Lean-adjacent (they use only
`sqrt_sqrt_eq_iff`). Proposition 3's proof is complete in structure and
uses only the classical second-derivative test, Kusmin–Landau, the
Proposition 3.4 pairing, and the standard monotone-sequence sum; **the
explicit constants have not been computed**, so it does not yet meet
the ledger's `EXACT — HUMAN PROOF` bar. It is not a conjecture about a
new object: every ingredient is textbook, and the census of Section 6
confirms each step.

## 4. The production and its bookkeeping

**Proposition 4 (EXACT — HUMAN PROOF).** Adding the \(OEOEE\) family to
the fate note's §4.1 changes (4.2) by exactly \(+\tfrac1{27}g_A(9t/32)\).

*Proof.* An \(OEOEE\)-start has \(\mathrm{word}_2=OE\), so it lies in
the \(OE\)-fiber of \(m_2=J^2(n)\), which sits at scale \(3t/4\) and
carries the word \(OEE\) — hence is odd, hence lies in
\(A^{\rm rest}_x\), not in the \(E\)-produced part. The \(OEOEE\)
family is therefore *inside* family 3, and must be removed from it
before being re-added at the better share. By Proposition 3.4 the
\(OEE\)-produced mass at scale \(3t/4\) is
\(\tfrac13g_A(9t/32)(1+o(1))\), two-sidedly (its proof gives the
asymptotic, not merely the lower bound). Family 3 applies the \(OE\)
production at share \(\eta=\tfrac23\), coefficient \(\tfrac29\);
the new family applies it at the ideal share, coefficient \(\tfrac13\).
Hence the change is
\(\tfrac13\cdot\tfrac13-\tfrac29\cdot\tfrac13=\tfrac19-\tfrac2{27}=\tfrac1{27}\).
Disjointness from families 1, 2 and Appendix C is immediate: family 1
is even; family 2 has \(\mathrm{word}_3=OEE\) against \(OEO\); Appendix
C has \(\mathrm{word}_2=OO\) against \(OE\). \(\square\)

## 5. The new exponents

| recursion | equation | root | Tao \(C\) |
|---|---|---|---|
| \(\lambda^{**}\), current | \(2^{-\lambda}+\tfrac19(\tfrac38)^\lambda+\tfrac29(\tfrac34)^\lambda=1\) | \(0.4480\) | 20 |
| **\(+OEOEE\), unconditional** | \(\ldots+\tfrac1{27}(\tfrac9{32})^\lambda=1\) | \(\mathbf{0.4801}\) | 19 |
| \(\lambda^{***}\), Appendix C | \(\ldots+\tfrac19(\tfrac9{32})^\lambda=1\) | \(0.5392\) | 18 |
| **\(+OEOEE\) and \(OOEEE\)** | \(\ldots+\tfrac4{27}(\tfrac9{32})^\lambda=1\) | \(\mathbf{0.5665}\) | 17 |

## 6. Census (COMPUTATIONALLY VERIFIED)

At \(P=10^6,10^7,10^8\) over \(J\)-length \(Y=P^{23/32}\):

| \(P\) | nesting failures | block-constancy violations | \(OEOEE\) share | \(\sum_w|T|^2/Y\) | \(\sum_w|T|/Y\) |
|---|---|---|---|---|---|
| \(10^6\) | 0 | 0 | \(0.0488\) | \(0.58\) | \(P^{-0.196}\) |
| \(10^7\) | 0 | 0 | \(0.0608\) | \(0.54\) | \(P^{-0.198}\) |
| \(10^8\) | 0 | 0 | \(0.0633\) | \(0.57\) | \(P^{-0.193}\) |

Ideal share \(\tfrac1{16}=0.0625\); mean block length matches
\(\tfrac43P^{1/4}\) to three digits; \(\sum_w|T|^2\asymp Y\) as Half B
predicts, against the trivial \(\mathcal NH^2\asymp P^{31/32}\); and the
observed \(\sum_w|T|\) saving \(P^{-0.19}\) beats the proved
\(P^{-1/8}\).

## 7. What this does and does not change

It moves \(\lambda\) toward the \(r=1\) ceiling \(0.4927\) — the value
the calculus note assigns to production words with **no two consecutive
\(O\)'s**. Section 8 shows the family reaches that ceiling exactly.

It does **not** touch the \(r\ge2\) rungs, which need genuinely nested
floors and therefore Paper B, nor the \(K_3\) cap at \(r=4\). The
ceiling analysis of the calculus note is unchanged.

## 8. The family, and why \(OEOEOE\) is not the next word

**The layer criterion (EXACT — HUMAN PROOF).** Write a no-\(OO\) word as
\((OE)^{K}E^{\,j}\), so \(\rho=(3/4)^K2^{-j}\). Its layers are
\(w_i=\lfloor n^{(3/4)^i}\rfloor\) at scale \(P^{(3/4)^i}\), and the
\(w_i\)-range has exponent \((3/4)^i-\rho\). The deepest genuinely
nested object is \(\psi(w_{K-1}^{3/2})\), so the binding layer is
\(w_{K-1}\), whose length **relative to its own scale** is

\[
\frac{(3/4)^{K-1}-\rho}{(3/4)^{K-1}}
=1-\rho\bigl(\tfrac43\bigr)^{K-1}
=1-\tfrac34\cdot 2^{-j},
\]

**independent of \(K\)**. It is \(\ge\tfrac12\) iff \(j\ge1\).

| word | \(K\) | \(j\) | \(\rho\) | binding layer | |
|---|---|---|---|---|---|
| \(OEOEE\) | 2 | 1 | \(9/32\) | \(5/8\) | ok |
| \(OEOEOE\) | 3 | **0** | \(27/64\) | \(1/4\) | **fails** |
| \(OEOEOEE\) | 3 | 1 | \(27/128\) | \(5/8\) | ok |
| \(OEOEOEOEE\) | 4 | 1 | \(81/512\) | \(5/8\) | ok |

**Why \(j=0\) fails.** On an interval of relative length \(\tfrac14\)
the phase \(\tfrac s2w^{3/2}\) has
\(g''\cdot L^2\asymp sW^{-1/2}W^{1/2}=s\): the quadratic term
contributes \(O(s)\) in total, so for the low modes the phase is
essentially **linear**, and the sum is \(\asymp L\) whenever its
frequency lands near an integer. There is no per-\(m'\) saving, and the
contagion recursion needs one per source. Measured worst case of
\(|\sum_{w\in K}\psi(w^{3/2})|/|K|\) over 60 placements:

| scale | relative length \(1/4\) | relative length \(5/8\) |
|---|---|---|
| \(W=10^8\) | **1.000** | \(0.009\) |
| \(W=10^9\) | \(0.571\) | \(0.005\) |

So \(OEOEOE\) is not merely unproved here; the elementary route
demonstrably does not reach it. One more trailing \(E\) restores
\(5/8\).

**The family.** Put \(V_1=OEE\) and \(V_{k+1}=OE\circ V_k\), i.e.

\[
V_k=(OE)^{k-1}OEE:\quad OEE,\ OEOEE,\ OEOEOEE,\ OEOEOEOEE,\dots
\]

Then \(|V_k|=2k+1\), \(\rho_k=(3/4)^{k-1}\tfrac38\), the ideal
coefficient is \(c_k=2^{-|V_k|}/\rho_k=3^{-k}\), and every \(V_k\) has
\(j=1\), hence binding layer \(5/8\) — the geometry does not degrade
with \(k\). Each \(V_{k+1}\)-start lies in the \(OE\)-fiber of a
\(V_k\)-produced element, so the bookkeeping of Proposition 4 repeats
verbatim and the net gain is
\((\tfrac13-\tfrac29)c_k=\tfrac19c_k=3^{-(k+2)}\) at scale
\(\rho_{k+1}\).

**Theorem 5 (EXACT — HUMAN PROOF).** With \(x=2^{-\lambda}\),
\(y=(3/4)^{\lambda}\), the whole family telescopes:

\[
\underbrace{x+\tfrac19xy+\tfrac29y}_{\lambda^{**}}
+\underbrace{\sum_{k\ge1}3^{-(k+2)}x\,y^{k+1}}_{V_2,V_3,\dots}
\;=\;1
\iff
x+\tfrac13y=1 .
\]

*Proof.* The family sum is \(\tfrac1{27}xy^2/(1-\tfrac13y)\). Put
\(x=1-\tfrac y3\); then
\(\tfrac19xy=\tfrac19y-\tfrac1{27}y^2\) and the family sum is
\(\tfrac1{27}y^2\), so the left side is
\(1-\tfrac y3+\tfrac19y-\tfrac1{27}y^2+\tfrac29y+\tfrac1{27}y^2=1\).
\(\square\)

The right-hand equation is the **ideal depth-two recursion**, root
\(0.4927\). So the elementary family closes the entire depth-two gap:

| productions | \(\lambda\) |
|---|---|
| \(\lambda^{**}\) | \(0.4480\) |
| \(+V_2\) | \(0.4801\) |
| \(+V_2,V_3\) | \(0.4891\) |
| \(+V_2,\dots,V_5\) | \(0.4924\) |
| whole family | \(0.4927\) |
| whole family \(+OOEEE\) | \(0.5769\) |

This changes how the gap should be read. The fate note records
\(0.448\to0.4927\) as "a dynamical averaging problem for the low-even
set". It is not: it is an infinite sequence of elementary productions,
each upgrading one more \(V_k\)-produced piece of \(A^{\rm rest}\) from
the sweep share \(\tfrac23\) to the ideal \(1\), and each costing a
bounded amount of classical work with **the same** \(5/8\) geometry.
Any finite truncation is a theorem; the convergence is geometric.

## 9. \(V_3=OEOEOEE\) worked out

**Lemma 6 (exact chain; EXACT — HUMAN PROOF).** Let \(n\) be odd with
\(\mathrm{word}_7(n)=OEOEOEE\) and put \(w_1=\lfloor n^{3/4}\rfloor\),
\(w_2=\lfloor w_1^{3/4}\rfloor\). Then

\[
J^2=w_1,\quad J^3=\lfloor w_1^{3/2}\rfloor,\quad J^4=w_2,\quad
J^5=\lfloor w_2^{3/2}\rfloor,\quad J^6=\lfloor w_2^{3/4}\rfloor,\quad
J^7=\lfloor w_2^{3/8}\rfloor,
\]

and \(J^7(n)=m'\iff w_2\in[m'^{8/3},(m'+1)^{8/3})
\iff n\in J(m'):=[m'^{128/27},(m'+1)^{128/27})\).

*Proof.* Three applications of \(\lfloor\sqrt{\lfloor y\rfloor}\rfloor=\lfloor\sqrt y\rfloor\)
at the three \(E\)-steps that follow an \(O\)-step, and one more at the
trailing \(E\). \(\square\) Again the fiber is exact.

**Lemma 7 (three-layer decomposition).** With \(\psi_1=\psi(n^{3/2})\),
\(\Lambda_1=(-1)^{w_1}\), \(\Lambda_2=\psi(w_1^{3/2})\),
\(\Lambda_3=(-1)^{w_2}\), \(\Lambda_4=\psi(w_2^{3/2})\),
\(\Lambda_5=\psi(w_2^{3/4})\),

\[
64\cdot\mathbf 1[\mathrm{word}_7=OEOEOEE]
=(1+\psi_1)(1-\Lambda_1)(1+\Lambda_2)(1-\Lambda_3)(1+\Lambda_4)(1+\Lambda_5),
\]

where \(\psi_1\) varies inside an \(n\)-block, \(\Lambda_1,\Lambda_2\)
vary inside a \(w_1\)-block, and \(\Lambda_3,\Lambda_4,\Lambda_5\) are
functions of \(w_2\). All six are \(\psi\) of **smooth monomials of the
variable of their own layer**.

| layer | scale | block length | count | relative length |
|---|---|---|---|---|
| \(n\) | \(P\) | — | \(Y=P^{101/128}\) | — |
| \(w_1\) | \(P^{3/4}\) | \(P^{1/4}\) | \(P^{69/128}\) | \(23/32\) |
| \(w_2\) | \(P^{9/16}\) | \(P^{3/16}\) | \(P^{45/128}\) | \(\mathbf{5/8}\) |

**Proposition 8.** \(|\mathcal O(m')|=\tfrac1{64}\#\{n\ \text{odd}\in J(m')\}
+O(|J(m')|P^{-3/32+\varepsilon})\).

*Reduction.* Four cases, by which layer the surviving factors live on.

| terms | method | saving |
|---|---|---|
| \(\psi_1\) present | Cauchy–Schwarz over \(w_1\), Kusmin–Landau per \(n\)-block (Section 3, Half B verbatim) | \(P^{-1/8}\) |
| \(\Lambda_2\) present, \(\psi_1\) absent | Cauchy–Schwarz over \(w_2\), Kusmin–Landau per \(w_1\)-block, Vaaler truncation \(S=H_2^{1/3}=P^{1/16}\) balancing \(\sum|{\rm inner}|^2\ll\omega^2L_2H_2S\) against the error \(L_2\omega H_2/S\) | \(P^{-3/32}\) |
| only \(\Lambda_1\) | pairing of consecutive \(w_1\) against the slowly varying weight | \(P^{-3/16}\) |
| only \(w_2\)-factors | one-variable sum at relative length \(5/8\) — Section 3 Half A verbatim, with \(W_2=P^{9/16}\) | \(P^{-3/32}\) |

Two cases tie at the binding \(P^{-3/32}\) (Section 11).
\(\square\)

**Proposition 9 (bookkeeping).** A \(V_3\)-start lies in the \(OE\)-fiber
of a \(V_2\)-produced element, so adding the family changes (4.2) by
\((\tfrac13-\tfrac29)c_2=\tfrac19\cdot\tfrac19=\tfrac1{81}\) at scale
\(\rho_3=\tfrac{27}{128}\), giving \(\lambda=0.4891\) with \(V_2\), and
\(0.5740\) alongside Appendix C. It is disjoint from families 1–4 and
from \(V_2\) (\(\mathrm{word}_5=OEOEO\) against \(OEOEE\)); its
two-sidedness is inherited from Proposition 3, so \(V_3\) is
conditional on \(V_2\).

### Census, and its limits

At \(P=10^6,10^7,10^8\) over \(Y=P^{101/128}\): **zero** chain failures,
**zero** fiber failures, **zero** block-constancy violations at either
layer; block lengths match \(\tfrac43P^{1/4}\) and \(\tfrac43P^{3/16}\)
to three digits; \(\sum_{w_1}|T|^2\approx0.56\,Y\) and
\(\sum_{w_2}|{\rm inner}|^2\approx\omega^2L_1\), both as predicted and
two orders below the trivial bounds.

The share is the one place the census is weak. It reads \(0.01748\),
\(0.01510\), \(0.01231\) against \(\tfrac1{64}=0.015625\) — drifting,
not converging. The cause is visible in the conditional shares: at
\(P=10^8\) the first four conditions give \(0.5003,0.4996,0.4940,0.5022\),
and only the last two — \(J^5\) even and \(w_3\) even — deviate
(\(0.4504\), \(0.4406\)). Those live on the \(w_2\) and \(w_3\) layers,
which a single fiber samples at only \(L_2=P^{45/128}=365\) and
\(P^{27/128}=49\) points. Aggregating over \(60\) fibers moves the
share from \(-21\%\) to \(-4.8\%\); and the functions themselves carry
no bias — over \(2\cdot10^5\) consecutive \(w\) at those scales,
\(\lfloor w^{3/2}\rfloor\) is even with share \(0.5087,0.5099\) and
\(\lfloor w^{3/4}\rfloor\) with \(0.4999,0.5000\).

So the deviation is a small-sample effect in the deepest layers, and it
sits well inside the proved error term: \(P^{-3/32}=0.18\) at
\(P=10^8\). Reaching \(10\%\) would need \(P\approx10^{10.7}\), so
**this census does not confirm the constant \(\tfrac1{64}\)** — it
confirms the structure. \(V_2\)'s census, where the binding layer is the
only deep one, does converge.

## 10. \(V_4=OEOEOEOEE\), and the saving law

**Proposition 10 (the saving law).** For \(V_k\) the layers are
\(n,w_1,\dots,w_{k-1}\) with \(w_i\) at scale \(P^{(3/4)^i}\) and block
length \(H_i=\tfrac13(3/4)^i\); the binding layer is \(w_{k-1}\), always
at relative length \(\tfrac58\). The sign sums fall into \(k-1\)
Cauchy–Schwarz cases — the one whose deepest varying factor sits at
layer \(i-1\) is summed over layer \(i\), with Vaaler truncation
balanced at \(3S=H_i\) and saving \(H_i/3\) — together with one
one-variable case at layer \(k-1\), of saving
\(\tfrac18(3/4)^{k-1}\). Since \(\tfrac19<\tfrac18\), the binding
saving is always the deepest Cauchy–Schwarz case:

\[
\boxed{\ \text{binding saving for }V_k\ =\ \tfrac19\bigl(\tfrac34\bigr)^{k-1}\ }
\qquad
\tfrac1{12},\ \tfrac1{16},\ \tfrac3{64},\ \tfrac9{256},\dots
\]

It decays geometrically but never vanishes, so **every \(V_k\) carries a
power saving** and every truncation of the family is a theorem.

*(Section 11 supersedes this law: summing \(|S_q|\) directly rather
than through Cauchy–Schwarz, and balancing every Vaaler truncation,
raises each Cauchy–Schwarz case from \(H_i/3\) to \(H_i/2\) and the
one-variable case from scale\(/8\) to scale\(/6\) — whereupon the two
tie and the binding saving becomes \(\tfrac16(3/4)^{k-1}\).)*

**\(V_4=OEOEOEOEE\).** \(\rho_4=\tfrac{81}{512}\),
\(Y=P^{431/512}\), ideal share \(2^{-8}=\tfrac1{256}\),
\(c_4=3^{-4}=\tfrac1{81}\).

| layer | scale | block length | count | relative length |
|---|---|---|---|---|
| \(n\) | \(P\) | — | \(P^{431/512}\) | — |
| \(w_1\) | \(P^{3/4}\) | \(P^{1/4}\) | \(P^{303/512}\) | \(101/128\) |
| \(w_2\) | \(P^{9/16}\) | \(P^{3/16}\) | \(P^{207/512}\) | \(23/32\) |
| \(w_3\) | \(P^{27/64}\) | \(P^{9/64}\) | \(P^{135/512}\) | \(\mathbf{5/8}\) |

Six cases, savings \(P^{-1/8},P^{-3/32},P^{-9/128}\) (the three
Cauchy–Schwarz ones), \(P^{-9/128}\) (the one-variable case at
\(W_3\)), and two pairing cases; binding \(P^{-9/128}\). A
\(V_4\)-start lies in the \(OE\)-fiber of a \(V_3\)-produced element, so
the net gain is \(\tfrac19c_3=\tfrac1{243}\) at
\(\rho_4=\tfrac{81}{512}\), giving \(\lambda=0.4916\) with \(V_2,V_3\)
and \(0.5761\) alongside Appendix C.

### Census: structure yes, constant no

At \(P=10^6,10^7,10^8\) over \(Y=P^{431/512}\): **zero** chain failures,
**zero** fiber failures, **zero** block-constancy violations across all
three \(w\)-layers, at every scale. The first four conditional shares
are \(0.5000,0.5000,0.4978,0.5013\) at \(P=10^8\).

The constant is out of reach, and by a wider margin than for \(V_3\).
The deepest layers are sampled at
\(L_3=P^{135/512}\) and \(L_4=P^{81/512}\) points — that is \(50\) and
\(7\) distinct values at \(P=10^8\) — so the last four conditional
shares swing (\(0.4767,0.5110,0.5701,0.4104\)) and the overall share
reads \(0.001512,\ 0.000984,\ 0.003554\) against
\(\tfrac1{256}=0.003906\): non-monotone, i.e. noise, not convergence.
Getting \(100\) distinct \(w_4\) values needs \(P\approx10^{12.7}\).

This is the expected shape of the census for deep \(V_k\) and is not
evidence against Proposition 10: the exact identities and the block
structure — which is what the proof actually uses — are confirmed
without a single failure, and the shares that a single fiber *can*
sample are all \(0.50\).

## 11. The constants

Writing them out changed the exponents. Two steps in Sections 3 and 10
were lossy: Half B went through Cauchy–Schwarz, and the Vaaler
truncations were fixed rather than balanced. Summing \(|S_q|\) directly
and balancing every truncation gives

\[
\boxed{\ \text{binding saving for }V_k=\tfrac16\bigl(\tfrac34\bigr)^{k-1}
=\tfrac18,\ \tfrac3{32},\ \tfrac9{128},\ \tfrac{27}{512},\dots\ }
\]

replacing \(\tfrac19(3/4)^{k-1}\), and the two binding cases now **tie
exactly**: the deepest Cauchy–Schwarz case gives \(H_{k-1}/2\) and the
one-variable case gives \(\tfrac16(3/4)^{k-1}\), and
\(H_{k-1}/2=\tfrac12\cdot\tfrac13(3/4)^{k-1}\) is the same number. This
does not move \(\lambda\): the exponents depend on the coefficients
\(2^{-2k}\) and the bookkeeping, not on the savings, which only have to
be positive powers.

### 11.1 Toolkit

- **(T1) Vaaler** — Paper B Lemma 3.5 as printed: \(\psi(x)=V_J(x/2)+O(\Delta_J(x/2))\)
  with \(|a_q|\le\min(1,2/|q|)\) and \(\Delta_J\ge0\) whose coefficients,
  constant term included, are \(\le 1/(J+1)\).
- **(T2) Kusmin–Landau.** \(f'\) monotone with \(\lVert f'\rVert\ge\delta\):
  \(|\sum e(f)|\le\cot(\pi\delta/2)\le 2/(\pi\delta)\). (Checked:
  \(\max_{0<\delta\le1/2}[\cot(\pi\delta/2)-2/(\pi\delta)]=-5.2\cdot10^{-4}\).)
- **(T3) Second-derivative test**, derived from (T2). If
  \(\lambda\le|f''|\le\alpha\lambda\) on an interval of length \(M\) and
  \(0<\lambda\le\pi/4\), then
  \(|\sum e(f)|\le(\alpha\lambda M+1)\bigl(2.26\lambda^{-1/2}+1\bigr)\).
  *Proof.* Split by \(\lfloor f'\rfloor\); \(f'\) crosses at most
  \(\alpha\lambda M+1\) integers. Discard \(\{\lVert f'\rVert<\delta\}\),
  of length \(\le2\delta/\lambda\), i.e. \(\le2\delta/\lambda+1\)
  integers; apply (T2) elsewhere. The bracket is
  \(2/(\pi\delta)+2\delta/\lambda+1\), minimised at
  \(\delta=(\lambda/\pi)^{1/2}\) with value
  \(4/\sqrt{\pi\lambda}+1\le2.26\lambda^{-1/2}+1\). \(\square\)
  (Checked on \(4000\) random instances of \(f=\tfrac q2x^{3/2}\):
  worst \(|{\sum}|/\text{bound}=0.52\).)
- **(T4) Block counting.** If \(L\) consecutive blocks tile an
  \(\alpha\)-range of length \(V\), each of length \(\le\delta\), then
  for each \(j\ge0\) at most \(4(V+1)\) blocks meet the annulus
  \(\{jδ\le\lVert\alpha\rVert<(j+1)\delta\}\).
- **(T5) Pairing.** \(|g(v{+}1)-g(v)|\le\Delta\), \(|g|\le G\):
  \(\bigl|\sum_{v\le V}(-1)^vg(v)\bigr|\le V\Delta/2+G\).

### 11.2 Sizes

\((8/3)m'^{5/3}-1\le L\le(8/3)(m'+1)^{5/3}+1\);
\(|\omega(w)-\tfrac23w^{1/3}|\le\tfrac32\); \(Y=\sum_w\omega(w)\), with
\(Y\ge\tfrac{16}9m'^{23/9}-1\).

### 11.3 Half B

With \(\alpha_q(w)=\tfrac{3q}2w^{2/3}\), block length
\(\le\delta_q=qm'^{-8/9}\) and range
\(V_q\le\tfrac{8q}3(m'+1)^{7/9}\), (T2)+(T4) give

\[
\sum_{w}|S_q(w)|\le 4(V_q+1)\omega_{\max}
+\tfrac8{\pi\delta_q}(V_q+1)\bigl(1+\log\tfrac1{2\delta_q}\bigr)
\le\tfrac{64}9qm'^{5/3}+6.79\,m'^{5/3}\bigl(1+\tfrac89\log m'\bigr).
\]

Feeding this through (T1) with truncation \(R\),

\[
\sum_w|T(w)|\ \le\ 35.5\,R\,m'^{5/3}
+27.2\,m'^{5/3}\bigl(1+\tfrac89\log m'\bigr)(1+\log R)+\frac Y{R+1},
\]

and \(R=0.224\,m'^{4/9}\) gives \(\le15.9\,m'^{19/9}+\text{logs}
=8.9\,Y\,m'^{-4/9}+\text{logs}\). Note \(m'^{-4/9}=P^{-1/8}\).

### 11.4 Half A

Partial summation splits \(\omega=\tfrac23w^{1/3}+\eta\), \(|\eta|\le\tfrac32\);
the \(\eta\)-part costs \(\le\tfrac32L\le3Ym'^{-8/9}\), negligible.
For the smooth part: with \(\Lambda_2\) present, (T1)+(T3) at
\(\lambda=\tfrac{3s}8W^{-1/2}\), \(W=m'^{8/3}\), give
\(9.85\,S^{1/2}m'^{17/9}+Y/S\); balancing at \(S=0.318\,m'^{4/9}\)
yields \(\le11.2\,m'^{19/9}=6.3\,Y\,m'^{-4/9}\). The remaining cases use
(T5): \(\Lambda_3\) alone gives \(\le0.89m'^{14/9}\)
(\(=0.5\,Ym'^{-1}\)); \(\Lambda_1\Lambda_3\) gives \(\le1.33m'^{17/9}\);
\(\Lambda_1\) alone \(\le2.67m'^{5/3}\).

### 11.5 The bound

Eight \(a=1\) terms at \(8.9\), four \(a=0,c=1\) terms at \(6.3\), the
rest lower order:

\[
\bigl|16|\mathcal O(m')|-Y\bigr|\ \le\ 100\,Y\,m'^{-4/9}(1+\log m')^2,
\qquad\text{i.e.}\qquad
|\mathcal O(m')|=\tfrac{Y}{16}\bigl(1+\theta\bigr),\ \
|\theta|\le 100\,m'^{-4/9}(1+\log m')^2 .
\]

The log-mass follows: \(\sum_{n\in\mathcal O(m')}1/n\ge
\tfrac1{9m'}\bigl(1-|\theta|-\tfrac{32}{9m'}\bigr)\), which is
Proposition 4's input with an explicit \(\varepsilon\).

### 11.6 Measured margins

| \(m'\) | \(Y\) | \(16|\mathcal O|-Y\) | \(/(Ym'^{-4/9})\) | share |
|---|---|---|---|---|
| 60 | 63574 | \(-2230\) | 0.216 | 0.06031 |
| 120 | 369795 | \(11005\) | 0.250 | 0.06436 |
| 200 | 1358503 | \(-30279\) | 0.235 | 0.06111 |
| 250 | 2399746 | \(-4770\) | 0.023 | 0.06238 |

against \(\tfrac1{16}=0.0625\). The envelope holds with the measured
ratio never above \(0.25\), so the constant \(100\) above is generous by
some \(400\times\); Half B's bound is met with a factor \(8\) of slack
and Half A's with \(30\)–\(500\).

**Status.** The chain is explicit end to end and every step is
numerically checked, but it is a single pass: the constants have not
been audited the way Paper B's were, and (T3), the sizes in 11.2 and the
assembly in 11.5 are mine rather than the corpus's. I would not move
Theorem 1's printed exponent to \(0.4801\) on this alone — the right
next step is an audit pass in the style of the Paper B ledger, after
which the promotion is a bookkeeping change.
