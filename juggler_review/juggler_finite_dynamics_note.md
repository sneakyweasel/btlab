---
title: "Cycle Financing and Near-Convergent Diophantine Obstructions in the Juggler Map"
author: Philippe Cochin
date: 1 September 2026
keywords:
  - Juggler map
  - Juggler sequence
  - floor-power maps
  - cycle financing
  - integer dynamics
  - cycles
header-includes:
  - \usepackage{amsmath,amssymb}
  - \AtBeginDocument{\author{Philippe Cochin \\ \texttt{philippe@cochin.fr}}}
---

## Abstract

The Juggler map is the nonlinear integer map
\[
J(n)=
\begin{cases}
\lfloor\sqrt n\rfloor,&n\ \text{even},\\
\lfloor n^{3/2}\rfloor,&n\ \text{odd}.
\end{cases}
\]
It is conjectured that every positive integer eventually reaches \(1\).
This paper does not prove that conjecture. It proves period lower
bounds for a hypothetical nontrivial cycle, once a verified descent
floor is given.

We develop a cycle-financing inequality for this floor-power map.
Exact integer cells give a one-step logarithmic defect; cycle
minimality lets that defect be unrolled against the cycle
minimum; the formal surplus \(3^o-2^L\) must then be paid by a
finite accumulated budget. For a hypothetical cycle of length
\(L\) with \(o\) odd steps and minimum \(n\),
\[
n\log n\cdot(3^o-2^L)\le L\cdot 3^o.
\]
This inequality is the main theorem; every numerical period
bound below is an instantiation of it, or of its coupled
walk-charge refinement, at a certified descent floor.
As a consequence, combining the inequality with the known
verification through \(10^6\) yields \(L\ge 25781\); at the
laboratory-certified descent floor \(N_0=26254995\) the same
table yields \(L\ge 50508\). The novelty is not a new
computational record; it is that implication. A walk-charge
envelope — transport of the floor losses to a
reduced base, identification of the extremal exponent walk as a
rotation word, and a Denjoy--Koksma bound over certified
Ostrowski blocks, census-free on the window
\([50508,301994)\) — then extends the exclusion at the
laboratory floor: any nontrivial cycle has period at least
\(176251\). The main numerical result evaluates the same
certified kill criterion at a second certified floor,
\(N_0=162849448\), on the surviving lengths — including those
beyond the census-free window: any nontrivial Juggler cycle has
period at least \(478245\). We
also prove that every nontrivial cycle contains at least four
even steps, and hence has period at least eleven; that bound
uses no descent floor. The core lemmas are formalized in
Lean 4; the descent floors and the per-length kill tables are
independently certified computations, and the paper does not
claim to be formally verified as a whole.

**2020 Mathematics Subject Classification.** 11B83, 37P99, 11Y55.

## 1. Introduction

The Juggler sequence was introduced by Pickover [1,2] as an
interesting variation of the Collatz problem. Pickover's later
exposition is Chapter 45 of [2], pp. 102--106. The object of study
is the one-step map \(J:\mathbb N\to\mathbb N\) displayed in the
abstract. The *Juggler sequence* starting at \(n\) is the trajectory of
iterates \(n,\,J(n),\,J^2(n),\ldots\). The On-Line Encyclopedia of
Integer Sequences records the one-step values of \(J\) as A094683
[3] and the number of steps to reach \(1\) (when that occurs) as
A007320 [4]; those catalogue entries are not theorems of this
paper.

The trajectory of \(3\) is \(3,5,11,36,6,2,1\). The trajectory of \(37\)
already peaks at \(24906114455136\). Universal arrival at \(1\)
remains an open conjecture. This paper does not prove that
conjecture. It proves period lower bounds for a *hypothetical*
nontrivial cycle, once a verified descent floor is given.

Throughout, \(\mathbb N=\{1,2,3,\ldots\}\). Write \(J^k\) for the
\(k\)-fold iterate, and write \(\lfloor x\rfloor\) for the integer
part of a real \(x\ge 0\): discard the fractional part. Thus
\(\lfloor 5.196\ldots\rfloor=5\) and \(\lfloor 6\rfloor=6\). The
floor is applied after every branch of \(J\), not once at the end
of a walk.

The map combines a contracting even branch with an expanding odd
branch,
\[
E(n)=\lfloor n^{1/2}\rfloor,\qquad
O(n)=\lfloor n^{3/2}\rfloor,
\]
so \(J(n)=E(n)\) when \(n\) is even and \(J(n)=O(n)\) when \(n\) is
odd.

**Trajectory.** The *trajectory* of \(n\in\mathbb N\) is the sequence of
values \(n_0=n\), \(n_{i+1}=J(n_i)\) (also called an orbit in some
dynamics texts).

**Word.** The *word* of the first \(k\) steps is the length-\(k\)
string \(w\in\{O,E\}^k\) with \(w_i=O\) if \(n_i\) is odd and
\(w_i=E\) if \(n_i\) is even. The word is the list of branch
labels, not the list of values. The integer \(k\) is any finite
prefix length; the definition does not assume that the trajectory
reaches \(1\).

**Ideal exponent.** A word of length \(k\) with \(o\) odd letters
has ideal exponent \(3^o/2^k\). Ignoring floors, those letters
would multiply the start by that ratio. Floors make the actual
image smaller.

**Realized word.** A word \(w\) is *realized* at \(n\) when the
first \(\lvert w\rvert\) parities of the trajectory of \(n\) are exactly
the letters of \(w\). Equivalently: a formal string over
\(\{O,E\}\) is an itinerary only when some start actually follows
those branches. That is what is meant by: a word is available only
when the trajectory realizes those parities. Floors are applied after
every letter of a realized word.

**Cell.** The map \(J\) is not invertible. For \(m\in\mathbb N\),
the *cell* (or one-step preimage) of \(m\) is the set
\[
J^{-1}(m)=\{k\in\mathbb N:J(k)=m\}.
\]
An even image has a whole interval of even parents; an odd image
has at most one odd parent (Lemma 3.1). A cell is not a
cellular-automaton cell and not an approximation.

**Lemma 1.1 (three fates).**
Let \(n\in\mathbb N\). The trajectory of \(n\) does exactly one of the
following: (i) some iterate equals \(1\); (ii) some iterate
\(m\ge 2\) returns, and the trajectory is eventually periodic through a
cycle containing \(m\); (iii) the trajectory is unbounded. In
particular, a bounded infinite trajectory is eventually periodic.

*Proof.* The map \(J\) is a well-defined function
\(\mathbb N\to\mathbb N\), so the forward trajectory is an infinite
sequence in \(\mathbb N\). If some term equals \(1\), we are in
(i); note \(J(1)=1\). If the trajectory is unbounded, we are in (iii).
If the trajectory is infinite and bounded, the pigeonhole principle
supplies a repeated value \(m\); uniqueness of the successor
\(J(m)\) then forces a cycle, which is (ii) unless \(m=1\), already
covered by (i). \(\square\)

The lemma lists the only logical possibilities. It does not assert
which fate occurs for a given start, and it is not a termination
theorem.

| Object | Meaning |
| --- | --- |
| \(J\) | the one-step map |
| \(E\), \(O\) | even and odd branches |
| trajectory | the sequence of values |
| word | a finite string in \(\{O,E\}\) of parities |
| realized word | the trajectory actually follows those letters |
| \(3^o/2^k\) | ideal exponent of a word of length \(k\) with \(o\) odd letters |
| \(J^{-1}(m)\) | cell: the set of one-step preimages of \(m\) |
| \(N_0\) | a verified descent floor (a computational input) |
| CycleMin | a minimum-based rotation of a cycle word |

The mechanism is the interaction of three elementary facts:
exact integer cells, a logarithmic defect, and cycle
minimality. Exact cells give a one-step logarithmic defect;
cycle minimality lets the defect be unrolled against the cycle
minimum; the formal surplus \(3^o-2^L\) must then be paid by a
finite accumulated budget. That is Theorem 4.4:
\[
n\log n\cdot(3^o-2^L)\le L\cdot 3^o.
\]
The inequality \(\log(1+u)\le u\) is the only analytic input; it
is not the content of the theorem.

Write \(N_0\) for a *verified descent floor*: every start
\(2\le n\le N_0\) reaches \(1\). A floor is an input, not the
result. Two instances are used. The base instance is
\(N_0=10^6\), reported by Weisstein [5] and recomputed here by
exact first-passage. Combined with Theorem 4.4 it gives
\[
\text{known verification through }10^6
\ +\
\text{this inequality}
\quad\Rightarrow\quad
L\ge 25781.
\]
The laboratory instance is \(N_0=26254995\), certified by the
same exact first-passage method (Proposition 5.1); the same
table then gives \(L\ge 50508\) (Theorem 5.2), and the
walk-charge envelope of Section 5 amplifies it to
\(L\ge 176251\) (Theorem 5.9). The main numerical result is
Corollary 5.10: at the second certified floor
\(N_0=162849448\), the same kill criterion — a certified
computation of the Theorem 5.9 comparison, evaluated directly
on the surviving lengths, including those beyond the
\([50508,301994)\) window of Theorem 5.8 — gives
\(L\ge 478245\). The census-free window theorem itself stops at
\(301994\); the second-floor extension is a certified
evaluation of the same criterion, not an extension of that
window. The architecture is
\[
\text{envelope}
\to
\text{cycle minimum}
\to
\text{finance}
\to
n_{\max}(L)
\to
N_0
\to
L\ge 25781\ \text{at}\ 10^6,
\]
extended at the laboratory floor by
\[
\text{transport}
\to
\text{hug adversary}
\to
\text{word identity}
\to
\text{Denjoy--Koksma}
\to
\text{window}
\to
L\ge 176251.
\]
The computation supplies the endpoint \(N_0\). The mathematics
amplifies that floor to the period bound.

Roadmap. Section 2 records the power envelope and the exact
defect identity that explains it. Section 3 classifies
minimum-based cycle words and proves that every nontrivial
cycle has at least four even letters. Section 4 records the
excursion necklace of a minimum-based word, unrolls the cell
logarithm around that minimum, obtains the finance inequality,
and applies it at the known floor \(10^6\). The necklace is
the geometry of the unroll, not a fourth main theorem. A
run-type packing of the same identity is a supporting
refinement; the arithmetic of the leftover lengths is
secondary. Section 5 certifies the laboratory floor
\(26254995\), replaces the length-only charge by a coupled
exponent-walk charge, identifies its extremal word as a
rotation word, and proves a census-free envelope for every
length in the window \([50508,301994)\); the resulting kill
table gives the period bound \(176251\), and a certified
evaluation of the same kill criterion at a second certified
floor raises it to \(478245\) (Corollary 5.10). Section 6
records limitations.

A nonempty realized word \(w\) with
\(J^{|w|}(n)=n\) is a *cycle word*. The unique fixed point is \(1\);
a cycle is *nontrivial* when it contains some \(n\ge 2\). A cycle
word at \(n\) is *minimum-based* when \(n\) is a cycle minimum:
\(J^j(n)\ge n\) for every \(0\le j<|w|\). Every cycle word has a
minimum-based rotation.

All exceptional sets below are *finance-survivor* sets: lengths
that a stated form of the finance inequality does not exclude at
the verified descent floor. They are not candidate cycle sets.
A survivor count "through \(X\)" is inclusive: it counts every
surviving length \(L\le X\).

### 1.0 Main results

**Contribution 1 — cycle-financing inequality.**
For a minimum-based cycle of length \(L\) with \(o\) odd steps,
\[
n\log n\cdot(3^o-2^L)\le L\cdot 3^o
\]
(Theorem 4.4). Floor defects become a quantitative bound on the
cycle minimum.

**Contribution 2 — structural word obstruction.**
Every nontrivial cycle word has at least four even letters, and
hence period at least eleven (Theorem 3.22 and Corollary 3.23).
The argument classifies the minimum-based word geometry; it is
not a raw census of words of length at most ten. This bound does
not use the verified descent floor.

**Contribution 3 — explicit conditional consequence for
hypothetical cycles.**
Combined with the independently verified descent floor \(N_0=10^6\),
there is no nontrivial Juggler cycle of length at most \(25780\).
Equivalently, any nontrivial cycle has period at least \(25781\)
(Theorem 4.6(A)). At the laboratory-certified floor
\(N_0=26254995\) the same table gives period at least \(50508\)
(Theorem 5.2).

**Contribution 4 — walk-charge envelope and the main period
bound.**
On a minimum-based cycle every state is coupled through one
closed exponent walk. Transport of the floor losses to a
reduced base (Theorem 5.3), identification of the extremal walk
as the rotation (hug) word (Theorem 5.4, Lemma 5.6), and a
Denjoy--Koksma bound over certified Ostrowski blocks
(Theorem 5.7) give a uniform envelope for every length in the
window \([50508,301994)\) (Theorem 5.8) — census-free on that
window. At the laboratory
floor the resulting kill table leaves a single finance survivor
below \(2\cdot 10^5\): any nontrivial cycle has period at least
\(176251\) (Theorem 5.9), the first laboratory instance. The
main numerical result is Corollary 5.10: at the second
certified floor \(N_0=162849448\), the same kill criterion,
evaluated as a certified computation on the additional
survivors (the window theorem itself stops at \(301994\)),
leaves only the semiconvergent fan member \(478245\): any
nontrivial cycle has period at least \(478245\).

These statements are not interchangeable. Theorem 4.4 is
the conceptual sharp inequality (constant \(1\)). Corollary 4.5
is the convenient length-only statewise bound that turns a
descent floor into a per-length exclusion. Theorem 4.6 is the
numerical certification of that bound, and it uses a conservative
coefficient \(6/5\) only as a uniform majorant; the headline
cutoff \(25781\) is not an artifact of that majorant. Theorem 4.7
is a run-type refinement of the same defect sum. The leftover
lengths through \(10^5\) are supporting material, not a second
main theorem.

### 1.1 Related work

Pickover's later exposition is Chapter 45 of [2], already cited
above. Weisstein [5]
records the map, the stopping-time sequences A094670, A094679,
A095908, and a verification of arrival at \(1\) through \(10^6\).
That verified descent floor is the computational input to
Theorem 4.6; the first-passage run of Appendix B recomputes it.
OEIS A094716 [6] records extreme heights, including the start
\(48443\) whose peak has \(972\,463\) digits. Those height
records do not bound the period.

Prasad--Prasad [7] estimate excursion and stopping constants for
juggler-like maps by a random-walk large-deviation model; those
estimates do not apply to exact cycles. Small-cycle censuses are
a standard first layer for Collatz-like maps, surveyed by
Lagarias [8,9]. Those results do not transfer: the branches of
\(J\) are floor powers rather than affine maps (Crandall [10],
Matthews--Watts [11]). In particular there is no identity of the
form \(n(2^K-3^p)=C\). A check of Pickover [1,2], Weisstein [5],
the OEIS records [3,4,6], the Prasad--Prasad estimates [7], and
the standard Collatz cycle-bound sources [8--13] found no
published explicit lower bound on the period of a nontrivial
cycle for this exact floor-power Juggler map. Informal near-miss
notes and later unverified webpage floors are not used.

Goodstein's theorem is a superficially similar statement about
natural numbers --- every Goodstein sequence terminates at \(0\)
--- which cannot be proved in Peano arithmetic [14]. No such
independence claim is made for the Juggler conjecture, and this
paper does not study Goodstein sequences.

The layers of the argument are as follows.

1. *Classical ideas, not claimed as new:* cycle financing
   (Simons--de Weger [12]); logarithmic and continued-fraction
   approximation of \(\log 2/\log 3\); cycle-word restrictions
   and leftover packaging (Eliahou [13]; Lagarias [8,9]); the
   Denjoy--Koksma inequality and Ostrowski numeration, used as
   known tools in Section 5.
2. *New object:* the exact one-step floor-power cells of \(J\).
3. *New theorem:* the Juggler-specific cycle-minimum finance
   inequality of Theorem 4.4.
4. *New consequence:* \(L\ge 25781\) at the verified descent
   floor \(10^6\).
5. *Supporting organization:* the run-packing refinement of the
   same defect sum (Theorem 4.7).
6. *New theorem:* the reduced-base transport and the uniform
   window envelope of Section 5 (Theorems 5.3 and 5.8).
7. *New consequence:* period at least \(176251\) at the
   laboratory floor \(26254995\) (Theorem 5.9), and \(478245\)
   at the second certified floor \(162849448\)
   (Corollary 5.10, by direct evaluation of the same criterion
   beyond the \(301994\) window boundary).

The
argument below is elementary and independent of the Diophantine
tools of [12]: floor-power defects are relatively \(O(1/x)\) in
logarithms, so a uniform logarithmic floor-error bound, valid
above the verified floor, excludes every length that is not a
finance-survivor for Theorem 4.4. To the best of our knowledge,
the Juggler-specific inequality and the explicit period bound it
produces are new.

**Novelty statement.**
For this nonlinear floor-power map, exact floor defects convert
into a cycle-financing inequality that forces the minimum of a
hypothetical cycle below the independently verified descent
region unless the period is at least \(25781\). Coupling the
states through the closed exponent walk and bounding the
extremal rotation word by Denjoy--Koksma over certified
Ostrowski blocks raises that period bound to \(176251\) at the
laboratory floor, census-free on an explicit window of lengths,
and — by certified evaluation of the same kill criterion on the
survivors beyond that window — to \(478245\) at the second
certified floor.

### 1.2 Verification

The arguments of Sections 2, 3, and 4 may be read without machine
assistance. The core mathematical lemmas are mechanized in Lean 4;
selected finite classifications and numerical tables are
independently certified computations. Appendix A records the Lean
names. The finite tables used by Lemmas 3.5, 3.7, 3.11 and
Theorems 3.12--3.20 are `native_decide` evaluations in the modules
named there.

**Proposition 1.3 (certified computational input).**
A machine-verifiable certificate establishes that every integer
\(2\le n\le 10^6\) reaches \(1\). Precisely: an exact-integer
first-passage run records, for each such \(n\), a finite realized
word with image strictly below the start; strong induction on
that image reaches \(1\). The longest first passage in the window
has \(253\) steps (seed \(78901\)). Weisstein [5] records the
same computational verification; the run here is an independent
recomputation. The certificate files, SHA-256 hashes, and
regeneration commands are Appendix B.

**Roles.** Independently proved: the finance inequality
(Theorem 4.4). Computational input: every \(2\le n\le 10^6\)
reaches \(1\) (this proposition), every
\(2\le n\le 26254995\) reaches \(1\) (Proposition 5.1, the
laboratory instance), and every \(2\le n\le 162849448\) reaches
\(1\) (Corollary 5.10, the second laboratory instance).
Independently recomputed: the exact
first-passage runs of Appendix B. Not proved: global
termination.

Theorem 4.6 applies Corollary 4.5 to this input and certifies
the table with the conservative coefficient \(6/5\); its
certified identity is Lean (`cycleMin_defect_finance`,
`DefectFinance.lean`), the per-length table stays a verified
computation. Theorem 4.7
is a human proof; Theorem 4.8 reuses the gap table under that
packing. Proposition 4.9 is integer arithmetic in Lean. In
Section 5, Theorem 5.7 is a human proof (Denjoy--Koksma is used
as a known tool; its per-block hypotheses — convergent quality
\(|\theta-p/q|<1/q^2\) and the block permutation — are Lean,
`theta_convergent_quality`, `theta_block_permutations`) and so
is the rotation identification in
Lemma 5.6, whose word identity itself is Lean
(`budgetedWord_eq_hugWord`); the Laplace bound of
Proposition 5.5 is Lean (`rotation_average_le`,
`rotationAverage_gap`; the ergodic identification stays
human); the transport
inequality of Theorem 5.3 (`cycleMin_transport`), the
defect-to-hug-charge consequence of §5.2
(`cycleMin_defect_le_charge`, `cycleMin_defect_le_hug_charge`),
the charge-maximisation half of Theorem 5.4
(`hug_charge_maximal`; strict uniqueness stays human), the
digit-cap step and digit scan of Theorem 5.8 (`ostroDigit_le`,
`theta_digitSum_le`, `window_digit_scan`), and the kill
template of Theorem 5.9 (`cycleMin_hug_kill_criterion`) are
Lean-verified; Theorems 5.2 and 5.9 are independently certified
computations at the laboratory floor, with the same trust
boundary as Theorem 4.6 (exact integer arithmetic plus guarded
float comparisons). This is not a claim that the paper as a
whole is formally verified.

```text
Repository:  https://github.com/sneakyweasel/balanced_ternary
Commit:      7802f78bec58c68cec92a2efb3db4a502f916277
Lean:        leanprover/lean4:v4.33.0
Mathlib:     v4.33.0 (lake-manifest rev db584cd6d46c92f209a44c0f1c829460d327499d)
Build:       lake build Problems.JugglerPaper   (from formal/)
Computation: python -m research.juggler_sequence.cycle_finance
             (parity table); run-type table in budget_opt.json
SHA-256:     Appendix B
```

The commit is the repository state that produced the finance
tables. A later editorial commit of this text does not change
those hashes.

## 2. Envelope

Let \(\mathcal B=\{E,O\}\). A finite word \(w\in\mathcal B^*\) is
*realized* at \(n\in\mathbb N\) when the successive parities of the
trajectory of \(n\) are exactly the letters of \(w\). Write \(J^{|w|}(n)\)
for the endpoint after those letters, and \(\#O(w)\) for the number
of odd letters. When \(w\) is realized, this endpoint is the
\(|w|\)-fold iterate.

**Theorem 2.1 (fixed-word monotonicity).**
If \(n\le m\) and both realize \(w\), then
\(J^{|w|}(n)\le J^{|w|}(m)\).

*Proof.* Induct on \(w\). The empty word is immediate. The images
after a common realized prefix remain ordered, and both current
states realize the same next letter. The even branch is the
monotone integer square root; the odd branch is \(x\mapsto x^3\)
followed by the integer square root. \(\square\)

The realizing set of a fixed word need not be an interval: \(OE\) is
realized at \(7\) and at \(11\) but not at \(9\).

**Theorem 2.2 (finite-word power envelope).**
If \(w\) is realized at \(n\) and \(m=J^{|w|}(n)\), then
\[
m^{2^{|w|}}\le n^{3^{\#O(w)}}.
\]

*Proof.* The empty word is the equality \(n\le n\). Suppose a
realized prefix of length \(\ell\) with odd count \(o\) ends at
\(x\) and satisfies \(x^{2^\ell}\le n^{3^o}\), and the next letter
is realized.

If the next letter is even, then \(J(x)^2\le x\). Raising the
inductive bound to the second power gives
\[
J(x)^{2^{\ell+1}}=(J(x)^2)^{2^\ell}\le x^{2^\ell}\le n^{3^o}.
\]
The odd count is unchanged.

If the next letter is odd, then \(J(x)^2\le x^3\), so
\[
J(x)^{2^{\ell+1}}=(J(x)^2)^{2^\ell}\le x^{3\cdot 2^\ell}
=(x^{2^\ell})^3\le\bigl(n^{3^o}\bigr)^3=n^{3^{o+1}}.
\]
This is the claimed bound after one more odd letter. \(\square\)

**Corollary 2.3 (exponent-gap contraction).**
If \(n\ge2\), \(w\) is realized at \(n\), and
\(3^{\#O(w)}<2^{|w|}\), then \(J^{|w|}(n)<n\).

*Proof.* Let \(m=J^{|w|}(n)\) and \(k=|w|\). Theorem 2.2 gives
\(m^{2^k}\le n^{3^{\#O(w)}}\). The exponent gap and \(n\ge2\) give
\(n^{3^{\#O(w)}}<n^{2^k}\), so \(m^{2^k}<n^{2^k}\). Since \(m\ge1\),
one has \(m<n\). \(\square\)

The corollary includes familiar contracting blocks such as \(OOOEE\).
It does not prove that every start realizes some contracting word.

### 2.4 Exact floor defect

Theorem 2.2 is the inequality form of an exact identity
\[
n^{3^{\#O(w)}}=J^{|w|}(n)^{2^{|w|}}+\Delta_w(n),\qquad\Delta_w(n)\ge0.
\]
The identity, its vanishing law, and the two-term composition are
Theorems 2.4--2.6 and Corollary 2.7 in Appendix C. A mixed realized
word has \(\Delta_w(n)>0\). This explains why the envelope of
Theorem 2.2 is true, and why a mixed cycle word is formally
expanding. Theorem 4.4 uses only the nonnegativity
\(\Delta_w(n)\ge0\).

No uniform local tax exists: the relative slack of a single
letter tends to \(0\) with the state. Finance must therefore be
a global comparison, not a fixed cost per odd or even step. A
quantitative itinerary-dependent lower bound on \(\Delta_w\), or
a tighter upper bound on \(\sum 1/(x_i\log x_i)\), would improve
the period cutoff; neither is proved here.

## 3. Structural restrictions on cycle words

The role of this section in the paper is structural, not
numerical. The minimum geometry established here — the cycle
minimum is odd, prefixes to even states are superquadratic
(Theorem 3.2), a minimum-based word has the canonical run form
of Lemma 3.21b, and the last even letter lands in an explicit
cell (Lemma 3.4(iv)) — is exactly what the finance unroll of
Section 4 and the transport of Section 5 consume. The
even-count exclusion (Theorem 3.22: every nontrivial cycle word
has at least four even letters, hence period at least eleven)
is the section's own headline, but as a period bound it is
superseded the moment financing appears; it is retained because
it is floor-free. The small-period censuses (Theorems 3.6
and 3.8) are supporting. Main-text proofs are kept to the short
structural lemmas; the longer case analyses — Lemmas 3.5
and 3.7, the censuses of Theorems 3.6 and 3.8, and the family
exclusions of Theorems 3.12--3.21 — are Appendix D. After the one-step cells, a minimum-based word
has a canonical run form. There are only three even-count
regimes with \(e\le 3\); each reduces to a finite collection of
geometries \(O^aEO^bEO^cE\). Those geometries are eliminated by
a next-square obstruction, by long odd-run growth against a
last-even cell, or by a finite exceptional window. The family
calculations are Appendix D.

The exact one-step fibers are
\[
J(n)=q\iff q^2\le n<(q+1)^2
\quad(n\ \text{even})
\]
and
\[
J(n)=m\iff m^2\le n^3<(m+1)^2
\quad(n\ \text{odd}).
\]

**Lemma 3.1 (odd cells are unique).**
An odd fiber contains at most one integer. An even fiber is a
parity-restricted square interval and may contain many predecessors.

*Proof.* Suppose \(a<b\) lie in the same odd cell indexed by \(m\).
Then \((a+1)^3\le b^3<(m+1)^2\) and \(m^2\le a^3\). Subtracting the
latter lower bound from the former upper bound gives
\[
3a^2+3a+1=(a+1)^3-a^3<(m+1)^2-m^2=2m+1,
\]
hence \(3a^2+3a<2m\) and \(3a^2<2m\). If \(a=0\), then \(m=0\) and
the displayed strict inequality is already impossible. If \(a>0\),
squaring and using \(m^2\le a^3\) gives \(9a^4<4m^2\le 4a^3\),
contradicting \(4a^3<9a^4\). \(\square\)

**Theorem 3.2 (cycle restrictions).**
Let \(w\) be a cycle word at \(n\ge2\).

(i) The word is formally expanding:
\[
2^{|w|}<3^{\#O(w)}.
\]
A contracting word cannot close a nontrivial cycle.

(ii) The cycle minimum is odd and the cycle maximum is even. A
minimum-based orientation cannot end in an odd letter.

(iii) A realized word \(v\) is *superquadratic* if
\[
3^{\#O(v)}\ge 2^{|v|+1}.
\]
Any realized path from a start \(n\ge2\) to a state at least \(n^2\)
is superquadratic. On a cycle minimum the path to any later even
state is superquadratic. The prefix \(OOE\) is expanding
(\(9>8\)) but not superquadratic (\(9<16\)), so it cannot carry the
minimum to square scale.

*Proof.* For (i), Theorem 2.2 applied to a cycle endpoint gives
\(n^{2^{|w|}}\le n^{3^{\#O(w)}}\). Since \(n\ge2\), comparison of
exponents gives \(2^{|w|}\le 3^{\#O(w)}\); equality is impossible
because the two sides have different prime divisors and \(|w|\ge 1\).
Alternatively: a mixed cycle word has \(\Delta_w(n)>0\) by
Theorem 2.5 in Appendix C, so the envelope is strict; a monochrome
tower cannot return for \(n\ge 2\).

Every state on such a cycle is at least \(2\): once a trajectory reaches
\(1\), it remains there and cannot return to a start \(n\ge 2\). An
even state \(x\ge 2\) satisfies \(J(x)<x\), so a cycle minimum cannot
be even. An odd state \(x\ge 3\) satisfies \(J(x)>x\), so a cycle
maximum cannot be odd. This proves the first assertion of (ii). For
the final-letter assertion, let \(x\) be the predecessor of a
minimum-oriented return \(n\). If the last letter were odd, the odd
return cell would give \(n^2\le x^3<(n+1)^2\). Minimality gives
\(x\ge n\), hence \(n^3<(n+1)^2\), impossible for \(n\ge 3\); and the
minimum is odd, so \(n\ge 3\).

For (iii), let a realized word \(v\) send \(n\) to \(y\ge n^2\).
Theorem 2.2 gives
\[
n^{2^{|v|+1}}=(n^2)^{2^{|v|}}
\le y^{2^{|v|}}\le n^{3^{\#O(v)}}.
\]
Since \(n\ge 2\), comparison of exponents proves the superquadratic
inequality. On a cycle minimum, if a later state \(y\) is even, its
successor is at least \(n\). Thus \(n\le J(y)=\lfloor\sqrt y\rfloor\),
so \(n^2\le y\), and the preceding argument applies to that prefix.
\(\square\)

**Lemma 3.21b (canonical run form).**
After rotation to a minimum-based orientation, the word begins
with \(OO\) and ends with \(E\); hence every word with
\(1\le e\le 3\) even letters has the canonical run decomposition
\(O^aEO^bEO^cE\) (unused runs empty). The case \(e=0\) is
all-odd and is already forbidden by the last-letter restriction.
No other cyclic rotation needs a separate case.

*Proof.* Theorem 3.2: the minimum is odd, so the word cannot
begin with \(E\) or \(OE\), and it cannot end with an odd letter.
Thus a minimum-based word starts \(OO\) and ends \(E\), so
\(e\ge 1\). The remaining letters are odd runs separated by the
\(e\) even letters, so the word is \(O^{a_1}E\cdots O^{a_e}E\)
with \(a_1\ge 2\). For \(e\le 3\) this is \(O^aEO^bEO^cE\) with
unused runs empty. Every cycle word has a minimum-based rotation
of the same even-count, and that orientation is already in this
form. \(\square\)

Thus it is enough to exclude the three regimes \(e=1,2,3\). The
rest of the section does that. Theorems 3.6 and 3.8 record the
short-period consequences; Theorem 3.22 is the structural
statement.

**Lemma 3.3 (coarse lower envelope).**
For \(n\ge 1\), write \(q=\lfloor\sqrt n\rfloor\). Then
\(q^2\le n<(q+1)^2\). For \(q\ge 1\) one has
\((q+1)^2\le 4q^2\), and the second inequality is strict for
\(q\ge 2\), while for \(q=1\) one has \(n<4\). In all cases
\[
n<4\,\lfloor\sqrt n\rfloor^2.
\]
Thus an even step satisfies \(n\le 4\,J(n)^2\) and an odd step
satisfies \(n^3\le 4\,J(n)^2\). Composing along a realized word \(v\)
of length \(k\) with odd count \(o\) gives
\[
n^{3^{o}}\le C_v\,J^{k}(n)^{2^{k}}.
\]
The constant starts at \(1\) and updates by
\(C\mapsto C\cdot 4^{2^{j}}\) on an even letter and
\(C\mapsto C^{3}\cdot 4^{2^{j}}\) on an odd letter, at step \(j\).
In particular \(C_{OOO}=2^{38}\) and \(C_{OOOO}=2^{130}\).

*Proof.* The comparison \(n<4q^2\) is the paragraph above. The
composition law is the same recurrence as the proof of Theorem 2.2,
with a factor \(4^{2^j}\) inserted at each letter. The values
\(C_{OOO}\) and \(C_{OOOO}\) are the result of that recurrence on
those two words. \(\square\)

**Lemma 3.4 (next-square thresholds).**
(i) If \(q\ge 5\) realizes \(OO\), then \(J^2(q)\ge(q+1)^2\).
(ii) If \(q\ge 3\) realizes \(OOO\), then \(J^3(q)\ge(q+1)^2\).
(iii) If a realized word \(v\) satisfies \(J^{|v|}(q)\ge(q+1)^2\) and
the next realized letter is odd, then
\(J^{|v|+1}(q)\ge(q+1)^2\).
(iv) If \(vE\) is a cycle word at \(n\), then
\(J^{|v|}(n)<(n+1)^2\).
(v) If \(a\ge 3\), then \(O^aE\) is not a cycle word at any
\(n\ge 2\).

*Proof.* For (i), write \(m=\lfloor q^{3/2}\rfloor\). The bound
\(J^2(q)\ge(q+1)^2\) follows from \(m^3\ge(q+1)^4\), because then
\(\lfloor m^{3/2}\rfloor\ge(q+1)^2\). If \(q=5\), then
\(11^2=121\le 125=5^3<144=12^2\), so \(m=11\), and
\(11^3=1331\ge 6^4=1296\). Since \(q\) realizes \(OO\), it is odd, so
the only remaining case is \(q\ge 7\). Then \(m\ge q^{3/2}-1\), so it
is enough that \((q^{3/2}-1)^3\ge(q+1)^4\). Expanding the left side
and dropping the positive remainder \(3q^{3/2}-1\) reduces this to
\(q^{9/2}-3q^3\ge(q+1)^4\), or equivalently
\(\sqrt q-3/q\ge(1+1/q)^4\). The left side increases for \(q>0\) and
the right side decreases, so the case \(q=7\) suffices:
\[
\sqrt7-\frac37>\frac52-\frac37=\frac{29}{14}
  >\frac{4096}{2401}=\left(\frac87\right)^4,
\]
where \(\sqrt7>5/2\) follows from \(25/4<7\).

For (ii), the trajectory \(3\to 5\to 11\to 36\) gives \(J^3(3)=36\ge 16\).
If \(q\ge 5\) realizes \(OOO\), then it realizes \(OO\), so (i) gives
\(J^2(q)\ge(q+1)^2\). The third letter is odd, hence
\(J^3(q)=J(J^2(q))\ge J^2(q)\).

For (iii), the image after \(v\) is odd and at least \((q+1)^2\ge 4\),
so the odd branch does not decrease it.

For (iv), the last letter is even, so the preimage \(z=J^{|v|}(n)\)
is even and satisfies \(n^2\le z<(n+1)^2\).

For (v), suppose \(O^aE\) is a cycle word at \(n\ge 2\). The start
is odd, hence at least \(3\), and realizes \(O^a\). Parts (ii) and
(iii) give \(J^a(n)\ge(n+1)^2\), contradicting (iv). \(\square\)

**Lemma 3.5 (two length-six exclusions).**
Neither \(OOOEOE\) nor \(OOOOEE\) is a cycle word at any \(n\ge 2\).

*Proof.* Appendix D.

**Theorem 3.6 (small-cycle census).**
No word of length at most six is a cycle word at any \(n\ge 2\).
Equivalently, a nontrivial Juggler cycle, if one exists, has period at
least seven.

*Proof.* Appendix D. The reduction used there — an all-odd word
cannot return, and every mixed cycle word rotates to an
even-terminating cycle word based at a cycle state \(m\ge 2\) —
is reused by Theorem 3.8 and Theorem 3.22.

Lemma 3.4(v) excludes every odd-run-then-even word \(O^aE\) with
\(a\ge 3\), of any length.

**Lemma 3.7 (two length-seven exclusions).**
Neither \(OOOOEOE\) nor \(OOOOOEE\) is a cycle word at any \(n\ge 2\).

*Proof.* Appendix D.

**Theorem 3.8 (small-cycle census through length seven).**
No word of length at most seven is a cycle word at any \(n\ge 2\).
Equivalently, a nontrivial Juggler cycle, if one exists, has period at
least eight.

*Proof.* Appendix D.

Theorems 3.6 and 3.8 are supporting period statements. The
structural claim is the even-count exclusion of Theorem 3.22.
The same cells organise leftover words by even-count. Write
\[
e_a=2\bigl(3^a-2^a\bigr)
\]
for \(a\ge 0\).

**Lemma 3.9 (trailing even run).**
If a cycle word based at \(n\) ends with \(r\ge 1\) even letters,
the state immediately before that run is strictly less than
\((n+1)^{2^r}\).

*Proof.* The case \(r=1\) is Lemma 3.4(iv). Suppose the claim holds
for some \(r\ge 1\), and let \(vE^{r+1}\) be a cycle word at \(n\).
Write \(z=J^{|v|}(n)\). The inductive hypothesis applied to the
suffix \(E^r\) after the first of those even letters gives
\(J(z)<(n+1)^{2^r}\). The state \(z\) is even, so
\(z<(J(z)+1)^2\le\bigl((n+1)^{2^r}\bigr)^2=(n+1)^{2^{r+1}}\).
\(\square\)

**Lemma 3.10 (odd-run lower envelope).**
If \(n\ge 1\) realizes \(O^a\), then
\[
n^{3^a}\le 2^{e_a}\,J^a(n)^{2^a}.
\]

*Proof.* Lemma 3.3 supplies a multiplicative constant \(C_v\) along
any realized word, with \(C_\varepsilon=1\),
\(C\mapsto C\cdot 4^{2^j}\) on an even letter, and
\(C\mapsto C^3\cdot 4^{2^j}\) on an odd letter, at step \(j\). On
the pure odd word \(O^a\) every letter is odd, so
\(C_{O^{a+1}}=C_{O^a}^3\cdot 4^{2^a}\). Writing
\(C_{O^a}=2^{e_a}\) with \(e_0=0\) yields the recurrence
\(e_{a+1}=3e_a+2^{a+1}\), because \(4^{2^a}=2^{2^{a+1}}\). The closed
form \(e_a=2(3^a-2^a)\) satisfies the recurrence and the initial
value. \(\square\)

**Lemma 3.11 (seven-odd window).**
No integer \(n\) with \(2\le n<256\) realizes the word \(O^7\).

*Proof.* This is a table of \(254\) seven-step evaluations: at every
such start, some letter fails to match the current parity. The same
finite check is the Lean `native_decide` evaluation behind
`no_follows_seven_odds_of_lt256` (Appendix A). \(\square\)

**Theorem 3.12 (two-even leftover families).**
Let \(k\ge 6\) and \(n\ge 2\). Neither \(O^{k-2}EE\) nor
\(O^{k-3}EOE\) is a cycle word at \(n\).

*Proof.* Appendix D.

A cycle word \(w\) at \(n\) is *minimum-based* when \(n\) is a
cycle minimum: \(J^j(n)\ge n\) for every \(0\le j<|w|\). The
remainder after a proper prefix of a cycle word need not itself be
a cycle word at the prefix endpoint. The next statement therefore
transports the tail inequality of Theorem 3.12, not the cycle-word
exclusion at a later start.

**Theorem 3.13 (first-even transport).**
Let \(n\ge 2\). No minimum-based cycle word at \(n\) has the form
\(O^aEO^bEE\) with \(a\ge 2\) and \(b\ge 4\), or the form
\(O^aEO^bEOE\) with \(a\ge 2\) and \(b\ge 3\).

*Proof.* Appendix D.

The hypothesis that the start is a cycle minimum is essential. If
\(y<n\), the leftover cell is measured against a larger start and
need not contradict the tail at \(y\). In particular, Theorem 3.13
does not assert that those words fail to be cycle words at a
non-minimum start. That upgrade is Theorem 3.21.

**Theorem 3.14 (three trailing evens).**
Let \(a\ge 6\) and \(n\ge 2\). The word \(O^aEEE\) is not a cycle
word at \(n\).

*Proof.* Appendix D.

**Theorem 3.15 (mixed bunched family \(EOEE\)).**
Let \(a\ge 5\) and \(n\ge 2\). The word \(O^aEOEE\) is not a cycle
word at \(n\).

*Proof.* Appendix D.

**Theorem 3.16 (mixed bunched family \(EOOEE\)).**
Let \(a\ge 4\) and \(n\ge 2\). The word \(O^aEOOEE\) is not a
cycle word at \(n\).

*Proof.* Appendix D.

**Theorem 3.17 (mixed bunched family \(EOOOEE\)).**
Let \(a\ge 3\) and \(n\ge 2\). The word \(O^aEOOOEE\) is not a
cycle word at \(n\).

*Proof.* Appendix D.

**Theorem 3.18 (mixed bunched family \(EEOE\)).**
Let \(a\ge 5\) and \(n\ge 2\). The word \(O^aEEOE\) is not a
cycle word at \(n\).

*Proof.* Appendix D.

**Theorem 3.19 (mixed bunched family \(EOEOE\)).**
Let \(a\ge 4\) and \(n\ge 2\). The word \(O^aEOEOE\) is not a
cycle word at \(n\).

*Proof.* Appendix D.

**Theorem 3.20 (mixed bunched family \(EOOEOE\)).**
Let \(a\ge 3\) and \(n\ge 2\). The word \(O^aEOOEOE\) is not a
cycle word at \(n\).

*Proof.* Appendix D.

**Theorem 3.21 (gapped leftovers as cycle words).**
Let \(n\ge 2\). No cycle word at \(n\) has the form \(O^aEO^bEE\)
with \(a\ge 2\) and \(b\ge 4\), or the form \(O^aEO^bEOE\) with
\(a\ge 2\) and \(b\ge 3\).

*Proof.* Appendix D.

Theorems 3.12--3.21 assemble into an even-count exclusion: no
cycle word has fewer than four even letters, so a nontrivial
cycle has period at least eleven (Theorem 3.22). Section 4
excludes later periods by financing.

Every integer \(2\le n<12\) reaches \(1\), so a cycle minimum is
at least \(12\). Write \(e\) for the number of even letters.
Lemma 3.21b is the canonical run form.

**Lemma 3.21a (classification).**
Every minimum-based cycle word with at most three even letters
belongs to one of the families excluded by Lemma 3.4(v) and
Theorems 3.12--3.21.

*Proof.* Lemma 3.21b puts the word in the form
\(O^aEO^bEO^cE\) with \(a\ge 2\) and unused runs empty. If
\(e=0\), the word is all-odd. If \(e=1\), it is \(O^aE\). If
\(e=2\), a last run \(c\ge 2\) is the internal-even bootstrap of
Lemma 3.4, and the remaining shapes are the two-even families of
Theorem 3.12. If \(e=3\), again \(c\ge 2\) is the bootstrap, while
\(c\in\{0,1\}\) is either a gapped leftover (Theorem 3.21) or one
of the seven bunched families (Theorems 3.14--3.20). \(\square\)

| \(e\) | remaining minimum-based forms | elimination |
|---:|---|---|
| \(0\) | all-odd | cannot return (Theorem 3.6) |
| \(1\) | \(O^aE\) | next-square; Lemma 3.4(v) |
| \(2\) | \(O^aEE\), \(O^aEOE\), last run \(\ge 2\) | Theorem 3.12; Lemma 3.4 |
| \(3\) | bunched families and gapped leftovers | Theorems 3.14--3.21 |
| \(\ge 4\) | not excluded by even-count | finance (Section 4) |

**Theorem 3.22 (even-count).**
No word with fewer than four even letters is a cycle word at any
\(n\ge 2\). Equivalently, a nontrivial cycle word has at least
four even letters.

*Proof.* Every cycle word has a minimum-based rotation, with the
same even-count. Lemma 3.21b puts that orientation in canonical
run form; Lemma 3.21a names the families. In detail:

If \(e=0\), the word is all-odd and cannot return, as in
Theorem 3.6.

If \(e=1\), the word is \(O^aE\) with \(a\ge 2\). The case
\(a=2\) is \(OOE\), excluded in Theorem 3.6. The cases
\(a\ge 3\) are Lemma 3.4(v).

If \(e=2\), the word is \(O^aEO^cE\) with \(a\ge 2\). A last
odd-run \(c\ge 2\) is an internal even letter followed by
\(OO\) or \(OOO\). Lemma 3.4 at the cycle minimum
(\(n\ge 12\)) contradicts the last-even cell. The remaining
shapes are \(O^aEE\) and \(O^aEOE\). Expansion forces
\(a\ge 4\) and \(a\ge 3\) respectively, so both are
Theorem 3.12.

If \(e=3\), the word is \(O^aEO^bEO^cE\) with \(a\ge 2\).
Again \(c\ge 2\) is the internal-even bootstrap. The remaining
last runs are \(c=0\) and \(c=1\). For \(c=0\) and
\(b\ge 4\) the word is a gapped leftover \(O^aEO^bEE\),
excluded by Theorem 3.21. For \(c=0\) and \(b\le 3\) the
word is one of \(O^aEEE\), \(O^aEOEE\), \(O^aEOOEE\),
\(O^aEOOOEE\), excluded by Theorems 3.14--3.17 once
expansion supplies the stated lower bounds on \(a\). For
\(c=1\) and \(b\ge 3\) the word is a gapped leftover
\(O^aEO^bEOE\), excluded by Theorem 3.21. For \(c=1\) and
\(b\le 2\) the word is one of \(O^aEEOE\), \(O^aEOEOE\),
\(O^aEOOEOE\), excluded by Theorems 3.18--3.20.

Thus \(e\le 3\) is impossible. \(\square\)

**Corollary 3.23.**
A nontrivial cycle, if one exists, has period at least eleven.

*Proof.* Theorem 3.22 gives four even letters, hence
\(o\le L-4\). Formal expansion is \(2^L<3^o\le 3^{L-4}\).
The comparison \(2^L<3^{L-4}\) first holds at \(L=11\).
\(\square\)

In particular there is no cycle of length eight, nine, or ten.

## 4. Cycle finance

A cycle word is formally expanding (Theorem 3.2), yet the trajectory
returns exactly. The multiplicative surplus \(3^o-2^L\) must be
financed by the floor remainders, which are relatively \(O(1/x)\)
in logarithms. The resulting bound on the cycle minimum excludes
every period that is not admissible for the inequality, once a
uniform logarithmic floor-error bound is available above a
verified descent floor.

The identity is unrolled along a circular word. After rotation
to a cycle minimum that word is a necklace of odd-run
excursions. The geometry below records that itinerary. It
introduces no new theorem: every named constraint is Theorem 3.2,
Lemma 3.4, Lemma 3.21b, or the last-even cell.

### The excursion necklace

Write \(n\) for a cycle minimum and
\[
w=O^{a_1}EO^{a_2}E\cdots O^{a_e}E
\]
for a minimum-based orientation (Lemma 3.21b), so \(a_1\ge 2\),
\(\sum_i a_i=o\), and \(e=L-o\). The odd landings are the
*valleys* \(v_i\) and the even state just before each final \(E\)
is the *peak* \(p_i\):
\[
v_0=n,\qquad
p_i=J^{a_{i+1}}(v_i),\qquad
v_{i+1}=J(p_i)=\lfloor\sqrt{p_i}\rfloor
\quad(0\le i<e),
\]
with \(v_e=n\). The itinerary is
\[
n
\;\xrightarrow{\;OO\;}
\text{first high region}
\;\xrightarrow{\;E\;}
v_1
\;\xrightarrow{\;O^{a_2}E\;}
\cdots
\;\xrightarrow{\;O^{a_{e-1}}E\;}
v_{e-1}
\;\xrightarrow{\;O^{a_e}E\;}
n.
\]

Two meanings of *entry* must not be conflated. *Cycle entry* is
the distinguished cut that places the minimum at the start of
the word. *Dynamical entry* is the last even step into \(n\).
The second is a genuine boundary condition; the first is a
choice of origin.

#### Cycle minimum and the forced lift

The minimum is odd, so the word cannot begin with \(E\) or
\(OE\), and it cannot end with an odd letter (Theorem 3.2).
The first two letters are therefore \(OO\):
\[
n\overset{O}{\longrightarrow}y\overset{O}{\longrightarrow}z.
\]
For \(n\ge 5\) one has \(z=J^2(n)\ge(n+1)^2\) (Lemma 3.4(i)).
In particular \(OOE\) cannot be a cycle word
(`no_cycle_word_ooe`). On a cycle minimum the first even
residual overshoots the entry cell: the first peak satisfies
\(p_0\ge(n+1)^2\). That is the opposite of the last-peak
condition below. Even \(J^2(n)\) may continue with \(E\); odd
\(J^2(n)\) continues with \(O\). Either way the minimum-based
prefix is still \(OO\).

#### Excursions, valleys, and peaks

An ordinary excursion is one block \(O^{a}E\). In the itinerary
semantics that word is `oddEvenBlock a 1`. Write
\[
\mu(a)=\frac{3^a}{2^{a+1}}
\]
for the ideal (floor-free) exponent of the block. The block is
formally expanding if and only if \(\mu(a)>1\), equivalently
\(2^{a+1}<3^a\). Thus \(OE\) contracts (\(\mu(1)=3/4\)) and
\(OOE\) expands (\(\mu(2)=9/8\)). This is a reparameterization
of the word envelope of Theorem 2.2, not a transition law on
pairs \((a_i,a_{i+1})\). Lemma 3.4(v) forbids \(O^aE\) as a
*cycle word* for \(a\ge 3\); it does not forbid an internal
block of that shape.

The trajectory is then the wave
\[
v_0\to p_0\to v_1\to p_1\to\cdots\to v_{e-1}\to p_{e-1}\to v_0.
\]
On a cycle minimum every even state is already at least \(n^2\)
(Theorem 3.2(iii)). Valleys dominate a logarithmic defect sum
because \(1/(x\log x)\) is largest there; peaks are huge and
cheap. That is why the run-type packing of Theorem 4.7 charges
\(\mathtt{OOE}\)-scale valleys, \(\mathtt{OE}\)-scale valleys,
and evens separately. The packed comparison is an extremal
charge of the same sum, not a uniqueness theorem for the
actual word. Expanding blocks can climb and a later \(OE\) can
drop without crossing the anchor: four consecutive expanding
blocks occur already at the certified start \(1999\) recorded
in Section 6.

#### Closure and the entry cell

The valley sequence is circular. The last letter is \(E\), so
the last peak occupies the last-even cell of Lemma 3.4(iv):
\[
n^2\le p_{e-1}<(n+1)^2.
\]
The minimum is odd, so \(p_{e-1}\neq n^2\)
(`cycle_last_even_ne_odd_sq`) and \(p_{e-1}\) is even. Thus
\[
n^2+1\le p_{e-1}<(n+1)^2,\qquad p_{e-1}\text{ even}.
\]
An ordinary excursion needs only \(v_i\ge n\). The last
excursion must hit this cell and land on \(n\):
\[
v_{e-1}
\overset{O^{a_e}}{\longrightarrow}
p_{e-1}
\overset{E}{\longrightarrow}
n.
\]
The first peak overshoots the same cell; the last peak lands
in it. Those are different even states.

Once the trajectory returns to \(n\), the prefix \(OO\) is forced
again. A genuine cycle is a closed necklace of excursions
whose first block starts \(OO\), whose last peak lies in the
entry cell, and whose entire trajectory stays at least \(n\). The
global constraints already proved are
\[
\sum_i a_i=o,\qquad e=L-o,\qquad 2^L<3^o,
\]
together with periodicity \(\prod_{i=0}^{e-1} v_{i+1}/v_i=1\).

#### What remains

Finance (Theorem 4.4) sits around the necklace: the surplus
\(3^o-2^L\) must be paid by floor losses, and at the verified
floor \(N_0=10^6\) this forces \(L\ge 25781\). The run-type
packing of Theorem 4.7 is a refinement of the same defect sum
along the valleys and peaks just named. Subsequent refinements
of one component of the necklace recovered Theorem 4.7 or
closed. They are not claims of this note.

The pieces are understood separately: the forced lift at \(n\),
the blocks \(O^{a_i}E\), and the last-even landing. What is
not proved is a link strong enough to exclude the leftover
lengths,
\[
\text{minimum geometry}
+\text{necklace of excursions}
+\text{entry cell}
\;\Rightarrow\;\bot.
\]
That is a formulation of the remaining cycle problem, not a
theorem. A genuine lower bound on the number of odd runs would
feed Theorem 4.7; none is proved here.

Throughout this section write \(L=|w|\) and \(o=\#O(w)\) for a
cycle word \(w\) based at a cycle minimum \(n\ge 2\). Natural
logarithms are written \(\log\) in this section and \(\ln\) in
Section 5; both denote the natural logarithm. The unique one-step fibres of
Section 3 give, for every state \(x\ge 1\) with image
\(y=J(x)\),
\[
y^2\le x^e<(y+1)^2,
\qquad
e=\begin{cases}1,&x\text{ even},\\3,&x\text{ odd}.\end{cases}
\]

**Lemma 4.1 (dyadic-cell logarithm).**
If \(z,y\ge 1\) and \(z<(y+1)^2\), then
\(\log z\le 2\log y+2/y\).

*Proof.* The hypothesis gives \(\log z\le 2\log(y+1)\). The
inequality \(\log(1+u)\le u\) for \(u>0\) yields
\(\log(y+1)=\log y+\log(1+1/y)\le\log y+1/y\). \(\square\)

**Lemma 4.2 (one-step bounds).**
Let \(x\ge 2\) and \(y=J(x)\). If \(x\) is even, then
\(\log x\le 2\log y+2/y\). If \(x\) is odd, then
\(3\log x\le 2\log y+2/y\).

*Proof.* The even cell is \(y^2\le x<(y+1)^2\). The cell logarithm
lemma on \(z=x\) is the first claim. The odd cell is
\(y^2\le x^3<(y+1)^2\). The same lemma on \(z=x^3\) gives
\(\log(x^3)\le 2\log y+2/y\). \(\square\)

On a cycle minimum every proper prefix is non-contracting: a
prefix with \(3^{\#O}<2^{k}\) would satisfy
\(J^k(n)<n\) by Corollary 2.3, contradicting minimality. Thus
\(2^k\le 3^{o_k}\) for every prefix of length \(k\), where
\(o_k\) is the odd count of that prefix.

**Lemma 4.3 (unrolled envelope).**
Write \(x_k=J^k(n)\) and \(o_k\) for the odd count of the length-\(k\)
prefix. For every \(0\le k\le L\),
\[
3^{o_k}\log n
\le
2^k\log x_k
+\frac{k\,3^{o_k}}{n}.
\]

*Proof.* The case \(k=0\) is an equality. Suppose the claim holds
at \(k<L\), and write \(x=x_k\) and \(y=x_{k+1}\). Minimality gives
\(n\le y\), and the prefix law gives \(2^{k+1}\le 3^{o_{k+1}}\),
hence
\[
\frac{2^{k+1}}{y}\le\frac{3^{o_{k+1}}}{n}.
\]

If the next letter is even, then \(o_{k+1}=o_k\) and the one-step
bound gives \(\log x\le 2\log y+2/y\). Multiply by \(2^k\) and add the
inductive remainder:
\[
3^{o_k}\log n
\le
2^{k+1}\log y
+\frac{2^{k+1}}{y}
+\frac{k\,3^{o_k}}{n}
\le
2^{k+1}\log y
+\frac{(k+1)\,3^{o_k}}{n}.
\]

If the next letter is odd, then \(o_{k+1}=o_k+1\). Multiply the
inductive bound by \(3\) and apply the one-step bound in the form
\(3\log x\le 2\log y+2/y\):
\[
3^{o_k+1}\log n
\le
2^{k+1}\log y
+\frac{2^{k+1}}{y}
+\frac{k\,3^{o_k+1}}{n}
\le
2^{k+1}\log y
+\frac{(k+1)\,3^{o_k+1}}{n}.
\]
This is the claim at \(k+1\). \(\square\)

\vspace{0.8em}

**Theorem 4.4 (finance).**
Let \(w\) be a cycle word of length \(L\) with \(o\) odd letters,
based at a cycle minimum \(n\ge 2\). Then
\[
n\log n\cdot(3^o-2^L)\le L\cdot 3^o.
\]

*Proof.* Apply Lemma 4.3 at \(k=L\). Periodicity gives
\(x_L=n\) and \(o_L=o\), so
\[
3^o\log n\le 2^L\log n+\frac{L\cdot 3^o}{n}.
\]
The word is formally expanding, so \(3^o>2^L\). Rearranging and
multiplying by \(n\) is the claim. \(\square\)

\vspace{0.4em}

This is the conceptual centre of the note. Exact cells give a
one-step logarithmic defect; cycle minimality lets the defect
be unrolled against the cycle minimum; the formal surplus
\(3^o-2^L\) must then be paid by a finite accumulated budget.
Ideal dynamics expands and exact dynamics returns, so the floor
errors finance the expansion. The inequality \(\log(1+u)\le u\)
is the only analytic input; the content is that interaction.
The Lean form is exactly Theorem 4.4 (constant \(1\)):
`cycleMin_finance`.

**Hierarchy of forms.**
These three layers must not be conflated.

1. *Theorem 4.4* is the conceptual sharp inequality. Constant
   \(1\):
   \[
   n\log n\cdot(3^o-2^L)\le L\cdot 3^o,
   \]
   equivalently \(\theta\le L/(n\log n)\) with
   \(\theta=1-2^L/3^o\). It charges every cell defect at the
   cycle minimum. Lean: `cycleMin_finance`.

2. *Corollary 4.4c* (below) is the same cell-log unroll with
   remainders kept as \(1/x_{i+1}\). It is the strongest proved
   form of those defects. Lean: `cycleMin_finance_inv_sum`.

3. *Corollary 4.5* is the convenient length-only statewise
   bound: a verified descent floor \(N_0\) plus a parity charge
   of the defect sum produces a per-length threshold
   \(n_{\max}(L)\) and excludes every \(L\) with
   \(n_{\max}(L)\le N_0\).

4. *Theorem 4.6* is the numerical certification of Corollary 4.5
   at \(N_0=10^6\). The certified identity is the conservative
   relative-defect form
   \[
   1-\frac{2^L}{3^o}
   \le
   \frac65\sum_{i=1}^{L}\frac{1}{x_i\log x_i}.
   \]
   The factor \(6/5\) is a convenient uniform majorant of
   \(-\log(1-\delta)/\delta\) on \([0,1/6]\). It is not
   Theorem 4.4, and the headline cutoff \(25781\) is not an
   artifact of that majorant. The identity itself is Lean for
   any cycle minimum \(n\ge 400\) (`cycleMin_defect_finance`,
   `DefectFinance.lean`); the per-length numeric table stays a
   verified computation.

The relative-defect unroll is a parallel identity, not
Theorem 4.4 multiplied by \(6/5\). Charging every state at the
cycle minimum in that identity recovers the coarser comparison
\(\theta\le(6/5)L/(n\log n)\), which is Theorem 4.4 with
coefficient \(6/5\). At this floor that uniform charge excludes
only through length \(1053\). The computational table uses a
stricter length-only parity charge of the same identity.

**Corollary 4.4c (inv-sum).**
Let \(w\) be a cycle word of length \(L\) with \(o\) odd letters,
based at a cycle minimum \(n\ge 2\). Write \(x_i=J^i(n)\). Then
\[
(3^o-2^L)\log n\le 3^o\sum_{i=1}^{L}\frac1{x_i},
\]
equivalently \(\theta\le\bigl(\sum_i 1/x_i\bigr)/\log n\).

*Proof.* The same induction as Lemma 4.3, keeping each cell
defect as \(2^{k+1}/x_{k+1}\) instead of replacing it by
\(3^{o_{k+1}}/n\). At \(k=L\) one has \(x_L=n\). Lean:
`cycleMin_log_envelope_inv`, `cycleMin_finance_inv_sum`.
\(\square\)

The computational table of Theorem 4.6 uses a weaker per-step
bound, valid on every cycle because every start below \(12\)
reaches \(1\) (so every cycle state is at least \(12\)). For a
state \(x\) with image \(y=J(x)\ge 12\), the relative defect
\(\delta=(x^e-y^2)/x^e\) satisfies \(\delta\le 2/y\le 1/6\).
Writing \(\varepsilon=-\tfrac12\log(1-\delta)\) and using
\(-\log(1-\delta)\le\tfrac65\delta\) on \([0,1/6]\) gives
\(\varepsilon\le(6/5)/y\). Unrolling
\(t_{i+1}=(e_i/2)\,t_i-\varepsilon_i\) around the cycle then yields
the conservative identity displayed in item 4 of the hierarchy.
This chain is Lean end to end (`DefectFinance.lean`): the
per-step losses in image form (`log_floorPower_even_ge_sub`,
`log_floorPower_odd_ge_sub`, from
\(-\log(1-\delta)\le\tfrac65\delta\) on \([0,1/6]\),
`neg_log_one_sub_le_sixth`), the amplification priced by the
upper invariant \(\log x_k\le w_k\log n\)
(`cycleMin_log_le_weight`), and the charged unroll
(`cycleMin_charge_prefix`), closed at \(x_L=n\).

On a minimum-based cycle of length \(L\) with \(o\) odd letters
and \(e=L-o\) even letters, the last letter is even, so \(e\ge 1\)
and the number of odd-run starts is at most \(e\). Every even
state satisfies \(x\ge n^2\). Every odd state preceded by an odd
state satisfies \(x\ge t=\lfloor n^{3/2}\rfloor\). Therefore
\[
\sum_{i=1}^{L}\frac{1}{x_i\log x_i}
\le
\frac{e}{n\log n}
+\frac{o-e}{t\log t}
+\frac{e}{2n^2\log n},
\]
and
\[
n\log n\left(1-\frac{2^L}{3^o}\right)
\le
\frac65\left(
e+(o-e)\frac{n\log n}{t\log t}+\frac{e}{2n}
\right).
\]
The optimal uniform coefficient on \([0,1/6]\) is
\(6\log(6/5)\approx 1.093\). Replacing \(6/5\) by that constant,
or even by \(1\), on the same parity charge does not change the
first surviving length: one still has
\(n_{\max}(25780)\le 10^6<n_{\max}(25781)\). The published table
and the count \(141\) keep the proved coefficient \(6/5\). The
cutoff \(25781\) is therefore not an artifact of an avoidable
loss in the majorant.

**Lemma 4.4b (odd-count monotonicity).**
Write \(\theta(o)=1-2^L/3^o\) and
\[
R(o)=e+(o-e)\alpha+\frac{e}{2n},
\qquad
e=L-o,
\qquad
\alpha=\frac{n\log n}{t\log t}.
\]
The certified parity comparison is
\(n\log n\cdot\theta(o)\le(6/5)R(o)\). For every \(n\ge 12\)
one has \(\alpha<1/2\), hence
\[
R(o+1)-R(o)=2\alpha-1-\frac1{2n}<0.
\]
Also \(\theta(o+1)>\theta(o)\). Therefore if the comparison
fails at some admissible \(o\), it fails at every larger odd
count. Equivalently, the largest \(n\) at which the comparison
can hold occurs at the least admissible odd count
\(o_{\min}(L)=\min\{o:3^o>2^L\}\). The same monotonicity holds
for any positive coefficient in place of \(6/5\), and for the
constant-\(1\) comparison of Theorem 4.4.

*Proof.* The difference \(R(o+1)-R(o)\) is the displayed
coefficient of \(o\). For \(n\ge 12\) one has
\(t=\lfloor n^{3/2}\rfloor\ge n^{3/2}-1>2n\), hence
\(\alpha<(n\log n)/(2n\log(2n))=(\log n)/(2\log(2n))<1/2\).
The map \(o\mapsto\theta(o)\) is strictly increasing on
integers \(o\) with \(3^o>2^L\). If
\(n\log n\cdot\theta(o)>(6/5)R(o)\), then
\(n\log n\cdot\theta(o+1)>(6/5)R(o)>(6/5)R(o+1)\). \(\square\)

Define
\[
\gamma(L)=\frac{3^{o_{\min}(L)}}{2^L}-1,
\]
and write \(n_{\max}(L)\) for the largest integer \(n\) at which
the displayed parity inequality can still hold at
\(o=o_{\min}(L)\). The coarser comparison
\(n\log n\le (6/5)L\cdot 3^{o_{\min}}/(3^{o_{\min}}-2^L)\) is
used only as a check; Theorem 4.6 uses \(n_{\max}(L)\) from the
parity form. Lemma 4.4b is why that table may be computed at
\(o_{\min}\) alone.

**Proposition 4.4a (finance-survivor algorithm).**
Fix a verified descent floor \(N_0\). For each integer
\(1\le L\le 10^5\), compute
\(o_{\min}(L)=\min\{o:3^o>2^L\}\) by exact integer arithmetic
and \(n_{\max}(L)\) from the parity inequality, and retain
\(L\) if and only if \(n_{\max}(L)>N_0\). The resulting
finance-survivor set is
\[
\mathcal E(N_0)=\bigl\{L:1\le L\le 10^5,\; n_{\max}(L)>N_0\bigr\}.
\]
The printed instance is \(\mathcal E=\mathcal E(10^6)\), with
\(\lvert\mathcal E\rvert=141\).

**Corollary 4.5.**
If every integer \(2\le n\le N_0\) reaches \(1\), then no
nontrivial cycle of length \(L\) exists whenever
\(n_{\max}(L)\le N_0\).

*Proof.* A periodic state never reaches \(1\), so every cycle
state is at least \(N_0+1\). The length-only parity charge of
the certified relative-defect identity then forces the minimum
to satisfy the displayed inequality, hence \(n\le n_{\max}(L)\).
This is the convenient statewise bound in the hierarchy after
Theorem 4.4; it is not a replacement for that theorem.
\(\square\)

Record values of the parity \(n_{\max}\) include
\(n_{\max}(19)=133\), \(n_{\max}(84)=2323\),
\(n_{\max}(569)=23568\), \(n_{\max}(1054)=788014\), and
\(n_{\max}(25781)=26254995\).

**Theorem 4.6 (verified computation).**
Every integer \(2\le n\le 10^6\) reaches \(1\). Consequently:

(A) there is no nontrivial Juggler cycle of length at most
\(25780\);

(B) if a nontrivial cycle has period \(L\le 10^5\), then
\(L\in\mathcal E\), where \(\lvert\mathcal E\rvert=141\).

The bound closes continuously through \(25780\); \(25781\) is
the first integer for which this particular inequality does not
exclude a cycle. The coefficient \(6/5\) is the certification
majorant of item 4 in the hierarchy after Theorem 4.4, not the
source of the cutoff.

*Proof.* The descent floor is Proposition 1.3. The gap table
computes \(o_{\min}(L)\) and \(n_{\max}(L)\) for every
\(1\le L\le 10^5\) by Lemma 4.4b. Corollary 4.5 at \(N_0=10^6\)
excludes every \(L\) with \(n_{\max}(L)\le 10^6\). The
contiguous excluded prefix is \(L\le 25780\). The complementary
set in range is \(\mathcal E\); checksums are Appendix B.
\(\square\)

### Run packing

Theorem 4.7 refines the length-only charge by separating the
unique minimum, \(\mathtt{OOE}\)-scale valleys,
\(\mathtt{OE}\)-scale valleys, internal odds, and evens. It is
a supporting comparison at the same floor; the leftover count
\(141\to 99\) does not raise the cutoff. A cycle cannot put an
\(\mathtt{OE}\)-start at the minimum (Theorem 3.2), and an
\(n\)-circuit of \(k\) odds and \(\ell\) evens stays at least
\(n\) only if \(3^k\ge 2^{k+\ell}\).

**Theorem 4.7 (run-type packing).**
Let \(w\) be a cycle word of length \(L\) with \(o=o_{\min}(L)\)
odd letters and \(e=L-o\) even letters, based at a cycle
minimum \(n\ge 12\). Write \(v\) for the least odd integer with
\(v^3\ge n^4\), and write \(t=\lfloor n^{3/2}\rfloor\). Then
\(o-e<e\), the largest number of \(n\)-scale valleys compatible
with the even cap is \(o-e\) copies of \(\mathtt{OOE}\), and the
remaining \(2e-o\) circuits are \(\mathtt{OE}\) from \(v\). The
cycle minimum occurs once, so
\[
\sum_{i=1}^{L}\frac{1}{x_i\log x_i}
\le
\frac{1}{n\log n}
+\frac{o-e-1}{(n+2)\log(n+2)}
+\frac{2e-o}{v\log v}
+\frac{1}{t\log t}
+\frac{o-e-1}{t_+\log t_+}
+\frac{e}{2n^2\log n},
\]
where \(t_+=J(n+2)\). Combined with the \(6/5\) unroll this is
strictly smaller than the parity sum of Corollary 4.5 whenever
\(2e-o>0\). Sending the cycle maximum to infinity removes one
even term and does not change the valley packing.

*Proof.* The statement is at \(o=o_{\min}(L)\). Lemma 4.4b
already excludes every larger odd count from the parity
comparison used in Theorem 4.6; the packing is a refinement at
that same odd count. Formal expansion at \(o_{\min}\) forces \(3o<2L\) on
every leftover length in range, equivalently \(o-e<e\). The
even-cap comparison \(3^k\ge 2^{k+\ell}\) is the ideal power
envelope; floors only help. An \(\mathtt{OE}\)-start is followed
by an even state, so Theorem 3.2 gives \(J(v)\ge n^2\) and
therefore \(v^3\ge n^4\). Unique visit of the cycle minimum is
periodicity. The displayed sum charges one cheap valley at
\(n\), the remaining \(o-e-1\) cheap valleys at the next odd
integer \(n+2\), the expensive valleys at \(v\), one internal
odd at \(t\), the remaining internals at \(J(n+2)\), and every
even at \(n^2\). Any deeper odd run or any higher valley only
decreases the sum. \(\square\)

**Theorem 4.8 (run-type table).**
At the verified descent floor \(N_0=10^6\), the packed comparison
of Theorem 4.7 excludes the \(42\) lengths
\(56347+1054k\) for \(k=0,\ldots,41\) and leaves an explicit
set \(\mathcal E_{\mathrm{run}}=\mathcal E_{\mathrm{run}}(10^6)\)
of \(99\) lengths. The first survivor remains \(25781\). In
particular, if a nontrivial cycle has period \(L\le 10^5\), then
\(L\in\mathcal E_{\mathrm{run}}\).

*Proof.* The \(141\) lengths of Theorem 4.6(B) are tested at
\(n=10^6+1\) against the packed right-hand side. The comparison
is certified on each length: no entry is left uncertain. The
\(42\) excluded lengths are exactly the arithmetic progression
named in the statement. The complementary set in that range is
\(\mathcal E_{\mathrm{run}}\). Checksums are Appendix B.
The period cutoff remains \(25781\).
\(\square\)

### Arithmetic structure of the finance survivors

The leftover lengths cluster around the continued-fraction
approximants of \(\log 2/\log 3\). That organizes the table; it
does not constrain a hypothetical cycle.

**Proposition 4.9 (finance-survivor lattice).**
Write \(v_*=(25781,16266)\) and \(v_{1054}=(1054,665)\). Then
\[
25781\cdot 665-1054\cdot 16266=1,
\]
so these two vectors are a unimodular basis of \(\mathbb Z^2\).
Every length in \(\mathcal E_{\mathrm{run}}\), and every one of
the \(42\) packing deaths of Theorem 4.8, is of the form
\((L,o_{\min})=a\,v_*+b\,v_{1054}\). With the table cap
\(L\le 10^5\) the \(99\) survivors fall in three affine slices
of counts \(29\), \(47\), and \(23\). The identification with
\(\mathcal E_{\mathrm{run}}\) is Theorem 4.8. This is a change
of coordinates for \((L,o)\), not a relation between
hypothetical cycles.

*Proof.* The determinant identity is integer arithmetic. The
generator comparison \(3^{665}>2^{1054}>3^{664}\) gives
\(o_{\min}(1054)=665\). Direct evaluation of \(o_{\min}\) on
the \(141\) lengths of Theorem 4.6(B) places each pair
\((L,o_{\min})\) on the displayed lattice, with the \(42\)
packing deaths the \(F_1\) continuation \(b\ge 29\). \(\square\)

## 5. The laboratory instance and the walk-charge envelope

Everything in Sections 2--4 is floor-generic: Corollary 4.5
accepts any verified descent floor. This section first records
a second, laboratory-certified instance of the same
architecture, then replaces the length-only charge by a coupled
exponent-walk charge. The extremal walk is identified exactly
as a rotation word, and a Denjoy--Koksma bound over certified
Ostrowski blocks produces an envelope valid for *every* length
in an explicit window — no per-length census and no dynamic
program is needed on that window. The kill table at the
laboratory floor then yields the period bound \(176251\), and
the second certified floor raises it to \(478245\)
(Corollary 5.10). Throughout, survivors are finance-survivors
in the sense of Section 1.

### 5.1 The laboratory floor

**Proposition 5.1 (laboratory descent floor; certified
computational input).**
Every integer \(2\le n\le 26254995\) reaches \(1\). Precisely:
an exact-integer first-passage run records, for each such
\(n\), a finite realized word with image strictly below the
start; strong induction on that image reaches \(1\). The run
walks the \(13127497\) odd starts (even starts descend by
\(E\)) over \(106\) contiguous chunk records. Three bit-cap
seeds (\(7110201\), \(13184021\), \(13782577\)) are resolved
exactly at a \(512\cdot 10^6\)-bit cap with exact integer
square roots, the largest intermediate having \(298912128\)
bits (seed \(7110201\)); the maximum first passage is \(325\)
steps (seed \(15909091\)). Certificate hashes are in
Appendix B. The floor \(26254995=n_{\max}(25781)\) is the
cheapest floor that moves the Theorem 4.6 cutoff.

**Theorem 5.2 (raised cutoff; verified computation).**
At \(N_0=26254995\) the parity table of Theorem 4.6 excludes
every length \(L\le 50507\): any nontrivial Juggler cycle has
period at least \(50508\). The first finance survivor is
\(L=50508\) with \(n_{\max}(50508)=162848325\); \(19\) parity
survivors remain through \(L=2\cdot 10^5\) (run packing leaves
\(11\) at the same cutoff).

*Proof.* Proposition 5.1 supplies the floor; Corollary 4.5 and
the gap table of Proposition 4.4a exclude every \(L\) with
\(n_{\max}(L)\le 26254995\). The contiguous excluded prefix is
\(L\le 50507\); checksums are Appendix B. \(\square\)

### 5.2 Transport to a reduced base

The parity and run-pack tables price valleys independently. On
a real minimum-based cycle every state is coupled through one
closed exponent walk. With \(a_k\) the number of odd letters
among the first \(k\), set
\[
u_k=(1+\mu)a_k-k,\qquad \mu=\log_2(3/2).
\]
The defect-free floors give the upper envelope
\(x_k\le n^{2^{u_k}}\), and cycle minimality forces
\(u_k\ge 0\) at every step. The lower envelope requires
controlling the accumulated floor losses; that is the transport
lemma.

**Theorem 5.3 (transport).**
On a minimum-based cycle with minimum \(n\ge 400\), length
\(L\), \(o\) odd and \(e\) even letters, every state satisfies
\[
x_k\ \ge\ \bigl(n\,e^{-D}\bigr)^{w_k},
\qquad
w_k=2^{u_k},
\qquad
D=\frac{1.05\,e}{n}+\frac{0.7\,o}{n^{3/2}}.
\]

*Proof.* Write \(\ln x_k\ge w_k\ln n-E_k\). The floor losses
give the recursion \(E'\le\tfrac32E+1.05\,x^{-3/2}\) at an odd
letter and \(E'\le\tfrac12E+1.05\,x^{-1/2}\) at an even letter,
using \(-\ln(1-t)\le 1.05\,t\) on \(t\le 0.05\). Unrolling, the
amplification from injection \(j\) to state \(k\) is exactly
\(w_k/w_{j+1}\). Odd injections have \(x_j\ge n\) and
\(w_{j+1}\ge\tfrac32\), contributing at most \(0.7\,n^{-3/2}\)
each; even injections have \(x_j\ge n^2\) (Theorem 3.2(iii))
and \(w_{j+1}\ge 1\), contributing at most \(1.05/n\) each.
Hence \(E_k\le w_k D\). \(\square\)

The transport inequality is Lean end to end in log form: the
walk weight \(w_k=2^{u_k}=3^{a_k}/2^k\) is rational, so the
per-step floor losses (`log_floorPower_odd_ge`,
`log_floorPower_even_ge`), the exact weight recursion, and the
full induction (`cycleMin_transport`, `WalkTransport.lean`) are
elementary real arithmetic over the formalized cycle envelopes
`cycleMin_iterate_ge`, `cycleMin_even_ge_sq`, and
`cycleMin_prefix_pow_le`.

Consequently the cyclic defect sum \(\sum_i 1/(x_i\ln x_i)\) is
bounded above by the maximum of the walk charge
\(\sum_k g(u_k)\), \(g(u)=1/(n'^{2^u}2^u\ln n')\), over all
nonnegative closed exponent walks with \(o\) up-steps,
evaluated at the *reduced base* \(n'=n\,e^{-D}\). No free
parameter remains; the walk value feeds the \(6/5\) unroll of
Theorem 4.4 exactly as the parity charge did. At the laboratory
floor and window lengths, \(D\le 4.6\cdot 10^{-3}\), so
\(\ln n'\ge 17.07\).

This consequence is itself Lean end to end
(`WalkChargeMax.lean`): writing the charge through the rational
weight, \(g=1/(e^{W\nu}W\nu)\) with \(W=2^u=3^a/2^k\) and
\(\nu=\ln n'\), exponentiating the transport inequality gives
\(\sum_k 1/(x_k\ln x_k)\le\sum_k g(w_k)\)
(`cycleMin_defect_le_charge`), and the charge of the realized
word is dominated by the hug charge of the same length
(`cycleMin_defect_le_hug_charge`, using Theorem 5.4 below), all
under the recorded hypothesis \(\nu>0\).

### 5.3 The adversary is the hug word

**Theorem 5.4 (hug exchange).**
Among nonnegative exponent walks with prescribed \((L,o)\), the
*hug word* — take \(E\) at every step where \(u\ge 1\), else
\(O\) — is prefix-minimal: writing \(a_k\) for the odd count of
a length-\(k\) prefix,
\[
a_k^{\mathrm{hug}}\le a_k
\qquad\text{for every admissible walk and every }k,
\]
equivalently \(u_k^{\mathrm{hug}}\le u_k\). Consequently the
hug word maximises the walk charge: since \(g\) is strictly
decreasing in \(u\),
\[
g\bigl(u_k^{\mathrm{hug}}\bigr)\ge g(u_k)
\quad\text{for every }k,
\qquad\text{hence}\qquad
\sum_{k}g(u_k)\ \le\ \sum_{k}g\bigl(u_k^{\mathrm{hug}}\bigr).
\]

*Proof.* At the first disagreement with any other admissible
word, the hug word holds \(E\) where the other holds \(O\),
because hug takes \(O\) only when \(E\) is illegal and the two
words share the same prefix state. The odd-count gap
\(\delta_k=a_k(\text{other})-a_k(\text{hug})\) is a path with
steps in \(\{-1,0,+1\}\) that cannot go negative, since
\(\delta=0\) restores the same state. This is the displayed
prefix-minimality \(a_k^{\mathrm{hug}}\le a_k\); since
\(u_k=(1+\mu)a_k-k\) with the same \(k\), it transfers verbatim
to \(u_k^{\mathrm{hug}}\le u_k\). Feasible pairs
(\((1+\mu)o\ge L\)) never strand: when the odd budget is
exhausted, \(u=\text{surplus}+e_{\mathrm{left}}
\ge e_{\mathrm{left}}\), so the remaining evens are legal.
Applying the strict antitonicity of \(g\) termwise and summing
over \(k\) is the charge comparison. The prefix-minimality core
is Lean: `hugOdds_le_of_admissible`. \(\square\)

*Remark (uniqueness).* The hug word is in fact the *unique*
prefix-minimal admissible path in its \((L,o)\) class, so it
uniquely maximises the charge; at the first disagreement the
competitor already carries a strictly larger prefix odd count,
and strict monotonicity of \(g\) makes the total comparison
strict. Uniqueness is not used by the kill table; only the
displayed domination is.

The analytic half is also Lean, in a strengthened form
(`WalkChargeMax.lean`): the charge is antitone in the rational
weight (`stateCharge_antitone`, elementary \(\exp\)
monotonicity — no charge integral), so the exact hug word
maximises the total charge over *all* admissible exponent
walks, not just a fixed \((L,o)\) class
(`hug_charge_maximal`). Only the strict within-\((L,o)\)
uniqueness of the maximiser remains a human argument.

The statement is about the \(u\ge 0\) relaxation, not about
realized cycle words. Word-order (Christoffel) prefix-dominance
is *false* for this family — the greedy word \(OOEO\) beats
\(OOOE\) at \((L,o)=(4,3)\) — so the exchange argument above,
not a dominance order, is the correct mechanism.

Realized words do, however, dominate the hug word at the level
of odd counts: on any minimum-based cycle word, every length-\(k\)
prefix carries at least \(o_{\min}(k)\) odd letters. This is
Lean end to end (`cycleMin_prefix_odds_ge_hug`,
`cycleMin_odds_ge_hug`), composing the formalized cycle prefix
envelope \(2^k\le 3^{a_k}\) (`cycleMin_prefix_pow_le`) with the
hug minimality `hugOdds_least`. It is exactly the sense in which
the hug word is the cheapest adversary any hypothetical cycle
can present. The survivor-lattice generators of Proposition 4.9
lie on this hug diagonal: \((1054,665)\), \((25781,16266)\), and
the seed \((50508,31867)\) all satisfy \(o=o_{\min}(L)\) (Lean:
`hugOdds_1054`, `hugOdds_lattice_base`, `hugOdds_seed`).

**Proposition 5.5 (rotation average).**
The infinite hug walk is the rotation by \(\alpha=\log_2(3/2)\)
on \(\mathbb R/(1+\alpha)\mathbb Z\). Unique ergodicity of the
irrational rotation — extended, in the standard way, from
continuous observables to Riemann-integrable ones — gives
the charge-per-letter
\[
C_*(n')=\frac1{\ln 3}\int_1^3 n'^{\,1-t}\,t^{-2}\,dt
\ <\ \frac1{\ln 3\,\ln n'} .
\]

*Proof.* Substituting \(s=(t-1)\ln n'\) gives
\(C_*=\frac1{\ln 3\,\ln n'}\int_0^{2\ln n'}
e^{-s}(1+s/\ln n')^{-2}\,ds\), and the integrand is at most
\(e^{-s}\). \(\square\)

The display and its quantitative sharpening are Lean
(`RotationAverage.lean`): the quadratic majorant
\(t^{-2}\le 1-2(t-1)+3(t-1)^2\) on \([1,3]\) — the product with
\(t^2\) is \(1+4(t-1)^3+3(t-1)^4\) — turns the Laplace bound into
an exact antiderivative evaluation, giving
\(C_*(n')\le\bigl(1-\tfrac2\nu+\tfrac6{\nu^2}\bigr)/(\ln 3\,\nu)\)
at \(\nu=\ln n'\) with no quadrature
(`rotation_average_lt`, `rotationAverage_le`,
gap form `rotationAverage_gap`). Only the ergodic
*identification* of \(C_*\) as the infinite-word average
remains classical prose. The observable has one wrap
discontinuity, so bare unique ergodicity — uniform Birkhoff
convergence for *continuous* observables — is not invoked
directly: the identification uses its standard extension to
Riemann-integrable observables of an irrational rotation, and
the observable here is monotone with a single jump, hence
Riemann integrable and of bounded variation.

This is the infinite-word average, not a finite-\(L\)
inequality: on the certified survey the finite leftover charge
exceeds \(C_*\) by up to \(1.57\cdot 10^{-5}\), so
\(C_L\le C_*\) is false. The next two subsections quantify the
finite-\(L\) error.

### 5.4 Word identity

Write \(C_L\) for the charge-per-letter of the budgeted hug
word at \((L,o_{\min}(L))\).

**Lemma 5.6 (word identity).**
For every \(L\), the budgeted hug word at \((L,o_{\min}(L))\)
equals the exact rotation \(L\)-prefix generated by the integer
rule: \(E\) at step \(k\) if and only if \(3^a\ge 2^{k+1}\),
where \(a\) is the number of odd letters already used. In
particular \(C_L\) is a Birkhoff average of the rotation.

*Proof.* The exact rule keeps \(u\in[0,1+\alpha)\), so its
\(L\)-prefix uses exactly
\(o_{\min}=\lceil L\log 2/\log 3\rceil\) odd letters. A first
budget-forced divergence between the two words would make the
exact prefix use more of one letter than its own total, which
is impossible. Lean: `budgetedWord_eq_hugWord`, with the window
invariant `hugOdds_pow_ge` / `hugOdds_pow_lt` and minimality
`hugOdds_least` (`WalkChargeWords.lean`). \(\square\)

### 5.5 Denjoy--Koksma over certified Ostrowski blocks

Two classical ingredients are used here in a fixed coordinate,
so we record both explicitly.

*The coordinate change.* The infinite hug walk is rotation by
\(\alpha=\log_2(3/2)\) on the circle
\(\mathbb R/(1+\alpha)\mathbb Z\) (Proposition 5.5). Rescaling
by \(1/(1+\alpha)\) conjugates it to rotation by
\[
\theta=\frac{\alpha}{1+\alpha}
=\frac{\log(3/2)}{\log 3}
\]
on the standard circle \(\mathbb R/\mathbb Z\): with
\(\alpha=\log(3/2)/\log 2\) one has
\(1+\alpha=\log 3/\log 2\), and the quotient is the display.
The observable \(F(u)=n'^{\,1-2^u}/2^u\) is transported by the
same rescaling; a homeomorphic change of coordinate does not
change its total variation. All Ostrowski data below —
quotients, convergents, digits — refer to this \(\theta\).

*The Denjoy--Koksma inequality (classical; used as known).*
If \(f:\mathbb R/\mathbb Z\to\mathbb R\) has bounded variation
\(\mathrm{Var}(f)\) and \(p_j/q_j\) is a continued-fraction
convergent of the irrational \(\theta\), then for every \(x\),
\[
\Bigl|\sum_{k=0}^{q_j-1}f(x+k\theta)-q_j\int_0^1 f\Bigr|
\le\mathrm{Var}(f).
\]
The inequality is invoked below only at convergent
denominators of \(\theta\), never at an arbitrary good rational
approximation: the certified pairs \((p_j,q_j)\) are produced
by the continued-fraction recurrence from the certified shared
quotient prefix of \(\theta\)
(`theta_convergent_denominators`, `theta_convergent_numerators`,
`cf_lower_prefix`, `cf_upper_prefix`), so they are genuine
convergents of \(\theta\), unimodular and coprime
(`theta_convergents_unimodular`, `theta_convergents_coprime`).
Their approximation quality \(|\theta-p_j/q_j|<1/q_j^2\) and
the fact that the \(q_j\) rotation steps of one block permute
the \(q_j\) grid cells are additionally verified in Lean
(`theta_convergent_quality`, `theta_block_permutations`); the
variation-versus-integral inequality itself is the classical
statement and is not re-proved.

**Theorem 5.7 (block envelope).**
For the exact rotation prefix of length \(L\) at reduced base
\(n'\),
\[
\bigl|C_L-C_*(n')\bigr|\ \le\ \frac{2\,s(L)}{L},
\qquad
s(L)=\sum_j b_j,
\]
for any decomposition \(L=\sum_j b_jq_j\) into convergent
denominators \(q_j\) of \(\theta=\log(3/2)/\log 3\).

*Proof.* The observable \(F(u)=n'^{\,1-2^u}/2^u\) decreases on
the circle from \(F(0)=1\) to \(F\bigl((1+\alpha)^-\bigr)
=n'^{-2}/3\), so its variation including the wrap jump is
\(<2\); the rescaled observable on \(\mathbb R/\mathbb Z\) has
the same variation. The Denjoy--Koksma inequality stated above,
applied per block with the certified convergent quality
\(|\theta-p_j/q_j|<1/q_j^2\), bounds
the ergodic sum of each block of length \(q_j\) within
\(\mathrm{Var}(F)\) of \(q_jC_*\). The decomposition
\(L=\sum_jb_jq_j\) partitions the length-\(L\) trajectory segment
into consecutive blocks whose starting phases differ; since
Denjoy--Koksma holds uniformly in the starting phase \(x\), it
applies independently to each block, whatever phase that block
inherits from its predecessor. Summing the \(s(L)\) blocks
gives the display. \(\square\)

The denominator list
\[
1,\,2,\,3,\,8,\,19,\,65,\,84,\,485,\,1054,\,24727,\,50508,\,
125743,\,176251
\]
is certified by an interval continued fraction on the
big-integer sandwich \(2^{17087915}>3^{10781274}\) and
\(2^{16785921}<3^{10590737}\). The sandwich, the resulting real
bounds on \(\theta\), the shared quotient prefix of the two
rational endpoints, and the convergent recurrence are Lean
(`theta_sandwich_upper`, `theta_sandwich_lower`,
`lower_lt_walkTheta`, `walkTheta_lt_upper`, `cf_lower_prefix`,
`cf_upper_prefix`, `theta_convergent_denominators`,
`OstrowskiSandwich.lean`); the cylinder-interval bridge from the
endpoints to \(\theta\) itself is classical. The quantitative
hypothesis Denjoy--Koksma needs per block is also Lean: with the
matching numerators \(0,1,1,3,7,24,31,179,389,9126,18641,
46408,65049\) (`theta_convergent_numerators`), consecutive
pairs are unimodular, all pairs are coprime, every certified
convergent satisfies \(|\theta-p/q|<1/q^2\) against the
sandwich (`theta_convergents_unimodular`,
`theta_convergents_coprime`, `theta_convergent_quality`), and
each block's \(q\) rotation steps permute the \(q\) grid cells
(`theta_block_permutations`). Only the classical
variation-versus-integral inequality itself remains prose.
A Koksma-type bound
with constant \(1\) (that is, \(+1/L\)) is *false* for this
observable; the correct constant is \(2s(L)\).

### 5.6 The window theorem

**Theorem 5.8 (uniform window envelope).**
For every \(L\in[50508,\,301994)\), at the laboratory floor,
\[
C_L\ \le\ C_*(n')+\frac{2\,s(L)}{L}\ <\ \frac1{\ln 3\,\ln n'}.
\]

*Proof.* Greedy Ostrowski digits obey \(b_j\le a_{j+1}\), so
with the certified quotients
\(\theta=[0;2,1,2,2,3,1,5,2,23,2,2,1,\ldots]\) the digit sum on
the window satisfies \(s(L)\le 47\). This step is Lean: the
digit cap, exact reconstruction \(L=\sum_j b_jq_j\), and the
digit-sum bound hold for *any* denominator sequence satisfying
the convergent recurrence (`ostroDigit_le`, `ostro_sum_eq`,
`ostro_digitSum_le`, `OstrowskiNumeration.lean`), and the
certified \(\theta\) instance gives \(s(L)\le 47\) for every
\(L<301994\) structurally (`theta_digitSum_le`,
`greedyDigitSum_le`). The transport deficit
keeps \(\ln n'\ge 17.07\), hence
\[
\frac{2\,s(L)}{L}\le\frac{94}{50508}=1.87\cdot 10^{-3}
<0.00514\le\frac1{\ln 3\,\ln n'}-C_*(n'),
\]
the last gap from \(\int_0^{2\ln n}e^{-s}(1+s/\ln n)^{-2}ds
\le 1-2/\ln n+6/(\ln n)^2\), which is Lean
(`rotation_average_le`, gap form `rotationAverage_gap`,
`RotationAverage.lean`). Conclude by Lemma 5.6 and
Theorem 5.7. \(\square\)

*Scan sharpening (Lean).* An exact scan of all \(251486\)
window lengths gives max digit sum \(s=37\) (at \(L=275632\))
and a uniform envelope margin of at least \(5.48\). The digit
scan is Lean-verified: for every \(L\in[50508,301994)\) the
greedy digits over the certified denominators reconstruct \(L\)
and sum to at most \(37\) (`window_digit_scan`,
`window_digit_cap`, `window_digit_max`). The window theorem is
census-free; the scan only sharpens the constants.

### 5.7 Kill table and the period bound

The envelope controls the charge; kill decisions are the
per-length finance comparison
\(\theta(L)>\tfrac65\,B(L)\cdot\text{guard}\) of the
Theorem 4.6 architecture, which is Diophantine, not
envelope-limited.

The comparison template is itself Lean
(`cycleMin_hug_kill_criterion`, `DefectFinance.lean`): every
minimum-based cycle at \(n\ge 400\) with positive reduced
log-base must satisfy
\(1-2^L/3^o\le\tfrac65\sum_k g(\text{hugWeight}_k)\) at the
reduced base, chaining the Lean finance inequality
(`cycleMin_defect_finance`, the certified identity of
Theorem 4.6) with the defect-to-hug-charge envelope of §5.2.
The kill decisions below verify the numeric *failure* of this
inequality per length; only that evaluation, and the parity
refinement of Corollary 4.5, remain verified computation.

**Theorem 5.9 (verified computation; period bound at the
laboratory floor).**
At \(N_0=26254995\), the walk charge of Theorem 5.3 excludes
\(18\) of the \(19\) parity survivors of Theorem 5.2 through
\(L=2\cdot 10^5\). Kill margins run from \(1.1204\) at the seed
\(L=50508\) (required improvement over parity \(6.87\), walk
supplies \(7.70\); deficit \(D=7.4566\cdot 10^{-4}\)), through
\(1.1195\) and \(1.1187\) at its multiples \(101016\) and
\(151524\), up to \(7.69\) at the parity-marginal lengths. The
sole walk survivor is \(L=176251\) (margin \(0.159\); required
improvement \(48\)). The combined parity + walk contiguous
excluded prefix is \(176250\): any nontrivial Juggler cycle has
period at least \(176251\).

*Proof.* Theorem 5.2 leaves the \(19\) parity survivors. Each
is priced by the exact \((\text{step},\text{odd-count})\)
lattice dynamic program at the reduced base (Theorem 5.3) and
compared against \(\theta(L)\) under the \(6/5\) unroll;
substituting the census-free envelope of Theorem 5.8 instead
recovers the same \(18\) kills (margin \(1.1196\) at
\(L=50508\); \(L=176251\) survives at \(0.1588\)). Checksums
are Appendix B. \(\square\)

*Calibration.* At the base instance \((L,N_0)=(25781,10^6)\)
the walk charge gives margin \(0.196\) — correctly no kill
(required improvement \(32.5\), walk supplies \(6.37\)). The
mechanism did not change between the two floors; the target
did.

**Corollary 5.10 (verified computation; second laboratory
floor).**
Every integer \(2\le n\le 162849448\) reaches \(1\)
(first-passage certificate exactly as in Proposition 5.1: the
extension segment walks \(68297226\) odd starts over \(547\)
contiguous chunk records with exact integer square roots and no
failures of any kind; the maximum first passage is \(433\)
steps at seed \(78641579\), and the largest intermediate has
\(463362780\) bits at seed \(92502777\); hashes in Appendix B).
At \(N_0=162849448\) the parity table excludes the previous
survivor cluster \(\{50508,101016,151524\}\) outright and
leaves \(25\) survivors through \(L=6\cdot 10^5\); the walk
charge of Theorem 5.3 kills the \(15\) below \(478245\)
(margins \(1.198\) at \(176251\) and \(352502\), up to
\(8.44\)); lengths \(L\le 176250\) stay excluded because both
exclusions are monotone in the floor. Survivor lengths above
\(301994\) lie beyond the window of Theorem 5.8; each kill
there is a direct certified evaluation of the Theorem 5.9
comparison at the reduced base, not an instance of the window
theorem. The combined contiguous
excluded prefix is \(478244\): any nontrivial Juggler cycle has
period at least \(478245\). This is the main numerical result
of the paper.

The sole survivor is the semiconvergent fan member
\(478245=176251+301994\): required improvement over parity
\(19.46\), direct walk margin \(0.4334\) — the obstruction is
the Diophantine quality of \(|3^o-2^L|\) along the fan, not the
envelope. The kill table recomputes on commodity hardware in
minutes (Appendix B).

Beyond \(q_{13}=301994\) the window theorem needs deeper
certified quotients of \(\theta\), and killing the remaining
near-convergent survivors (starting with the fan member
\(L=478245\)) is a Diophantine question about \(|3^o-2^L|\);
neither is attempted here. The survivors are
finance-survivors, not candidate cycles.

## 6. Limitations and future directions

The result does not imply termination. The remaining
finance-survivor lengths are uncontrolled, and existence of a
cycle at such a length is open.

A start \(n\ge 2\) has a *descent certificate* if there exists a
realized finite word \(w\) with \(J^{|w|}(n)<n\). Even starts
realize \(E\); an odd start with even image realizes \(OE\). The
complement of those two words is the odd-to-odd class. If every
start above \(1\) has some descent certificate, strong induction
yields arrival at \(1\). That hypothesis is not proved, and a
uniform run bound on expanding blocks is unavailable: four
consecutive expanding blocks occur already at
\[
1999\xrightarrow{OOE}5169
\xrightarrow{OOOOEE}50093
\xrightarrow{OOE}193753
\xrightarrow{OOE}887471.
\]

The next concrete direction is the number \(p\) of odd runs on a
minimum-based cycle --- equivalently, the number of excursions
on the necklace of Section 4. The run form already gives
\(p\le e\) and, because the first odd run has length at least
two, \(p\le o-1\), hence \(p\le\min(e,o-1)<0.3691\,L\) on an
expanding word. That is only the trivial ceiling. A genuine
lower bound on \(p\), or a peak-height / peak-count tradeoff,
would feed Theorem 4.7. Neither is proved here. The remaining
gap recorded there is the missing link from the forced lift at
the minimum, through the complete necklace, to the entry cell;
it is not a halt theorem.

The same pattern --- a piecewise power map, integer rounding,
and a cycle minimum --- produces a defect-financing obstruction.
The Juggler-specific content is the interaction of \(x^{3/2}\)
and \(x^{1/2}\). Analogous questions for other piecewise
floor-power maps are not taken up here.

Lean names are in Appendix A. The computational certificates
are Propositions 1.3 and 5.1.

## Appendix A. Lean names

The core mathematical lemmas of Sections 2--4 are mechanized in
Lean 4. The names below are the corresponding theorems in
`formal/Problems/Juggler/`, imported by `Problems.JugglerPaper`.
Selected finite classifications of Section 3 are `native_decide`
tables (Appendix D). Theorems 4.6 and 4.8 are independently
certified computations. Proposition 4.9's arithmetic is Lean;
its identification with \(\mathcal E_{\mathrm{run}}\) is
Theorem 4.8.

| Text | Lean |
|---|---|
| itinerary semantics | `follows_iff_word`, `image_eq_iterate`, `image_append` |
| Theorem 2.1 | `image_monotone_of_follows` |
| Theorem 2.2 | `power_bound_word` |
| Corollary 2.3 | `power_bound_contracts` |
| Theorem 2.4 | `global_defect_identity` |
| Theorem 2.5 | `global_defect_eq_zero_iff_localsTight`, `global_defect_eq_zero_implies_monochrome`, `power_bound_eq_iff_extremal` |
| Theorem 2.6 | `global_defect_append` |
| Corollary 2.7 | `image_eq_start_defectRatio` |
| per-step slack | `one_plus_eta_lt_succ_sq` |
| Lemma 3.1 | `odd_cell_unique` |
| CycleMin | `CycleMin` |
| Theorem 3.2 | `cycle_word_formally_expanding`, `cycleMin_start_odd`, `cycleMax_start_even`, `cycleMin_not_end_odd`, `square_scale_superquadratic`, `cycleMin_to_even_superquadratic` |
| Lemma 3.3 | `lower_growth_word` |
| Lemma 3.4 | `oo_suffix_threshold`, `ooo_suffix_threshold`, `threshold_inherits_odd_append`, `cycle_last_even_interval`, `cycle_last_even_ne_odd_sq`, `no_cycle_odd_run_append_even`, `no_cycle_word_ooe` |
| odd-run block | `oddEvenBlock` |
| Lemma 3.5 | `no_cycle_word_oooeoe`, `no_cycle_word_ooooee` |
| Theorem 3.6 | `no_cycle_word_length_le_six` |
| Lemma 3.7 | `no_cycle_word_ooooeoe`, `no_cycle_word_oooooee` |
| Theorem 3.8 | `no_cycle_word_length_le_seven`, with `no_cycle_word_ooeoooe`, `no_cycle_word_oooeooe` |
| Lemma 3.9 | `cycle_trailing_evens_lt` |
| Lemma 3.10 | `lowerDenom_replicate_odd`, `odd_run_lower_growth` |
| Lemma 3.11 | `no_follows_seven_odds_of_lt256` |
| Theorem 3.12 | `no_cycle_word_two_even_ee`, `no_cycle_word_two_even_eoe` |
| Theorem 3.13 | `no_cycleMin_gapped_three_even_ee`, `no_cycleMin_gapped_three_even_eoe` |
| Theorem 3.14 | `no_cycle_word_three_even_eee`, with `no_cycle_word_ooooooeee` |
| Theorem 3.15 | `no_cycle_word_three_even_eoee` |
| Theorem 3.16 | `no_cycle_word_three_even_eooee` |
| Theorem 3.17 | `no_cycle_word_three_even_eoooee` |
| Theorem 3.18 | `no_cycle_word_three_even_eeoe` |
| Theorem 3.19 | `no_cycle_word_three_even_eoeoe` |
| Theorem 3.20 | `no_cycle_word_three_even_eooeoe` |
| Theorem 3.21 | `no_cycle_word_gapped_three_even_ee`, `no_cycle_word_gapped_three_even_eoe` |
| Theorem 3.22 | `no_cycle_word_even_count_le_three` |
| Corollary 3.23 | `cycle_word_length_ge_eleven` |
| Lemma 3.21b | canonical run form; Theorem 3.2 |
| Lemma 3.21a | the case split of Theorem 3.22 |
| Lemma 4.1 | `log_le_two_log_add` |
| Lemma 4.2 | `log_step_even`, `log_step_odd` |
| Lemma 4.3 | `cycleMin_log_envelope` |
| Theorem 4.4 | `cycleMin_finance` |
| Corollary 4.4c | `cycleMin_log_envelope_inv`, `cycleMin_finance_inv_sum` |
| Lemma 4.4b | odd-count monotonicity; human proof, not Lean |
| Theorem 4.6 | certified identity `cycleMin_defect_finance`, per-step losses `log_floorPower_even_ge_sub`, `log_floorPower_odd_ge_sub`, invariants `cycleMin_log_le_weight`, `cycleMin_charge_prefix` (`DefectFinance.lean`); the numeric table is verified computation |
| Theorem 4.7 | run-type packing; human proof, not Lean |
| Theorem 4.8 | run-type table; verified computation, not Lean |
| Proposition 4.9 | `run_survivor_unimodular`, `run_survivor_seed_F2`, `run_survivor_seed_F3`, `three_pow_step_gt_two_pow_step`, `runSurvivors_length` |
| Proposition 5.1 | laboratory floor; certified computation, not Lean |
| Theorem 5.2 | raised cutoff; verified computation, not Lean |
| Theorem 5.3 | transport inequality `cycleMin_transport`, per-step losses `log_floorPower_even_ge`, `log_floorPower_odd_ge` (`WalkTransport.lean`); §5.2 consequence `cycleMin_defect_le_charge`, `cycleMin_defect_le_hug_charge` (`WalkChargeMax.lean`) |
| Theorem 5.4 | combinatorial core `hugOdds_le_of_admissible`; cycle-word domination `cycleMin_prefix_odds_ge_hug`, `cycleMin_odds_ge_hug`; charge maximisation `stateCharge_antitone`, `hug_charge_maximal` (`WalkChargeMax.lean`); strict within-\((L,o)\) uniqueness human |
| Proposition 5.5 | ergodic identification human; Laplace bound Lean: `inv_sq_le_quad`, `rotation_average_le`, `rotation_average_lt`, `rotationAverage_le`, `rotationAverage_lt`, `rotationAverage_gap` (`RotationAverage.lean`) |
| Lemma 5.6 | `budgetedWord_eq_hugWord`, `hugOdds_pow_ge`, `hugOdds_pow_lt`, `hugOdds_pow_gt`, `hugOdds_least` |
| Theorem 5.7 | Denjoy--Koksma's variation inequality (known), not Lean; quotient arithmetic `theta_sandwich_upper`, `theta_sandwich_lower`, `lower_lt_walkTheta`, `walkTheta_lt_upper`, `cf_lower_prefix`, `cf_upper_prefix`, `theta_convergent_denominators`; DK hypotheses `theta_convergent_numerators`, `theta_convergents_unimodular`, `theta_convergents_coprime`, `theta_convergent_quality` (\(|\theta-p/q|<1/q^2\)), `theta_block_permutations` |
| Theorem 5.8 | digit cap Lean: general numeration `ostroDigit_le`, `ostro_sum_eq`, `ostro_digitSum_le`, instance `theta_digitSum_le`, `greedyDigitSum_le`; scan `window_digit_scan`, `window_digit_cap`, `window_digit_max`; Denjoy--Koksma comparison human |
| Theorem 5.9 | kill template `cycleMin_hug_kill_criterion` (`DefectFinance.lean`); the per-length kill table is verified computation |
| Corollary 5.10 | second floor and kill table; verified computation, not Lean |
| short certificates (Section 6) | `even_finiteProgress`, `odd_even_finiteProgress` |
| no certificate \(\Rightarrow\) odd-to-odd | `no_finiteProgress_implies_odd_odd` |
| induction to \(1\) | `reachesOne_of_all_finiteProgress` |
| four-block chain | `four_block_pe_1999` |

## Appendix B. Admissible lengths

The record lengths of \(\gamma(L)\) through \(10^5\), with the
parity \(6/5\) bound \(n_{\max}\) of Section 4, are

| \(L\) | \(o_{\min}\) | \(n_{\max}\) |
|---:|---:|---:|
| \(1\) | \(1\) | \(3\) |
| \(3\) | \(2\) | \(7\) |
| \(11\) | \(7\) | \(25\) |
| \(19\) | \(12\) | \(133\) |
| \(84\) | \(53\) | \(2323\) |
| \(569\) | \(359\) | \(23568\) |
| \(1054\) | \(665\) | \(788014\) |
| \(25781\) | \(16266\) | \(26254995\) |
| \(50508\) | \(31867\) | \(162848325\) |

At the verified descent floor \(N_0=10^6\) the first seven rows
are excluded. The set \(\mathcal E=\mathcal E(10^6)\) is defined
by Proposition 4.4a: for each \(1\le L\le 10^5\), compute
\(o_{\min}(L)\) by exact integer arithmetic and \(n_{\max}(L)\)
from the parity inequality, and retain \(L\) if and only if
\(n_{\max}(L)>10^6\). This produces \(141\) lengths. The first
few are
\[
25781,\;26835,\;27889,\;28943,\;29997,
\]
and a typical combination is \(26835=25781+1054\). The last is
\(99561\). The complete list is the `lengths` array of
`data/research/juggler/cycle_finance/exceptions_parity.json`.
The SHA-256 of that array, serialized as a JSON list of integers
with no spaces, is
`dd71aa1527656ba51cb031bafa5497f7bfdbbc43151ffba2c595793326bf7944`.
The SHA-256 of the whole file `exceptions_parity.json` is
`6b4eec79295b70cdeb9f7db677b7fd57bcb9bd1b51177e1e74aad7bd6e2262ff`.
The SHA-256 of the first-passage file `floor.json` in the same
directory is
`5b1ce1eec61301cf5b4f969cd5b58954255194e5c7b21c08a518d71679af87fc`.
The parity table is written by
`research.juggler_sequence.cycle_finance.write_parity_artifacts`.
The first-passage file is regenerated by
`python -m research.juggler_sequence.cycle_finance`.

The run-type table of Theorem 4.8 is
`data/research/juggler/cycle_finance/budget_opt.json`. The
\(42\) excluded lengths are
`killed_by_budget`; their SHA-256, serialized as a JSON list of
integers with no spaces, is
`9d108776d6dc5dc1ae2594058850463cd2d3995cc57b9811471f08e3b818b90a`.
The complementary \(99\) lengths are \(\mathcal E_{\mathrm{run}}\).
Their SHA-256, in the same serialization, is
`9e2098923ccb39933630b116133a3fc2ddaf98ace4eb76dbab9b5ab9f6e604e6`.
The first few survivors remain
\[
25781,\;26835,\;27889,\;28943,\;29997;
\]
the last survivor is \(99477\). The three families and the
unimodular basis are Proposition 4.9. The finite leftover tables
of Section 3 are the Lean `native_decide` evaluations named in
Appendix A (`LeftoverEval.lean`, `LeftoverShort.lean`,
`LeftoverFamilies.lean`). The lattice arithmetic of
Proposition 4.9 is `RunSurvivorLattice.lean`.

The laboratory instance of Section 5 has its own artifacts. The
first-passage certificate of Proposition 5.1 is
`data/research/juggler/cycle_finance/floor_verify/N26254995/certificate.json`;
the SHA-256 of its chunk records is
`cbcbb540dd860b775d2a3b4351f7cf779609104d3aaf30c342aed6b87f36c9dc`.
The parity survivor list of Theorem 5.2 has SHA-256
`d5946efdfac95c715ea46c81979a0eeaf40ad8a1dc893d161bab84ffa7f2afd9`.
The walk-charge kill table of Theorem 5.9 is
`data/research/juggler/cycle_walk_charge/survey.json`; the
SHA-256 of the walk-alive list is
`225d76ad12802a690934d01e2d37b3418865441a6825a015dd883c989d8942ec`.
The second-floor certificate of Corollary 5.10 is
`data/research/juggler/cycle_finance/floor_verify/N162849448/certificate.json`;
the SHA-256 of its chunk records is
`35d9755ce52a225a161b009d0f3674b24a5d0add16035f09ea83cf3880414ae4`.
Its parity survivor scan is
`data/research/juggler/cycle_walk_charge/new_floor_parity_leftovers.json`,
and the \(15\) kill records under
`data/research/juggler/cycle_walk_charge/new_floor_kills/` have
SHA-256
`148180cbbfba93985b7a1be455fee16db97816f1534b1feca5a4740d475aeda0`
(concatenated in length order); the direct non-kill record for
the survivor \(478245\) (margin \(0.4334\)) is stored alongside.
The exact-integer CPU computation with guarded comparisons is
the authoritative record for every claim in this note; a GPU
implementation
(`research.juggler_sequence.cycle_walk_charge_gpu`) is provided
as an optional reproducibility aid, no statement depends on it,
and its performance figures live in the repository
documentation.
The probes are
`research.juggler_sequence.cycle_walk_charge` (transport and
kill table), `cycle_walk_ostrowski` (certified quotient
sandwich and block envelope), and `cycle_walk_window` (window
scan); artifacts live under
`data/research/juggler/cycle_walk_*`.

*Reproducibility of the second-floor kill table.* From a fresh
checkout of the repository, `pip install -e .` followed by, for
a survivor length \(L\),

```text
python -c "from research.juggler_sequence.cycle_walk_charge \
import certified_report; print(certified_report(L, 162849448))"
```

recomputes the authoritative certified record behind
Corollary 5.10 for that length (at \(L=478245\) it prints the
non-kill); the same call through the GPU port,
`python -m research.juggler_sequence.cycle_walk_charge_gpu L
162849448`, reproduces it in seconds per length on one consumer
GPU. The first-floor kill table of Theorem 5.9 is
`python -m research.juggler_sequence.cycle_walk_charge
--survey`.

## Appendix C. Exact floor defect

This appendix records the exact identity behind Theorem 2.2. The
present note uses only the nonnegativity \(\Delta_w(n)\ge0\). A
nontrivial itinerary-dependent lower bound on \(\Delta_w\) is left
for future work.

For a single branch,
\[
x^e=J(x)^2+\rho(x),\qquad
e=\begin{cases}1,&x\ \text{even},\\3,&x\ \text{odd},\end{cases}
\]
with \(0\le\rho(x)<2J(x)+1\). Write
\(\operatorname{gap}(a,\rho,e)=(a+\rho)^e-a^e\). The *global
defect* \(\Delta_w(n)\) is the terminal value of the resulting
power-gap recurrence.

**Theorem 2.4 (global defect identity).**
If \(w\) is realized at \(n\) and \(m=J^{|w|}(n)\), then
\[
n^{3^{\#O(w)}}=m^{2^{|w|}}+\Delta_w(n),\qquad\Delta_w(n)\ge0.
\]
Theorem 2.2 is the inequality \(\Delta_w(n)\ge0\).

*Proof.* Induct on \(w\). The empty word is \(n=n+0\). An even
letter substitutes \(x=J(x)^2+\rho(x)\) into the inductive
identity and lifts the new remainder through \(2^\ell\). An odd
letter cubes the identity and then substitutes
\(x^3=J(x)^2+\rho(x)\). Each step adds a nonnegative power-gap.
\(\square\)

For a one-letter illustration, \(n=3\) and \(w=O\) give
\(J(3)=5\) and \(3^3=27=5^2+2\), so \(\Delta_O(3)=2\).

**Theorem 2.5 (vanishing).**
If \(w\) is realized at \(n\), the following are equivalent:
\(\Delta_w(n)=0\); every local remainder along \(w\) vanishes; and
\(\bigl(J^{|w|}(n)\bigr)^{2^{|w|}}=n^{3^{\#O(w)}}\). In that case
\(w\) is monochrome: either \(w=E^k\) and \(n=a^{2^k}\) for an
even \(a\), or \(w=O^k\) and \(n=a^{2^k}\) for an odd \(a\). A
realized mixed word therefore has \(\Delta_w(n)>0\).

*Proof.* Theorem 2.4 gives the first and third items. A power-gap
vanishes if and only if its addend vanishes, so zero defect forces
every remainder to vanish, and conversely. Vanishing remainders
preserve parity, hence monochrome itineraries, and unique
factorization produces the two power towers. \(\square\)

**Theorem 2.6 (composition).**
If \(u\) is realized at \(n\) and \(v\) is realized at
\(m=J^{|u|}(n)\), then \(\Delta_{uv}(n)\) is the sum of two
power-gaps, one lifting \(\Delta_u(n)\) through \(3^{\#O(v)}\)
and one lifting \(\Delta_v(m)\) through \(2^{|u|}\). In
particular \(\Delta_v(m)^{2^{|u|}}\le\Delta_{uv}(n)\), and every
local remainder satisfies \(\rho_j^{2^j}\le\Delta_w(n)\).

*Proof.* Apply Theorem 2.4 to \(u\), to \(v\), and to \(uv\), and
expand the two power-gaps. \(\square\)

Composition is polynomial, not additive. The Lean form is
`global_defect_append`.

**Corollary 2.7 (cycle surplus).**
If \(w\) is a cycle word at \(n\), then
\(\Delta_w(n)=n^{3^{\#O(w)}}-n^{2^{|w|}}\) exactly.

*Proof.* Theorem 2.4 with \(m=n\). \(\square\)

A mixed word has strict total defect, but the relative slack of a
single letter tends to \(0\) with the state, so no uniform local
tax exists. Theorem 4.4 does not use these identities.

## Appendix D. Family exclusions

This appendix records the small-cycle censuses (Lemma 3.5,
Theorem 3.6, Lemma 3.7, Theorem 3.8) and the family-by-family
exhaustion used by Lemma 3.21a and Theorem 3.22. Each geometry is
killed by a next-square obstruction, by long odd-run growth
against a last-even cell, or by a finite exceptional window.

**Lemma 3.5 (two length-six exclusions).**
Neither \(OOOEOE\) nor \(OOOOEE\) is a cycle word at any \(n\ge 2\).

*Proof.* First, if \(n\ge 256\), then
\[
n^{81}>2^{130}(n+1)^{64}.
\]
Indeed \(257^{64}<2\cdot 256^{64}\) because
\((1+1/256)^{64}<e^{64/256}=e^{1/4}<2\), and
\(256(n+1)\le 257\,n\), so \((n+1)^{64}<2n^{64}\). Then
\(2^{130}(n+1)^{64}<2^{131}n^{64}\). Since \(n\ge 256=2^8\), one has
\(n^{17}\ge 2^{136}\), and therefore
\(2^{131}n^{64}<2^{136}n^{64}\le n^{81}\).

For \(2\le n<256\), neither word returns to its start. This is a
table of \(254\) evaluations of each word: at every start, either
some letter fails to match the current parity, or the six-step image
differs from the start. The same finite check is the Lean
`native_decide` evaluation behind `no_cycle_word_oooeoe` and
`no_cycle_word_ooooee` (Appendix A).

Now suppose \(OOOOEE\) is a cycle word at \(n\ge 256\), and write
\(z=J^4(n)\) for the image after the prefix \(OOOO\). Lemma 3.4(iv)
gives \(J(z)<(n+1)^2\), and the preceding even letter gives
\(z<(J(z)+1)^2\), hence \(z<(n+1)^4\). Lemma 3.3 on \(OOOO\) gives
\(n^{81}\le 2^{130}z^{16}\), so
\(n^{81}<2^{130}(n+1)^{64}\), contradicting the tail inequality.

Finally suppose \(OOOEOE\) is a cycle word at \(n\ge 256\). Write
\(z_3=J^3(n)\) and \(y=J(z_3)=\lfloor\sqrt{z_3}\rfloor\), so
\(z_3<(y+1)^2\). Lemma 3.3 on \(OOO\) gives
\(n^{27}\le 2^{38}z_3^8<2^{38}(y+1)^{16}\). Cubing yields
\(n^{81}<2^{114}(y+1)^{48}\). The last letters \(OE\) give the odd-cell
bound \(y^3<(n+1)^4\). Write \(A=n+1\ge 257\). We claim
\((y+1)^3<2A^4\). If \(y\le A\), this is \((A+1)^3<2A^4\). If
\(y>A\), then \(y\ge 258\), so \(3y+1<y^2\) and hence
\((y+1)^3=y^3+3y^2+3y+1<A^4+4y^2\), while \(4y^2<A^4\) because
\(4y^3<4A^4\le yA^4\). Raising \((y+1)^3<2A^4\) to the sixteenth
power gives \((y+1)^{48}<2^{16}(n+1)^{64}\). Combining with the cubed
lower envelope produces again \(n^{81}<2^{130}(n+1)^{64}\). \(\square\)

**Theorem 3.6 (small-cycle census).**
No word of length at most six is a cycle word at any \(n\ge 2\).

*Proof.* Rotating a cycle word by one letter moves the base point one
step along the trajectory and yields another cycle word; every state of
the cycle is at least \(2\), because a trajectory that reaches \(1\) stays
at \(1\) and cannot return to a start \(n\ge 2\).

If every letter is odd, the start is odd, hence \(n\ge 3\), and the
odd branch strictly increases there: \(J(x)>x\) for odd \(x\ge 3\),
since \(x^3\ge(x+1)^2\). The trajectory ascends strictly and never returns.
Otherwise some letter is even, and a rotation ending just after that
letter produces an even-terminating cycle word \(vE\) of the same
length based at a cycle state \(m\ge 2\). It therefore suffices to
exclude even-terminating cycle words of length at most six.

By Theorem 3.2(i) a cycle word is formally expanding. No
even-terminating word of length one or two is expanding (\(2>3^0\) and
\(4>3\)).

Length three: the only expanding candidate is \(OOE\). If \(m\ge 5\)
realizes \(OO\), Lemma 3.4(i) gives \(J^2(m)\ge(m+1)^2\), contradicting
Lemma 3.4(iv). The only smaller odd start is \(m=3\), where
\(J^2(3)=11\) is odd, so the final even letter is not realized.

Length four: the expanding filter requires three odd letters among the
first three, leaving only \(O^3E\), excluded by Lemma 3.4(v).

Length five: the filter requires four odd letters among the first
four, leaving only \(O^4E\), excluded by Lemma 3.4(v).

Length six: the filter requires at least four odd letters among the
first five, leaving \(O^5E\), \(EOOOOE\), \(OEOOOE\), \(OOEOOE\),
\(OOOEOE\), and \(OOOOEE\). Lemma 3.4(v) excludes \(O^5E\). The word
\(EOOOOE\) rotates one step onto \(OOOOEE\), and \(OEOOOE\) rotates
two steps onto \(OOOEOE\); both are excluded by Lemma 3.5.

It remains to exclude \(OOEOOE\). Let this word be a cycle word at
some start, and rotate to a cycle minimum \(m\ge 2\). The three
alignments of the two even letters are \(OOEOOE\), \(OEOOEO\), and
\(EOOEOO\). The last starts even, so it cannot be a minimum, by
Theorem 3.2(ii). The middle starts \(OE\): the first image is even
and strictly below \(m^2\), whereas every even state after a cycle
minimum is at least \(m^2\), as proved in Theorem 3.2(iii). Thus the
minimum orientation is \(OOEOOE\). In particular \(m\) is odd, so
\(m\ge 3\). The prefix \(OOE\) must be realized. If \(m=3\), then
\(3\to 5\to 11\) and \(11\) is odd, so \(OOE\) is not realized. Hence
\(m\ge 5\). Write \(y=J^3(m)\) for the state after \(OOE\). Then
\(y\ge m\) by minimality, so \(y\ge 5\). The suffix \(OO\)
is realized at \(y\), and Lemma 3.4(i) gives
\(J^2(y)\ge(y+1)^2\ge(m+1)^2\). The last letter is even, so
Lemma 3.4(iv) gives \(J^2(y)<(m+1)^2\). \(\square\)

**Lemma 3.7 (two length-seven exclusions).**
Neither \(OOOOEOE\) nor \(OOOOOEE\) is a cycle word at any \(n\ge 2\).

*Proof.* First, if \(n\ge 14\), then
\[
n^{243}>2^{422}(n+1)^{128}.
\]
Indeed \(14(n+1)\le 15n\), so
\((n+1)^{128}\le(15/14)^{128}n^{128}\). The finite comparison
\(2^{422}15^{128}<14^{243}\) then yields
\(2^{422}(n+1)^{128}<14^{115}n^{128}\le n^{243}\).

For \(2\le n<14\), neither word is realized: at every such start,
some letter fails to match the current parity. The same finite check
is the Lean `native_decide` evaluation behind
`no_cycle_word_ooooeoe` and `no_cycle_word_oooooee` (Appendix A).

Now suppose \(OOOOOEE\) is a cycle word at \(n\ge 14\), and write
\(z=J^5(n)\) for the image after the prefix \(OOOOO\). Lemma 3.4(iv)
on the last even letter, together with the preceding even letter,
gives \(z<(n+1)^4\). Lemma 3.3 on \(OOOOO\) gives
\(n^{243}\le 2^{422}z^{32}\), so
\(n^{243}<2^{422}(n+1)^{128}\), contradicting the tail inequality.

Finally suppose \(OOOOEOE\) is a cycle word at \(n\ge 14\). Write
\(z_4=J^4(n)\) and \(y=J(z_4)=\lfloor\sqrt{z_4}\rfloor\), so
\(z_4<(y+1)^2\). Lemma 3.3 on \(OOOO\) gives
\(n^{81}\le 2^{130}z_4^{16}<2^{130}(y+1)^{32}\). Cubing yields
\(n^{243}<2^{390}(y+1)^{96}\). The last letters \(OE\) give the odd-cell
bound \(y^3<(n+1)^4\). Write \(A=n+1\ge 15\). The same comparison
\((y+1)^3<2A^4\) as in Lemma 3.5 holds at this smaller scale. Raising
to the thirty-second power gives
\((y+1)^{96}<2^{32}(n+1)^{128}\). Combining with the cubed lower
envelope produces again \(n^{243}<2^{422}(n+1)^{128}\). \(\square\)

**Theorem 3.8 (small-cycle census through length seven).**
No word of length at most seven is a cycle word at any \(n\ge 2\).

*Proof.* The reduction of Theorem 3.6 applies at every length: an
all-odd word cannot return, and every mixed cycle word rotates to an
even-terminating cycle word based at a cycle state \(m\ge 2\).
Lengths at most six are Theorem 3.6. It remains to exclude
even-terminating cycle words of length seven.

By Theorem 3.2(i) a cycle word is formally expanding. The
even-terminating expanding length-seven words are exactly
\(O^6E\), \(EO^5E\), \(OEO^4E\), \(OOEO^3E\), \(O^3EO^2E\),
\(O^4EOE\), and \(O^5EE\). Lemma 3.4(v) excludes \(O^6E\). The word
\(EO^5E\) rotates one step onto \(O^5EE\), and \(OEO^4E\) starts
\(OE\), so it cannot be a cycle minimum (Theorem 3.2(iii)) and
rotates two steps onto \(O^4EOE\); both leftovers are excluded by
Lemma 3.7.

It remains to exclude \(OOEO^3E\) and \(O^3EO^2E\). Rotate either
word to a cycle minimum \(m\ge 2\). For \(OOEO^3E\) the minimum
orientation retains the internal even letter followed by the suffix
\(OOO\). Then \(m\ge 3\), the prefix through that even letter is
realized, and Lemma 3.4(ii) at threshold \(3\) contradicts the last
even cell. For \(O^3EO^2E\) the same bootstrap applies with suffix
\(OO\) and threshold \(5\), once \(m=3\) is removed: at \(m=3\) the
state after \(OOO\) is even, so the next even letter is not
realized. \(\square\)

**Theorem 3.12 (two-even leftover families).**
Let \(k\ge 6\) and \(n\ge 2\). Neither \(O^{k-2}EE\) nor
\(O^{k-3}EOE\) is a cycle word at \(n\).


*Proof.* First, if \(n\ge 256\), then
\[
n^{3^{k-2}}>2^{e_{k-2}}(n+1)^{2^k}.
\]
The case \(k=6\) is the tail inequality of Lemma 3.5. If the display
holds at some \(k\ge 6\), cubing both sides produces
\[
n^{3^{k-1}}
>
2^{3e_{k-2}}(n+1)^{3\cdot 2^k}.
\]
The recurrence of Lemma 3.10 gives \(e_{k-1}=3e_{k-2}+2^{k-1}\), so
the desired comparison at length \(k+1\) reduces to
\(2^{2^{k-1}}<(n+1)^{2^k}\). Equivalently \(2<(n+1)^2\), which holds
for every \(n\ge 256\).

Now suppose \(O^{k-2}EE\) is a cycle word at such an \(n\). Write
\(z=J^{k-2}(n)\). Lemma 3.9 with \(r=2\) gives \(z<(n+1)^4\).
Lemma 3.10 on the prefix \(O^{k-2}\) gives
\(n^{3^{k-2}}\le 2^{e_{k-2}}z^{2^{k-2}}\), hence
\(n^{3^{k-2}}<2^{e_{k-2}}(n+1)^{2^k}\), contradicting the tail.

Finally suppose \(O^{k-3}EOE\) is a cycle word at such an \(n\).
Write \(z=J^{k-3}(n)\) and \(y=\lfloor\sqrt z\rfloor\), so
\(z<(y+1)^2\). Lemma 3.10 on \(O^{k-3}\) and cubing produce
\(n^{3^{k-2}}<2^{3e_{k-3}}(y+1)^{3\cdot 2^{k-2}}\). The last letters
\(OE\) give the odd-cell bound \(y^3<(n+1)^4\). The comparison
\((y+1)^3<2(n+1)^4\) of Lemma 3.5 applies at this scale. Raising it
to the power \(2^{k-2}\) and using \(e_{k-2}=3e_{k-3}+2^{k-2}\)
recovers again \(n^{3^{k-2}}<2^{e_{k-2}}(n+1)^{2^k}\).

For \(2\le n<256\), the cases \(k=6\) and \(k=7\) are Lemmas 3.5
and 3.7. The remaining short words \(O^6EE\), \(O^5EOE\), and
\(O^6EOE\) fail to return on the same \(254\)-start window; this is
the Lean `native_decide` evaluation behind
`no_cycle_word_two_even_ee` and `no_cycle_word_two_even_eoe`
(Appendix A). Any longer leftover of either family begins with
seven consecutive odd letters, which Lemma 3.11 forbids on this
window. \(\square\)

**Theorem 3.13 (first-even transport).**
Let \(n\ge 2\). No minimum-based cycle word at \(n\) has the form
\(O^aEO^bEE\) with \(a\ge 2\) and \(b\ge 4\), or the form
\(O^aEO^bEOE\) with \(a\ge 2\) and \(b\ge 3\).


*Proof.* Write \(y=J^{a+1}(n)\) for the state after the first even
letter. Minimum-basedness gives \(y\ge n\). In the first family the
remainder after that letter is \(O^bEE\) with \(b+2\ge 6\); in the
second it is \(O^bEOE\) with \(b+3\ge 6\). The trailing-even and
last-odd cells of those remainders are measured against the cycle
start \(n\). Combined with Lemma 3.10 at the remainder start \(y\),
the same algebra as in Theorem 3.12 produces
\[
y^{3^{\ell-2}}
<
2^{e_{\ell-2}}(n+1)^{2^\ell}
\le
2^{e_{\ell-2}}(y+1)^{2^\ell},
\]
where \(\ell\) is the remainder length. If \(y\ge 256\), the first
paragraph of Theorem 3.12 supplies the opposite inequality at \(y\).

If \(y<256\), then \(n\le y<256\). A gapped leftover of total
length at least \(17\) has \(a\ge 7\) or \(b\ge 7\), so either the
prefix or the remainder realizes seven consecutive odd letters,
contradicting Lemma 3.11. The finitely many short-gap words with
\(2\le a\le 6\) and \(b\le 6\) fail to be minimum-based cycle words
on the window \(2\le n<256\); this is the Lean `native_decide`
evaluation behind `no_cycleMin_gapped_three_even_ee` and
`no_cycleMin_gapped_three_even_eoe` (Appendix A). \(\square\)

**Theorem 3.14 (three trailing evens).**
Let \(a\ge 6\) and \(n\ge 2\). The word \(O^aEEE\) is not a cycle
word at \(n\).


*Proof.* Write \(z=J^a(n)\). Lemma 3.9 with \(r=3\) gives
\(z<(n+1)^8\). Lemma 3.10 then yields
\(n^{3^a}<2^{e_a}(n+1)^{2^{a+3}}\) on any such cycle word. For
\(n\ge 128\) the opposite comparison
\[
n^{3^a}>2^{e_a}(n+1)^{2^{a+3}}
\]
holds. The case \(a=6\) is
\(n^{729}>2^{1330}(n+1)^{512}\). Indeed, for \(n\ge 128\) one has
\((n+1)^{512}<(129/128)^{512}n^{512}<e^4 n^{512}<64\,n^{512}\), so
the claimed bound reduces to \(n^{217}>2^{1336}\). Since
\(n\ge 128=2^7\), the left side is at least \(2^{1519}\). Cubing
the \(a=6\) comparison produces the general case: the recurrence of
Lemma 3.10 reduces the inductive step to \((n+1)^4>2\), which holds
for every \(n\ge 128\).

For \(2\le n<128\), the case \(a=6\) is a table of evaluations of
\(OOOOOOEEE\): at every such start the word fails to return. The
same finite check is the Lean `native_decide` evaluation behind
`no_cycle_word_ooooooeee` (Appendix A). For \(a\ge 7\) the prefix
contains seven consecutive odd letters, which Lemma 3.11 forbids
on this window. \(\square\)

**Theorem 3.15 (mixed bunched family \(EOEE\)).**
Let \(a\ge 5\) and \(n\ge 2\). The word \(O^aEOEE\) is not a cycle
word at \(n\).


*Proof.* First let \(n\ge 4\), and write \(z=J^a(n)\),
\(y=\lfloor\sqrt z\rfloor\), and \(p=J(y)\). Lemma 3.9 with
\(r=2\) after the prefix \(O^aEO\) gives \(p<(n+1)^4\). The letter
after \(y\) is odd, so Lemma 3.10 at length one yields
\(y^3\le 4p^2<4(n+1)^8\). For \(n\ge 4\) one has
\(4(n+1)^8<(n+1)^9\), hence \(y<(n+1)^3\). The even cell at \(z\)
then gives \(z<(y+1)^2\le(n+1)^6\). Combined with Lemma 3.10,
any such cycle word would satisfy
\[
n^{3^a}<2^{e_a}(n+1)^{6\cdot 2^a}.
\]

For \(a=5\) and \(n\ge 314\), the opposite comparison
\(n^{243}>2^{422}(n+1)^{192}\) holds. The base instance is the
finite inequality \(2^{422}315^{192}<314^{243}\). If the display
holds at some \(n\ge 1\), the elementary comparison
\(n(n+2)<(n+1)^2\) upgrades it to the same display at \(n+1\).
Cubing then produces the comparison at \(a+1\), once
\((n+1)^6>4\). In particular the case \(a=6\) already holds for
every \(n\ge 16\).

For \(2\le n<314\) and \(a=5\), and for \(2\le n<16\) and
\(a=6\), the word fails to return; these are the Lean
`native_decide` evaluations behind `no_cycle_word_three_even_eoee`
(Appendix A). For \(a\ge 7\) and \(n<256\), Lemma 3.11 applies. For
\(a\ge 6\) and \(n\ge 16\), the tail of the previous paragraph
applies. \(\square\)

**Theorem 3.16 (mixed bunched family \(EOOEE\)).**
Let \(a\ge 4\) and \(n\ge 2\). The word \(O^aEOOEE\) is not a
cycle word at \(n\).


*Proof.* First let \(n\ge 32\), and write \(z=J^a(n)\),
\(y=\lfloor\sqrt z\rfloor\), and \(p\) for the image after the
prefix \(O^aEOO\). Lemma 3.9 with \(r=2\) gives \(p<(n+1)^4\).
The two letters after \(y\) are odd, so Lemma 3.10 at length two
yields \(y^9\le 2^{10}p^4<2^{10}(n+1)^{16}\). For \(n\ge 32\) one
has \(2^{10}<(n+1)^2\), hence \(y<(n+1)^2\). The even cell at
\(z\) then gives \(z<(y+1)^2\le(n+1)^4\). Combined with
Lemma 3.10, any such cycle word would satisfy
\[
n^{3^a}<2^{e_a}(n+1)^{2^{a+2}}.
\]
For \(n\ge 256\) and \(a\ge 4\), this is the opposite of the
shared tail of Theorem 3.12 at length \(k=a+2\).

For \(2\le n<256\), the cases \(a=4,5,6\) fail to return on that
window; this is the Lean `native_decide` evaluation behind
`no_cycle_word_three_even_eooee` (Appendix A). For \(a\ge 7\),
Lemma 3.11 applies. \(\square\)

**Theorem 3.17 (mixed bunched family \(EOOOEE\)).**
Let \(a\ge 3\) and \(n\ge 2\). The word \(O^aEOOOEE\) is not a
cycle word at \(n\).


*Proof.* First let \(a\ge 4\) and \(n\ge 3\), and write
\(z=J^a(n)\), \(y=\lfloor\sqrt z\rfloor\), and \(p\) for the image
after the prefix \(O^aEOOO\). Lemma 3.9 with \(r=2\) gives
\(p<(n+1)^4\). The three letters after \(y\) are odd, so
Lemma 3.10 at length three yields
\(y^{27}\le 2^{38}p^8<2^{38}(n+1)^{32}\). For \(n\ge 3\) one has
\(2^{38}<(n+1)^{22}\), hence \(y<(n+1)^2\). The even cell at
\(z\) then gives \(z<(y+1)^2\le(n+1)^4\). Combined with
Lemma 3.10, any such cycle word would satisfy
\[
n^{3^a}<2^{e_a}(n+1)^{2^{a+2}}.
\]
For \(n\ge 256\) and \(a\ge 4\), this is the opposite of the
shared tail of Theorem 3.12 at length \(k=a+2\), already used in
Theorem 3.16.

Now let \(a=3\) and \(n\ge 256\). The same two-even cell gives
\(z<(y+1)^2\), so Lemma 3.10 at the prefix \(O^3\) yields
\(n^{27}<2^{38}(y+1)^{16}\). The three-odd envelope on \(y\) still
gives \(y^{27}<2^{38}(n+1)^{32}\).

If \(y<39\), then \(n^{27}<2^{38}\cdot 39^{16}\). The numerical
comparison \(2^{38}\cdot 39^{16}<24^{27}\) contradicts
\(n\ge 24\).

If \(y\ge 39\), the numerical comparison \(40^{27}<2\cdot 39^{27}\)
upgrades to \((y+1)^{27}<2y^{27}\), hence
\((y+1)^{27}<2^{39}(n+1)^{32}\). Cubing the prefix bound three
times produces \(n^{729}<2^{1026}(y+1)^{432}\). Raising the
successor bound to the sixteenth power produces
\((y+1)^{432}<2^{624}(n+1)^{512}\). Combining these displays
yields \(n^{729}<2^{1650}(n+1)^{512}\). The opposite comparison
holds at \(n=197\) and persists to every larger start by the
elementary comparison \(n(n+2)<(n+1)^2\) already used in
Theorem 3.15.

For \(2\le n<256\), the cases \(a=3,4,5,6\) fail to return on
that window; this is the Lean `native_decide` evaluation behind
`no_cycle_word_three_even_eoooee` (Appendix A). For \(a\ge 7\),
Lemma 3.11 applies. \(\square\)

**Theorem 3.18 (mixed bunched family \(EEOE\)).**
Let \(a\ge 5\) and \(n\ge 2\). The word \(O^aEEOE\) is not a
cycle word at \(n\).


*Proof.* First let \(n\ge 4\), and write \(z=J^a(n)\) and \(y\)
for the last odd letter of \(O^aEEOE\). The suffix \(EOE\) is a
cycle suffix, so the last-odd cube of Theorem 3.15 gives
\(y^3<(n+1)^4\). The two letters between \(z\) and \(y\) are
even, so \(z<(y+1)^4\). For \(n\ge 4\) the successor comparison
\((y+1)^3<2(n+1)^4\) upgrades this to \(z<(n+1)^6\). Combined
with Lemma 3.10, any such cycle word would satisfy the same
display as Theorem 3.15:
\[
n^{3^a}<2^{e_a}(n+1)^{6\cdot 2^a}.
\]
The opposite comparison is therefore the tail of Theorem 3.15:
it holds for \(a=5\) and \(n\ge 314\), and already for \(a=6\)
and \(n\ge 16\).

For \(2\le n<314\) and \(a=5\), and for \(2\le n<16\) and
\(a=6\), the word fails to return; these are the Lean
`native_decide` evaluations behind `no_cycle_word_three_even_eeoe`
(Appendix A). For \(a\ge 7\) and \(n<256\), Lemma 3.11 applies.
For \(a\ge 6\) and \(n\ge 16\), the tail of the previous
paragraph applies. \(\square\)

**Theorem 3.19 (mixed bunched family \(EOEOE\)).**
Let \(a\ge 4\) and \(n\ge 2\). The word \(O^aEOEOE\) is not a
cycle word at \(n\).


*Proof.* First let \(n\ge 32\), and write \(z=J^a(n)\),
\(w=\lfloor\sqrt z\rfloor\), and \(y\) for the last odd letter.
The suffix \(EOE\) again gives \(y^3<(n+1)^4\). The one-odd
envelope on \(w\) yields \(w^3\le 4s^2\), where \(s\) is the
image after \(O^aEO\). The last-odd cell and \(n\ge 32\) upgrade
this to \(w<(n+1)^2\), hence \(z<(w+1)^2\le(n+1)^4\). Combined
with Lemma 3.10, any such cycle word would satisfy
\[
n^{3^a}<2^{e_a}(n+1)^{2^{a+2}}.
\]
For \(n\ge 256\) and \(a\ge 4\), this is the shared tail already
used in Theorem 3.16.

For \(2\le n<256\), the cases \(a=4,5,6\) fail to return on that
window; this is the Lean `native_decide` evaluation behind
`no_cycle_word_three_even_eoeoe` (Appendix A). For \(a\ge 7\),
Lemma 3.11 applies. \(\square\)

**Theorem 3.20 (mixed bunched family \(EOOEOE\)).**
Let \(a\ge 3\) and \(n\ge 2\). The word \(O^aEOOEOE\) is not a
cycle word at \(n\).


*Proof.* First let \(a\ge 4\) and \(n\ge 4\), and write
\(z=J^a(n)\), \(u=\lfloor\sqrt z\rfloor\), and \(y\) for the last
odd letter. The suffix \(EOE\) gives \(y^3<(n+1)^4\), hence
\((y+1)^3<2(n+1)^4\). The two letters after \(u\) are odd, so
Lemma 3.10 at length two yields
\(u^9\le 2^{10}s^4<2^{10}(y+1)^8\). Cubing that display against
the last-odd successor bound produces
\(u^{27}<2^{38}(n+1)^{32}\). The same comparison as in
Theorem 3.17 then gives \(u<(n+1)^2\), hence
\(z<(u+1)^2\le(n+1)^4\). Combined with Lemma 3.10, any such
cycle word would satisfy the shared two-even tail of
Theorem 3.16.

Now let \(a=3\) and \(n\ge 256\). The prefix \(O^3\) against
\(z<(u+1)^2\) yields \(n^{27}<2^{38}(u+1)^{16}\), and the
two-odd plus last-odd geometry of the previous paragraph yields
\(u^{27}<2^{38}(n+1)^{32}\). These are the same two displays as
in the \(a=3\) case of Theorem 3.17, with \(u\) in place of
\(y\), and the same small/large split applies.

For \(2\le n<256\), the cases \(a=3,4,5,6\) fail to return on
that window; this is the Lean `native_decide` evaluation behind
`no_cycle_word_three_even_eooeoe` (Appendix A). For \(a\ge 7\),
Lemma 3.11 applies. \(\square\)

**Theorem 3.21 (gapped leftovers as cycle words).**
Let \(n\ge 2\). No cycle word at \(n\) has the form \(O^aEO^bEE\)
with \(a\ge 2\) and \(b\ge 4\), or the form \(O^aEO^bEOE\) with
\(a\ge 2\) and \(b\ge 3\).


*Proof.* Every cycle word has a minimum-based rotation. It is
therefore enough to check that every cyclic shift of either word
is an already-excluded cycle-minimum orientation.

Write \(w\) for the gapped word. In the first family,
\(\lvert w\rvert=a+b+3\). The rotation by \(k=0\) is the original
word, excluded as a cycle minimum by Theorem 3.13. The rotation
by \(k=a+1\) is the bootstrap word \(O^bEEO^aE\). That word has
an internal even letter and last gap at least \(2\). If
\(a\ge 3\), the last-gap threshold of Lemma 3.4 at \(OOO\) and
\(N=3\) excludes it. If \(a=2\), the same lemma at \(OO\) and
\(N=5\) excludes every start \(n\ge 5\); the remaining odd start
\(n=3\) does not realize four consecutive odd letters, so it
cannot follow \(O^b\) for \(b\ge 4\). The rotation by
\(k=a+b+2\) begins with the last even letter of \(w\), which
Theorem 3.2 forbids at a cycle minimum. Every other rotation
ends with an odd letter, likewise forbidden at a cycle minimum.

In the second family, \(\lvert w\rvert=a+b+4\). The same four
classes appear: the original word is Theorem 3.13; the rotation
by \(k=a+1\) is \(O^bEOEO^aE\), excluded by the same last-gap
thresholds, with the remaining start \(n=3\) and \(a=2\) either
failing to realize four odds or, when \(b=3\), reaching \(6\)
after \(OOOE\) and then meeting an odd letter; the rotation by
\(k=a+b+2\) begins \(OE\), forbidden by Theorem 3.2; and every
other rotation ends odd.

The original start need not be a cycle minimum. After rotation
the start is a minimum, so the hypothesis \(y<n\) that blocked
Theorem 3.13 does not arise. \(\square\)

## Acknowledgments

Computational and formal-assistant tools were used in the
development and verification of the manuscript; all mathematical
statements and code are the responsibility of the author.

## References

1. C. A. Pickover, *Computers and the Imagination: Visual Adventures
   Beyond the Edge*, St. Martin's Press, New York, 1991, ch. 40,
   p. 232.
2. C. A. Pickover, *The Mathematics of Oz: Mental Gymnastics from
   Beyond the Edge*, Cambridge University Press, Cambridge, 2002,
   ch. 45, pp. 102--106.
3. OEIS Foundation Inc., “Juggler sequence: if \(n\) even then
   \(\lfloor\sqrt n\rfloor\) else \(\lfloor n^{3/2}\rfloor\),”
   Sequence A094683 in *The On-Line Encyclopedia of Integer Sequences*,
   https://oeis.org/A094683 (accessed 28 August 2026).
4. OEIS Foundation Inc., “Number of steps needed for n to reach 1 in
   the juggler sequence,” Sequence A007320 in *The On-Line
   Encyclopedia of Integer Sequences*,
   https://oeis.org/A007320 (accessed 29 August 2026).
5. E. W. Weisstein, “Juggler Sequence,” *MathWorld*,
   https://mathworld.wolfram.com/JugglerSequence.html (accessed
   29 August 2026).
6. OEIS Foundation Inc., “Largest value in trajectory of n under the
   juggler map of A094683,” Sequence A094716 in *The On-Line
   Encyclopedia of Integer Sequences*,
   https://oeis.org/A094716 (accessed 29 August 2026).
7. V. Prasad and M. A. Prasad, “Estimates of the maximum excursion
   constant and stopping constant of juggler-like sequences,”
   ResearchGate preprint, 2025.
   https://doi.org/10.13140/RG.2.2.14110.04168.
8. J. C. Lagarias, “The \(3x+1\) problem and its generalizations,”
   *Amer. Math. Monthly* 92 (1985), 3--23.
   [doi:10.1080/00029890.1985.11971528](https://doi.org/10.1080/00029890.1985.11971528).
9. J. C. Lagarias (ed.), *The Ultimate Challenge: The \(3x+1\)
   Problem*, American Mathematical Society, Providence, RI, 2010.
10. R. E. Crandall, “On the ``\(3x+1\)'' problem,” *Math. Comp.* 32
    (1978), 1281--1292.
    [doi:10.1090/S0025-5718-1978-0480321-3](https://doi.org/10.1090/S0025-5718-1978-0480321-3).
11. K. R. Matthews and A. M. Watts, “A generalization of Hasse's
    generalization of the Syracuse algorithm,” *Acta Arith.* 43
    (1984), 167--175.
    [doi:10.4064/aa-43-2-167-175](https://doi.org/10.4064/aa-43-2-167-175).
12. J. L. Simons and B. M. M. de Weger, “Theoretical and
    computational bounds for \(m\)-cycles of the \(3n+1\)-problem,”
    *Acta Arith.* 117 (2005), 51--70.
    [doi:10.4064/aa117-1-3](https://doi.org/10.4064/aa117-1-3).
13. S. Eliahou, “The \(3x+1\) problem: new lower bounds on
    nontrivial cycle lengths,” *Discrete Math.* 118 (1993),
    45--56.
    [doi:10.1016/0012-365X(93)90052-U](https://doi.org/10.1016/0012-365X(93)90052-U).
14. L. Kirby and J. Paris, “Accessible independence results for
    Peano arithmetic,” *Bull. London Math. Soc.* 14 (1982),
    285--293.
    [doi:10.1112/blms/14.4.285](https://doi.org/10.1112/blms/14.4.285).
