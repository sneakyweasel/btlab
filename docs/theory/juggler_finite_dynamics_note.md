---
title: "Lower Bounds for Cycle Lengths in the Juggler Map"
author: Philippe Cochin
date: 11 September 2026
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

The Juggler map sends an even positive integer to the integer part of its
square root and an odd positive integer to the integer part of its
three-halves power. We obtain restrictions on hypothetical nontrivial
cycles. For a cycle with minimum \(n\), length \(L\), and \(o\) odd steps,
we prove the cycle-financing inequality
\[
n\log n\,(3^o-2^L)\le L\,3^o.
\]
It bounds the formal expansion that accumulated floor losses can offset.
A refinement transports these losses to a reduced base and bounds the
resulting exponent-walk charge using an irrational rotation,
Denjoy--Koksma estimates, and finite Ostrowski decompositions. Combined
with the verified descent inputs described in the paper, the inequalities
give period lower bounds of \(25781\), \(176251\), \(478245\), and
\(780239\) at floors \(10^6\), \(26254995\), \(162849448\), and
\(350000000\), respectively. Separately, finite-word exclusions give at
least four even steps without a descent-floor input; an exact computational
classification strengthens this to eight even steps and period at least
twenty-two. For cycles whose maximum is below the cube of their minimum,
we also determine the complete rank order and mechanical itinerary,
derive a uniform log-log grid bound, and prove the further height
restriction \(M<m^3-m^{15/8}\) for \(m\ge7\), where \(m,M\) are the
minimum and maximum. Successive genuine return-gap contractions sharpen
this to \(M<m^3-(1/2)m^{253/128}\) for \(m\ge2^{24}\), and to
\(M<m^3-(1/2)m^{127/64}\) for \(m\ge2^{128}\), with a slightly
stronger exponent in the latter case. A terminal word factorization
identifies the expansion still uncontrolled by these contractions.
Exact short-return cells identify the rounding information discarded
by several relaxed no-cycle criteria.
The core inequalities and selected classifications are
formalized in Lean 4. The descent computations, per-length numerical
comparisons, and remaining analytic identifications are distinguished
from those formal proofs. A limitation result applies to charges retaining
a positive contribution at a fixed floor. Neither the exclusion of all
nontrivial cycles nor universal termination is established.

**2020 Mathematics Subject Classification.** Primary 11B83;
secondary 37P99, 11Y55.

**Keywords.** Juggler map, Juggler sequence, floor-power map, cycle
financing, integer dynamics.

## 1. Introduction

The Juggler sequence was introduced by Pickover [1,2] as an
interesting variation of the Collatz problem. Pickover's later
exposition is Chapter 45 of [2], pp. 102--106. We study \(J:\mathbb N\to\mathbb N\),
\[
J(n)=\begin{cases}
\lfloor\sqrt n\rfloor,&n\text{ even},\\
\lfloor n^{3/2}\rfloor,&n\text{ odd}.
\end{cases}
\] The *Juggler sequence* starting at \(n\) is the trajectory of
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

**Itinerary.** The *itinerary* of the first \(k\) steps is the length-\(k\)
string \(w\in\{O,E\}^k\) with \(w_i=O\) if \(n_i\) is odd and
\(w_i=E\) if \(n_i\) is even. Synonyms: itinerary = parity sequence;
trajectory = orbit. The itinerary is the list of branch
labels, not the list of values. The integer \(k\) is any finite
prefix length; the definition does not assume that the trajectory
reaches \(1\).

**Ideal exponent.** An itinerary of length \(k\) with \(o\) odd letters
has ideal exponent \(3^o/2^k\). Ignoring floors, those letters
would send a start \(n\) to \(n^{3^o/2^k}\); equivalently, the
ratio multiplies \(\log n\). Applying floors can only decrease the image.

**Realized itinerary.** An itinerary \(w\) is *realized* at \(n\) when the
first \(\lvert w\rvert\) parities of the trajectory of \(n\) are exactly
the letters of \(w\). Equivalently: a formal string over
\(\{O,E\}\) is an itinerary only when some start actually follows
those branches. That is what is meant by: an itinerary is available only
when the trajectory realizes those parities. Floors are applied after
every letter of a realized itinerary.

**One-step preimage.** The map \(J\) is not invertible. For \(m\in\mathbb N\),
the *one-step preimage* of \(m\) is the set
\[
J^{-1}(m)=\{k\in\mathbb N:J(k)=m\}.
\]
For each target \(m\), its even parents are the even integers \(k\)
with \(m^2\le k<(m+1)^2\). Its odd parents satisfy
\(m^2\le k^3<(m+1)^2\), and there is at most one such odd
integer (Lemma 3.1). These are statements about the parent's branch,
independent of the target's parity.

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
| itinerary | a finite string in \(\{O,E\}\) of parities |
| realized itinerary | the trajectory actually follows those letters |
| \(3^o/2^k\) | ideal exponent of an itinerary of length \(k\) with \(o\) odd letters |
| \(J^{-1}(m)\) | the one-step preimage of \(m\) |
| \(N_0\) | a verified descent floor (a computational input) |
| CycleMin | a minimum-based rotation of a cycle itinerary |

The mechanism is the interaction of three elementary facts:
exact integer one-step preimages, a logarithmic defect, and cycle
minimality. Exact one-step preimages give a one-step logarithmic defect;
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
result. Four instances are used. The base instance is
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
\(L\ge 176251\) (Theorem 5.9). Corollary 5.10 evaluates the
same kill criterion at the second certified floor
\(N_0=162849448\), every survivor lying inside the
\([50508,16785921)\) window of Theorem 5.8, whose envelope
therefore covers their charge, and gives \(L\ge 478245\). The main numerical result is
Corollary 5.11: at the third certified floor
\(N_0=350000000\) the same comparison gives \(L\ge 780239\).
The census-free window theorem covers
\([50508,16785921)\) --- every nonendpoint member
\(L_0,\ldots,L_{54}\) of the semiconvergent fan of Proposition 5.12;
the endpoint \(L_{55}=16785921\) is excluded by the half-open interval ---
so the charge side of the later-floor kills
needs no per-length dynamic program. The kill comparison itself
stays per-length, because its left-hand side \(\theta(L)\) is a
Diophantine quantity the envelope does not control. The architecture is
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
\begin{aligned}
\text{transport}&\to\text{hug adversary}\to\text{itinerary identity}\\
&\to\text{Denjoy--Koksma}\to\text{window}\to L\ge176251.
\end{aligned}
\]
The computation supplies the endpoint \(N_0\). The mathematics
amplifies that floor to the period bound.

Roadmap. Section 2 records the power envelope and the exact
defect identity that explains it. Section 3 classifies
minimum-based cycle itineraries and proves that every nontrivial
cycle has at least four even letters (Theorem 3.22); Theorem 3.31
raises that to eight even letters, and period at least twenty-two,
once the cycle minimum is at least \(300\). Section 4 records the
excursion necklace of a minimum-based itinerary, unrolls the one-step-preimage
logarithm around that minimum, obtains the finance inequality,
and applies it at the known floor \(10^6\). The necklace is
the geometry of the unroll, not a fourth main theorem. A
run-type packing of the same identity is a supporting
refinement; the arithmetic of the leftover lengths is
secondary. Section 5 certifies the laboratory floor
\(26254995\), replaces the length-only charge by a coupled
exponent-walk charge, identifies its extremal word as a
rotation itinerary, and proves a census-free envelope for every
length in the window \([50508,16785921)\); the resulting kill
table gives the period bound \(176251\), a certified
evaluation of the same kill criterion at a second certified
floor raises it to \(478245\) (Corollary 5.10), and a third
certified floor raises it to \(780239\) (Corollary 5.11).
Section 6 records limitations.

A nonempty realized itinerary \(w\) with
\(J^{|w|}(n)=n\) is a *cycle itinerary*. The unique fixed point is \(1\);
a cycle is *nontrivial* when it contains some \(n\ge 2\). A cycle
word at \(n\) is *minimum-based* when \(n\) is a cycle minimum:
\(J^j(n)\ge n\) for every \(0\le j<|w|\). Every cycle itinerary has a
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

**Contribution 2 — structural itinerary obstruction.**
Every nontrivial cycle itinerary has at least four even letters, and
hence period at least eleven (Theorem 3.22 and Corollary 3.23).
That is the Lean statement, for every \(n\ge 2\), and it uses no
descent floor. The argument classifies the minimum-based itinerary
geometry; it is not a raw census of itineraries of length at most ten.
Theorem 3.31 is a computational strengthening of the same two
envelopes: once the cycle minimum is at least \(300\) (every
\(n\le 299\) reaches \(1\)), no cycle itinerary has fewer than eight
even letters, so a nontrivial cycle has period at least twenty-two.
That enumeration is not Lean.

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
as the rotation (hug) itinerary (Theorem 5.4, Lemma 5.6), and a
Denjoy--Koksma bound over certified Ostrowski blocks
(Theorem 5.7) give a uniform envelope for every length in the
window \([50508,16785921)\) (Theorem 5.8) — census-free on that
window, which covers \(L_0,\ldots,L_{54}\) but not its endpoint
\(L_{55}=16785921\). At the laboratory
floor the resulting kill table leaves a single finance survivor
below \(2\cdot 10^5\): any nontrivial cycle has period at least
\(176251\) (Theorem 5.9), the first laboratory instance. The
second-floor evaluation is Corollary 5.10: at
\(N_0=162849448\) the same kill criterion,
evaluated on the additional survivors --- all inside the
window, so all with a census-free charge bound --- leaves only the
semiconvergent fan member \(478245\). The
main numerical result is Corollary 5.11: at the third
certified floor \(N_0=350000000\) that comparison leaves only
the next fan member \(780239\): any nontrivial cycle has
period at least \(780239\).

**Contribution 5 — floor-free gap transfer and the short-cycle
reduction.**
The finance inequality ties the relative surplus to the linear
form \(\Lambda=o\log 3-L\log 2\) without any floor:
\(n\log n\cdot\min(\Lambda,1)\le 2L\) (Theorem 4.10, Lean
`cycleMin_gap_transfer`). With Rhin's effective measure this
excludes every cycle with \(L^{14.3}\le n\log n/915\)
(Corollary 4.11), for all \(n\ge 2\). The statement is a
reduction, not a kill: it is weaker than the finance table at
every certified floor, and it shows that the no-cycle problem is
exactly the exclusion of long cycles,
\(L>(n\log n/915)^{1/14.3}\), where the finance survivors
(\(L\approx n^{0.59}\)) live.

**Contribution 6 — complete cycle order under a height hypothesis.**
For a primitive cycle with \(m>1\) and \(M<m^3\), the sorted states
rotate by the even count, the period and odd count are coprime, and
the itinerary from its minimum is exactly the ceiling mechanical word
(Theorem 3.33). The associated threshold maps have a common period and
interlacing cycles at each fixed threshold (Theorem 3.35); Proposition 3.36
controls the entire sorted cycle in log-log coordinates. Propositions
3.37--3.38 show precisely why a one-unit successor allowance or exact
within-branch differences alone cannot prove no-cycle. They concern
different maps and are not counterexamples to the Juggler conjecture.

**Contribution 7 — a periodic height gap and exact short-return guards.**
For \(m\ge7\), Theorem 3.39 strengthens the hypothesis \(M<m^3\)
to \(M<m^3-m^{15/8}\). It uses the ordered return images of the
minimum and maximum retained states, followed by exact parity faces
of the floor cells. Appendix E gives exact carry recovery, a finite
bound on consecutive transitions in a polynomial growth family, and
counterfamilies delimiting two proposed guard summaries. The family
obstructions concern prescribed blocks; the height gap uses actual
periodicity. None increases the numerical period floor.

**Contribution 8 — successive return gaps and the terminal passage.**
Theorem 3.40 strengthens the height strip through two and then three
genuine changes of the return boundary, at the stated distinct minimum
thresholds. It retains every floor error and actual intermediate guard.
Proposition 3.41 factors the terminal words around a mixed \(OE/EO\)
passage, whose gap contracts, and identifies the remaining uncontrolled
prefix. Appendix F gives the full error, rank and height proofs, and
the precise obstruction to a uniform one-sided error certificate.

Section 6.3 complements the height results with an upper-cell charge
bound. At the exact counts \((780239,492276,287963)\), it restricts
an actual cubic-cycle minimum to \(350000000<m<520000000\).
The local odd-to-odd upper-square gap is Lean verified; the charge proof
and its interval evaluation have separate evidence boundaries. Appendix
E.7 rules out full eventually periodic and single-polynomial domains for
an invariant all-\(OOE\) construction, while leaving sparse trajectories
unexcluded.

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

**Companion manuscripts.** Two later manuscripts by the author
build on this one and are cited where they bear on the cycle
problem. Paper B [16] proves parity equidistribution of the nested
floor powers along the itineraries of \(J\), with power savings,
completely through depth four for odd-rooted itineraries and for the
two length-five contractors, giving the certified-descent densities
\(13/16\) and \(7/8\); its only input from this paper is the
contraction criterion of Theorem 2.2. Paper C [17] proves that every
nonempty backward-closed set — in particular the basin of any
nontrivial cycle, and the set of divergent starts — has logarithmic
count \(\gg(\log x)^{\lambda}\) for \(\lambda<\lambda^{**}=0.4926\), and reduces the
Juggler conjecture to a Tao-type almost-all statement whose bounded
target is the certified floor of Section 5 and whose descent step is
the power envelope of Theorem 2.2 (`power_bound_word`). Section 6.1
states precisely what those results add to the cycle problem, and
what they leave untouched.

The layers of the argument are as follows.

1. *Classical ideas, not claimed as new:* cycle financing
   (Simons--de Weger [12]); logarithmic and continued-fraction
   approximation of \(\log 2/\log 3\), including Rhin's effective
   measure for \(o\log 3-L\log 2\) [15], used only in
   Corollary 4.11; cycle-itinerary restrictions
   and leftover packaging (Eliahou [13]; Lagarias [8,9]); the
   Denjoy--Koksma inequality and Ostrowski numeration, used as
   known tools in Section 5.
2. *New object:* the exact one-step floor-power preimages of \(J\).
3. *New theorem:* the Juggler-specific cycle-minimum finance
   inequality of Theorem 4.4.
4. *New consequence:* \(L\ge 25781\) at the verified descent
   floor \(10^6\).
5. *Supporting organization:* the run-packing refinement of the
   same defect sum (Theorem 4.7).
6. *New theorem:* the reduced-base transport and the uniform
   window envelope of Section 5 (Theorems 5.3 and 5.8).
7. *New consequence:* period at least \(176251\) at the
   laboratory floor \(26254995\) (Theorem 5.9), \(478245\)
   at the second certified floor \(162849448\)
   (Corollary 5.10), and \(780239\) at the third certified
   floor \(350000000\) (Corollary 5.11), every survivor inside
   the window of Theorem 5.8.
8. *Reduction:* the floor-free gap transfer (Theorem 4.10) and
   the short-cycle exclusion \(L^{14.3}>n\log n/915\)
   (Corollary 4.11), which locate the open problem in the long
   regime without claiming anything there.

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
extremal rotation itinerary by Denjoy--Koksma over certified
Ostrowski blocks raises that period bound to \(176251\) at the
laboratory floor, census-free on an explicit window of lengths,
and — by certified evaluation of the same kill criterion on the
surviving lengths, all of which lie inside that window, the
comparison against \(\theta(L)\) remaining per-length — to
\(478245\) at the second certified floor and \(780239\) at the
third.

### 1.2 Verification

The arguments of Sections 2, 3, and 4 may be read without machine
assistance. The core mathematical lemmas are mechanized in Lean 4;
selected finite classifications and numerical tables are
independently certified computations. Appendix A records the Lean
names. The finite tables used by Lemmas 3.5, 3.7, 3.11 and
Theorems 3.12--3.20 are `decide +kernel` evaluations in the modules
named there: the reduction is performed by the Lean kernel, so these
tables add no trust assumption beyond it. That holds throughout the
Juggler layer with one exception, `window_digit_scan`: a scan of a quarter
of a million window lengths in Section 5's Ostrowski certification, which
uses `native_decide` and so also trusts the Lean compiler and runtime.
`#print axioms` on any theorem displays whether it depends on it.

The structural digit identity `greedy_eq_ostro` identifies the
fold and recursive algorithms for all lengths; `greedy_eq_ostro_below_window`
is its bounded corollary. Likewise `greedy_reconstruct_all` is an exact
reconstruction theorem. The remaining native scan sharpens the digit cap
from \(47\) to \(37\) on its stated sub-window. The bound
`window_digit_cap` inherits that scan's runtime dependency, as recorded
by the axiom audit.

Section 3.10's finite-order statements, exact rounding results, and
quantitative log-log grid inequalities are also formalized. The grid proof
starts from integer square-cell inequalities and the actual successor map;
its geometric conclusion is not an assumption. Appendix A identifies the
public declarations. The illustrative asymptotic comparison following
Proposition 3.36 and the open absolute-cell question remain written analysis.
Section 3.11's actual-cycle seam and integer height gap are formalized
from periodic-orbit hypotheses. Appendix E's formal coverage includes
the short OE/OOE cells, subtractive rank returns, exact family-chain bound,
and retained-remainder recovery. Its larger analytic constructions and
full tower discussions remain written where Appendix A indicates.
The new proofs use kernel verification and add no native scan.
Section 3.12's two height restrictions are formalized from actual
periodic-set hypotheses. The section, forced batches, odd endpoint gaps
and genuine transfers are constructed internally. Appendix F's exact
floor-loss bounds and finite certificate threshold are also formalized.
Section 3.13's primitive terminal construction is also formalized from
an ordinary actual periodic orbit, with its minimum and attained maximum.
The proof retains original-set adjacency and all guards, identifies the
absolute odd/even cut, and proves the strict mixed-gap inequality.
Common-prefix amplification remains uncontrolled. No general no-cycle
theorem is asserted.
The real projection description and the higher-difference consequence
are explanatory deductions from the listed results. The grid endpoints
use the namespace `Problems.Juggler.CubicGrid`.

Reproducibility has three layers. The repository command
`research.juggler_sequence.paper_a_audit` recomputes selected parity
thresholds, finite fan identities, and constants, and checks the stored
walk-comparison records. The standalone script
`tools/check_paper_a_numeric.py` independently screens every length below
the four headline cutoffs using rational logarithm bounds and interval
arithmetic; it assumes the archived descent floors. Replaying those floors
requires the separate exact-integer first-passage computation. Appendix B
identifies its coverage and records. Neither an archive hash nor the
arithmetic audit replaces that replay.

Near a convergent, double precision is insufficient to identify an exact
integer crossing without a guard: the \(25781\) threshold can shift by
one integer when \(L\log2-o\log3\) is evaluated naively. The independent
checker uses outward interval comparisons and rational screening. The
historical GPU and CPU tables remain separately identified in Appendix B.

The build command `python tools/build_paper_a.py` produces the canonical
PDF and synchronized distribution copies from this source.
`python tools/build_paper_a.py --check` checks their provenance and hashes.
The manuscript source, formalization map, and reviewer packet in
`docs/theory/` are the editorial inputs; files in `juggler_review/` and
the companion's paper directories are generated exports. No external
submission or universal termination proof is implied by a successful build.

**Proposition 1.3 (certified computational input).**
An exact-integer first-passage computation checks that every odd start
\(3\le n\le10^6\) reaches a value strictly below its start. Even
starts descend in one step, so strong induction gives arrival at \(1\)
for every \(2\le n\le10^6\). The archived files retain chunk summaries,
counts, maximal first-passage lengths, and exceptional-seed resolutions;
they do not retain a realized word for every start. Reproducing the
descent assertion requires the exact computation, not only checking a
summary's hash. The first four chunks of the \(26254995\)-floor run
cover the odd starts through \(10^6\); their maximal first-passage
lengths are \(253,213,188,188\). Thus the maximum is \(253\), at seed
\(78901\). Weisstein [5] reports the same coverage; the archived run
is a separate computation. Artifact locations and commands appear in
Appendix B.

**Roles.** Independently proved: the finance inequality
(Theorem 4.4). Computational input: every \(2\le n\le 10^6\)
reaches \(1\) (this proposition), every
\(2\le n\le 26254995\) reaches \(1\) (Proposition 5.1, the
laboratory instance), every \(2\le n\le 162849448\) reaches
\(1\) (Corollary 5.10, the second laboratory instance), and
every \(2\le n\le 350000000\) reaches \(1\) (Corollary 5.11,
the third laboratory instance).
Independently recomputed: the exact
first-passage runs of Appendix B. Not proved: global
termination.

Theorem 4.6 applies Corollary 4.5 to this input and certifies
the table with the conservative coefficient \(6/5\). The whole
comparison it tests is Lean: `cycleMin_defect_threeTerm`
(`FinanceTransfer.lean`) is the certified identity
`cycleMin_defect_finance` composed with the three-class charge
`cycleMin_threeTerm`, so what stays verified computation is the
per-length arithmetic and the descent floor, not the inequality.
Theorem 4.7 carries two hypotheses --- the itinerary is primitive and
contains no \(\mathtt{EE}\) --- without which its displayed counts fail;
§4 prices them below. Given them the display is Lean
(`cycleMin_sixTerm`), so they are sufficient as well as necessary.
Theorem 4.8 reuses the gap table under that packing, and \(18\)
of its \(42\) exclusions inherit the second hypothesis. Proposition 4.9 is integer arithmetic in Lean. In
Section 5's Denjoy--Koksma core is Lean end to end relative to the circle
integral. Its observable's variation is
`observable_window_variation_lt_two`, proved for `periodicObservable`
itself on every unit window; `denjoy_koksma_rotation` is Lean from
positivity, coprimality and \(|\theta-p/q|\le1/q^2\), and
`denjoy_koksma_blocks` composes the blocks uniformly in their starting
phase. The one-statement display is `hugCharge_sub_circleMean_le`. Two
bridges in the printed Theorem 5.7 stay human: it quantifies over any
decomposition into actual convergents while that named theorem fixes the
certified Ostrowski assembly, and it writes the circle integral as the
explicit \(C_*\) of Proposition 5.5.
Lemma 5.6 is Lean on both halves: the itinerary identity
(`budgetedWord_eq_hugWord`) and the rotation identification
(`hugOdds_eq_sub_floor`, `hugWalk_eq_fract`, `HugRotation.lean`).
The Laplace bound of Proposition 5.5 is Lean (`rotation_average_le`,
`rotationAverage_gap`), and `denjoy_koksma_blocks` proves convergence of
the finite hug averages to the circle integral for the bounded-variation
observable. The elementary change of variables identifying that circle
integral with the displayed `rotationAverage (log n')` remains prose; the transport
inequality of Theorem 5.3 (`cycleMin_transport`), the
defect-to-hug-charge consequence of §5.2
(`cycleMin_defect_le_charge`, `cycleMin_defect_le_hug_charge`),
the charge-maximisation and strict-uniqueness halves of Theorem 5.4
(`hug_charge_maximal`, `hug_charge_unique`), the general digit machinery
and the instantiated cap below \(q_{13}=301994\) (`ostroDigit_le`,
`theta_digitSum_le`, `window_digit_scan`), and the kill
template of Theorem 5.9 (`cycleMin_hug_kill_criterion`) are
Lean-verified; Theorems 5.2 and 5.9 are independently certified
computations at the laboratory floor, with the same trust
boundary as Theorem 4.6 (exact integer arithmetic plus guarded
float comparisons). This is not a claim that the paper as a
whole is formally verified.

```text
Repository:  https://github.com/sneakyweasel/btlab
Commit:      7802f78bec58c68cec92a2efb3db4a502f916277
Lean:        leanprover/lean4:v4.33.1
Mathlib:     v4.33.1 (lake-manifest rev 0df444a360eaa60ab8c11dca51a86af692955474)
Build:       lake build Problems.JugglerPaper   (from formal/)
Computation: python -m research.juggler_sequence.cycle_finance
             (parity table); run-type table in budget_opt.json
SHA-256:     Appendix B
```

The commit is the repository state that produced the finance
tables. A later editorial commit of this text does not change
those hashes.

### 1.3 Notation

The table records the core notation used in the envelope, itinerary
exclusions, finance and walk estimates. Sections 3.10--3.13, 6.3 and
Appendices E--F introduce additional local notation, defined where it is used.
In the core estimates, \(G_a\) denotes the exponent in Lemma 3.3's
constant, \(h\) the per-step exponent, and \(T(u)\) the backward
exponent of a suffix. These are distinct from the even count \(e\),
the step loss \(\varepsilon_i\), and the digit sum \(s(L)\).

| symbol | meaning | first used |
|---|---|---|
| \(J\) | the Juggler map | §1 |
| \(n\) | a start; on a cycle, its minimum | throughout |
| \(N_0\) | a verified descent floor: every start \(\le N_0\) reaches \(1\) | §1 |
| \(x_k\) | the state after \(k\) steps | §4 |
| \(w\), \(v\), \(u\) | an itinerary word, a prefix of it, a suffix of it | §1, §3.9 |
| \(O\), \(E\) | the odd and the even letter | §1 |
| \(L\) | the length of \(w\); on a cycle, the period | §3 |
| \(o\), \(e\) | the odd and even letter counts, \(e=L-o\) | §3 |
| \(a\), \(b\), \(c\) | the odd-run lengths of the canonical form \(O^aEO^bEO^cE\) | §3 |
| \(a_i\), \(a_k\) | the \(i\)-th odd run; the odd count after \(k\) steps | §4, §5 |
| \(r\) | the length of a trailing even run | §3.9 |
| \(h\) | the per-step exponent: \(1\) on an even letter, \(3\) on an odd one | §4 |
| \(G_a\) | \(2(3^a-2^a)\), the exponent of \(2\) in Lemma 3.3's constant | §3 |
| \(X_a\), \(Y_a\) | \(3(3^a-2^a)\) and \(2\cdot3^a-3\cdot2^a\), the sharp envelope exponents | §3.9 |
| \(B(u)\) | the backward envelope of a suffix (Lemma 3.25) | §3.9 |
| \(T(u)\) | \(2^{|u|}/3^{\#O(u)}\), the backward exponent of a suffix | §3.9 |
| \(\theta\) | \(1-2^L/3^o\), the expansion margin | §1, §4 |
| \(\Lambda\) | \(o\log3-L\log2=-\log(1-\theta)\) | §3, §5 |
| \(\mu\) | \(\log_2(3/2)\) | §5 |
| \(u_k\) | \((1+\mu)a_k-k\), the exponent walk | §5 |
| \(w_k\) | \(2^{u_k}=3^{a_k}/2^k\), the walk weight | §5 |
| \(n'\) | \(n\,e^{-D}\), the reduced base, with \(D\) the deficit of §5.1 | §5 |
| \(C_L\), \(C_*\) | the charge per letter of a word, and its limit | §5 |
| \(g\) | the charge weight \(1/(e^{W\nu}W\nu)\) | §5 |
| \(p_j/q_j\) | the continued-fraction convergents of \(\log_23\) | §5 |
| \(b_j\), \(s(L)\) | the Ostrowski digits of \(L=\sum_jb_jq_j\), and their sum | §5 |
| \(n_{\max}(L)\) | the largest cycle minimum the kill criterion admits at length \(L\) | §1, §5 |

In these core estimates, \(e\) is also Euler's number in the numerical
displays of §3 and §5, where it appears as \(e^{x}\).
\(s\) is an integration variable inside the two displays of §5.4 that
evaluate \(C_*\); the digit sum always carries its argument, \(s(L)\).
These conventions govern the core estimates; local symbols are reset
explicitly. In particular, \(I_b\) is the threshold interval and
\(m,M\) are extrema in §3.10; \(Q(s)\) is an odd-integer projection
in §3.11; \(U,V,P,Q\) are words in §3.13; and \(e_W(x)\) is the
absolute word loss in Appendix F. Local \(d\) symbols in Appendices
E--F denote quantities defined in their displays, including divisors,
carries and gaps.

## 2. Envelope

Let \(\mathcal B=\{E,O\}\). A finite itinerary \(w\in\mathcal B^*\) is
*realized* at \(n\in\mathbb N\) when the successive parities of the
trajectory of \(n\) are exactly the letters of \(w\). Write \(J^{|w|}(n)\)
for the endpoint after those letters, and \(\#O(w)\) for the number
of odd letters. When \(w\) is realized, this endpoint is the
\(|w|\)-fold iterate.

**Theorem 2.1 (fixed-itinerary monotonicity).**
If \(n\le m\) and both realize \(w\), then
\(J^{|w|}(n)\le J^{|w|}(m)\).

*Proof.* Induct on \(w\). The empty itinerary is immediate. The images
after a common realized prefix remain ordered, and both current
states realize the same next letter. The even branch is the
monotone integer square root; the odd branch is \(x\mapsto x^3\)
followed by the integer square root. \(\square\)

The realizing set of a fixed word need not be an interval: \(OE\) is
realized at \(7\) and at \(11\) but not at \(9\).

**Theorem 2.2 (finite-itinerary power envelope).**
If \(w\) is realized at \(n\) and \(m=J^{|w|}(n)\), then
\[
m^{2^{|w|}}\le n^{3^{\#O(w)}}.
\]

*Proof.* The empty itinerary is the equality \(n\le n\). Suppose a
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
It does not prove that every start realizes some contracting itinerary.

### 2.4 Exact floor defect

Theorem 2.2 is the inequality form of an exact identity
\[
n^{3^{\#O(w)}}=J^{|w|}(n)^{2^{|w|}}+\Delta_w(n),\qquad\Delta_w(n)\ge0.
\]
The identity, its vanishing law, and the two-term composition are
Theorems 2.4--2.6 and Corollary 2.7 in Appendix C. A mixed realized
word has \(\Delta_w(n)>0\). This explains why the envelope of
Theorem 2.2 is true, and why a mixed cycle itinerary is formally
expanding. Theorem 4.4 uses only the nonnegativity
\(\Delta_w(n)\ge0\).

No uniform local tax exists: the relative slack of a single
letter tends to \(0\) with the state. Finance must therefore be
a global comparison, not a fixed cost per odd or even step. A
quantitative itinerary-dependent lower bound on \(\Delta_w\), or
a tighter upper bound on \(\sum 1/(x_i\log x_i)\), would improve
the period cutoff; neither is proved here.

## 3. Structural restrictions on cycle itineraries

The role of this section in the paper is structural, not
numerical. The minimum geometry established here — the cycle
minimum is odd, prefixes to even states are superquadratic
(Theorem 3.2), a minimum-based itinerary has the canonical run form
of Lemma 3.21b, and the last even letter lands in an explicit
one-step preimage (Lemma 3.4(iv)) — is exactly what the finance unroll of
Section 4 and the transport of Section 5 consume. The
even-count exclusion (Theorem 3.22: every nontrivial cycle itinerary
has at least four even letters, hence period at least eleven)
is the section's own headline, but as a period bound it is
superseded the moment financing appears; it is retained because
it is floor-free. The small-period censuses (Theorems 3.6
and 3.8) are supporting. Main-text proofs are kept to the short
structural lemmas; the longer case analyses — Lemmas 3.5
and 3.7, the censuses of Theorems 3.6 and 3.8, and the family
exclusions of Theorems 3.12--3.21 — are Appendix D. After the one-step preimages, a minimum-based itinerary
has a canonical run form. The three regimes \(1\le e\le3\) use
\(O^{a_1}E\cdots O^{a_e}E\), with exactly \(e\) even letters.
These forms are eliminated by
a next-square obstruction, by long odd-run growth against a
last-even one-step preimage, or by a finite exceptional window. The family
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

**Lemma 3.1 (odd one-step preimages are unique).**
An odd fiber contains at most one integer. An even fiber is a
parity-restricted square interval and may contain many predecessors.

*Proof.* Suppose \(a<b\) lie in the same odd one-step preimage indexed by \(m\).
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
Let \(w\) be a cycle itinerary at \(n\ge2\).

(i) The itinerary is formally expanding:
\[
2^{|w|}<3^{\#O(w)}.
\]
A contracting itinerary cannot close a nontrivial cycle.

(ii) The cycle minimum is odd and the cycle maximum is even. A
minimum-based orientation cannot end in an odd letter.

(iii) A realized itinerary \(v\) is *superquadratic* if
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
Alternatively: a mixed cycle itinerary has \(\Delta_w(n)>0\) by
Theorem 2.5 in Appendix C, so the envelope is strict; a monochrome
tower cannot return for \(n\ge 2\).

Every state on such a cycle is at least \(2\): once a trajectory reaches
\(1\), it remains there and cannot return to a start \(n\ge 2\). An
even state \(x\ge 2\) satisfies \(J(x)<x\), so a cycle minimum cannot
be even. An odd state \(x\ge 3\) satisfies \(J(x)>x\), so a cycle
maximum cannot be odd. This proves the first assertion of (ii). For
the final-letter assertion, let \(x\) be the predecessor of a
minimum-oriented return \(n\). If the last letter were odd, the odd
return one-step preimage would give \(n^2\le x^3<(n+1)^2\). Minimality gives
\(x\ge n\), hence \(n^3<(n+1)^2\), impossible for \(n\ge 3\); and the
minimum is odd, so \(n\ge 3\).

For (iii), let a realized itinerary \(v\) send \(n\) to \(y\ge n^2\).
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
Let the cycle contain a state at least \(2\). After rotation to a minimum-based orientation, the itinerary begins
with \(OO\) and ends with \(E\); hence every itinerary with
\(1\le e\le 3\) even letters has the canonical run decomposition
\(O^{a_1}E\cdots O^{a_e}E\), with \(a_1\ge2\) and
\(a_i\ge0\) for \(i>1\). The case \(e=0\) is
all-odd and is already forbidden by the last-letter restriction.
No other cyclic rotation needs a separate case.

*Proof.* Theorem 3.2: the minimum is odd, so the itinerary cannot
begin with \(E\) or \(OE\), and it cannot end with an odd letter.
Thus a minimum-based itinerary starts \(OO\) and ends \(E\), so
\(e\ge 1\). The remaining letters are odd runs separated by the
\(e\) even letters, so the itinerary is \(O^{a_1}E\cdots O^{a_e}E\)
with \(a_1\ge 2\). The forms for \(e=1,2,3\) are respectively
\(O^aE\), \(O^aEO^cE\), and \(O^aEO^bEO^cE\).
Every nontrivial cycle itinerary has a minimum-based rotation
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
satisfies \(n^3\le 4\,J(n)^2\). Composing along a realized itinerary \(v\)
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
(iii) If a realized itinerary \(v\) satisfies \(J^{|v|}(q)\ge(q+1)^2\) and
the next realized letter is odd, then
\(J^{|v|+1}(q)\ge(q+1)^2\).
(iv) If \(vE\) is a cycle itinerary at \(n\), then
\(J^{|v|}(n)<(n+1)^2\).
(v) If \(a\ge 3\), then \(O^aE\) is not a cycle itinerary at any
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

For (v), suppose \(O^aE\) is a cycle itinerary at \(n\ge 2\). The start
is odd, hence at least \(3\), and realizes \(O^a\). Parts (ii) and
(iii) give \(J^a(n)\ge(n+1)^2\), contradicting (iv). \(\square\)

**Lemma 3.5 (two length-six exclusions).**
Neither \(OOOEOE\) nor \(OOOOEE\) is a cycle itinerary at any \(n\ge 2\).

*Proof.* Appendix D.

**Theorem 3.6 (small-cycle census).**
No itinerary of length at most six is a cycle itinerary at any \(n\ge 2\).
Equivalently, a nontrivial Juggler cycle, if one exists, has period at
least seven.

*Proof.* Appendix D. The reduction used there — an all-odd itinerary
cannot return, and every mixed cycle itinerary rotates to an
even-terminating cycle itinerary based at a cycle state \(m\ge 2\) —
is reused by Theorem 3.8 and Theorem 3.22.

Lemma 3.4(v) excludes every odd-run-then-even word \(O^aE\) with
\(a\ge 3\), of any length.

**Lemma 3.7 (two length-seven exclusions).**
Neither \(OOOOEOE\) nor \(OOOOOEE\) is a cycle itinerary at any \(n\ge 2\).

*Proof.* Appendix D.

**Theorem 3.8 (small-cycle census through length seven).**
No itinerary of length at most seven is a cycle itinerary at any \(n\ge 2\).
Equivalently, a nontrivial Juggler cycle, if one exists, has period at
least eight.

*Proof.* Appendix D.

Theorems 3.6 and 3.8 are supporting period statements. The
structural claim is the even-count exclusion of Theorem 3.22.
The same one-step preimages organise leftover itineraries by even-count. Write
\[
G_a=2\bigl(3^a-2^a\bigr)
\]
for \(a\ge 0\).

**Lemma 3.9 (trailing even run).**
If a cycle itinerary based at \(n\) ends with \(r\ge 1\) even letters,
the state immediately before that run is strictly less than
\((n+1)^{2^r}\).

*Proof.* The case \(r=1\) is Lemma 3.4(iv). Suppose the claim holds
for some \(r\ge 1\), and let \(vE^{r+1}\) be a cycle itinerary at \(n\).
Write \(z=J^{|v|}(n)\). The inductive hypothesis applied to the
suffix \(E^r\) after the first of those even letters gives
\(J(z)<(n+1)^{2^r}\). The state \(z\) is even, so
\(z<(J(z)+1)^2\le\bigl((n+1)^{2^r}\bigr)^2=(n+1)^{2^{r+1}}\).
\(\square\)

**Lemma 3.10 (odd-run lower envelope).**
If \(n\ge 1\) realizes \(O^a\), then
\[
n^{3^a}\le 2^{G_a}\,J^a(n)^{2^a}.
\]

*Proof.* Lemma 3.3 supplies a multiplicative constant \(C_v\) along
any realized itinerary, with \(C_\varepsilon=1\),
\(C\mapsto C\cdot 4^{2^j}\) on an even letter, and
\(C\mapsto C^3\cdot 4^{2^j}\) on an odd letter, at step \(j\). On
the pure odd word \(O^a\) every letter is odd, so
\(C_{O^{a+1}}=C_{O^a}^3\cdot 4^{2^a}\). Writing
\(C_{O^a}=2^{G_a}\) with \(G_0=0\) yields the recurrence
\(G_{a+1}=3G_a+2^{a+1}\), because \(4^{2^a}=2^{2^{a+1}}\). The closed
form \(G_a=2(3^a-2^a)\) satisfies the recurrence and the initial
value. \(\square\)

**Lemma 3.11 (seven-odd window).**
No integer \(n\) with \(2\le n<256\) realizes the itinerary \(O^7\).

*Proof.* This is a table of \(254\) seven-step evaluations: at every
such start, some letter fails to match the current parity. The same
finite check is the Lean `decide +kernel` evaluation behind
`no_follows_seven_odds_of_lt256` (Appendix A). \(\square\)

**Theorem 3.12 (two-even leftover families).**
Let \(k\ge 6\) and \(n\ge 2\). Neither \(O^{k-2}EE\) nor
\(O^{k-3}EOE\) is a cycle itinerary at \(n\).

*Proof.* Appendix D.

A cycle itinerary \(w\) at \(n\) is *minimum-based* when \(n\) is a
cycle minimum: \(J^j(n)\ge n\) for every \(0\le j<|w|\). The
remainder after a proper prefix of a cycle itinerary need not itself be
a cycle itinerary at the prefix endpoint. The next statement therefore
transports the tail inequality of Theorem 3.12, not the cycle-itinerary
exclusion at a later start.

**Theorem 3.13 (first-even transport).**
Let \(n\ge 2\). No minimum-based cycle itinerary at \(n\) has the form
\(O^aEO^bEE\) with \(a\ge 2\) and \(b\ge 4\), or the form
\(O^aEO^bEOE\) with \(a\ge 2\) and \(b\ge 3\).

*Proof.* Appendix D.

The hypothesis that the start is a cycle minimum is essential. If
\(y<n\), the leftover one-step preimage is measured against a larger start and
need not contradict the tail at \(y\). In particular, Theorem 3.13
does not assert that those itineraries fail to be cycle itineraries at a
non-minimum start. That upgrade is Theorem 3.21.

**Theorem 3.14 (three trailing evens).**
Let \(a\ge 6\) and \(n\ge 2\). The itinerary \(O^aEEE\) is not a cycle
word at \(n\).

*Proof.* Appendix D.

**Theorem 3.15 (mixed bunched family \(EOEE\)).**
Let \(a\ge 5\) and \(n\ge 2\). The itinerary \(O^aEOEE\) is not a cycle
word at \(n\).

*Proof.* Appendix D.

**Theorem 3.16 (mixed bunched family \(EOOEE\)).**
Let \(a\ge 4\) and \(n\ge 2\). The itinerary \(O^aEOOEE\) is not a
cycle itinerary at \(n\).

*Proof.* Appendix D.

**Theorem 3.17 (mixed bunched family \(EOOOEE\)).**
Let \(a\ge 3\) and \(n\ge 2\). The itinerary \(O^aEOOOEE\) is not a
cycle itinerary at \(n\).

*Proof.* Appendix D.

**Theorem 3.18 (mixed bunched family \(EEOE\)).**
Let \(a\ge 5\) and \(n\ge 2\). The itinerary \(O^aEEOE\) is not a
cycle itinerary at \(n\).

*Proof.* Appendix D.

**Theorem 3.19 (mixed bunched family \(EOEOE\)).**
Let \(a\ge 4\) and \(n\ge 2\). The itinerary \(O^aEOEOE\) is not a
cycle itinerary at \(n\).

*Proof.* Appendix D.

**Theorem 3.20 (mixed bunched family \(EOOEOE\)).**
Let \(a\ge 3\) and \(n\ge 2\). The itinerary \(O^aEOOEOE\) is not a
cycle itinerary at \(n\).

*Proof.* Appendix D.

**Theorem 3.21 (gapped leftovers as cycle itineraries).**
Let \(n\ge 2\). No cycle itinerary at \(n\) has the form \(O^aEO^bEE\)
with \(a\ge 2\) and \(b\ge 4\), or the form \(O^aEO^bEOE\) with
\(a\ge 2\) and \(b\ge 3\).

*Proof.* Appendix D.

Theorems 3.12--3.21 assemble into an even-count exclusion: no
cycle itinerary has fewer than four even letters, so a nontrivial
cycle has period at least eleven (Theorem 3.22). Section 4
excludes later periods by financing.

Every integer \(2\le n<12\) reaches \(1\), so a cycle minimum is
at least \(12\). Write \(e\) for the number of even letters.
Lemma 3.21b is the canonical run form.

**Lemma 3.21a (classification).**
Every nontrivial minimum-based cycle itinerary with at most three even letters
belongs to one of the families excluded by Lemma 3.4(v) and
Theorems 3.12--3.21.

*Proof.* Lemma 3.21b gives \(O^{a_1}E\cdots O^{a_e}E\)
with \(a_1\ge2\); write the last odd-run length as \(c\) when
\(e\ge2\). If
\(e=0\), the itinerary is all-odd. If \(e=1\), it is \(O^aE\). If
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
No itinerary with fewer than four even letters is a cycle itinerary at any
\(n\ge 2\). Equivalently, a nontrivial cycle itinerary has at least
four even letters.

*Proof.* Every cycle itinerary has a minimum-based rotation, with the
same even-count. Lemma 3.21b puts that orientation in canonical
run form; Lemma 3.21a names the families. In detail:

If \(e=0\), the itinerary is all-odd and cannot return, as in
Theorem 3.6.

If \(e=1\), the itinerary is \(O^aE\) with \(a\ge 2\). The case
\(a=2\) is \(OOE\), excluded in Theorem 3.6. The cases
\(a\ge 3\) are Lemma 3.4(v).

If \(e=2\), the itinerary is \(O^aEO^cE\) with \(a\ge 2\). A last
odd-run \(c\ge 2\) is an internal even letter followed by
\(OO\) or \(OOO\). Lemma 3.4 at the cycle minimum
(\(n\ge 12\)) contradicts the last-even one-step preimage. The remaining
shapes are \(O^aEE\) and \(O^aEOE\). Expansion forces
\(a\ge 4\) and \(a\ge 3\) respectively, so both are
Theorem 3.12.

If \(e=3\), the itinerary is \(O^aEO^bEO^cE\) with \(a\ge 2\).
Again \(c\ge 2\) is the internal-even bootstrap. The remaining
last runs are \(c=0\) and \(c=1\). For \(c=0\) and
\(b\ge 4\) the itinerary is a gapped leftover \(O^aEO^bEE\),
excluded by Theorem 3.21. For \(c=0\) and \(b\le 3\) the
word is one of \(O^aEEE\), \(O^aEOEE\), \(O^aEOOEE\),
\(O^aEOOOEE\), excluded by Theorems 3.14--3.17 once
expansion supplies the stated lower bounds on \(a\). For
\(c=1\) and \(b\ge 3\) the itinerary is a gapped leftover
\(O^aEO^bEOE\), excluded by Theorem 3.21. For \(c=1\) and
\(b\le 2\) the itinerary is one of \(O^aEEOE\), \(O^aEOEOE\),
\(O^aEOOEOE\), excluded by Theorems 3.18--3.20.

Thus \(e\le 3\) is impossible. \(\square\)

**Corollary 3.23.**
A nontrivial cycle, if one exists, has period at least eleven.

*Proof.* Theorem 3.22 gives four even letters, hence
\(o\le L-4\). Formal expansion is \(2^L<3^o\le 3^{L-4}\).
The comparison \(2^L<3^{L-4}\) first holds at \(L=11\).
\(\square\)

In particular there is no cycle of length eight, nine, or ten.

### 3.9 One inequality behind the eleven exclusions

The earlier exclusions use two envelopes: the odd-run lower envelope
of Lemma 3.10 pushes the state up, while the one-step preimage of the
trailing letters bounds it from above. A single comparison explains
the ten suffixes collected in Corollary 3.27.

**Lemma 3.24 (odd-run envelope in closed form).**
If \(n\ge 1\) realizes \(O^a\), then
\[
J^a(n)\ \ge\ 4\left(\frac n4\right)^{(3/2)^a}.
\]

*Proof.* Lemma 3.10 is \(n^{3^a}\le 2^{G_a}J^a(n)^{2^a}\) with
\(G_a=2(3^a-2^a)\). Taking \(2^a\)-th roots gives
\(J^a(n)\ge n^{(3/2)^a}\,2^{-G_a/2^a}\), and
\(G_a/2^a=2\bigl((3/2)^a-1\bigr)\), so the factor is
\(4^{\,1-(3/2)^a}\). \(\square\)

One constant and one exponent. The constant \(4\) is the whole cost of
Lemma 3.3's coarse step bound, paid once rather than \(a\) times, and
the exponent \((3/2)^a\) is the formal expansion rate. The next lemma
is the matching upper envelope, and it is Lemma 3.9 with the
hypothesis that the run is even deleted from the induction.

**Lemma 3.25 (backward envelope).**
Let \(w\) be a cycle itinerary at \(n\). For each suffix \(u\) of
\(w\), define an integer \(B(u)\) by
\[
B(\varepsilon)=n+1,\qquad
B(Eu)=B(u)^2,\qquad
B(Ou)=\min\{c\in\mathbb Z: c^3\ge B(u)^2\}.
\]
Then the state entering \(u\) is strictly less than \(B(u)\).

*Proof.* Induction on \(|u|\), from the empty suffix. The state
entering \(\varepsilon\) is the return \(n<n+1\). Let \(x\) be the
state entering \(Eu\) or \(Ou\) and \(y=J(x)\) the state entering
\(u\), so \(y<B(u)\) and, both being integers, \(y+1\le B(u)\). If
\(x\) is even, the even one-step preimage gives \(x<(y+1)^2\le B(u)^2\).
If \(x\) is odd, the odd one-step preimage gives \(x^3<(y+1)^2\le B(u)^2\),
so \(x\) is below the least integer whose cube reaches \(B(u)^2\).
\(\square\)

Lemma 3.9 is the case \(u=E^r\), where no cube root is taken and
\(B(E^r)=(n+1)^{2^r}\) exactly. In general, write
\[
T(u)\ =\ \frac{2^{|u|}}{3^{\#O(u)}}
\]
for the *backward exponent* of a suffix --- one factor \(2\) per even
letter, one factor \(\tfrac23\) per odd letter, read from the return
backwards. Then
\[
B(u)\ \ge\ (n+1)^{T(u)},
\]
with the excess coming only from rounding cube roots up. That excess
is additive in the state and therefore invisible in the exponent at
scale: for the ten suffixes below it is at most \(7\cdot 10^{-5}\) in
\(\log_{n+1}B(u)\) at \(n=10^3\), and below \(10^{-15}\) by \(n=10^{12}\).

**Theorem 3.26 (run--suffix law).**
Let \(w\) be a minimum-based cycle itinerary at \(n\ge 4\), and write
\(w=v\,O^a\,u\) where \(O^a\) is a maximal odd run, \(a\ge 1\), so that
\(u\) is empty or begins with an even letter. If \(u\) is nonempty,
then
\[
4\left(\frac n4\right)^{(3/2)^a}\ <\ B(u).
\]

*Proof.* Let \(m=J^{|v|}(n)\) be the state at the start of the run.
The itinerary is minimum-based, so \(m\ge n\ge 4\), and \(m\) realizes
\(O^a\). Lemma 3.24 at \(m\), with the right side increasing in
\(m\), gives \(J^a(m)\ge 4(n/4)^{(3/2)^a}\). That state is the one
entering \(u\), which Lemma 3.25 puts strictly below \(B(u)\).
\(\square\)

For a fixed suffix \(u\), the leading exponent of the backward
envelope is \(T(u)\). Thus \((3/2)^a>T(u)\) identifies shapes
that can be excluded once \(n\) is sufficiently large. At a specified
finite \(n\), however, the test is the exact displayed comparison with
\(B(u)\); the constants and the \(n+1\) terms cannot be dropped.
This does not assert formal non-expansion of every proper tail. The next
table evaluates the finite-envelope comparison for the stated suffixes.

**Corollary 3.27 (eleven statements, ten suffixes).**
Each row below is Theorem 3.26 for one suffix. The column *least
\(a\)* is the least odd-run length with \((3/2)^a>T(u)\); the
column \(n_u\) is the least cycle minimum at which the law fires,
computed against the exact envelope \(B(u)\) of Lemma 3.25.

| suffix \(u\) | \(T(u)\) | least \(a\) | \(n_u\) | printed in |
|---|---:|---:|---:|---|
| \(E\) | \(2\) | \(2\) | \(1032\) | Lemma 3.4(v), at \(a\ge3\) |
| \(EE\) | \(4\) | \(4\) | \(205\) | Theorems 3.12, 3.21 |
| \(EOE\) | \(8/3\) | \(3\) | \(109\) | Theorems 3.12, 3.21 |
| \(EEE\) | \(8\) | \(6\) | \(73\) | Theorem 3.14 |
| \(EOEE\) | \(16/3\) | \(5\) | \(60\) | Theorem 3.15 |
| \(EOOEE\) | \(32/9\) | \(4\) | \(45\) | Theorem 3.16 |
| \(EOOOEE\) | \(64/27\) | \(3\) | \(30\) | Theorem 3.17 |
| \(EEOE\) | \(16/3\) | \(5\) | \(60\) | Theorem 3.18 |
| \(EOEOE\) | \(32/9\) | \(4\) | \(45\) | Theorem 3.19 |
| \(EOOEOE\) | \(64/27\) | \(3\) | \(30\) | Theorem 3.20 |

Nine of the ten least odd-run lengths match the earlier statements. The tenth
is a strengthening: for \(u=E\) the law excludes \(a\ge 2\), so the word
\(OOE\) needs no appeal to the census of Theorem 3.6. Where a theorem
prints a threshold on \(n\), the law's is smaller --- \(205\) against
the \(256\) of Theorem 3.12, \(73\) against the \(128\) of Theorem 3.14,
\(45\) against the \(256\) of Theorem 3.16 --- because the backward
exponent is carried exactly as \(T(u)\) rather than rounded up to
the next power of two. Every threshold in the table is below the
certified descent floor by four orders of magnitude or more, so above
that floor Theorem 3.22 is Theorem 3.26 evaluated ten times.

Two caveats keep the table from replacing Appendix D outright. The
theorems it reproduces are stated for every \(n\ge 2\), and each closes
its window below the threshold with a `decide +kernel` evaluation; the
law says nothing there. And Theorem 3.21 upgrades Theorem 3.13 from
minimum-based itineraries to all cycle itineraries, which the law, being
a statement about a minimum-based orientation, does not do on its own.
Above the certified floor neither caveat is active.

**Lemma 3.28 (sharp odd-run envelope).**
Let \(O^a\) be an odd run inside a minimum-based cycle itinerary at
\(n\), starting at the state \(m\), and put
\[
X_a=3\bigl(3^a-2^a\bigr),\qquad Y_a=2\cdot 3^a-3\cdot 2^a .
\]
Then
\[
n^{X_a}\ <\ (n+1)^{Y_a}\bigl(J^a(m)+1\bigr)^{2^a}.
\]

*Proof.* Induction on \(a\). For \(a=1\) the odd one-step preimage gives
\(m^3<(J(m)+1)^2\), and \(m\ge n\), which is the claim with
\(X_1=3\), \(Y_1=0\). Suppose the display holds after \(k\) letters of
the run, with the state \(x_k\ge n\). Cubing gives
\[
n^{3X_k}<(n+1)^{3Y_k}(x_k+1)^{3\cdot 2^{k}} .
\]
Because \(n\le x_k\) one has \(n(x_k+1)\le(n+1)x_k\), hence
\((x_k+1)^{e}n^{e}\le(n+1)^{e}x_k^{e}\) for \(e=3\cdot2^{k}\);
multiplying through by \(n^{e}\) and substituting turns the display into
\[
n^{3X_k+e}<(n+1)^{3Y_k+e}\,x_k^{\,e}.
\]
Finally \(x_k^{3\cdot2^k}=(x_k^3)^{2^k}<\bigl((x_{k+1}+1)^2\bigr)^{2^k}\).
So \(X_{k+1}=3X_k+3\cdot2^{k}\) and \(Y_{k+1}=3Y_k+3\cdot2^{k}\), whose
solutions from \(X_1=3,\ Y_1=0\) are the stated closed forms.
\(\square\)

The difference from Lemma 3.24 is where minimum-basedness is used.
Lemma 3.24 uses it once, at the start of the run, and then pays
Lemma 3.3's factor \(4\) at every step. Lemma 3.28 uses it at *every*
step: the intermediate state is itself above the cycle minimum, so the
successor's \(+1\) can be traded for a factor \((n+1)/n\) rather than
for a factor \(4\). This is the chain already formalized at \(a=7\) in
`Problems/Juggler/O7EEEEGap.lean`, whose constants \(6177\) and
\(3990\) are \(X_7\) and \(Y_7\); `absorb_odd_step` there is the
inductive step above.

**Theorem 3.29 (run--suffix law, sharp form).**
In the situation of Theorem 3.26,
\[
n^{X_a}\ <\ (n+1)^{Y_a}\,B(u)^{2^a}.
\]

*Proof.* Lemma 3.28 bounds \(J^a(m)+1\) from below and Lemma 3.25
bounds \(J^a(m)+1\le B(u)\) from above. \(\square\)

Since \(X_a-Y_a=3^a\), the leading-order reading is unchanged: with
\(B(u)\approx(n+1)^{T(u)}\) the criterion is again the crossing
\((3/2)^a>T(u)\). What changes is the price. Theorem 3.26 has to
buy the crossing against a factor \(4^{(3/2)^a}\), which costs a margin
\(\log4/\log n\); Theorem 3.29 buys it against \((1+1/n)^{Y_a}\), which
costs a margin of order \(1/(n\log n)\). The crude form needs a floor
exponential in the reciprocal margin, the sharp form one merely linear
in it.

**Corollary 3.30 (the same table, sharply).**
For the ten suffixes of Corollary 3.27, the least cycle minimum at
which Theorem 3.29 fires is
\[
7,\;6,\;6,\;5,\;5,\;5,\;5,\;5,\;5,\;5
\]
in the order printed there, against \(1032,205,109,73,60,45,30,60,45,30\)
for Theorem 3.26 and \(256\) or \(128\) in the proofs of Appendix D.
Every \(n\le 299\) reaches \(1\), so a cycle minimum is at least
\(300\) and all ten are unconditional.

**Theorem 3.31 (even count at least eight).**
Every cycle itinerary based at \(n\ge2\) has at least eight even
letters. Consequently, every nontrivial cycle has period at least
twenty-two.

*Proof.* Let a minimum-based cycle itinerary have
\(e\le 7\) even letters and canonical run form
\(O^{a_0}E\cdots O^{a_{e-1}}E\). Apply Theorem 3.29 at run \(i\). Its
suffix has \(e-i\) even letters and \(\sum_{j>i}a_j\) odd ones, so
\(T(u)\le 2^{\,e-i}\), with equality exactly when the later runs
are empty; and the criterion is monotone in \(B(u)\), so that empty case
is the worst. Hence
\[
a_i\ \le\ \Bigl\lfloor (e-i)\,\tfrac{\log 2}{\log(3/2)}\Bigr\rfloor,
\]
and the thresholds of those bounding applications --- rows \(r\le 7\) of
the table in Remark 3.32 --- are all at most \(55\). The run bounds are
\((5,3,1)\), \((6,5,3,1)\), \((8,6,5,3,1)\), \((10,8,6,5,3,1)\) and
\((11,10,8,6,5,3,1)\) for \(e=3,\dots,7\), leaving \(16\), \(186\),
\(2037\), \(25353\) and \(325452\) canonical forms once formal expansion
\(3^{o}>2^{o+e}\) is imposed. Theorem 3.29 closes every one of them, the
first four at \(n\ge16\) and the last at \(n\ge64\). The cases
\(e\le2\) are Theorem 3.22. A cycle minimum is at least \(300\), so
\(n\ge64\) is free. Given \(e\ge8\), formal expansion
\(2^{L}<3^{L-8}\) first holds at \(L=22\). \(\square\)

This replaces \(e\ge4\) and period \(\ge11\) in Theorem 3.22 and
Corollary 3.23 --- it doubles the floor-free period bound --- which remain the statements proved for every \(n\ge2\)
without any descent input. Numerically the gain is of no consequence
--- Theorem 4.6 already gives period \(\ge25781\) at a floor of
\(10^{6}\) --- but Corollary 3.23 is the paper's only bound that needs no
floor at all, and this is how far the same two envelopes carry it.

**Remark 3.32 (where the law stops, and why Section 4 exists).**
The reading \(B(u)\approx(n+1)^{T(u)}\) is good only while the
backward exponent stays comfortably above \(1\), because the envelope of
Lemma 3.25 rounds a cube root up at every odd letter. For short
suffixes that rounding is invisible: over the ten suffixes of
Corollary 3.27 it moves \(\log_{n+1}B(u)\) by at most \(7\cdot10^{-5}\)
at \(n=10^{3}\). For a cycle candidate read as one long word it is the
whole story. There the exponent of the full word is
\(2^{L}/3^{o}=1-\theta\), just *below* one, so the envelope hovers at
\(n\) itself and the \(+1\) rounded into each of the \(L\) backward
steps is no longer negligible; accumulated, it is exactly the factor
\(L\) that Theorem 4.4 carries on its right-hand side. The
run--suffix law is sharp on short tails and degenerates to the finance
inequality on the whole cycle. That is the division of labour between
this section and the next.

The margins the law has to pay for are the same objects Section 5
fights. For the pure trailing block \(O^{a_r}E^{r}\), writing \(a_r\)
for the least \(a\) with \((3/2)^{a}>2^{r}\), the margin is
\(\theta\) at \((o,L)=(a_r,a_r+r)\):

| \(r\) | \((o,L)\) | \(L/o\) | \(\theta_r\) | \(n\) threshold |
|---:|---|---|---:|---:|
| \(1\) | \((2,3)\) | \(3/2\) | \(0.1111\) | \(7\) |
| \(2\) | \((4,6)\) | \(3/2\) | \(0.2099\) | \(6\) |
| \(3\) | \((6,9)\) | \(3/2\) | \(0.2977\) | \(5\) |
| \(4\) | \((7,11)\) | \(11/7\) | \(0.0636\) | \(16\) |
| \(5\) | \((9,14)\) | \(14/9\) | \(0.1676\) | \(8\) |
| \(6\) | \((11,17)\) | \(17/11\) | \(0.2601\) | \(6\) |
| \(7\) | \((12,19)\) | \(19/12\) | \(0.0135\) | \(55\) |
| \(11\) | \((19,30)\) | \(30/19\) | \(0.0762\) | \(15\) |
| \(14\) | \((24,38)\) | \(19/12\) | \(0.0267\) | \(32\) |

The spikes sit at \(11/7\) and \(19/12\), the semiconvergent and the
convergent of \(\log_2 3\) at smallest denominator, and the thresholds
they carry grow like \(1/\theta_r\) rather than like
\(\exp(1/\theta_r)\) --- which is why they stay in the tens. What
limits Theorem 3.31 is therefore not any threshold but the enumeration:
the number of canonical forms with \(e\) even letters grows faster than
\(e!\). The obstruction that stops this section and the obstruction
that leaves the semiconvergent fan of Section 5 standing are the same
arithmetic; only the denominators differ.

*What each further even letter is worth.* Expansion at even count
\(e\) needs \(L\log(3/2)>e\log3\), so each further even letter buys
\(\log3/\log(3/2)\in(2.70,2.71)\) in period: the thresholds are
\(11,14,17,19,22\) at \(e=4,5,6,7,8\). Both ends of that constant are
integer certificates rather than numerical bounds on logarithms:
\((3/2)^{27/10}<3\) is \(3^{17}<2^{27}\), and \(3<(3/2)^{271/100}\)
is \(2^{271}<3^{171}\), the latter tight to four significant figures
(`expansion_rate_lower`, `expansion_rate_upper`, `expansion_e4`,
`expansion_e5`, `expansion_e6`, `FanLaw.lean`).

An earlier draft of this section priced a fifth even letter as a
family program in the style of Theorems 3.14--3.20: two further
gapped-leftover theorems and some twenty-five bunched families, for
three units of period. Theorem 3.31 makes that program unnecessary.
The route it takes is not a longer case analysis but a cheaper
envelope --- Lemma 3.28 in place of Lemma 3.24 --- and the case
analysis it then needs is mechanical rather than hand-written. What
the earlier accounting got right is that raising the even count is
the only route to a stronger floor-free statement; what it got wrong
is the assumption that the eleven exclusions had to be generalised
one at a time.

### 3.10 Cycle order below the cubic height

The preceding restrictions concern the itinerary or its counts. A height
hypothesis gives additional information about the order of all states in
the closed orbit. Throughout this subsection a primitive cycle means its
distinct states in one traversal; \(m\) and \(M\) denote its minimum and
maximum. The bounds obtained here do not exclude every cycle or improve
the numerical period bounds in Section 5.

**Theorem 3.33 (cubic-band order).**
Suppose \(C\) is a primitive nontrivial Juggler cycle of length \(L\),
minimum \(m>1\), maximum \(M<m^3\), and odd-state count \(o\).
Put \(e=L-o\) and list its states as
\(c_0=m<c_1<\cdots<c_{L-1}=M\). Then
\[
\begin{split}
&c_i\text{ is odd}\quad\Longleftrightarrow\quad i<o
\quad\Longleftrightarrow\quad c_i<m^2,\\
&J(c_i)=c_{(i+e)\bmod L},\qquad \gcd(L,o)=1.
\end{split}\tag{CB1}
\]
If \(a_k\) is the number of odd steps in the first \(k\) steps from
the minimum, then, for \(0\le k\le L\),
\[
a_k=\left\lceil\frac{ko}{L}\right\rceil.\tag{CB2}
\]
Thus the letter at position \(k\), starting with position zero, is
\(O\) precisely when
\(\lceil(k+1)o/L\rceil-\lceil ko/L\rceil=1\).
This specifies the word, rather than only its letter counts.

In particular, a primitive nontrivial cycle whose minimum-based word
is not (CB2), or whose counts satisfy \(\gcd(L,o)>1\), must satisfy
\(M\ge m^3\). Since \(m\) is odd and \(M\) even, the integer
consequence is \(M\ge m^3+1\). This is a conditional height bound,
not a global cycle exclusion.

**Proof.** A cycle with minimum greater than 1 has odd minimum \(m\ge3\):
an even minimum would map below itself. Its maximum is even, since
\(\lfloor\sqrt{x^3}\rfloor>x\) for every integer \(x\ge3\).
Thus \(o,e>0\).

If an even state \(x\in C\) satisfied \(x<m^2\), then
\(J(x)<m\), impossible. If an odd state \(x\in C\) satisfied
\(x\ge m^2\), then
\(J(x)\ge\lfloor\sqrt{(m^2)^3}\rfloor=m^3>M\), also impossible.
Therefore the first \(o\) sorted states are exactly the odd states.

For any even \(x\in C\) and odd \(y\in C\), monotonicity gives
\[
J(x)\le\lfloor\sqrt M\rfloor
\le\lfloor\sqrt{m^3}\rfloor\le J(y).
\]
The possible equality from taking floors must be handled: \(J\)
permutes the states of a primitive cycle, so it is injective on
\(C\). Equality of these images would force \(x=y\), impossible
for opposite parities. Hence every even image is strictly below
every odd image. Each branch is nondecreasing, and injectivity on
\(C\) makes its restriction strictly increasing.

The \(e\) even images are consequently \(c_0,\ldots,c_{e-1}\),
in that order, and the \(o\) odd images are
\(c_e,\ldots,c_{L-1}\), in that order. This proves
\(J(c_i)=c_{(i+e)\bmod L}\).
Adding \(e\) modulo \(L\) has an orbit of size
\(L/\gcd(e,L)\). Primitivity requires that size to be \(L\),
so \(\gcd(e,L)=\gcd(o,L)=1\).

From rank zero the rank at time \(k\) is \(ke\bmod L\).
An even step occurs exactly when adding \(e\) wraps past \(L\):
the starting rank is then at least \(L-e=o\). The number of wraps
in the first \(k\) additions is \(\lfloor ke/L\rfloor\).
The odd count is therefore
\(k-\lfloor ke/L\rfloor=\lceil ko/L\rceil\), proving (CB2).
No exact logarithmic closure is used.


**Proposition 3.34 (threshold comparison map).**
For every integer \(b\ge3\), define a different map on
\(I_b=\{b,b+1,\ldots,b^3-1\}\):
\[
S_b(x)=\begin{cases}
\lfloor\sqrt{x^3}\rfloor,&x<b^2,\\
\lfloor\sqrt{x}\rfloor,&x\ge b^2.
\end{cases}\tag{CB3}
\]
It maps \(I_b\) into itself, has no fixed point, and therefore has
a cycle of length at least two. All its primitive cycles have the
rank-rotation and mechanical-word properties in (CB1)--(CB2), counting
branch labels instead of actual odd integers. Their minima are at
least \(b\), so this construction is unbounded in scale.

**Map distinction:** (CB3) chooses its branch by size. It is not the
Juggler map. A cycle of (CB3) is a Juggler cycle if and only if every
state satisfies
\[
x\text{ odd}\quad\Longleftrightarrow\quad x<b^2.\tag{CB4}
\]
The construction does not assert that (CB4) ever holds on a full cycle.

**Proof.** For \(b\le x<b^2\),
\(b\le x<\lfloor\sqrt{x^3}\rfloor<b^3\).
For \(b^2\le x<b^3\),
\(b\le\lfloor\sqrt x\rfloor<b^2\le x\).
Both conclusions follow directly from the square/cube inequalities;
the strict growth uses \(x\ge3\). Thus (CB3) preserves the nonempty
finite set \(I_b\), and neither branch has a fixed point there.
Every orbit eventually repeats, yielding a primitive cycle of
length at least two.

On any such cycle the states using the odd branch are its lower
part \(x<b^2\). The even-branch images are at most
\(\lfloor\sqrt{b^3-1}\rfloor\), and the odd-branch images are
at least \(\lfloor\sqrt{b^3}\rfloor\).
Once again these weak inequalities become strict between cycle
images by injectivity. The same sorting and modular-rank argument
proves (CB1)--(CB2) with branch counts. Since the least state is at
least \(b\), these closed orbits exist beyond any fixed lower bound.

Their formal exponent is also strictly expanding. Composing
\(S_b(x)\le x^{3/2}\) or \(S_b(x)\le x^{1/2}\) around a cycle
with minimum \(r>1\) gives
\(r\le r^{3^o/2^L}\), hence \(3^o\ge2^L\).
Equality is impossible for positive \(o,L\), since a positive
power of 3 is odd and a positive power of 2 is even.
Consequently \(3^o>2^L\). This sign, exact floors, distinctness,
closed-orbit order and unbounded minimum coexist in the relaxed map.
They do not force the missing parity rule (CB4).


**Theorem 3.35 (common period and interlacing).** For a
fixed \(b\ge3\), all primitive cycles of \(S_b\) have the same
period, lower/upper counts, and minimum-based mechanical word. If
there are \(t\) cycles of common period \(L\), they interlace:
in the sorted list of all \(tL\) periodic points, each cycle occupies
exactly one residue class of ranks modulo \(t\).

**Proof.** Let \(P\) be the union of all periodic points. It is a
nonempty finite invariant set, and \(S_b\) permutes it. Put
\(N=|P|\), and let \(E\) count its upper-branch points. As in
Theorem 3.33, branch monotonicity and separated image ranges, with
injectivity removing ties, make the rank permutation addition by
\(E\) modulo \(N\). Write \(t=\gcd(N,E)\). This permutation has
exactly \(t\) orbits, each of length \(L=N/t\), namely the rank
residue classes modulo \(t\). The upper states occupy the final
\(E\) ranks. Since \(t\mid E\), every residue class contains
exactly \(e=E/t\) of them. All cycles therefore have counts
\((o,e)=((N-E)/t,E/t)\), and Theorem 3.33's wrap count gives
their identical minimum-based word. This does not assert uniqueness.

**Proposition 3.36 (uniform sorted grid).** Let \(C\)
be a primitive threshold cycle, or an actual Juggler cycle with
\(m>1\) and \(M<m^3\). Retain its sorted states \(c_i\) and
counts \((L,o,e)\), and put
\[
T=\log3,\quad \alpha=\log(3/2),\quad
\Lambda=o\log3-L\log2>0,
\quad v_i=\log\frac{\log c_i}{\log m}.
\]
Extend \(v_{i+L}=v_i+T\). With \(w_i=v_i-iT/L\),
\[
\operatorname{osc}(w)\le\left(1-\frac1L\right)\Lambda,
\qquad
\left|v_i-\frac{iT}{L}\right|
\le\left(1-\frac1L\right)\Lambda.\tag{CB5}
\]
The lifted adjacent gaps \(h_i=v_{i+1}-v_i>0\), including the
gap at the seam, satisfy
\[
\max h_i-\min h_i\le\Lambda,
\qquad
\left|h_i-\frac TL\right|
\le\left(1-\frac1L\right)\Lambda.\tag{CB6}
\]
These are uniform bounds on every rank, without a factor \(L\)
in the error.

**Proof.** Let \(p_i=3/2\) for \(i<o\) and \(p_i=1/2\)
otherwise, and let \(y_i\) be the successor of \(c_i\). Define
\[
\delta_i=\log\frac{p_i\log c_i}{\log y_i}\ge0.
\]
All states exceed 1. Exact floors give \(y_i\le c_i^{p_i}\),
which justifies the sign. The rank rule and the periodic lift give
\[
v_{i+e}=v_i+\alpha-\delta_i.\tag{CB7}
\]
For an upper step the lift adds \(T\), converting \(-\log2\)
to \(\alpha\). Summing over all ranks gives
\[
\sum_i\delta_i=L\alpha-eT=\Lambda,
\qquad
w_{i+e}-w_i=\frac\Lambda L-\delta_i.\tag{CB8}
\]
In particular \(\Lambda\ge0\). Equality would give
\(3^o=2^L\), impossible for positive branch counts, so
\(\Lambda>0\).
For distinct ranks \(i,j\), choose \(1\le k\le L-1\) with
\(j\equiv i+ke\pmod L\). The \(k\) indices traversed are
distinct because \(\gcd(e,L)=1\). Thus
\[
w_j-w_i=\frac{k\Lambda}{L}
 -\sum_{r=0}^{k-1}\delta_{i+re}.
\]
The partial sum is between 0 and \(\Lambda\), proving the
oscillation bound. Since \(w_0=0\), it also proves the absolute
bound in (CB5). Subtracting (CB7) at neighboring ranks gives
\(h_{i+e}-h_i=\delta_i-\delta_{i+1}\). Iteration expresses any
difference of two gaps as the difference of two partial sums of
the \(\delta_i\); each lies in \([0,\Lambda]\). Hence the gap
range is at most \(\Lambda\). Its mean is \(T/L\), and the
maximum distance from the mean of \(L\) values of range at most
\(\Lambda\) is at most \((1-1/L)\Lambda\), proving (CB6).
The seam gap is positive because \(M<m^3\), irrespective of
whether (CB6) supplies a positive numerical lower bound.

**Parity-scale limitation.** Actual lower states are distinct odd
integers, so \(c_i\ge m+2i\) for \(i<o\). A necessary consequence
of (CB5) is
\[
\log\frac{\log(m+2i)}{\log m}
\le\frac{i\log3}{L}+\Lambda.
\]
If \(\Lambda\le C/L\), the case \(i=1\) gives
\[
L\le\frac{\log3+C}{\log(\log(m+2)/\log m)}
\sim\frac{\log3+C}{2}\,m\log m.
\]
This does not conflict with a minimum of order \(L^2\). More
specifically, for an unanchored rank \(i>0\), the interval for a state permitted by (CB5) has width
of order \(c_i\log(c_i)\Lambda\) in the local regime
\(\Lambda\log(c_i)\ll1\).
In the illustrative regime \(\Lambda\) comparable to \(1/L\)
and \(m\) comparable to \(L^2/(\log L)^2\), that permitted width
is already of order \(L/\log L\) at low unanchored ranks and
therefore does not determine parity. The minimum \(c_0=m\) is fixed
exactly and has no such uncertainty. This is a statement about the
precision of (CB5), not a lower bound on the actual error or an assertion
that a cycle realizes this scale. Proposition 6.3b supplies an additional
upper-cell restriction, including a constraint on the leading constant.

**Proposition 3.37 (one-unit successor allowance).** For every
odd \(b\ge3\), define
\[
D_b=\{x\text{ odd}:b\le x\le b^2\}
\cup\{x\text{ even}:b^2+1\le x\le b^3-1\}.
\]
For \(b\le z\le b^3\), let
\(P_b(z)=\max\{d\in D_b:d\le z\}\), and set
\[
R_b(x)=\begin{cases}
P_b(x^{3/2}),&x\text{ odd},\\
P_b(\sqrt x),&x\text{ even}.
\end{cases}
\]
This finite map has a nontrivial cycle and every edge satisfies
\[
R_b(x)\in\{J(x),J(x)-1\}.
\tag{CB9}
\]
The exponent agrees with the actual source parity at every state.
All its primitive cycles have \(M<m^3\), the rank-rotation rule,
coprime counts, and the mechanical word. Therefore correct source
parity, this global order, and one-sided power-rounding loss below
2 admit closed orbits at arbitrarily large minima.

**Proof and boundary check.** Adjacent members of \(D_b\) have
gap 2, except the gap 1 from \(b^2\) to \(b^2+1\). Therefore
\(0\le z-P_b(z)<2\), including \(z=b^3\), whose image is
\(b^3-1\). Odd source images lie between \(b^{3/2}\) and
\(b^3\); even source images lie strictly between \(b\) and
\(b^{3/2}\). The projection is defined in each case and preserves
\(D_b\). Odd steps strictly increase, since
\(x^{3/2}-x\ge3\sqrt3-3>2\) for \(x\ge3\); even steps
strictly decrease. Finiteness gives a nontrivial cycle. Its minimum
is odd and at least \(b\), its maximum is even and below \(b^3\),
so \(M<m^3\). The common nondecreasing projection preserves the
weak separation of the two image ranges; injectivity on a cycle
makes it strict. The rank proof applies again. Finally an integer
output at one-sided distance less than 2 from the real power differs
from its floor by either 0 or 1, proving (CB9).

The inclusion of \(b^2\) is essential: ending the lower odd range
at \(b^2-2\) would create a gap 3 and would not prove (CB9).
The exact-floor characterization "odd iff \(x<m^2\)" is **not**
imported into this altered map; an odd source \(b^2\) is allowed.
The rank and mechanical-word conclusions, which do not need that
characterization, are the ones retained.

No assertion is made that every \(R_b\) cycle contains an altered
edge. Proving that assertion uniformly would itself exclude the
cubic-band Juggler cycles: a cycle with all corrections zero is an
actual Juggler cycle, and any actual cubic-band cycle lies in
\(D_m\) and is unchanged by \(R_m\). For the explicit cycle in Proposition 3.38, each odd edge is altered.

**Equal rotation fractions do not detect an alteration.** At
\(b=3\), \(S_b\) has \(3\to5\to11\to3\), while \(R_b\)
has \(3\to5\to10\to3\). They have identical period and counts,
but different cycles. Thus replacing the map by a monotone downward
projection need not strictly change its common rotation fraction.

**Proposition 3.38 (branch offsets are invisible to differences).** Define \(G\) on positive integers by
\(G(1)=1\), \(G(x)=J(x)-1\) for odd \(x\ge3\), and
\(G(x)=J(x)\) for even \(x\). It has the primitive cycle
\[
13,45,300,17,69,572,23,109,1136,33,188,13.\tag{CB10}
\]
Its minimum is 13, its maximum is \(1136<13^3\), and its counts
are \((L,o,e)=(11,7,4)\). It is also a cycle of
\(R_{11}\). Every source uses its actual parity, and the same
rank and mechanical-word conditions hold.

Nevertheless, for every pair of odd sources \(x,x'\ge3\), or
every pair of even positive sources,
\[
G(x')-G(x)=J(x')-J(x).\tag{CB11}
\]
This is a global identity, not a numerical approximation on (CB10).
On sources greater than 1, all within-branch higher finite differences erase the
constant shift. Thus global rank order, correct source parity, and
even the complete within-branch image-difference data of \(J\)
restricted to sources greater than 1 do not by themselves exclude cycles.
Differences involving the fixed point 1 are deliberately excluded:
since \(G(1)=J(1)\), they could anchor the odd-branch constant.

**Exact witness certificate.** The entries in the middle column
are certified by \(J(x)^2\le x^h<(J(x)+1)^2\), with \(h=3\)
on odd sources and \(h=1\) on even sources. Subtracting one on
each odd row yields the successive states of (CB10).

| \(x\) | \(J(x)\) | \(G(x)\) |
|---:|---:|---:|
| 13 | 46 | 45 |
| 45 | 301 | 300 |
| 300 | 17 | 17 |
| 17 | 70 | 69 |
| 69 | 573 | 572 |
| 572 | 23 | 23 |
| 23 | 110 | 109 |
| 109 | 1137 | 1136 |
| 1136 | 33 | 33 |
| 33 | 189 | 188 |
| 188 | 13 | 13 |

All eleven states are distinct. Each row can be checked directly by the displayed square-cell inequalities. Formula (CB11) follows immediately
by subtracting the same branch constant on both sides.

**Why the strict nearest-even gap test also fails.** Suppose two
sources \(x<x'\) on the same branch have same-parity successors
in (CB10). Their image gap \(d'=G(x')-G(x)\) is even. For the
relevant real branch \(f\), (CB11) gives
\[
\left|d'-\bigl(f(x')-f(x)\bigr)\right|<1,
\]
because the difference of the two fractional parts lies strictly
between \(-1\) and 1. Thus \(d'\) is the unique even integer
within distance less than 1 of the smooth increment. This
strict gap test survives every changed odd edge of this example.

The lost information is the absolute position of each branch image
inside its unit floor cell. Subtracting neighboring equations
removes an additive constant for each branch. A proof using gaps
must restore those constants through absolute values or a relation
between the branches. This counterexample concerns a different map;
it neither proves nor refutes the no-cycle statement for \(J\).


**The remaining absolute floor-cell question.** Define the wrong-parity set

\[
B_b=\{x\in I_b:x<b^2,\ x\text{ even}\}\ \cup
\{x\in I_b:x\ge b^2,\ x\text{ odd}\}.
\]

Must every cycle of \(S_b\) meet \(B_b\), for every integer \(b\ge3\)?
An affirmative answer is equivalent to excluding all actual Juggler cycles
with \(m>1\) and \(M<m^3\). Indeed, a threshold cycle avoiding \(B_b\)
is an actual cycle, and an actual cycle in this height range is an
\(S_m\) cycle by Theorem 3.33. The regime \(M\ge m^3\) is separate.

Proposition 3.38 rules out a contradiction based only on the within-branch
differences on sources greater than 1: subtraction removes a branch constant.
The exact conditions retain more information. With successor \(y\), they are

\[
y^2\le x^3<(y+1)^2\quad(x\text{ odd}),\qquad
y^2\le x<(y+1)^2\quad(x\text{ even}).
\]

The uniform wrong-parity conclusion from these absolute cells remains open
in this paper. Finite checks of the threshold or altered maps do not settle it.

### 3.11. A periodic return boundary and a sharper height ceiling

The absolute-cell question has a partial answer near the top of the
cubic height band. This restriction uses the return map of the complete
periodic set. Isolated admissible blocks do not supply its ordering
condition.

Write \(O(x)=\operatorname{isqrt}(x^3)\) and
\(E(x)=\operatorname{isqrt}(x)\). These are prescribed branches;
a word in \(O,E\) need not agree with the parities of its intermediate
states. Composition is chronological: \(F_{OOE}=E\circ O\circ O\).
Let \(Q(s)\) denote the greatest odd integer not exceeding \(s\).

**Theorem 3.39 (periodic return height restriction).** Suppose that an
actual Juggler cycle has minimum \(m\ge5\) and maximum \(M<m^3\). Put
\[
q=O(m),\qquad t=E(M),\qquad z=F_{OOE}(m)=Q(m^{9/8}).
\]
Then \(m,q,t,z\) are odd and
\[
t^3+2\le[z(z-2)]^2,\qquad M+2\le(t+1)^2. \tag{RC1}
\]
Consequently, if \(T\) is the greatest positive odd integer satisfying
\(T^3+2\le[z(z-2)]^2\), then
\[
M\le(T+1)^2-2. \tag{RC2}
\]
For \(m\ge7\), a simpler consequence is
\[
\boxed{M<m^3-m^{15/8}.} \tag{RC3}
\]
Equivalently, the positive integer gap satisfies
\((m^3-M)^8>m^{15}\).

*Proof.* We first record two branch estimates, valid without source-parity
assumptions:
\[
O(O(x))\ge x^2\quad(x\ge3),\qquad
F_{OOE}(x)>x\quad(x\ge5). \tag{RC4}
\]
For the first, take \(k=\operatorname{isqrt}(x)\). If \(x\ge4\), then
\(k\ge2\), \(x\le k^2+2k\le k^3\), and \(O(x)\ge kx\).
Thus \(O(x)^3\ge x^4\), which implies the claim. At \(x=3\),
\(O(O(3))=11\ge9\).
For the second, if \(x\ge9\), then \(k\ge3\) and
\(k^3\ge x+12\). Hence
\[
O(x)^3\ge(x+12)x^3>(x+1)^4.
\]
The last inequality follows from
\(8x^3-6x^2-4x-1>0\). For \(x=5,6,7,8\), the first images
are \(11,14,18,22\), whose cubes are respectively at least
\(6^4,7^4,8^4,9^4\). The excluded values \(3,4\) satisfy
\(F_{OOE}(x)=x\).

Let \(C\) be the cycle set. Its actual parities make it an \(S_m\)
cycle: an even source has square root at least \(m\), and so is at
least \(m^2\); an odd source at least \(m^2\) would have image at
least \(m^3\), contrary to the height assumption. In particular,
the minimum is an odd source and the maximum is an even source.
Every even-branch image is below \(m^2\), and two successive odd
branches reach at least \(m^2\) by (RC4). Therefore the successive
returns after even steps have only the words \(OE\) and \(OOE\).

The correct section, including its strict upper endpoint, is
\[
Y=C\cap[m,q),\qquad q=O(m).
\]
All odd-branch images are at least \(q\). All even-branch images
are at most \(\operatorname{isqrt}(m^3-1)\le q\).
Equality with \(q\) is impossible: \(q\) is already the image of
\(m\), and the cycle map is injective on \(C\). Thus \(Y\) is exactly
the set of even-branch images and \(t=E(M)=\max Y\).
Every point of \(Y\) is odd. The return word at \(x\in Y\) is
\(OOE\) when \(x^3<m^4\), and \(OE\) otherwise.

The minimum \(m\) uses \(OOE\), since
\(F_{OE}(m)=\lfloor m^{3/4}\rfloor<m\).
The maximum \(t\) uses \(OE\), since an \(OOE\) return would
increase it by (RC4). Set
\[
z=F_{OOE}(m),\qquad w=F_{OE}(t).
\]
Monotonicity and \(t<q\) give
\[
w\le F_{OE}(q)=z.
\]
These images are distinct. Indeed, the first-return map is a
permutation of \(Y\), and \(m<t\), since the return of \(m\) is
larger than \(m\). Hence \(w<z\). Since both are odd,
\[
w\le z-2. \tag{RC5}
\]
The short-word identity in Appendix E.1 gives
\(z=Q(m^{9/8})\); here its odd-output hypothesis is supplied by the
actual cycle.

Write \(p=O(t)\). The states \(p,M\) are even, whereas \(t,w,z\)
are odd. The exact cells and their parity faces imply
\[
p+2\le(w+1)^2\le(z-1)^2,\qquad
t^3+2\le(p+1)^2\le[z(z-2)]^2.
\]
The cell for \(M\mapsto t\) similarly gives \(M+2\le(t+1)^2\).
This proves (RC1) and its integer ceiling (RC2).

For the smooth bound (RC3), even the weaker consequence
\[
t^3<(z-1)^4,\qquad z^8\le m^9
\]
is sufficient. Set \(r=m^{3/8}\). Since \(m\ge7\), \(r\ge2\).
We have \(z\le r^3\), and
\[
(r^3-1)^4\le(r^4-r)^3,
\]
because the difference of the right and left sides is
\((r^3-1)^3\ge0\). Thus \(t<r^4-r\), and
\[
M<(r^4-r+1)^2-2<r^8-r^5.
\]
The last comparison follows from the exact identity
\[
r^8-r^5-\bigl((r^4-r+1)^2-2\bigr)
=(r-2)(r^4-r)+1>0.
\]
Since \(r^8=m^3\) and \(r^5=m^{15/8}\), this proves (RC3).
\(\square\)

**A further smooth consequence of the integer seam.** The sharper
first inequality in (RC1) also gives
\[
t<m^{3/2}-\frac43m^{3/8}.
\]
Indeed \(g(z)=z^{4/3}-\frac43z^{1/3}\) is positive for \(z\ge3\),
is increasing there, and
\[
g(z)^3-[z(z-2)]^2=\frac4{27}z(9z-16)>0.
\]
This analytic reformulation is a written consequence; the proof of
(RC3) above does not depend on differentiating \(g\).

**Scope and finite controls.** A threshold cycle in the region
\(m^3-m^{15/8}\le M<m^3\), \(m\ge7\), must therefore have at least
one wrong-parity state. This does not exclude the lower part of the
cubic band or the regime \(M\ge m^3\), and it does not increase the
period bound \(780239\).
The integer ceiling at hypothetical minimum \(9\) improves the earlier
minimum-only extrema ceiling from \(674\) to \(482\); at minimum
\(6569\), it improves \(283462537742\) to \(283388004962\).
These are conditional arithmetic evaluations, not assertions that
cycles with those minima exist.

The threshold cycle
\[
(9,27,140,11,36,216,14,52,374,19,82)
\]
has \(Y=\{9,11,14,19\}\), \(t=19\), \(z=11\), and \(w=9\).
It satisfies \(19^3=6859\le9799=[11(11-2)]^2-2\), yet has
wrong parities, including the even retained base \(14\).
Thus the new necessary extrema conditions are not a complete guard test.
Appendix E records the exact carry formulas and the limitations of
several proposed summaries of the missing guards.


### 3.12. Successive return gaps and larger height exclusions

The ordered return section supplies further restrictions because
selected neighboring states remain distinct after a common return word.
The floor errors must be bounded before this discreteness can be used.
Successive left inductions preserve one boundary pair; only genuine
right inductions transport it.

Retain the notation \(m,M,Y,t,w,z\) of Theorem 3.39, and use
chronological words
\[
A=OOE,\quad B=OE,\quad C=A^2B,\quad D=AC^2,\quad W=D^3C.
\]
Write
\[
\gamma=\frac{243}{256},\qquad
\delta=\frac{531441}{524288},\qquad
\rho=\delta^3\gamma=\frac{3^{41}}{2^{65}},
\qquad \sigma=\frac{13}{128}+1-\rho.
\]
Here \(7/64<\sigma<1/8\).

**Theorem 3.40 (successive return height restrictions).** Let an
actual Juggler cycle have minimum \(m\) and maximum \(M<m^3\).
Then the following statements hold.

(i) If \(m\ge2^{24}\), two genuine transfers of the original boundary
through \(C\) give
\[
z-w\ge6,\qquad
z-w>\frac{26240}{59049}m^{13/128},
\qquad
M<m^3-\frac{1}{2}m^{253/128}.
\tag{SR1}
\]

(ii) If \(m\ge2^{128}\), a subsequent genuine transfer through \(W\)
gives
\[
z-w\ge8,\qquad z-w>\frac25m^\sigma,
\qquad
M<m^3-\frac{1}{2}m^{381/128-\rho}.
\tag{SR2}
\]
In particular,
\[
M<m^3-\frac{1}{2}m^{127/64}.
\tag{SR3}
\]
The exponent \(381/128-\rho\) is approximately \(1.98795995227\).
The clean bounds (SR1) and (SR3) have the respective integer forms
\[
m^{253}<\bigl[2(m^3-M)\bigr]^{128},\qquad
m^{127}<\bigl[2(m^3-M)\bigr]^{64}.
\]
The natural-number gaps are positive under \(M<m^3\).

*Proof.* The complete return on the sorted set
\(Y=\{y_0<\cdots<y_{a+b-1}\}\) has lower word \(A\), upper word \(B\),
and rank rotation \(i\mapsto i+b\pmod{a+b}\).
Appendix F proves the forced batch identities
\[
a=2b+r,\quad b=2r+s,\quad 0<s<r
\]
on the first domain, and additionally
\[
r=3s+u,\qquad 0<u<s
\]
on the second. They place the successive boundary pairs at
\[
(y_{b-1},y_b),\quad
(y_{b-r-1},y_{b-r}),\quad
(y_{s-1},y_s),\quad
(y_{s-u-1},y_{s-u}).
\]
The first two changes apply \(C\); the third applies \(W\).
All displayed indices exist on their respective domains, and all
traces belong to the same actual cycle.

The prescribed maps have absolute losses below \(9/8\) and \(6/5\),
respectively, at the stated cutoffs. Their paired estimates strictly
contract every integer gap at least two. Since each displayed pair
has distinct odd endpoints, each genuine transfer decreases the
positive even gap by at least two. The quantitative versions give
the gap bounds in (SR1)--(SR2). Appendix F.4 combines them with the
original exact cells
\[
t^3+2\le[w(w+2)]^2,\qquad M+2\le(t+1)^2,\qquad z^8\le m^9,
\]
and proves the displayed height restrictions. \(\square\)

These domains are materially different. The first cutoff is
\(2^{24}=16777216\); the second is approximately \(3.4\cdot10^{38}\).
The stronger exponent in (ii) does not replace the result in (i)
below the larger cutoff. Both give wrong-parity obstructions for
threshold cycles only in their stated excluded height strips.
The remaining cubic region and every taller cycle are unexcluded,
and the numerical period floor remains \(780239\).

### 3.13. The terminal mixed passage

The last two-point return must also be accounted for before gap
contractions could imply no-cycle.

**Proposition 3.41 (terminal prefix and suffix).** At every Euclidean
return stage with words \(U,V\), there are chronological words \(P,Q\)
such that
\[
UV=P\,OE\,Q,\qquad VU=P\,EO\,Q.
\tag{SR4}
\]
Initially \(P=O,\ Q=OE\). A left substitution changes \(P\) to \(UP\);
a right substitution changes \(Q\) to \(QV\).

At a primitive actual cubic-band cycle's terminal two-base section
\(\{m,v\}\), the common prefix sends this adjacent pair to the
largest odd and smallest even source pair \((h,s)\). The mixed
words \(OE,EO\) send it to \((t,q)=(E(M),O(m))\), and \(Q\) sends
\((t,q)\) back to \((m,v)\). For \(m\ge3\),
\[
0<q-t<s-h.
\tag{SR5}
\]

*Proof.* The concatenation identities follow by induction from
\(U=OOE,\ V=OE\). Both full return traces follow their actual guards;
their common prefix preserves adjacency until the labels differ.
It therefore ends at the unique adjacent pair across the odd/even
threshold. The middle and final images follow from
\(O(h)=M,\ E(s)=m,\ U(m)=v,\ V(v)=m\).
Moreover,
\[
h<m^2,\quad s\ge m^2+1,\quad
t=\lfloor h^{3/4}\rfloor,\quad
q=\lfloor(m^2)^{3/4}\rfloor.
\]
Since the derivative of \(x^{3/4}\) is below one for \(x\ge h\ge3\),
\[
q-t<(m^2)^{3/4}-h^{3/4}+1<m^2-h+1\le s-h.
\]
The cycle order gives \(t<q\). Appendix F.5 records the complete
word and gap accounting. \(\square\)

The mixed contraction supplies no bound on amplification through
\(P\), and current estimates control only the certified factors
of \(Q\). Their exact ideal exponent product is
\[
p_P\frac34p_Q=\frac{3^o}{2^L}>1.
\]
An additional estimate comparing the two parts is required.
Appendix F.6 also shows why the present one-sided error certificate
cannot stay uniform at a fixed minimum as the contracting word
exponent approaches one. These observations leave the global
no-cycle question open.


## 4. Cycle finance

A cycle itinerary is formally expanding (Theorem 3.2), yet the trajectory
returns exactly. The multiplicative surplus \(3^o-2^L\) must be
financed by the floor remainders, which are relatively \(O(1/x)\)
in logarithms. The resulting bound on the cycle minimum excludes
every period that is not admissible for the inequality, once a
uniform logarithmic floor-error bound is available above a
verified descent floor.

The identity is unrolled along a circular word. After rotation
to a cycle minimum that itinerary is a necklace of odd-run
excursions. The geometry below records that itinerary. It
introduces no new theorem: every named constraint is Theorem 3.2,
Lemma 3.4, Lemma 3.21b, or the last-even one-step preimage.

### The excursion necklace

Write \(n\) for a cycle minimum and
\[
w=O^{a_1}EO^{a_2}E\cdots O^{a_e}E
\]
for a minimum-based orientation (Lemma 3.21b), so \(a_1\ge 2\),
\(\sum_i a_i=o\), and \(e=L-o\). Let \(v_i\) be the landing
state at the start of block \(i+1\), and \(p_i\) the even state
just before its final \(E\). If \(a_{i+1}>0\), then \(v_i\)
is odd and the block rises to \(p_i\). If \(a_{i+1}=0\), then
\(v_i=p_i\) is even; it is neither an odd valley nor a new peak.
Thus the valley/peak terminology below applies to actual transitions
between maximal odd and even runs. In general the block-boundary
identities are
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
the itinerary. *Dynamical entry* is the last even step into \(n\).
The second is a genuine boundary condition; the first is a
choice of origin.

#### Cycle minimum and the forced lift

The minimum is odd, so the itinerary cannot begin with \(E\) or
\(OE\), and it cannot end with an odd letter (Theorem 3.2).
The first two letters are therefore \(OO\):
\[
n\overset{O}{\longrightarrow}y\overset{O}{\longrightarrow}z.
\]
For \(n\ge 5\) one has \(z=J^2(n)\ge(n+1)^2\) (Lemma 3.4(i)).
In particular \(OOE\) cannot be a cycle itinerary
(`no_cycle_itinerary_ooe`). On a cycle minimum the first even
residual overshoots the entry one-step preimage: the first peak satisfies
\(p_0\ge(n+1)^2\). That is the opposite of the last-peak
condition below. Even \(J^2(n)\) may continue with \(E\); odd
\(J^2(n)\) continues with \(O\). Either way the minimum-based
prefix is still \(OO\).

#### Excursions, valleys, and peaks

An ordinary excursion is one block \(O^{a}E\). In the itinerary
semantics that itinerary is `oddEvenBlock a 1`. Write
\[
\mu(a)=\frac{3^a}{2^{a+1}}
\]
for the ideal (floor-free) exponent of the block. The block is
formally expanding if and only if \(\mu(a)>1\), equivalently
\(2^{a+1}<3^a\). Thus \(OE\) contracts (\(\mu(1)=3/4\)) and
\(OOE\) expands (\(\mu(2)=9/8\)). This is a reparameterization
of the itinerary envelope of Theorem 2.2, not a transition law on
pairs \((a_i,a_{i+1})\). Lemma 3.4(v) forbids \(O^aE\) as a
*cycle itinerary* for \(a\ge 3\); it does not forbid an internal
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

#### Closure and the entry one-step preimage

The valley sequence is circular. The last letter is \(E\), so
the last peak occupies the last-even one-step preimage of Lemma 3.4(iv):
\[
n^2\le p_{e-1}<(n+1)^2.
\]
The minimum is odd, so \(p_{e-1}\neq n^2\)
(`cycle_last_even_ne_odd_sq`) and \(p_{e-1}\) is even. Thus
\[
n^2+1\le p_{e-1}<(n+1)^2,\qquad p_{e-1}\text{ even}.
\]
An ordinary excursion needs only \(v_i\ge n\). The last
excursion must hit this one-step preimage and land on \(n\):
\[
v_{e-1}
\overset{O^{a_e}}{\longrightarrow}
p_{e-1}
\overset{E}{\longrightarrow}
n.
\]
The first peak overshoots the same one-step preimage; the last peak lands
in it. Those are different even states.

Once the trajectory returns to \(n\), the prefix \(OO\) is forced
again. A genuine cycle is a closed necklace of excursions
whose first block starts \(OO\), whose last peak lies in the
entry one-step preimage, and whose entire trajectory stays at least \(n\). The
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
+\text{entry one-step preimage}
\;\Rightarrow\;\bot.
\]
That is a formulation of the remaining cycle problem, not a
theorem. A genuine lower bound on the number of odd runs would
feed Theorem 4.7; none is proved here.

Throughout this section write \(L=|w|\) and \(o=\#O(w)\) for a
cycle itinerary \(w\) based at a cycle minimum \(n\ge 2\). Natural
logarithms are written \(\log\) in this section and \(\ln\) in
Section 5; both denote the natural logarithm. The unique one-step fibres of
Section 3 give, for every state \(x\ge 1\) with image
\(y=J(x)\),
\[
y^2\le x^h<(y+1)^2,
\qquad
h=\begin{cases}1,&x\text{ even},\\3,&x\text{ odd}.\end{cases}
\]

**Lemma 4.1 (dyadic one-step-preimage logarithm).**
If \(z,y\ge 1\) and \(z<(y+1)^2\), then
\(\log z\le 2\log y+2/y\).

*Proof.* The hypothesis gives \(\log z\le 2\log(y+1)\). The
inequality \(\log(1+u)\le u\) for \(u>0\) yields
\(\log(y+1)=\log y+\log(1+1/y)\le\log y+1/y\). \(\square\)

**Lemma 4.2 (one-step bounds).**
Let \(x\ge 2\) and \(y=J(x)\). If \(x\) is even, then
\(\log x\le 2\log y+2/y\). If \(x\) is odd, then
\(3\log x\le 2\log y+2/y\).

*Proof.* The even one-step preimage is \(y^2\le x<(y+1)^2\). The one-step-preimage logarithm
lemma on \(z=x\) is the first claim. The odd one-step preimage is
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
Let \(w\) be a cycle itinerary of length \(L\) with \(o\) odd letters,
based at a cycle minimum \(n\ge 2\). Then
\[
n\log n\cdot(3^o-2^L)\le L\cdot 3^o.
\]

*Proof.* Apply Lemma 4.3 at \(k=L\). Periodicity gives
\(x_L=n\) and \(o_L=o\), so
\[
3^o\log n\le 2^L\log n+\frac{L\cdot 3^o}{n}.
\]
The itinerary is formally expanding, so \(3^o>2^L\). Rearranging and
multiplying by \(n\) is the claim. \(\square\)

\vspace{0.4em}

This is the conceptual centre of the note. Exact one-step preimages give a
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
   \(\theta=1-2^L/3^o\). It charges every one-step-preimage defect at the
   cycle minimum. Lean: `cycleMin_finance`.

2. *Corollary 4.4c* (below) is the same one-step-preimage-log unroll with
   remainders kept as \(1/x_{i+1}\). It is the strongest proved
   form of those defects. Lean: `cycleMin_finance_inv_sum`.

3. *Corollary 4.5* is the convenient length-only statewise
   bound: a verified descent floor \(N_0\) plus the three-class
   charge of the defect sum produces a per-length threshold
   \(n_{\max}(L)\) and excludes every \(L\) with
   \(n_{\max}(L)\le N_0\). The charge is
   \[
   \sum_i \frac1{x_i\log x_i}\ \le\
   \frac{e}{n\log n}+\frac{o-e}{t\log t}+\frac{e}{2n^{2}\log n},
   \qquad t=\lfloor n^{3/2}\rfloor ,
   \]
   charging valleys at \(n\), internal odds at \(t\), and evens
   at \(n^{2}\). It is called the *parity* charge in the tables
   and in places below, which is historical and slightly
   misleading: it is **not** a two-class split of odds against
   evens, and the \(t\)-scale middle term is exactly what makes
   it sharper than one. Lean: `cycleMin_threeTerm` from
   `CycleMin` alone, with no hypothesis about \(\mathtt{EE}\).

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
stricter length-only three-class charge of the same identity.

**Corollary 4.4c (inv-sum).**
Let \(w\) be a cycle itinerary of length \(L\) with \(o\) odd letters,
based at a cycle minimum \(n\ge 2\). Write \(x_i=J^i(n)\). Then
\[
(3^o-2^L)\log n\le 3^o\sum_{i=1}^{L}\frac1{x_i},
\]
equivalently \(\theta\le\bigl(\sum_i 1/x_i\bigr)/\log n\).

*Proof.* The same induction as Lemma 4.3, keeping each one-step preimage
defect as \(2^{k+1}/x_{k+1}\) instead of replacing it by
\(3^{o_{k+1}}/n\). At \(k=L\) one has \(x_L=n\). Lean:
`cycleMin_log_envelope_inv`, `cycleMin_finance_inv_sum`.
\(\square\)

The computational table of Theorem 4.6 uses a weaker per-step
bound, valid on every cycle because every start below \(12\)
reaches \(1\) (so every cycle state is at least \(12\)). For a
state \(x\) with image \(y=J(x)\ge 12\), the relative defect
\(\delta=(x^h-y^2)/x^h\) satisfies \(\delta\le 2/y\le 1/6\).
Writing \(\varepsilon=-\tfrac12\log(1-\delta)\) and using
\(-\log(1-\delta)\le\tfrac65\delta\) on \([0,1/6]\) gives
\(\varepsilon\le(6/5)/y\). Unrolling
\(t_{i+1}=(h_i/2)\,t_i-\varepsilon_i\) around the cycle then yields
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
state is at least \(N_0+1\). The length-only three-class charge
of the certified relative-defect identity then forces the minimum
to satisfy the displayed inequality, hence \(n\le n_{\max}(L)\).
This is the convenient statewise bound in the hierarchy after
Theorem 4.4; it is not a replacement for that theorem.
\(\square\)

Record values of the three-class \(n_{\max}\) include
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
Let \(w\) be a cycle itinerary of length \(L\) with \(o=o_{\min}(L)\)
odd letters and \(e=L-o\) even letters, based at a cycle
minimum \(n\ge 12\). Assume further that \(w\) is primitive and
that \(w\) contains no \(\mathtt{EE}\). Write \(v\) for the least
odd integer with
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
strictly smaller than the three-class sum of Corollary 4.5 whenever
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
primitivity, which is why that hypothesis is stated: a cycle word
concatenated with itself is again based at a cycle minimum, and the
display charges only one valley at \(n\). The no-\(\mathtt{EE}\)
hypothesis enters at the split of the \(e\) valleys into cheap and
expensive. Counting on indices rather than on blocks, an odd letter is a
*valley* when its cyclic predecessor is even; the valleys are then in
bijection with the maximal even runs, and the counting lemma gives
\(\#\text{cheap}\le o-\#\text{blocks}\). Only when no
\(\mathtt{EE}\) occurs do the blocks number \(e\), giving the
\(\#\text{cheap}\le o-e\) the packing uses; the subsection *The packing hypothesis and its price* below shows
the hypothesis is not removable. The displayed sum charges one cheap valley at
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
particular, if a nontrivial cycle has period \(L\le 10^5\) and its
itinerary satisfies the hypotheses of Theorem 4.7, then
\(L\in\mathcal E_{\mathrm{run}}\).

The two halves of that progression do not carry the same weight. The
\(24\) lengths with \(k\ge 18\), from \(75319\) up, are excluded
with no hypothesis about \(\mathtt{EE}\) at all: at most half the odd
letters can be cheap valleys whatever the word does
(`two_mul_cheap_le_odd`), and charging \(\lfloor o/2\rfloor\) of them
at \(n+2\) still excludes exactly those lengths. The \(18\) with \(k\le 17\), from \(56347\) to \(74265\),
are excluded only under the no-\(\mathtt{EE}\) hypothesis, and the
subsection below exhibits admissible words that defeat each. Dropping that hypothesis
therefore leaves \(117\) lengths in place of \(99\). It does not move
the cutoff, which is \(25781\) either way and comes from Corollary 4.5.

*Proof.* The \(141\) lengths of Theorem 4.6(B) are tested at
\(n=10^6+1\) against the packed right-hand side. The comparison
is certified on each length: no entry is left uncertain. The
\(42\) excluded lengths are exactly the arithmetic progression
named in the statement. The complementary set in that range is
\(\mathcal E_{\mathrm{run}}\). Checksums are Appendix B.
The period cutoff remains \(25781\).
\(\square\)

### The packing hypothesis and its price

Theorem 4.7 assumes the itinerary contains no \(\mathtt{EE}\). The
assumption is not cosmetic and it is not removable, and since \(18\) of
Theorem 4.8's \(42\) exclusions rest on it, it is worth saying exactly
what it buys and what it costs.

**Why the packing needs it.** The extremality argument counts *blocks*
\(\mathtt{O}^{a}\mathtt{E}\). Counting instead on indices, where nothing
is assumed, call an odd letter a *valley* when its cyclic predecessor is
even and an *internal* when that predecessor is odd. The valleys are then
in bijection with the maximal even runs. If the itinerary carries \(m\)
cyclic \(\mathtt{EE}\) adjacencies, the \(e\) even letters form \(e-m\)
maximal runs, so

\[
\#\text{valleys}=e-m,\qquad
\#\text{internals}=o-e+m,\qquad
\#\text{cheap}\le\min(o-e+m,\ e-m),
\]

with the expensive valleys making up the rest. The bound
\(\#\text{cheap}\le o-e\) that Theorem 4.7 uses is the case \(m=0\); in
general the counting lemma gives only
\(\#\text{cheap}\le o-\#\text{blocks}\), and with \(\mathtt{EE}\) present
the even letters outnumber the blocks. The paper's phrasing --- \(o-e\)
copies of \(\mathtt{OOE}\) and \(2e-o\) circuits of \(\mathtt{OE}\) ---
already presupposes one even letter per block.

**What it is worth.** At every one of the \(42\) lengths, at
\(n=10^6+1\), the ratio of the Corollary 4.5 charge to the packed one is
\(1.4048\), uniformly; to leading order it is \(e/(o-e)\), the packing
moving the \(n\)-scale charge from \(e\) valleys to \(o-e\). That
constant is the whole budget of the refinement, and each of the \(42\)
dies with margin \(\theta/\text{packed}\in[1.0033,1.3535]\) --- inside
that budget of necessity, since each survives the unpacked charge.

**The second cap, and the split.** The quantity \(\#\text{cheap}\) is
bounded both by \(o-e+m\) and by the valley count \(e-m\) it is part of.
The two cross at \(m=e-o/2\), where both equal \(o/2\); past the crossing
the valleys themselves run out and the majorant falls again. So
\(\mathtt{EE}\) cannot inflate the \(n\)-scale charge beyond
\((o/2)/(o-e)=1.2047\), however much of it a word carries. Since
\(\theta/\text{packed}\) rises monotonically along the progression and
crosses that ceiling between \(L=74265\) and \(L=75319\), the \(42\)
split cleanly: the \(24\) lengths from \(75319\) up are excluded whatever
the itinerary, and the \(18\) from \(56347\) to \(74265\) are not.

**The \(24\) are a theorem, not an observation.** The split above is
read off a scan over \(m\), but the surviving half needs no scan. Call
an odd letter a *cheap valley* when its cyclic predecessor is even and its
cyclic successor is odd --- the start of an odd run of length at least
two. A cheap valley is a valley; its successor is an odd letter with an
odd predecessor, hence an internal; and the successor map is injective on
the window. So the cheap valleys sit inside the valleys and inject into
the internals, and those two classes partition the odd letters
(`valley_add_internal`), giving

\[
2\cdot\#\text{cheap}\ \le\ o
\]

with no reference to \(\mathtt{EE}\) --- Lean `two_mul_cheap_le_odd`,
from `cheap_le_valley` and `cheap_le_internal`. Feeding
\(\lfloor o/2\rfloor\) to `sixTerm_bound_packed` in place of the
packing's \(o-e\) therefore yields a comparison carrying none of
Theorem 4.7's hypotheses, and at \(N_0=10^6\) that comparison excludes
exactly the \(24\). The bound is of course weaker than the packed one
--- it charges more valleys at the \(n+2\) scale --- and it remains
below the charge of Corollary 4.5, as it must.

**The \(18\) are genuinely lost without the hypothesis.** For each there
is a word satisfying every restriction this paper proves for a
cycle-minimum itinerary --- \(3^{a_j}\ge2^j\) at every prefix, the
per-run cap of Theorem 3.31, \(o=o_{\min}(L)\), and the
\(\mathtt{OO}\ldots\mathtt{E}\) shape --- and carrying more
\(\mathtt{EE}\) than the comparison can absorb. The witness is the Beatty
interleaving of \(\mathtt{OOE}\) and \(\mathtt{OE}\) blocks over \(e-k\)
even letters followed by a tail of \(k\) even letters, with \(k\) between
\(51\) and \(3926\). Its odd runs have length at most two, which is the
packing's own extremal shape, so no claim about run structure is
violated; what fails is only the correspondence between blocks and even
letters. Granting the extremality of the run packing in full therefore
does not restore the counting, and no sharpening of the run analysis
will: what would be needed is a restriction sensitive to the floors,
whereas every restriction used above is exponent bookkeeping, exact for
the multipliers and blind to the floors.

*Remark (why the run cap cannot help).* The least admissible odd count is
defined by \(3^{o}>2^{L}\), that is \(o\log(3/2)>e\log 2\), and the
per-run cap of Theorem 3.31, which Theorem 3.29's run--suffix law
supplies, is
\(\lfloor(e-i)\log 2/\log(3/2)\rfloor\) with \(i\) the number of even
letters already spent. The two use the same constant, so at every one of
the \(42\) lengths

\[
\Big\lfloor e\cdot\frac{\log 2}{\log(3/2)}\Big\rfloor=o_{\min}(L)-1 .
\]

The single-run word \(\mathtt{O}^{o}\mathtt{E}^{e}\) is therefore
forbidden by exactly one letter, and two blocks are already admissible
--- carrying \(e-2\) adjacencies. The cap and the odd count are the same
inequality read twice, which is why the cap is never far from binding and
never actually binds.

**What this does not say.** Theorem 4.7 is true as stated, with its
hypotheses, and Theorem 4.8's \(42\) exclusions are correct under them.
A defeated exclusion does not produce a cycle of that length; it means
the comparison does not rule one out. And the count \(m\) is treated here
as free, whereas a realised itinerary's \(\mathtt{EE}\) count is fixed by
the dynamics --- the witnesses are admissible for the restrictions this
paper proves, not exhibited as cycles.

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

### The gap transfer and the short-cycle reduction

Everything above turns a verified descent floor into per-length
exclusions. At the five upper-convergent denominators
\(19,84,1054,50508,176251\), the computed ratio
\(n_{\max}(q_k)\log n_{\max}(q_k)/(q_kq_{k+1})\)
lies in \([0.41,0.53]\). This finite comparison motivates the
discussion in Section 6.2; it is not by itself a global scaling theorem.

This subsection records the one statement
of the note that needs no floor. It transfers a lower bound on
the linear form
\[
\Lambda=\Lambda(L,o)=o\log 3-L\log 2=-\log\!\Bigl(1-\theta\Bigr),
\qquad \theta=1-\frac{2^L}{3^o},
\]
into a bound on the cycle minimum. The only new input is
\(\log\frac1{1-\theta}\le\frac{\theta}{1-\theta}\).

**Theorem 4.10 (gap transfer).**
Let \(w\) be a cycle itinerary of length \(L\) with \(o\) odd
letters, based at a cycle minimum \(n\ge 2\). Then
\[
n\log n\cdot\min(\Lambda,1)\le 2L.
\]

*Proof.* Write \(A=3^o\), \(B=2^L\), \(P=n\log n\ge 0\). Theorem
4.4 reads \(P(A-B)\le LA\). If \(A\le B\) then \(\Lambda\le 0\)
and the left side is nonpositive. If \(A\ge 2B\), then
\(A-B\ge A/2\), so \(PA/2\le LA\), hence
\(P\min(\Lambda,1)\le P\le 2L\).
If \(B<A<2B\), then
\(\Lambda=\log(A/B)\le A/B-1=(A-B)/B\), so
\(P\Lambda\le P(A-B)/B\le LA/B\le 2L\). \(\square\)

The Lean form is `cycleMin_gap_transfer`; the abstract corollary
"\(\varepsilon\le\min(\Lambda,1)\) implies
\(n\log n\cdot\varepsilon\le 2L\)" is `cycleMin_length_of_gap`.

**Corollary 4.11 (short cycles are excluded).**
Rhin's effective estimate [15, Proposition, p. 160, (7)] applies
to the absolute value of an integer linear form in \(1,\log2,\log3\).
For a nontrivial cycle, \(L\ge11\), \(0<o<L\), and
\(\Lambda=o\log3-L\log2>0\). Substituting
\((u_0,u_1,u_2)=(0,-L,o)\) gives height \(H=L\) and
\[
\Lambda\ge L^{-13.3}>e^{-6.1256}L^{-13.3}.
\]
We retain the weaker constant to state the following consequence:
\[
n\log n\le2e^{6.1256}L^{14.3}<915L^{14.3},
\qquad
L>\Bigl(\frac{n\log n}{915}\Bigr)^{1/14.3}.
\]
In particular, a cycle with \(L^{14.3}\le n\log n/915\) is
excluded without a descent-floor input.

*Proof.* Corollary 3.23 supplies \(L\ge11\), so Rhin's height
condition is satisfied. Set \(\varepsilon=e^{-6.1256}L^{-13.3}\).
Then \(0<\varepsilon\le\min(\Lambda,1)\), and Theorem 4.10
gives the first displayed upper bound. The inequality
\(2e^{6.1256}<915\) completes the proof. This use of Rhin is an
external theorem, not a Lean proof of the transcendence estimate.
\(\square\)

**Remark (what the reduction does and does not do).**
Corollary 4.11 is a reduction of the no-cycle problem, not a
kill. It says that the only cycles left to exclude are the *long*
ones, \(L>(n\log n/915)^{1/14.3}\); every shorter cycle is
excluded by transcendence plus finance alone. At the certified
floors of Section 5 this is toothless — at \(N_0=3.5\cdot 10^8\)
it forces only \(L\ge 4\), while the finance table forces
\(L\ge 780239\) — which is the floor-level statement that a
Baker-type transfer cannot compete with the exact gap. The value
of the corollary is that it is floor-free and identifies the
frontier exactly: the finance survivors of Theorems 4.6 and 5.9
have \(L\approx n^{0.59}\) --- the measured exponent
\(\log L/\log n_{\max}(L)\) is \(0.595\) at \(L=25781\), \(0.573\) at
\(50508\), \(0.582\) at \(176251\) and \(0.611\) at \(780239\) --- far
inside the long regime, and no
refinement of the defect *upper* bound can move them into the
short one, because along the convergents the required minimum
\(n_{\max}(q_k)\) grows quadratically in \(L\). Excluding long
cycles is a statement about the parity word of a specific orbit
at depth \(L\), which no estimate in this note or in the
companion discrepancy manuscript [16] controls. The problem "no
nontrivial Juggler cycle" is therefore exactly the problem "no
long Juggler cycle," and it remains open.

## 5. The laboratory instance and the walk-charge envelope

Everything in Sections 2--4 is floor-generic: Corollary 4.5
accepts any verified descent floor. This section first records
a second, laboratory-certified instance of the same
architecture, then replaces the length-only charge by a coupled
exponent-walk charge. The extremal walk is identified exactly
as a rotation itinerary, and a Denjoy--Koksma bound over certified
Ostrowski blocks produces an envelope valid for *every* length
in an explicit window — no per-length census and no dynamic
program is needed on that window. The kill table at the
laboratory floor then yields the period bound \(176251\), and
the second certified floor raises it to \(478245\)
(Corollary 5.10) and the third to \(780239\)
(Corollary 5.11). Throughout, survivors are finance-survivors
in the sense of Section 1.

### 5.1 The laboratory floor

**Proposition 5.1 (laboratory descent floor; certified
computational input).**
Every integer \(2\le n\le 26254995\) reaches \(1\). Precisely:
an exact-integer first-passage run records, for each such
\(n\), a finite realized itinerary with image strictly below the
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
\(L=50508\) with \(n_{\max}(50508)=162848324\); \(19\) parity
survivors remain through \(L=2\cdot 10^5\) (run packing leaves
\(11\) at the same cutoff). This is the one row in the paper where
the exact \(n_{\max}\) of Section 4 and the value in the committed
table differ, and the reason is worth recording: the crossing at
\(L=50508\) is sharp to a relative \(2.7\cdot10^{-10}\), which is
*below* the \(10^{-9}\) relative guard the table's generator adds to
the right-hand side. That guard is deliberate and conservative --- it
can only make \(n_{\max}\) larger, hence can only refuse to exclude a
length --- so the table prints \(162848325\). Both values give the
same exclusion here, since the floor \(162849448\) exceeds either.

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
nonnegative exponent walks of length \(L\),
evaluated at the *reduced base* \(n'=n\,e^{-D}\). No free
parameter remains; the walk value feeds the \(6/5\) unroll of
Theorem 4.4 exactly as the parity charge did. At the laboratory
floor, for the original sub-window \(L<301994\), one has
\(D\le4.6\cdot10^{-3}\) and \(\ln n'\ge17.07\).
The extended window requires the bounds in Theorem 5.8.

This consequence is itself Lean end to end
(`WalkChargeMax.lean`): writing the charge through the rational
weight, \(g=1/(e^{W\nu}W\nu)\) with \(W=2^{u_k}=3^{a_k}/2^k\) and
\(\nu=\ln n'\), exponentiating the transport inequality gives
\(\sum_k 1/(x_k\ln x_k)\le\sum_k g(w_k)\)
(`cycleMin_defect_le_charge`), and the charge of the realized
word is dominated by the hug charge of the same length
(`cycleMin_defect_le_hug_charge`, using Theorem 5.4 below), all
under the recorded hypothesis \(\nu>0\).

### 5.3 The adversary is the hug itinerary

**Theorem 5.4 (hug exchange).**
Among all nonnegative exponent walks of length \(L\), the
*hug itinerary* — take \(E\) at every step where \(u\ge 1\), else
\(O\) — is prefix-minimal: writing \(a_k\) for the odd count of
a length-\(k\) prefix,
\[
a_k^{\mathrm{hug}}\le a_k
\qquad\text{for every admissible walk and every }k,
\]
equivalently \(u_k^{\mathrm{hug}}\le u_k\). Consequently the
hug itinerary maximises the walk charge: since \(g\) is strictly
decreasing in \(u\),
\[
g\bigl(u_k^{\mathrm{hug}}\bigr)\ge g(u_k)
\quad\text{for every }k,
\qquad\text{hence}\qquad
\sum_{k}g(u_k)\ \le\ \sum_{k}g\bigl(u_k^{\mathrm{hug}}\bigr).
\]

*Proof.* At the first disagreement with any other admissible
itinerary, the hug itinerary holds \(E\) where the other holds \(O\),
because hug takes \(O\) only when \(E\) is illegal and the two
words share the same prefix state. The odd-count gap
\(\delta_k=a_k(\text{other})-a_k(\text{hug})\) is a path with
steps in \(\{-1,0,+1\}\) that cannot go negative, since
\(\delta=0\) restores the same state. This is the displayed
prefix-minimality \(a_k^{\mathrm{hug}}\le a_k\); since
\(u_k=(1+\mu)a_k-k\) with the same \(k\), it transfers verbatim
to \(u_k^{\mathrm{hug}}\le u_k\). The greedy word uses exactly
\(o_{\min}(L)\) odd letters (Lemma 5.6). It therefore belongs to
the class with that prescribed odd count, while still dominating every
admissible word with a larger odd count.

Applying the strict antitonicity of \(g\) termwise and summing
over \(k\) is the charge comparison. The prefix-minimality core
is Lean: `hugOdds_le_of_admissible`. \(\square\)

*Remark (uniqueness).* The hug itinerary is in fact the *unique*
prefix-minimal admissible path in the class \((L,o_{\min}(L))\), so it
uniquely maximises the charge; at the first disagreement the
competitor already carries a strictly larger prefix odd count,
and strict monotonicity of \(g\) makes the total comparison
strict. The profile equality for every charged prefix \(k<L\)
is also formalized by `hug_charge_unique`; the prescribed total odd
count determines the last letter. Uniqueness is not needed for the
exclusion criterion.

The analytic half is also Lean, in a strengthened form
(`WalkChargeMax.lean`): the charge is antitone in the rational
weight (`stateCharge_antitone`, elementary \(\exp\)
monotonicity — no charge integral), so the exact hug itinerary
maximises the total charge over *all* admissible exponent
walks, not just a fixed \((L,o)\) class
(`hug_charge_maximal`). The equality case for the charged profile
is formalized by `hug_charge_unique`, using `stateCharge_strictAnti`
and `stateCharge_inj`.

The statement is about the \(u\ge 0\) relaxation, not about
realized cycle itineraries. Word-order (Christoffel) prefix-dominance
is *false* for this family — the greedy word \(OOEO\) beats
\(OOOE\) at \((L,o)=(4,3)\) — so the exchange argument above,
not a dominance order, is the correct mechanism.

Realized itineraries do, however, dominate the hug itinerary at the level
of odd counts: on any minimum-based cycle itinerary, every length-\(k\)
prefix carries at least \(o_{\min}(k)\) odd letters. This is
Lean end to end (`cycleMin_prefix_odds_ge_hug`,
`cycleMin_odds_ge_hug`), composing the formalized cycle prefix
envelope \(2^k\le 3^{a_k}\) (`cycleMin_prefix_pow_le`) with the
hug minimality `hugOdds_least`. It is exactly the sense in which
the hug itinerary is the cheapest adversary any hypothetical cycle
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
gap form `rotationAverage_gap`). Lean's
`hugCharge_sub_circleMean_le` identifies the limiting hug average with
the circle integral `circleMean n'`; the elementary change of variables
equating that integral with the displayed \(C_*(n')\) remains prose.
The observable has one wrap discontinuity, so bare unique ergodicity —
uniform Birkhoff convergence for *continuous* observables — is not
invoked directly. But the observable is monotone with a single jump,
hence of bounded variation, and for such an observable §5.5's
Denjoy--Koksma bound `denjoy_koksma_blocks` already gives
\(|C_L-\mathrm{circleMean}|\le s(L)\,\mathrm{Var}(F)/L\) at every \(L\).
Unique ergodicity is not needed;
that Mathlib has no `UniquelyErgodic` costs this paper nothing.

This is the infinite-itinerary average, not a finite-\(L\)
inequality: on the certified survey the finite leftover charge
exceeds \(C_*\) by up to \(1.57\cdot 10^{-5}\), so
\(C_L\le C_*\) is false. The next two subsections quantify the
finite-\(L\) error.

### 5.4 Itinerary identity

Write \(C_L\) for the charge-per-letter of the budgeted hug
word at \((L,o_{\min}(L))\).

**Lemma 5.6 (itinerary identity).**
For every \(L\), the budgeted hug itinerary at \((L,o_{\min}(L))\)
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
`hugOdds_least` (`WalkChargeItineraries.lean`).

The identification with the rotation is Lean too, and it is a floor
identity rather than analysis (`HugRotation.lean`). Minimality says
`hugOdds` is the least \(a\) with \(2^k\le3^a\), and a least element of
that shape is a ceiling: `hugOdds_eq_ceil` reads it as
\(\lceil k\log2/\log3\rceil\), hence `hugOdds_eq_sub_floor` as
\(k-\lfloor k\theta\rfloor\) and `hugEvens_eq_floor` as
\(\lfloor k\theta\rfloor\). The letter rule is then the wrap
(`hugLetter_iff_floor_step`: even exactly when
\(\lfloor(k+1)\theta\rfloor=\lfloor k\theta\rfloor+1\)), the exponent
walk is the rotation orbit (`hugWalk_eq_fract`:
\(u_k=\log_2 3\cdot\{k\theta\}\)), and `periodicObservable_hugWalk` is
the "in particular" of the statement --- the \(k\)-th term of the
rotation's ergodic sum at phase \(0\) is the observable at the walk's
position after \(k\) steps. Neither the certified sandwich nor
irrationality of \(\theta\) is used. \(\square\)

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

*The Denjoy--Koksma inequality (classical; see [18, Theorem 3.1, p. 73]).*
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
the *residue* permutation are additionally verified in Lean
(`theta_convergent_quality`, `theta_block_permutations`): the latter
says \(i\mapsto p_ji\) is a bijection of \(\mathbb Z/q_j\mathbb Z\).

The residue permutation must not be confused with a permutation of
fixed half-open cells. For example, at \(p/q=3/8\), the points
\(0\) and \(3\theta\) both lie in \([0,1/8)\). The argument
below instead anchors cells at the starting phase and chooses their
endpoint convention according to the sign of \(\theta-p/q\).

The variation-versus-integral inequality itself is classical, and its
analytic half is now Lean (`Problems/Juggler/DenjoyKoksma.lean`), for
arbitrary cut points rather than for a rotation:
`value_sub_mean_le_variation` --- a value of \(f\) on a cell differs from the
mean of \(f\) there by at most the variation there --- together with the
\(n\)-fold additivity of variation (`sum_eVariationOn_Icc`, Mathlib having only
the binary form) gives `denjoy_koksma_abstract`: one sample point per cell,
and the sample sum is within the total variation of the integral.
`denjoy_koksma_unit` is that on \([0,1]\) with \(q\) uniform cells, the shape
applied per block below.

The *geometric* step --- that the orbit
\(x, x+\theta, \ldots, x+(q-1)\theta\) visits each phase-anchored, sign-oriented cell exactly once, which
is where \(|\theta-p/q|\le 1/q^2\) is used --- is now Lean as well
(`Problems/Juggler/DenjoyKoksmaOrbit.lean`), and with it the whole
inequality. `denjoy_koksma_rotation` and its mean form
`denjoy_koksma_rotation_mean` are the display above, for a one-periodic
\(f\) of bounded variation, uniformly in the starting phase \(x\). Both
modules are in this paper's barrel. Mathlib has neither Denjoy--Koksma nor
unique ergodicity of the irrational rotation --- there is no
`UniquelyErgodic` in Mathlib at all --- so this is the only Lean path to
the display.

**Phase anchoring.** A fixed-grid argument would place the cells at \([i/q,(i+1)/q)\) and asked the blocks to permute them.
That is false, and the counterexample is small: \(q=2\), \(\theta=0.7\),
\(p=1\), \(x=0.49\) puts both orbit points in \([0,\tfrac12)\). Two changes
make it true. The cells must be anchored at the starting phase \(x\), and
which way they are half-open must follow the sign of \(\delta=\theta-p/q\).
Writing \(k\theta=\lfloor kp/q\rfloor+(kp\bmod q)/q+k\delta\), point \(k\)
sits at the left endpoint of cell \(kp\bmod q\) displaced by \(k\delta\), and
\(|k\delta|\le (q-1)/q^{2}<1/q\) is under one cell width --- so it stays in
that cell when \(\delta\ge0\) and falls into the previous one when
\(\delta\le0\). `orbitCell` is that assignment; `orbitCell_inj` is its
injectivity, which needs only \(\gcd(p,q)=1\) --- the residue permutation
this paper already certified as `theta_block_permutations`; and
`orbit_mem_cell` is the displacement bound. `denjoy_koksma_cellmap` then
takes the assignment in the direction the orbit supplies it, point
\(\mapsto\) cell, so no permutation has to be inverted.

The cell argument therefore proves the required rotation estimate
uniformly in the starting phase, with the endpoint convention just stated.

**And blocks compose.** The proof below cuts a length \(L=\sum_jb_jq_j\)
into consecutive blocks whose starting phases differ, and leans on the
inequality being uniform in \(x\) so that each block may be treated
independently, whatever phase it inherits from its predecessor. That step
is `denjoy_koksma_blocks`: an induction over a list of certified pairs
\((p_j,q_j)\), repeating a pair for each of the \(b_j\) copies, giving

\[
\Bigl|\sum_{k<L}f(x+k\theta)-L\int_0^1f\Bigr|\ \le\ s(L)\,\mathrm{Var}(f),
\qquad s(L)=\sum_jb_j,
\]

where \(\mathrm{Var}(f)\) bounds the variation over every window of length
one. The displayed bound of Theorem 5.7 is this with
\(\mathrm{Var}(F)<2\), divided by \(L\).

**And the observable's own variation.** That
\(F(u)=n'^{\,1-2^u}/2^u\) has \(\mathrm{Var}(F)<2\) including the wrap jump
is `observable_window_variation_lt_two` (`JumpVariation.lean`). The
rescaling is not a separate step there: `periodicObservable` is defined as
\(F\) of the fractional part times the period \(1+\alpha=\log_2 3\), so it
lives on \(\mathbb R/\mathbb Z\) from the start, and the rotation number
\(\alpha/(1+\alpha)\) is `walkTheta`. The variation itself needed three
general facts Mathlib lacks --- that variation ignores a sign
(`eVariationOn_neg`, giving the antitone counterpart of
`MonotoneOn.eVariationOn_eq`), that it is subadditive in the *function*
and not only in the set (`eVariationOn_add_le`), and the shape itself
(`eVariationOn_le_of_jump`): a fall, plus a jump, and the proof is a
decomposition \(f=g+h\) into an antitone part and a monotone step rather
than a computation of the supremum.

`periodic_window_variation_le` then reads that off for *every* window
\([y,y+1]\), which is what the uniformity in \(x\) requires, and
`block_envelope` and `theta_block_envelope` are the display: for any list
of certified convergents --- a pair repeated once per Ostrowski digit ---
the ergodic sum is within \(2\,s(L)\) of \(L\,C_*\).

**The Ostrowski assembly closes too.** `ostroBlocks` gives level \(i\) one
copy of the certified pair at level \(12-i\) per Ostrowski digit, matching
the association in `theta_sum_eq`; `ostroBlocks_snd_sum` says the
denominators sum to \(L\) and `ostroBlocks_length` that the length is
\(s(L)\), so `theta_block_envelope_of_length` is the display at an
arbitrary length with no window hypothesis. Feeding the digit cap
\(s(L)\le47\) through it, `theta_block_envelope_window` makes the bound
the constant \(94=2\cdot47\) for every \(L<301994\).

The reading of \(C_L\) as that ergodic sum --- Lemma 5.6's rotation
identification --- is Lean as well (`HugRotation.lean`), so the chain
from the integer rule to the envelope is formal throughout, and
`HugChargeEnvelope.lean` states the theorem once rather than leaving it
a chain to compose: `hugCharge_sub_circleMean_le` is
\(|C_L-C_*|\le 2s(L)/L\) at every \(L>0\), and
`hugCharge_sub_circleMean_window` is \(94/L\) on the certified window.

One thing there is a definition and not a theorem, and the file says so.
`hugCharge` is *defined* as the average of this section's observable
along the exponent walk. That the walk positions are the budgeted word's
is `budgetedWord_eq_hugWord`; that the \(k\)-th term of the rotation's
ergodic sum is the observable at the \(k\)-th walk position is
`periodicObservable_hugWalk`. What no theorem can supply is that the
phrase "charge per letter" denotes this normalisation rather than
another --- `stateCharge`, Theorem 5.4's envelope charge, is
proportional to it but not equal. The two named theorems are what make
this the defensible choice.

This settles the ergodic-convergence part of what Proposition 5.5 called
classical. The observable is monotone with one jump, hence of bounded
variation, and the display above forces
\(|C_L-\mathrm{circleMean}|\le s(L)\,\mathrm{Var}(F)/L\). The elementary
change of variables from `circleMean n'` to the displayed explicit
\(C_*(n')\) remains human. Unique ergodicity is not needed once
Denjoy--Koksma is available --- which is why Mathlib's not having
`UniquelyErgodic` costs this paper nothing.

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
`OstrowskiSandwich.lean`); the two power inequalities are checked by
the Lean kernel through `norm_num`, not by the compiled runtime, so the
sandwich that carries this certification rests on the kernel alone.
The cylinder-interval bridge identifying the displayed list as a literal
continued-fraction prefix of \(\theta\) remains classical prose. It is not
needed for the formal block bound: the quantitative hypothesis
Denjoy--Koksma needs per block is Lean directly. With the
matching numerators \(0,1,1,3,7,24,31,179,389,9126,18641,
46408,65049\) (`theta_convergent_numerators`), consecutive
pairs are unimodular, all pairs are coprime, every certified
convergent satisfies \(|\theta-p/q|<1/q^2\) against the
sandwich (`theta_convergents_unimodular`,
`theta_convergents_coprime`, `theta_convergent_quality`), and
each certified pair has the requisite residue permutation
(`theta_block_permutations`). The variation-versus-integral inequality,
the signed anchored orbit-cell argument, its mean form, and uniform block
composition are Lean (`denjoy_koksma_abstract`, `denjoy_koksma_rotation`,
`denjoy_koksma_rotation_mean`, `denjoy_koksma_blocks`).
A Koksma-type bound
with constant \(1\) (that is, \(+1/L\)) is *false* for this
observable; the correct constant is \(2s(L)\).

### 5.6 The window theorem

**Theorem 5.8 (uniform window envelope).**
For every \(L\in[50508,\,16785921)\), evaluate the reduced base
at \(n=26254996\) and \(o=o_{\min}(L)\). Then
\[
C_L\ \le\ C_*(n')+\frac{2\,s(L)}{L}\ <\ \frac1{\ln 3\,\ln n'}.
\]

*Proof.* Greedy Ostrowski digits obey \(b_j\le a_{j+1}\), so
with the certified quotients
\(\theta=[0;2,1,2,2,3,1,5,2,23,2,2,1,1,55,\ldots]\) the digit sum
satisfies \(s(L)\le\sum_{j\le13}a_j=47\) for \(L<q_{13}=301994\),
and on the remaining range \(L=b\,q_{13}+r\) with \(1\le b\le a_{14}=55\)
and \(r<q_{13}\), so \(s(L)\le b+47\). The general digit cap, exact
reconstruction \(L=\sum_j b_jq_j\), and digit-sum bound are Lean for any
denominator sequence satisfying the convergent recurrence
(`ostroDigit_le`, `ostro_sum_eq`, `ostro_digitSum_le`,
`OstrowskiNumeration.lean`). The instantiated Lean theorem
`theta_digitSum_le` supplies \(s(L)\le47\) only for \(L<q_{13}=301994\),
and `hugCharge_sub_circleMean_window` has the same range. The extension
from \(q_{13}\) to \(q_{14}\) is the human arithmetic just displayed:
identify the next quotient \(a_{14}=55\), write \(L=bq_{13}+r\), and apply
the general block envelope with \(s(L)\le b+47\). Lean does certify the
endpoint power inequalities
(`theta_sandwich_lower`, `theta_sandwich_upper`,
\(2^{16785921}<3^{10590737}\) and \(3^{10781274}<2^{17087915}\)); it does
not contain the named extended-window instance.
Put \(\nu=\ln n'\). Since \(n=26254996\) and
\(0\le D\le1.05L/n\), the entire window satisfies
\[
16.41<\log n-\frac{1.05\cdot16785921}{n}\le\nu<17.084.
\]
The digit caps give, without a scan,
\[
\frac{2s(L)}{L}\le
\max\!\left(\frac{94}{50508},\frac{96}{301994}\right)
<0.001862.
\]
For the second range this follows from
\(2(b+47)/(bq_{13})\le96/q_{13}\), since \(b\ge1\).
The quadratic integral majorant of Proposition 5.5 gives
\[
\frac1{\ln3\,\nu}-C_*(e^\nu)
\ge h(\nu):=\frac{2\nu-6}{\ln3\,\nu^3}.
\]
Because \(h'(\nu)=(18-4\nu)/(\ln3\,\nu^4)<0\) on this
interval, \(h(\nu)>h(17.084)>0.00514>0.001862\).
Combining this with Theorem 5.7 proves the strict comparison.
The digit reconstruction and block inequality are formalized as described
above; these explicit extended-window bounds are human arithmetic.
\(\square\)

*Why the window reaches \(q_{14}\), and why that is the natural stop.*
The bound \(2s(L)/L\) is worst at the *small* end, not the large one:
a large Ostrowski digit forces a large \(L\), since \(b_j=c\) requires
\(L\ge c\,q_j\). On \([q_{13},q_{14})\) the two effects give
\(2s(L)/L\le 2(b+47)/(b\,q_{13})\le3.18\cdot10^{-4}\), maximised at
\(b=1\) and an order below the value at \(L=50508\); an exhaustive
scan of \([50508,2\cdot10^{6})\) puts the true maximum at
\(9.3766\cdot10^{-4}\), attained at \(L=74654\) with \(s=35\). So the
window costs nothing to extend across the nonendpoint members of the
\(a_{14}=55\) fan, and it stops at \(q_{14}=16785921\) only because
that is where the next partial quotient begins. The same sufficient comparison can be checked at another fixed
evaluation floor by bounding \(\nu\) for that floor and comparing
\(h(\nu)\) with the digit bound above. No assertion uniform over
arbitrarily large floors follows from the present calculation.

Two consequences, and one thing that is *not* a consequence. First,
\(q_{14}=16785921\) is exactly \(L_{55}\), the last member of the
semiconvergent fan of Proposition 5.12. Because the window is half-open,
it covers precisely \(L_0,\ldots,L_{54}\) and excludes \(L_{55}\).
Second, the window theorem is not what limits the walk
charge; that is Remark 5.8a.

What does *not* follow is that the kill tables become census-free. The
window theorem is a uniform upper bound on the **charge**, so no
per-length dynamic program is needed to bound \(B(L)\) anywhere on
\([50508,16785921)\). The kill decision is the comparison
\(\theta(L)>\tfrac65B(L)\cdot\text{guard}\), and its left-hand side
\(\theta(L)=1-2^L/3^{o_{\min}(L)}\) is a per-length Diophantine
quantity that the envelope says nothing about. Corollaries 5.10 and
5.11 identify exactly that quantity as the obstruction at the surviving
fan members. So the extension removes the per-length *dynamic program*
from every nonendpoint fan member and leaves the per-length *arithmetic*
in place.
Eliminating the latter would need a lower bound on the Diophantine
deficit that is uniform along the fan --- a genuinely different
statement, and one this paper does not prove.

**Remark 5.8a (what the walk charge can ever buy).**
The charge of Theorem 5.3 prices a state at exponent \(u\) by
\(f(u)=1/(x\ln x)\) with \(x=(n')^{2^{u}}\), so
\(f(u)/f(0)=2^{-u}\exp(-(2^{u}-1)\ln n')\). Since
\(2^{u}-1=u\ln2+O(u^{2})\), the charge decays on the scale
\(u\asymp1/\ln n'\): it is a Laplace-type boundary layer at \(u=0\),
not a hard cutoff, and \(1/(\ln3\,\ln n')\) --- the same quantity
Theorem 5.8 carries --- is the scale of its effective mass rather than
the width of an interval. Integrating the layer against the walk gives
an *empirical scaling law* for the advantage over the length-only
parity charge,
\[
\frac{\text{parity}}{\text{walk}}\ \approx\ c\,\ln n',
\qquad c\approx0.44 .
\]
The constant is fitted, not derived; only the \(\ln n'\) dependence is
explained by the boundary layer.
Measured at \(L=50508\) over ten orders of magnitude in the floor, the
ratio \( (\text{improvement})/\ln n'\) runs
\(0.461,\,0.451,\,0.446,\,0.445,\,0.439,\,0.432,\,0.427\) at
\(n_0=10^{6},\,2.6\cdot10^{7},\,1.6\cdot10^{8},\,3.5\cdot10^{8},\,
10^{10},\,10^{13},\,10^{16}\): constant to \(8\%\) across the range.

So the walk charge is neither exhausted nor cheap to improve. It is not
limited by certification depth, which the extension above showed has
room to spare, and it is not limited by the envelope: substituting the
census-free envelope of Theorem 5.8 for the exact lattice program
changes the margin at \(L=50508\) from \(1.1204\) to \(1.1196\), a
difference of \(0.07\%\). It is limited by the shape of \(f\). Since
the advantage grows like \(\ln n'\), **doubling the walk charge's
efficiency requires squaring the descent floor**.

One caution about that cross-check, because it is easy to over-read.
Both quantities compared there live on the *relaxed* class: the lattice
program admits every binary word with \(o\) odds, \(e\) evens and
\(u_k\ge0\), realizable or not. The agreement to \(0.07\%\) therefore
says the envelope is tight against the relaxed optimum, and says
nothing about how far that optimum sits above the true maximum over
*realizable* words. That is a separate question, and it is the only
place in this construction where a factor of the size in question could
plausibly hide, so it is worth measuring rather than assuming.

**Proposition 5.8b (the relaxation cannot hide a constant).**
For \(14\le L\le24\) and \(o=o_{\min}(L)\), let \(\mathcal A(L)\) be the
class the lattice program maximises over --- all masks with \(o\) odds
whose exponent walk stays nonnegative --- and let
\(\mathcal R(L)\subseteq\mathcal A(L)\) be those realized as
\(\mathrm{word}_L(m)\) for some odd \(m<2\cdot10^{7}\). Then

1. the charge-maximising element of \(\mathcal A(L)\) lies in
   \(\mathcal R(L)\) at every one of those eleven lengths, so the two
   maxima agree exactly; and
2. that agreement does not depend on (1). Ordering \(\mathcal A(L)\) by
   charge, the second element carries at least \(0.9846\) of the
   maximum and the tenth at least \(0.9214\), both ratios *increasing*
   in \(L\) (at \(L=24\): \(0.9898\) and \(0.9481\)); and membership of
   \(\mathcal R(L)\) is independent of charge to measurement accuracy
   --- at \(L=24\) the realized fraction is \(0.698,0.702,0.689,0.694,
   0.689,0.691,0.697,0.698,0.697,0.695\) across the ten charge deciles.
   So the first realized word appears within the first few ranks
   whatever the argmax does, and the realized maximum is within about
   one percent of the relaxed maximum regardless.

*Discussion.* The relaxation is not vacuous: the realized fraction
\(\lvert\mathcal R\rvert/\lvert\mathcal A\rvert\) is \(1.000\) through
\(L=21\) and then falls to \(0.992\), \(0.906\), \(0.695\), so by
\(L=24\) the program maximises over half again as many words as can
occur. But the words it adds are spread uniformly through the charge
ordering rather than concentrated where the charge is small, and the
ordering is flat at the top; those two facts together, not the
coincidence in (1), are what bound the slack.

It is worth recording what this rules out. A relaxation that cost a
factor of \(8\) would have to remove almost the entire top of the
charge ordering, and \(\mathcal R\) removes about \(30\%\) of it
uniformly. Whatever explains the walk charge's advantage being
\(\approx0.44\ln n'\) rather than something larger, it is not the
exponent-walk relaxation.

**Proposition 5.8c (flatness at the kill-table lengths).**
Part (2) of Proposition 5.8b rests on the charge ordering being flat at
the top, and enumeration establishes that only for \(L\le24\). It can
be established directly at the lengths the kill tables use, without
enumerating, by running the lattice program of Theorem 5.3 with the
\(K\) best partial sums per state in place of the best one: max-plus
becomes top-\(K\)-plus, the rolling array grows by a factor \(K\), and
the pass stays linear in \(L\). At \(K=16\), writing \(r_j\) for the
\(j\)-th largest charge,
\[
1-\frac{r_{16}}{r_1}=
\begin{cases}
9.44\cdot10^{-2}, & L=18,\\
6.24\cdot10^{-2}, & L=24,\\
5.42\cdot10^{-8}, & L=50508,\ n'=2.6\cdot10^{7},\\
6.80\cdot10^{-9}, & L=176251,\ n'=1.6\cdot10^{8},\\
1.08\cdot10^{-9}, & L=780239,\ n'=3.5\cdot10^{8}.
\end{cases}
\]
So the top does not merely stay flat at the operative lengths: it
flattens by seven orders of magnitude between \(L=24\) and
\(L=50508\), and continues to flatten with \(L\).

*Proof of the computation.* The recursion and admissible class are
those of Theorem 5.3; only the accumulator changes. The top-\(K\)
program reproduces the exhaustive top ten at \(L=18\) to \(10^{-18}\),
and its GPU form agrees with the host form bitwise, so the values above
are the same objects the kill tables use. \(\square\)

The reason is visible in the charge. At the operative lengths the sum
is carried by the \(\asymp L/(\ln3\ln n')\) states with \(u\approx0\),
and the closest a nonnegative walk can come to \(u=0\) other than
exactly is \(\asymp1/o\); perturbing the extremal walk therefore moves
one contribution by a relative \(\asymp\ln n'/o\) out of a total of
\(\asymp L/\ln n'\) equal terms. At \(L=50508\) that predicts
\(\approx8\cdot10^{-8}\) against the measured \(5.4\cdot10^{-8}\).

Together with Proposition 5.8b this closes the question the relaxation
raised. Whatever removes \(30\%\) of the admissible words, it must
remove *all sixteen* of the leading walks before the realized maximum
falls by as much as \(5\cdot10^{-8}\); realizability is spread
uniformly through the ordering, so that is not what is happening. The
exponent-walk relaxation is not hiding a constant, at the lengths where
the constant would matter.

One limit remains on how far this should be read. \(\mathcal R(L)\) is
a scanned lower bound on the realizable set, so a word missing from it
can only raise the realized maximum: the measurement bounds the slack
above, which is the direction that matters. An earlier and
thinner scan (\(m<2\cdot10^{6}\)) put the \(L=22\) argmax outside
\(\mathcal R\) and the realized fraction at \(0.38\); at
\(2\cdot10^{7}\) both reverse, which is the expected behaviour when a
length-\(L\) word occurs with density \(\approx2^{-L}\), and a caution
against reading one absence as an exclusion.

What the boundary layer does suggest is that improvement will not come
from a better envelope for this charge. It raises a sharper question
than "find a better charge": is *every* charge that depends only on the
transported exponent \(u\), under the same one-step defect budget,
subject to the same \(O(1/\ln n')\) concentration? A positive answer
would turn the observation above into a limitation theorem for the
whole class, and would be worth more than another constant.


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
exclusions are monotone in the floor. Every survivor here lies
inside the window \([50508,16785921)\) of Theorem 5.8, so the
*charge* side of each kill is census-free; the per-length lattice
program is run as a cross-check and agrees to \(0.07\%\). The
comparison against \(\theta(L)\) remains per-length. The combined contiguous
excluded prefix is \(478244\): any nontrivial Juggler cycle has
period at least \(478245\).

The sole survivor at this floor is the semiconvergent fan member
\(478245=176251+301994\): required improvement over parity
\(19.46\), direct walk margin \(0.4334\) — the obstruction is
the Diophantine quality of \(|3^o-2^L|\) along the fan, not the
envelope. The kill table recomputes on commodity hardware in
minutes (Appendix B). Corollary 5.11 evaluates the same
criterion at the next cheap floor.

**Corollary 5.11 (verified computation; third laboratory
floor).**
Every integer \(2\le n\le 350000000\) reaches \(1\)
(first-passage certificate exactly as in Proposition 5.1: the
extension segment from \(162849449\) walks \(93575276\) odd
starts over \(749\) contiguous chunk records with exact integer
square roots; two bit-cap seeds \(172376627\) and
\(240154767\) are resolved at a \(3\cdot 10^9\)-bit cap, the
largest intermediate having \(1493770145\) bits at seed
\(172376627\); the maximum first passage is \(466\) steps at
seed \(198424189\); hashes in Appendix B).
At \(N_0=350000000\) the parity table leaves \(17\) survivors
through \(L=8\cdot 10^5\); the five leftovers below
\(478245\) stay excluded because both exclusions are monotone
in the floor, and the walk charge of Theorem 5.3 kills the
\(10\) leftovers in \([478245,755512]\) (margins \(1.00555\)
at \(478245\), up to \(7.824\) at \(504026\)). Every survivor here
lies inside the window \([50508,16785921)\) of Theorem 5.8, so the
*charge* side of each kill is census-free and the per-length
lattice program is only a cross-check; the comparison against
\(\theta(L)\) remains per-length. The combined contiguous excluded prefix is
\(780238\): any nontrivial Juggler cycle has period at least
\(780239\). This is the main numerical result of the paper.

The sole survivor is the semiconvergent fan member
\(780239=176251+2\cdot 301994\): required improvement over
parity \(14.46\), direct walk margin \(0.6049\) — the
obstruction remains the Diophantine quality of
\(|3^o-2^L|\) along the fan, not the envelope. The kill table
is the GPU floating-point certified comparison of the same
Theorem 5.9 criterion (Appendix B).

At and beyond \(q_{14}=16785921\), the stated half-open window would need
a further block argument and certified quotient data. Within this walk-charge criterion, the remaining
near-convergent comparisons depend on the small positive forms
\(o\log3-L\log2\), starting with the fan member \(L=780239\),
which is already inside the present window. The geometric restrictions
of Sections 3.10--3.13 and 6.3 supply separate necessary conditions.
The family leftover --- the
semiconvergent fans of \(\log 2/\log 3\) reduced to
dangerous-position partial quotients — is the working draft
[juggler_near_convergent_diophantine_note.md](juggler_near_convergent_diophantine_note.md).
The survivors are finance-survivors, not candidate cycles.

### 5.8 The price of the fan

The paragraph above says the obstruction is Diophantine and stops. It
can be made quantitative, and the answer is short: the frontier lengths
form one explicit arithmetic progression of \(56\) terms, ending on the
next convergent, and the descent floor each term costs is computable in
closed form. Nothing here is a new exclusion. It is a price list for the
exclusions that remain, and it says exactly what the walk charge of this
section bought.

**Proposition 5.12 (fan law).**
Let \(q_{12}=176251\), \(q_{13}=301994\) be the consecutive convergent
denominators of \(\log 2/\log 3\) bracketing the frontier, with
numerators \(p_{12}=111202\), \(p_{13}=190537\). Put
\[
L_k=q_{12}+k\,q_{13},\qquad o_k=p_{12}+k\,p_{13},\qquad 0\le k\le 55 .
\]
Then \(o_k=o_{\min}(L_k)\) for every such \(k\); the linear form is
exactly affine in \(k\),
\[
\Lambda_k=o_k\log 3-L_k\log 2=\Lambda_0+k\Lambda',
\qquad
\Lambda_0=3.6002\cdot10^{-6},
\quad
\Lambda'=-6.4508\cdot10^{-8};
\]
and \(k=55\) is the last index with \(\Lambda_k>0\), because
\(\Lambda_0/\lvert\Lambda'\rvert=55.81\). At that last index
\(L_{55}=16785921=q_{14}\) and \(o_{55}=10590737=p_{14}\): the fan ends
on the next convergent, which is where the partial quotient
\(a_{14}=55\) is consumed.

*Proof.* \(\Lambda\) is linear in \((o,L)\) and
\((o_k,L_k)=(p_{12},q_{12})+k\,(p_{13},q_{13})\), which is the affine
formula; \(\Lambda'=\Lambda(q_{13})<0\) because \(3^{p_{13}}<2^{q_{13}}\),
consecutive convergents lying on opposite sides. Since
\(\Lambda_k\in(0,\log 3)\) for \(0\le k\le 55\), one has
\(3^{o_k}>2^{L_k}>3^{o_k-1}\), which is \(o_k=o_{\min}(L_k)\). The sign
change at \(55.81\) is arithmetic, and
\(q_{14}=a_{14}q_{13}+q_{12}\) with \(a_{14}=55\) identifies the
endpoint. \(\square\)

Because \(\Lambda_k\) *decreases* in \(k\), so does \(\theta(L_k)\), and
\(n_{\max}(L_k)\) increases: the fan grows strictly more expensive as it
is climbed, and the cheapest member is always the one at the current
frontier within this fan. The following transition has been checked
computationally at \(k=1,\ldots,12,20,31,40,52,54\):
\[
N_0\ \ge\ n_{\max}(L_k)
\qquad\Longrightarrow\qquad
\text{period}\ \ge\ L_{k+1},
\]
No all-index transition theorem is asserted: excluding a fan member
also requires ruling out intervening non-fan lengths. (At
\(k=0\) alone one extra length intervenes, the doubling
\(2q_{12}=352502\), whose threshold \(1044095006\) sits \(1793\) above
\(n_{\max}(q_{12})\); the multiples \(mq_{12}\) cluster just above
\(n_{\max}(q_{12})\) in the same way and are all cleared by
\(n_{\max}(L_1)\).)

| \(k\) | \(L_k\) | \(\Lambda_k\) | \(n_{\max}(L_k)\) = floor that passes \(L_k\) |
|---|---|---|---|
| \(0\) | \(176251\) | \(3.600\cdot10^{-6}\) | \(1.044\cdot10^{9}\) |
| \(1\) | \(478245\) | \(3.536\cdot10^{-6}\) | \(2.756\cdot10^{9}\) |
| \(2\) | \(780239\) | \(3.471\cdot10^{-6}\) | \(4.480\cdot10^{9}\) |
| \(3\) | \(1082233\) | \(3.407\cdot10^{-6}\) | \(6.238\cdot10^{9}\) |
| \(6\) | \(1988215\) | \(3.213\cdot10^{-6}\) | \(1.182\cdot10^{10}\) |
| \(31\) | \(9538065\) | \(1.600\cdot10^{-6}\) | \(1.040\cdot10^{11}\) |
| \(52\) | \(15879939\) | \(0.246\cdot10^{-6}\) | \(1.034\cdot10^{12}\) |
| \(54\) | \(16483927\) | \(0.117\cdot10^{-6}\) | \(2.199\cdot10^{12}\) |
| \(55\) | \(16785921\) | \(0.052\cdot10^{-6}\) | \(4.866\cdot10^{12}\) |

Three readings of this table.

*What the walk charge is worth.* Corollary 5.11 reaches \(L_2=780239\)
from \(N_0=3.5\cdot10^{8}\). Finance and parity alone reach it only from
\(n_{\max}(L_1)=2.756\cdot10^{9}\). The walk charge is therefore worth a
factor \(7.9\) in descent floor at the present frontier — and a factor
\(6.4\) at the previous one, where Corollary 5.10 reached \(L_1\) from
\(1.63\cdot10^{8}\) against a finance requirement of
\(1.044\cdot10^{9}\).

*What the next step costs.* A purely computational route to
\(L_3=1082233\) — no walk charge, no new idea, only a longer
first-passage run — needs
\(N_0\ge n_{\max}(780239)=4479642886\), a floor \(12.8\) times the
present one. The walk charge does very much better, and by a factor
that can be measured rather than guessed.

**Observation 5.13 (finite margin scaling).**
For two lengths evaluated at two floors each, fitting the kill margin
\(\theta(L)/(\tfrac65B(L,N_0))\) to a power of \(N_0\log N_0\)
gives effective exponents \(1.0491\) and \(1.0458\).
Their mean, approximately \(1.047\), is an empirical interpolation;
it is not a proved asymptotic law.

*Evidence.* The committed kill records contain two lengths priced at
two floors each. At \(L=176251\) the margin runs \(0.158796\) at
\(N_0=26254995\) to \(1.198309\) at \(162849448\); at \(L=478245\) it
runs \(0.433383\) at \(162849448\) to \(1.005552\) at \(350000000\).
The implied exponents are \(1.0491\) and \(1.0458\), agreeing to
\(0.31\%\). The excess over \(\beta=1\) is the secondary dependence of
the reduced base on the floor; it is not needed for the conclusion
below, which is unchanged at \(\beta=1\).

Applied to the present survivor, \(L=780239\) at margin \(0.604888\),
this predicts a kill at \(N_0=5.53\cdot10^{8}\). Evaluating the
criterion directly gives

\[
\text{the walk charge kills } L=780239 \text{ from } N_0=553906250,
\]

so the prediction is accurate to \(0.2\%\), and the walk charge is
worth a factor \(4479642886/553906250=8.09\) in descent floor here —
against \(7.9\) at the previous frontier and \(6.4\) at the one before.
These three comparisons suggest a useful local estimate. Other fan
members require direct evaluation; a uniform factor of eight over the
entire fan is not established.

**Corollary 5.14 (conditional; the next period bound).**
If every integer \(2\le n\le 554000000\) reaches \(1\), then any
nontrivial Juggler cycle has period at least \(1082233\).

*Proof, modulo the floor.* At \(N_0=554000000\) the parity table of
Corollary 4.5 leaves twenty survivors below \(L_3=1082233\), and the
walk charge of Theorem 5.3 kills all of them. Everything at or below
\(780239\) is excluded because both exclusions are monotone in the
floor and \(554000000>350000000\), except \(780239\) itself, which is
killed here at margin \(1.000884\). The nine survivors above it are
killed with margins
\[
\begin{array}{r|r@{\quad}r|r@{\quad}r|r}
806020 & 8.076 & 830747 & 2.908 & 881255 & 4.596\\
931763 & 6.101 & 956490 & 1.663 & 982271 & 7.451\\
1006998 & 3.203 & 1032779 & 8.669 & 1057506 & 4.595
\end{array}
\]
all by the certified evaluation of the Theorem 5.9 comparison at the
reduced base. The next length, \(L_3=1082233\), survives at margin
\(0.70815\). Hence the contiguous excluded prefix is \(1082232\).
\(\square\)

The kill table is therefore *already done*; the only missing input is
the descent floor. Extending the certified floor from \(3.5\cdot10^{8}\)
to \(5.54\cdot10^{8}\) is a first-passage run over roughly
\(1.0\cdot10^{8}\) further odd starts — comparable in size to the
extension Corollary 5.11 already performed, and a factor \(1.58\) in
floor rather than the \(12.8\) that finance alone would demand. We do
not carry out that run here; Corollary 5.14 is stated conditionally so
that the computation and the criterion are separable, which is the
architecture of Corollaries 5.10 and 5.11 as well.

*Further computational costs.* The fan table reports parity-charge
thresholds through \(L_{55}\). Extrapolating the locally measured
walk improvement to every member would be a heuristic; the conditional
next-period claim in Corollary 5.14 uses direct comparisons instead.
The limitation proved in Proposition 6.2a concerns fixed-floor charges
with a positive length-uniform anchor contribution.

## 6. Limitations and future directions

Section 3.10 isolates a second unresolved question: whether absolute
floor-cell alignment forces every threshold cycle to contain a
wrong-parity state. Theorems 3.39--3.40 exclude successively wider
top strips at their explicit minimum thresholds. The remaining region
and the taller-cycle case are still unresolved. Appendix E's family
and guard results do not establish the uniform conclusion.

Proposition 3.41 identifies a paired-gap issue: amplification
through the terminal common prefix must be compared with the mixed
passage and suffix contractions using the shared absolute cells.
The present estimates cover only certified suffix factors. Their
one-sided error certificate also requires increasingly large minima
as the contracting exponent approaches one (Appendix F.6).
Neither observation excludes the terminal mixed-word return.

The result does not imply termination. The remaining
finance-survivor lengths are uncontrolled, and existence of a
cycle at such a length is open.

A start \(n\ge 2\) has a *descent certificate* if there exists a
realized finite itinerary \(w\) with \(J^{|w|}(n)<n\). Even starts
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

The number \(p\) of odd runs on a minimum-based cycle ---
equivalently, the number of excursions on the necklace of
Section 4 --- is another natural statistic to test. The run
form gives \(p\le e\) and, because the first odd run has length
at least two, \(p\le o-1\), hence \(p\le\min(e,o-1)<0.3691\,L\)
on an expanding itinerary; that is only the trivial ceiling, and
a genuine lower bound on \(p\), or a peak-height / peak-count
tradeoff, would feed Theorem 4.7.

The following comparison records a limitation of this statistic. A bound on \(p\)
is only useful if it constrains the *adversary*, and for the
walk charge the adversary is the extremal walk of Theorem 5.3,
which can be recovered from the lattice program by storing its
decisions. That walk turns out to saturate both ceilings at
once. Writing \(p\) for its odd-run count:

| \(L\) | \(84\) | \(1054\) | \(25781\) | \(50508\) |
|---|---|---|---|---|
| \(p\) | \(31\) | \(389\) | \(9515\) | \(18641\) |
| \(\min(e,o-1)\) | \(31\) | \(389\) | \(9515\) | \(18641\) |
| longest odd run | \(2\) | \(2\) | \(2\) | \(2\) |

So \(p=e\) exactly, at every length tested: every even run has
length one, and the walk is a word in the two blocks
\(\mathtt{OE}\) and \(\mathtt{OOE}\) alone, mixed at the density
\(\log2/\log3\) --- the hug itinerary of Theorem 5.4, in its
Sturmian form. At \(L=84\) it is
\(\mathtt{O^2E\,O^2E\,O^2E\,OE\,O^2E\,O^2E\,OE\,\cdots}\).

These relaxed extremal words attain the displayed run-count ceiling
at the tested lengths. Thus a lower bound on run count alone would not
exclude those particular relaxed words. A constraint coupling peak
height, parity realization, and exact return could still be stronger.

The repository also measures realization of short hug prefixes among
odd \(m<4\cdot10^6\): relative to \(2^{-(l-1)}\), the observed
frequency ratio is about \(1.00\) at \(l=8,9,10\) and \(1.38\)
at \(l=18\). This finite experiment establishes realization of those
short prefixes. It does not establish realization at lengths such as
\(780239\), realization by cycle minima, or exact closure of the
full word. These remain possible sources of further restrictions.

Corollary 4.11 excludes a short-period regime in terms of the cycle
minimum. None of the finite realization or charge comparisons supplies
a lower bound on that minimum growing with the period. The general
cycle and termination problems remain open.

### 6.1 Relation to the companion manuscripts

The companion manuscripts [16,17] use the power envelope and descent floor
proved or recorded here. Their analytic and counting results are separate
inputs, and the period bounds of Sections 2--5 do not depend on them.

*The envelope supplies a bounded target.* If the exponent walk of a start
\(n\in(y,2y]\) reaches
\[
u_t\le-\log_2\!\left(\frac{\log(2y)}{\log N_0}\right),
\]
Theorem 2.2 gives \(J^t(n)\le N_0\), after which the verified descent
floor gives arrival at \(1\). Paper C [17] combines a quantitative
almost-all version of this event with a lower bound for backward-closed
sets. Its parity or stopped-pressure hypotheses remain unproved; a larger
finite floor alone does not establish them.

For numerical scale comparisons at \(N_0=350000000\),
\[
N_0^{4/3}\approx2.47\cdot10^{11},\qquad
N_0^{3/2}\approx6.55\cdot10^{12},\qquad
N_0^2\approx1.23\cdot10^{17}.
\]
These are conversions of the supplied floor, not additional cycle
exclusions or a proof of an almost-all hypothesis.

*A cycle's basin has a separate lower bound.* Paper C's stated contagion
theorem gives
\(\sum_{m\in B(C),\,m\le x}1/m\gg(\log x)^\lambda\)
for every \(\lambda<\lambda^{**}=0.4926\ldots\), if the basin
\(B(C)\) of a nontrivial cycle exists. This is a result of the companion
manuscript, not a new theorem here. For a primitive cycle \(C\) with
minimum \(n\) and period \(L\), the present paper instead gives
\[
\theta\log n\le\sum_{x\in C}\frac1x\le\frac Ln,
\qquad \theta=1-2^L/3^o.
\]
The first inequality is Corollary 4.4c and the second follows from
minimality. These constraints concern the cycle states; they do not give
an upper bound on the basin that could contradict contagion.

*Odd share and the finite frontier.* Every nontrivial cycle has
\(o/L>\log2/\log3\). If \(n\log n>2L\), Theorem 4.10 also implies
\[
0<\frac oL-\frac{\log2}{\log3}
\le\frac{2}{n\log n\log3}.
\]
The frontier lengths \(176251,478245,780239\) are members of the
finite fan in Proposition 5.12. The auxiliary denominator \(301994\)
is the adjacent lower-convergent denominator used to generate that fan;
it is not itself one of these surviving lengths. A constraint on the
odd share of live starts averaged over many starts is a different
statement from a restriction on one periodic orbit.

*Current scope of the companion hypotheses.* Paper B's depth-five
certificate class has stated density \(7/8\); the proposed length-seven
and length-eight extensions remain outside its established conclusions.
Paper C's revised cylinder hypotheses concern bad words or bad prefixes,
and its stopped-pressure formulations concern live starts. The
unrestricted all-word versions are not assumed: terminating cylinders
already obstruct them. The scale-average stopped-pressure bound remains
an open arithmetic input. These corrections do not change Paper A's
finite cycle bounds, and no companion result is used here to exclude
the surviving lengths.

### 6.2 Scope of the method's limitations

At the tabulated upper-convergent denominators, the finance threshold
is well approximated by a constant multiple of \(q_kq_{k+1}\) after
multiplication by \(\log n_{\max}\). The exact denominator recurrence is
\[
q_{k+1}=a_{k+1}q_k+q_{k-1}.
\]
The numbers \(3.4,5.8,23.5,2.5,1.7\) in the numerical comparison
are approximate ratios \(q_{k+1}/q_k\), not the integer partial
quotients \(a_{k+1}\). A square-root scaling in the floor can be a
useful local heuristic, but a global asymptotic for the first surviving
period would require control of continued-fraction quotients and the
intervening lengths. No such global theorem is claimed here.

The following proposition gives a precise limitation under an explicit
normalization assumption.

**Proposition 6.2a (what an anchor-normalized charge can exclude).**
Call \(\Phi\) a *charge* if every cycle minimum \(n\) with word of length
\(L\) satisfies
\(\sum_{i<L}1/(x_i\log x_i)\le\Phi(n,L)\), with \(\Phi\) nonincreasing in
its first argument. Fix \(N_0\ge2\), and call \(\Phi\)
*anchor-normalized at \(N_0\)* if there is a constant \(c_{N_0}>0\),
independent of \(L\), such that \(\Phi(N_0,L)\ge c_{N_0}\) for every \(L\).
Say \(\Phi\) *excludes* \(L\) at floor \(N_0\) when
\(\theta(L)>\tfrac65\Phi(N_0,L)\). Then an anchor-normalized charge excludes
only finitely many denominators \(q_k\) of the upper convergents
\(p_k/q_k>\log2/\log3\).

*Proof.* Anchor normalization makes exclusion at \(N_0\) require
\(\theta(L)>\tfrac65c_{N_0}\), a positive threshold fixed once \(N_0\)
is. Along an upper convergent \(p_k/q_k>\alpha:=\log2/\log3\), one has
\(p_k=o_{\min}(q_k)\), and therefore
\[
0<-\log\bigl(1-\theta(q_k)\bigr)=p_k\log3-q_k\log2
=q_k\log 3\,\Bigl(\tfrac{p_k}{q_k}-\alpha\Bigr)
<\frac{\log 3}{q_{k+1}}.
\]
The last bound is the standard convergent estimate. Since
\(q_{k+1}\to\infty\), it gives \(\theta(q_k)\to0\), so only finitely many
upper-convergent denominators clear the fixed threshold. \(\square\)

The explicit finance, run-packing and walk-charge majorants in Sections 4
and 5 are anchor-normalized: their displayed fixed-floor formulas retain a
positive first-state contribution uniformly in \(L\), the last entering
`cycleMin_hug_kill_criterion`. Proposition 6.2a therefore applies to
refinements that preserve this feature. It does not rule out a different
charge formulation whose value at \(N_0\) has no length-uniform positive
anchor, nor does it turn the present finite period bounds into a universal
no-go theorem.

The run--suffix inequalities require separate care. Theorem 3.26
compares the finite-state lower envelope
\(4(n/4)^{(3/2)^a}\) with the backward envelope \(B(u)\).
A leading-exponent comparison can suggest which shapes to test, but
does not remove the constants or finite-\(n\) margin. In particular,
it does not prove that every proper tail beginning with \(O\) is
formally non-expanding. Equality of two finite shape counts likewise
does not prove that the run--suffix inequalities are ineffective at
every length surviving finance.

The finite shape enumerations and charge comparisons describe the
instances computed in this paper. They do not rule out stronger
enumeration methods, improved charges without the normalization of
Proposition 6.2a, or restrictions valid specifically on realized cycles.
Primitivity makes orbit states distinct; it does not make every
block-boundary landing odd when adjacent even letters are permitted.
Consequently, any refinement using distinct odd valleys must count
actual maximal odd runs or impose the no-\(EE\) hypothesis.

A proof excluding all nontrivial cycles would need a further argument
beyond the finite period bounds and the scoped limitation above.

### 6.3 Absolute upper cells and the remaining signed-loss question

The cubic rank grid also strengthens the total floor-loss bound. This
section records that consequence, a local integer refinement, and the
precision still needed to convert these restrictions into an exclusion.

**Lemma 6.3a (odd-to-odd upper-square gap).** If both \(x\) and
\(J(x)\) are odd, then
\[
x^3+3\le(J(x)+1)^2.
\tag{UC1}
\]

*Proof.* More generally, let \(y\) be odd. The equality
\(x^3+1=(y+1)^2\) would give \(x^3=y(y+2)\).
Since \(\gcd(y,y+2)=1\), unique factorization would make both
positive factors cubes, say \(y=a^3\) and \(y+2=b^3\).
But \(a\ge1\), \(b\ge a+1\), and
\(b^3-a^3\ge3a^2+3a+1\ge7\), a contradiction.
For \(y=J(x)\), the exact upper cell makes
\((y+1)^2-x^3\) positive; it is odd when \(x,y\) are odd.
Having excluded one, it is at least three. \(\square\)

The integer argument is formalized by `cube_add_one_ne_odd_succ_sq`
and `floorPower_odd_image_upper_gap`. It is a local floor-cell
restriction and requires no cycle assumption.

**Proposition 6.3b (upper-cell charge on the sorted grid).** Let \(C\)
be a primitive exact threshold cycle, or a primitive actual Juggler cycle
with minimum \(m>1\) and maximum \(M<m^3\). Write \(m=\min C\),
let \(L=|C|\) be its least period, and let \(o\) be its lower-branch
count, equivalently its odd count in the actual case. Set
\[
T=\log3,\qquad \Lambda=o\log3-L\log2,
\qquad A=(\log m)e^{-(1-1/L)\Lambda}.
\]
Then \(A>0\), \(\Lambda>0\), and
\[
\Lambda<\frac{e^{-A}}A
 \sum_{i=0}^{L-1}e^{-iT(A+1)/L}
<\frac{e^{-A}}A\left(1+\frac{L}{T(A+1)}\right).
\tag{UC2}
\]

*Proof.* Retain the sorted states and defects of Proposition 3.36.
For an edge with target \(y\) and real branch exponent
\(p\in\{1/2,3/2\}\), the upper cell gives \(x^p<y+1\).
Consequently
\[
0\le\delta=\log\frac{p\log x}{\log y}
<\eta(y):=\log\frac{\log(y+1)}{\log y}
<\frac1{y\log y}.
\]
The last inequality uses \(\log(1+t)<t\) twice. Since targets
permute the states and the defects sum to \(\Lambda\),
\(\Lambda<\sum_i1/(c_i\log c_i)\).
The grid bound (CB5) gives \(\log c_i\ge A e^{iT/L}\).
For \(t=iT/L\ge0\), monotonicity and \(e^t\ge1+t\) yield
\[
c_i\log c_i\ge A e^{Ae^t+t}
\ge A e^A e^{(A+1)t}.
\]
This proves the first inequality in (UC2). With
\(z=T(A+1)/L>0\), the geometric sum is less than
\(1/(1-e^{-z})=1+1/(e^z-1)<1+1/z\), proving the second.
\(\square\)

For example, along a sequence with \(\log m\to\infty\),
\(\log m=o(L)\), and \(\Lambda\log m\to0\), this gives
\[
m(\log m)^2\Lambda\le(1+o(1))\frac L{\log3}.
\tag{UC3}
\]
Indeed \(A/\log m\to1\) and \(e^A/m\to1\). If additionally
\(\Lambda\sim c/L\) with fixed \(c>0\) and \(m\) grows
polynomially in \(L\), then
\(m(\log m)^2\le(1+o(1))L^2/(c\log3)\).
These are conditional scale restrictions, not an actual-cycle scaling
law or a uniform lower bound for \(\Lambda\). The bound also applies
to threshold cycles with wrong parity, so it does not itself detect
that defect.

**Corollary 6.3c (minimum range at the first surviving count pair).**
An actual primitive cubic-band cycle with
\[
(L,o,e)=(780239,492276,287963)
\]
must satisfy
\[
350000000<m<520000000.
\tag{UC4}
\]

*Proof and numerical boundary.* The lower bound is the certified descent
input of Corollary 5.11. At these fixed counts,
\[
3.4711981668\cdot10^{-6}<\Lambda
<3.4711981670\cdot10^{-6}.
\]
At \(m=520000000\), outward interval evaluation makes the last
right-hand side of (UC2) less than
\(3.230293215\cdot10^{-6}\). For fixed counts, \(A\) increases
with \(m\), while both positive factors in that bound decrease.
Thus (UC2) fails at every larger minimum as well. \(\square\)

The scalar comparison and its rational outward endpoints are reproduced
in the repository's cycle-rank-curvature control report, distributed
with the software. The finite upper-cell and geometric bounds in (UC2)
are now verified in Lean, including the scaled scalar consequence.
The monotonicity argument is now formalized in
`CubicGrid.closedGeometricChargeBound_strictAntiOn_minimum`.
The symbolic exclusion is
`CubicGrid.FullUpperCellChargeBounds.closedGeometric_cutoff_excludes`:
an upper bound at one minimum excludes every larger minimum at the same
fixed counts whenever that bound is at most the surplus. The nonlinear
version uses `CubicGrid.nonlinearChargeBound_strictAntiOn_minimum`
and `CubicGrid.FullUpperCellChargeBounds.nonlinear_cutoff_excludes`.
The numerical interval comparison itself remains verified computation
outside Lean. The asymptotic consequence (UC3) also remains written. The conclusion
concerns these exact counts and the cubic-height
hypothesis. It does not exclude period \(780239\) or raise the descent
floor.

**The unresolved signed comparison.** Return to an actual primitive
cubic-band cycle. Suppose \(o\ge3\), let
\(k=e^{-1}\pmod L\) lie in \((L/2,L)\), and put
\(\ell=L-k\), \(h=2k-L\). Start the chronological orbit at \(m\).
Its states at times \(h,k,L\) have ranks \(2,1,0\), respectively.
Let \(Q=[h,k)\) and \(R=[k,L)\) denote their source-time arcs.
Adding \(\ell\) pairs every Q edge with an R edge whose source
and target ranks are both one lower. No source crosses a branch cut,
so the complete two arcs have the same branch word.

For an actual edge \(x\to y\), put \(N=x^3\) on O and \(N=x\)
on E, and define the positive unused upper-cell capacity
\[
s=Z((y+1)^2)-Z(N),\qquad Z(t)=\log\log t.
\]
Write \(s_Q,s_R\) for its arc sums and \(C_Q,C_R\) for the sums
of \(\eta(y)\). As \(\eta\) decreases and the target ranks are
adjacent pairs,
\[
0<\varepsilon:=C_R-C_Q\le\eta(m)-\eta(M).
\]
Telescoping the actual losses along the two arcs gives
\[
s_R-s_Q=\varepsilon+\chi,\qquad
\chi=\log\frac{\log c_2\,\log m}{(\log c_1)^2}.
\tag{UC5}
\]
For \(t=0,2\), define
\[
H_t(y)=\log\frac{\log(2y-m+t)\,\log m}{(\log y)^2}.
\]
The condition
\[
H_0(c_1)+\varepsilon<s_R-s_Q<H_2(c_1)+\varepsilon
\tag{UC6}
\]
would be equivalent to \(0<c_2-2c_1+m<2\), impossible for three
odd integers. This is an exact reformulation of the missing estimate,
not an inequality that has been established.

The complete universal rank-envelope cap sums at the counts of
Corollary 6.3c leave a relaxed signed-loss interval of approximately
\([-1.307,1.307]\cdot10^{-6}\). At the boundary-scale first-triple
control, the forbidden window has width of order \(10^{-10}\).
That control uses \(m_0=350000001\) only as a diagnostic scale:
\(O(m_0)=6547900454916\) is even, so it is not an actual cycle
minimum. No simultaneous realization of all integer cells is asserted.

Lemma 6.3a changes the odd-to-odd cap from
\(V_1(y)\) to \(V_3(y)\), where
\(V_a(y)=Z((y+1)^2-a)-Z(y^2)\). For \(y>1\),
\[
0<V_1(y)-V_3(y)
=\int_{(y+1)^2-3}^{(y+1)^2-1}\frac{du}{u\log u}
\le\frac1{y^2\log y}.
\tag{UC7}
\]
Its total additional effect on those envelopes is at most
\(L/(m_0^2\log m_0)<3.238\cdot10^{-13}\).
It cannot repair this cap test's missing precision. Multiplying the
actual arc identities likewise only exponentiates (UC5). Balanced
rotation counts do not bound the variation of the actual unused
capacities. What remains is an arithmetic restriction on their joint
distribution at the shared integer states, strong enough to prove (UC6).

## Appendix A. Lean names and trust boundary

The proof object is the import closure of `formal/Problems/JugglerPaper.lean`.
From `formal/`, run `lake build Problems.JugglerPaper`, followed by
`lake env lean AxiomCheckPaperA.lean` to inspect the cited declarations'
dependencies. The exact toolchain is pinned in `formal/lean-toolchain`.
The optional [formalization map](juggler_finite_dynamics_formalization.md)
contains the detailed declaration-level explanations. Every name cited in
this manuscript must be reachable from the paper barrel; the associated
trust-boundary tests enforce that condition.

The core financing, transport, hug domination, and bounded-variation
rotation estimates are Lean theorems. The displayed change of variables
identifying the circle mean with \(C_*\), the explicit extension of
Theorem 5.8 beyond \(q_{13}\), and the use of Rhin are human arguments.
The descent floors, per-length comparisons, and Theorem 3.31's enumeration
are computational inputs. The native digit scan is recorded separately.
None of these distinctions is removed by compiling the barrel.

| Text | Lean declaration or evidence boundary |
|---|---|
| itinerary semantics | `follows_iff_itinerary`, `image_eq_iterate`, `image_append` |
| Theorem 2.1 | `image_monotone_of_follows` |
| Theorem 2.2 | `power_bound_word` |
| Corollary 2.3 | `power_bound_contracts` |
| Theorem 2.4 | `global_defect_identity` |
| Theorem 2.5 | `global_defect_eq_zero_iff_localsTight`, `global_defect_eq_zero_implies_monochrome`, `power_bound_eq_iff_extremal` |
| Theorem 2.6 | `global_defect_append` |
| Corollary 2.7 | `image_eq_start_defectRatio` |
| per-step slack | `one_plus_eta_lt_succ_sq` |
| Lemma 3.1 | `odd_preimage_unique` |
| CycleMin | `CycleMin` |
| Theorem 3.2 | `cycle_itinerary_formally_expanding`, `cycleMin_start_odd`, `cycleMax_start_even`, `cycleMin_not_end_odd`, `square_scale_superquadratic`, `cycleMin_to_even_superquadratic` |
| Lemma 3.3 | `lower_growth_word` |
| Lemma 3.4 | `oo_suffix_threshold`, `ooo_suffix_threshold`, `threshold_inherits_odd_append`, `cycle_last_even_interval`, `cycle_last_even_ne_odd_sq`, `no_cycle_odd_run_append_even`, `no_cycle_itinerary_ooe` |
| odd-run block | `oddEvenBlock` |
| Lemma 3.5 | `no_cycle_itinerary_oooeoe`, `no_cycle_itinerary_ooooee` |
| Theorem 3.6 | `no_cycle_itinerary_length_le_six` |
| Lemma 3.7 | `no_cycle_itinerary_ooooeoe`, `no_cycle_itinerary_oooooee` |
| Theorem 3.8 | `no_cycle_itinerary_length_le_seven`, with `no_cycle_itinerary_ooeoooe`, `no_cycle_itinerary_oooeooe` |
| Lemma 3.9 | `cycle_trailing_evens_lt` |
| Lemma 3.10 | `lowerDenom_replicate_odd`, `odd_run_lower_growth` |
| Lemma 3.11 | `no_follows_seven_odds_of_lt256` |
| Theorem 3.12 | `no_cycle_itinerary_two_even_ee`, `no_cycle_itinerary_two_even_eoe` |
| Theorem 3.13 | `no_cycleMin_gapped_three_even_ee`, `no_cycleMin_gapped_three_even_eoe` |
| Theorem 3.14 | `no_cycle_itinerary_three_even_eee`, with `no_cycle_itinerary_ooooooeee` |
| Theorem 3.15 | `no_cycle_itinerary_three_even_eoee` |
| Theorem 3.16 | `no_cycle_itinerary_three_even_eooee` |
| Theorem 3.17 | `no_cycle_itinerary_three_even_eoooee` |
| Theorem 3.18 | `no_cycle_itinerary_three_even_eeoe` |
| Theorem 3.19 | `no_cycle_itinerary_three_even_eoeoe` |
| Theorem 3.20 | `no_cycle_itinerary_three_even_eooeoe` |
| Theorem 3.21 | `no_cycle_itinerary_gapped_three_even_ee`, `no_cycle_itinerary_gapped_three_even_eoe` |
| Theorem 3.22 | `no_cycle_itinerary_even_count_le_three` |
| Corollary 3.23 | `cycle_itinerary_length_ge_eleven` |
| Lemma 3.24 | closed form of Lemma 3.10; no separate Lean name |
| Lemma 3.25 | generalizes `cycle_trailing_evens_lt` past pure even runs |
| Theorem 3.26 | Corollary 3.27's ten rows are Theorems 3.12--3.21 above |
| Lemma 3.28 | `absorb_odd_step`, `cross_mul_pow`, `odd_run_ge` (`O7EEEEGap.lean`, now imported by `Problems.JugglerPaper`); \(X_7,Y_7\) are that module's 6177 and 3990 |
| Theorem 3.29 | `no_cycle_itinerary_oooooooeeee` is the row \(u=EEEE\), \(a=7\) |
| Theorem 3.31 | arithmetic core Lean (`EvenCountEight.lean`): per-run cap `runCapConst_gt`, `runCapConst_lt`; the table is the floor, `runCap_eq_floor`, `runCap_antitone`, tuples `runCap_tuple_three`--`runCap_tuple_seven`; period floor `period_ge_22_of_even_count`, sharp by `expansion_holds_at_22` and `expansion_fails_below_22`. The enumeration of 353044 canonical forms (`run_suffix_law.closure`, Python) is verified computation, not Lean |
| Theorem 3.33 | Exact parity and sorted order: `cubicBand_sorted_rotation`; coprimality and actual odd prefixes: `cubicBand_mechanical_itinerary` |
| Proposition 3.34 | `thresholdMap_invariant`, `thresholdMap_ne_self`, `thresholdMap_exists_primitive`, `threshold_sorted_rotation`, `thresholdMap_eq_floorPower_iff` |
| Theorem 3.35 | `threshold_all_periodic_rank_rotation`, `threshold_periods_equal`; `rankRotation_orbit_iff_residue`, `rankRotation_orbit_representatives`, `rankResidue_parameterization`, `rankRotation_orbit_upper_card`, `rankResidue_interlaces`; prefixes: `rankRotation_mechanical_prefix` |
| Proposition 3.36 | Exact-cycle realization: `threshold_cycle_grid`, `cubicBand_cycle_grid` with conclusion `RealizedGridBounds`; the illustrative asymptotic width comparison remains written analysis |
| Proposition 3.37 | `cubicParityProject_greatest`, `cubicRounding_eq_or_pred`, `cubicRounding_exists_primitive`, `cubicRounding_real_loss`, `cubicRounding_finite_invariant_rotation`; modular consequences as in Theorem 3.33 |
| Proposition 3.38 | `branchOffset_same_branch_difference`, `branchOffset_same_branch_smooth_gap`, `branchOffset_nearest_even_gap`; kernel-checked witness: `branchOffsetCycle_cells`, `branchOffsetCycle_primitive`, `branchOffsetCycle_bounds`, `branchOffsetCycle_counts`, `branchOffsetCycle_rank_rotation`, `branchOffsetCycle_mechanical_prefix` |
| Theorem 3.39 | Exact actual-cycle seam: `cycleMin_exact_return_seam`; integer height gap: `cubic_return_height_algebra`, `cycleMin_height_strip`, `cycleMin_all_states_height_strip`; top-strip obstruction: `threshold_cycle_wrong_parity`. The maximum-odd-integer restatement and the sharper fractional bound for \(t\) are written consequences |
| Appendix E.1 | OE cell: `oe_eq_iff`; OOE floor and odd endpoint: `ooe_one_integer`, `ooe_odd_maximal`; hidden-parity family: `oe_perfect_power_hidden_odd`. General root iteration, OOEOE projection and fixed-word asymptotics remain written |
| Appendix E.2 | Exact one-step rank returns: `left_subtractive_first_return`, `right_subtractive_first_return`; word statistics: `left_word_statistics`, `right_word_statistics`; guards: `follows_append`. Full accelerated tower partition remains written |
| Appendix E.3 | Square carry: `baseline_bounds`, `baseline_zero_iff`, `baseline_one_iff`, `baseline_two_iff`, `square_guard_iff`; genuine family block: `ooeFamily_juggler_block`. The unbounded real quotient-substitution error remains written |
| Theorem E.4 | `ooeFamilyReturn_mod_fortyeight`, `ooeFamilyReturn_valuation_drop`, `ooeFamily_juggler_chain_bound`, `ooeFamily_no_infinite_juggler_chain`. The additional 3-adic identity is written; six terminating traces are finite computations |
| Appendix E.5 | Initialized record: `record_initializes`, `endpoint_validation`; correction and signed floors: `exact_remainder_correction`, `exact_quotient_gap`, `corrected_quotient_integer`; executable recovery and hidden guards: `recoverPeak_eq`, `recoverPeak_guard_iff`. The further OOEOE composition is written |
| Appendix E.6 | Every-modulus witness: `guardResidueFamily_every_modulus`; cells and parities: `guardResidue_ooe_traces`, `guardResidue_nat_parities`; exact remainder and valuation: `guardResidue_first_remainders_zero`, `guardResidue_aggregate_valuation`; record collision and classifier obstruction: `guardResidueFamily_record_collision`, `guardResidueFamily_no_record_classifier`; common domain and threshold edges: `guardResidue_common_band_and_section`, `guardResidue_threshold_blocks`. The general positive-\(b\) construction and supplementary bookkeeping remain written |
| Theorem 3.40 | Actual-cycle gap and height bounds: `dc_cycle_gap`, `lr_cycle_gap`, `dc_cycle_height`, `lr_cycle_height`. The last two include the displayed real bounds and exact integer endpoints, from the stated minimum and cubic-band hypotheses |
| Theorem 3.40, cycle and threshold consequences | Ordinary cycle predicates: `cycleMin_dc_height`, `cycleMin_lr_height`. Wrong parity in the excluded threshold strips: `threshold_cycle_dc_wrong_parity`, `threshold_cycle_lr_wrong_parity` |
| Appendix F.1 | Exact transported loss: `loss_exact`; concave-tail bound: `loss_lt_budget`; common-floor paired estimate: `paired_bound`; exponent/count identity: `exponent_eq_counts` |
| Appendix F, finite even-gap bookkeeping | `even_transfers_sum`, `even_transfers_positive`: each strict even-gap step consumes at least two, with every transfer retained as a hypothesis |
| Appendix F.5, induced word counts | `count_determinant`, `count_coprime`, `expanded_count_gcd`: the induced count matrix has determinant one and preserves the gcd of the expanded totals |
| Appendix F.2–F.3 | Unconditional word bounds: `c_loss`, `w_loss`; gap contraction: `c_contract`, `w_contract`. Required growth: `ac_grows`, `d_grows`, `v_grows`; the sharper written helper errors and the earlier \(2^{15}\) growth cutoff are not needed in these formal proofs |
| Appendix F.2–F.4 | Actual section: `periodicExtrema_return_model`; forced batches: `dc_rank_stages`, `lr_rank_stage`; guarded pair placement: `periodicExtrema_dc_transfers`, `periodicExtrema_lr_transfers`; height transport: `height_of_power_gap` |
| Proposition 3.41 and Appendix F.5 | Guarded factorization: `induced_terminal_actual_factorization`. Primitive termination: `primitive_terminal`. Full actual-orbit construction, global adjacency, cut/extrema identification and strict mixed gap for \(m\ge3\): `periodicExtrema_terminal_cut`, `periodicOrbit_terminal_cut`. The periodic-set interface requires connectedness; the orbit interface derives it. Local cell inequality: `mixed_gap` |
| Appendix F.6 | Exact necessary threshold for the stated sufficient certificate: `certificate_requires_large_minimum`. Its near-unit asymptotic interpretation remains written; this is not a counterexample to actual paired contraction |
| Lemma 3.21b | canonical run form; Theorem 3.2 |
| Lemma 3.21a | the case split of Theorem 3.22 |
| Lemma 4.1 | `log_le_two_log_add` |
| Lemma 4.2 | `log_step_even`, `log_step_odd` |
| Lemma 4.3 | `cycleMin_log_envelope` |
| Theorem 4.4 | `cycleMin_finance` |
| Corollary 4.4c | `cycleMin_log_envelope_inv`, `cycleMin_finance_inv_sum` |
| Lemma 4.4b | `packingR_step` (the step in \(o\) is the constant \(2\alpha-1-1/2n\)), `alpha_lt_half` (\(\alpha<1/2\) once \(t\ge2n\)), `two_n_add_one_lt_rpow_three_halves` (which \(t=\lfloor n^{3/2}\rfloor\) gives for \(n\ge12\)), `packingR_step_neg`, `theta_strictMono`, and `comparison_fails_upward` for an arbitrary positive coefficient — \(6/5\) here and \(1\) in Theorem 4.4 (`OddCountMonotone.lean`) |
| Corollary 4.5 | See the accompanying formalization map. |
| Theorem 4.6 | certified identity `cycleMin_defect_finance`, per-step losses `log_floorPower_even_ge_sub`, `log_floorPower_odd_ge_sub`, invariants `cycleMin_log_le_weight`, `cycleMin_charge_prefix` (`DefectFinance.lean`); the numeric table is verified computation |
| Theorem 4.7 | See the accompanying formalization map. |
| Theorem 4.8 | run-type table; verified computation, not Lean |
| Proposition 4.9 | `run_survivor_unimodular`, `run_survivor_seed_F2`, `run_survivor_seed_F3`, `three_pow_step_gt_two_pow_step`, `runSurvivors_length` |
| Theorem 4.10 | `cycleMin_gap_transfer`; abstract length bound `cycleMin_length_of_gap` (`GapTransfer.lean`) |
| Corollary 4.11 | `cycleMin_length_of_gap` with Rhin's measure [15] as hypothesis; the transcendence input is classical, not Lean |
| Proposition 5.1 | laboratory floor; certified computation, not Lean |
| Theorem 5.2 | raised cutoff; verified computation, not Lean |
| Theorem 5.3 | transport inequality `cycleMin_transport`, per-step losses `log_floorPower_even_ge`, `log_floorPower_odd_ge` (`WalkTransport.lean`); §5.2 consequence `cycleMin_defect_le_charge`, `cycleMin_defect_le_hug_charge` (`WalkChargeMax.lean`) |
| Theorem 5.4 | combinatorial core `hugOdds_le_of_admissible`; cycle-itinerary domination `cycleMin_prefix_odds_ge_hug`, `cycleMin_odds_ge_hug`; charge maximisation `stateCharge_antitone`, `hug_charge_maximal` (`WalkChargeMax.lean`); strict uniqueness `stateCharge_strictAnti`, `stateCharge_inj`, `hug_charge_unique` — an admissible profile attaining the hug charge *is* the hug profile |
| Proposition 5.5 | Lean proves convergence of the finite hug average to `circleMean` by `denjoy_koksma_blocks` and the Laplace bounds `inv_sq_le_quad`, `rotation_average_le`, `rotation_average_lt`, `rotationAverage_le`, `rotationAverage_lt`, `rotationAverage_gap`; the elementary change of variables identifying `circleMean n'` with the displayed `rotationAverage (log n')` remains prose |
| Lemma 5.6 | itinerary identity `budgetedWord_eq_hugWord`, `hugOdds_pow_ge`, `hugOdds_pow_lt`, `hugOdds_pow_gt`, `hugOdds_least`; rotation identification (`HugRotation.lean`) `hugOdds_eq_ceil`, `hugOdds_eq_sub_floor`, `hugEvens_eq_floor`, `hugLetter_iff_floor_step`, `hugWalk_eq_fract`, and the Birkhoff reading `periodicObservable_hugWalk` |
| Theorem 5.7 | `value_sub_mean_le_variation`, `sum_eVariationOn_Icc`, `denjoy_koksma_abstract`, `orbitCell_inj`, `orbit_mem_cell`; detailed scope in the formalization map |
| Theorem 5.8 | `ostroDigit_le`, `ostro_sum_eq`, `ostro_digitSum_le`, `theta_digitSum_le`, `greedyDigitSum_le`; detailed scope in the formalization map |
| Theorem 5.9 | kill template `cycleMin_hug_kill_criterion` (`DefectFinance.lean`); the per-length kill table is verified computation |
| Proposition 5.12 | `fanLength`, `fanOdd`, `fanLambda`, affine step `fanLambda_affine`, negativity `fan_step_pow`, `fanLambda_step_neg`, monotonicity `fanLambda_strictAnti`, endpoints `fanLambda_55_pos`, `fanLambda_56_neg` (these *are* `theta_sandwich_lower` and `theta_sandwich_upper`), length `fan_positive_iff`, and `fan_frontiers`, `fan_endpoint`, `fan_past_endpoint` (`FanLaw.lean`) |
| Propositions 5.8b, 5.8c | the two forced walk letters `walk_first_letter_odd`, `walk_second_letter_odd`, `step_lt_two` (`FanLaw.lean`); the relaxation and flatness measurements are verified computation |
| Observation 5.13, Corollary 5.14 | finite fitted exponents and the separately evaluated conditional bound; computation, not Lean |
| Corollary 5.10 | second floor and kill table; verified computation, not Lean |
| Corollary 5.11 | third floor and kill table; verified computation, not Lean |
| Lemma 6.3a | `cube_add_one_ne_odd_succ_sq`, `floorPower_odd_image_upper_gap` (`UpperSquareGap.lean`); the integer upper-square gap only |
| Proposition 6.3b | Exact finite and closed charges: `power_cells_grid_charge`; scaled consequence: `power_cells_scaled_charge`; actual and threshold interfaces: `cubicBand_cycle_upper_charge`, `threshold_cycle_upper_charge`. Ordinary-orbit and minimum-based itinerary extraction at the true least period: `periodicOrbit_upper_charge`, `cycleMin_upper_charge`. The abstract statements retain both cell faces, rank translation, and transitivity; the interfaces derive these from actual connected cycles. The asymptotic consequence (UC3) remains written |
| Corollary 6.3c | Fixed-count monotonicity and symbolic exclusion: `CubicGrid.closedGeometricChargeBound_strictAntiOn_minimum`, `CubicGrid.FullUpperCellChargeBounds.closedGeometric_cutoff_excludes`. The outward numerical interval comparison at the stated counts remains outside Lean |
| Section 6.3 signed comparison | Written transport identities and interval controls; no inequality forcing the forbidden window is established |
| Propositions E.7--E.8 | Written residue and inverse-polynomial finite-difference proofs; no uniform theorem is inferred from finite trajectory checks |
| short certificates (Section 6) | `even_finiteProgress`, `odd_even_finiteProgress` |
| no certificate \(\Rightarrow\) odd-to-odd | `no_finiteProgress_implies_odd_odd` |
| induction to \(1\) | `reachesOne_of_all_finiteProgress` |
| four-block chain | `four_block_pe_1999` |

## Appendix B. Admissible lengths

The record lengths of \(\gamma(L)\) through \(10^5\), with the
parity \(6/5\) bound \(n_{\max}\) of Section 4, are

| \(L\) | \(o_{\min}\) | \(n_{\max}\) |
|---:|---:|---:|
| \(1\) | \(1\) | \(2\) |
| \(3\) | \(2\) | \(7\) |
| \(11\) | \(7\) | \(25\) |
| \(19\) | \(12\) | \(133\) |
| \(84\) | \(53\) | \(2323\) |
| \(569\) | \(359\) | \(23568\) |
| \(1054\) | \(665\) | \(788014\) |
| \(25781\) | \(16266\) | \(26254995\) |
| \(50508\) | \(31867\) | \(162848324\) |

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
The \(10^6\) longest first-passage figures of Proposition 1.3
(\(253\) steps at seed \(78901\)) are the opening chunk of the
laboratory-floor certificate,
`data/research/juggler/cycle_finance/floor_verify/N26254995/chunks/3_250002.json`
(\(3\le n\le 250002\); SHA-256
`6303b62c9b1819deaf9715338f84899c1d75eb50dcab850a7b8fb28874ec19bc`).
The file `floor.json` in the same directory as
`exceptions_parity.json` is a later \(n_{\mathrm{top}}=2\cdot10^6\)
companion and is not the \(10^6\) certificate. The parity table is
written by
`research.juggler_sequence.cycle_finance.write_parity_artifacts`.
The table gives exact crossings of the stated \(6/5\) comparison.
The historical guarded generator returned the conservative upper values
\(3\) and \(162848325\) at \(L=1\) and \(L=50508\), respectively;
these must not be confused with the exact crossings \(2\) and
\(162848324\). Neither correction changes the stated period bounds.

The run-type table of Theorem 4.8 is
`data/research/juggler/cycle_finance/budget_opt.json`. The
\(42\) excluded lengths are
`killed_by_budget`; their SHA-256, serialized as a JSON list of
integers with no spaces, is
`9d108776d6dc5dc1ae2594058850463cd2d3995cc57b9811471f08e3b818b90a`.
The complementary \(99\) lengths form the table \(\mathcal E_{\mathrm{run}}\)
under Theorem 4.7's primitive and no-\(EE\) hypotheses.
Their SHA-256, in the same serialization, is
`9e2098923ccb39933630b116133a3fc2ddaf98ace4eb76dbab9b5ab9f6e604e6`.
The first few survivors remain
\[
25781,\;26835,\;27889,\;28943,\;29997;
\]
the last survivor is \(99477\). The three families and the
unimodular basis are Proposition 4.9. The finite leftover tables
of Section 3 are the Lean `decide +kernel` evaluations named in
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
The third-floor certificate of Corollary 5.11 is
`data/research/juggler/cycle_finance/floor_verify/N350000000/certificate.json`;
the SHA-256 of its chunk records is
`c57f5ccc9bce980f478dafec00c449050a5e217a4f0f3e100916c41dacbe7472`.
Its parity survivor scan is
`data/research/juggler/cycle_walk_charge/N350000000_parity_leftovers.json`,
and the \(10\) kill records under
`data/research/juggler/cycle_walk_charge/N350000000_kills/` have
SHA-256
`d16ccfed52757d4a44368a6549a8149ccbc926472737276c577912346db854ab`
(concatenated in length order); the direct non-kill record for
the survivor \(780239\) (margin \(0.6049\)) is stored alongside.
The exact-integer CPU computation with guarded comparisons is
the authoritative record for the first- and second-floor claims
in this note. The third-floor kill table is the GPU
floating-point certified comparison
(`research.juggler_sequence.cycle_walk_charge_gpu`), the same
IEEE-double kernel previously checked against stored CPU
records to relative error below \(10^{-13}\); its performance
figures live in the repository documentation.
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
python -m research.juggler_sequence.paper_a_audit
```

runs the Paper A arithmetic audit when executed from the repository
root. It recomputes selected exact parity thresholds, compares stored
walk margins, checks the finite fan identities, and checks the constants
used in Corollary 4.11. It does not replay all descent trajectories.
For a direct per-length CPU report, save the following as a script and
run it from the repository root after installing the project:

```python
import argparse
from research.juggler_sequence.cycle_walk_charge import certified_report

parser = argparse.ArgumentParser()
parser.add_argument("length", type=int)
parser.add_argument("floor", type=int)
args = parser.parse_args()
print(certified_report(args.length, args.floor))
```

For example, `python report_length.py 478245 162849448` evaluates
the non-excluded endpoint of Corollary 5.10. The committed third-floor
records use `cycle_walk_charge_gpu.gpu_certified_report` with floor
\(350000000\), and therefore require the corresponding GPU runtime.
Do not use its `--write` option to regenerate a different floor: that
option selects a fixed output directory. The precise software version,
dependency environment, and archived data must accompany a release.

## Appendix C. Exact floor defect

This appendix records the exact identity behind Theorem 2.2. The
present note uses only the nonnegativity \(\Delta_w(n)\ge0\). A
nontrivial itinerary-dependent lower bound on \(\Delta_w\) is left
for future work.

For a single branch,
\[
x^h=J(x)^2+\rho(x),\qquad
h=\begin{cases}1,&x\ \text{even},\\3,&x\ \text{odd},\end{cases}
\]
with \(0\le\rho(x)<2J(x)+1\). Write
\(\operatorname{gap}(a,\rho,h)=(a+\rho)^h-a^h\). The *global
defect* \(\Delta_w(n)\) is the terminal value of the resulting
power-gap recurrence.

**Theorem 2.4 (global defect identity).**
If \(w\) is realized at \(n\) and \(m=J^{|w|}(n)\), then
\[
n^{3^{\#O(w)}}=m^{2^{|w|}}+\Delta_w(n),\qquad\Delta_w(n)\ge0.
\]
Theorem 2.2 is the inequality \(\Delta_w(n)\ge0\).

*Proof.* Induct on \(w\). The empty itinerary is \(n=n+0\). An even
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
realized mixed itinerary therefore has \(\Delta_w(n)>0\).

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
If \(w\) is a cycle itinerary at \(n\), then
\(\Delta_w(n)=n^{3^{\#O(w)}}-n^{2^{|w|}}\) exactly.

*Proof.* Theorem 2.4 with \(m=n\). \(\square\)

A mixed itinerary has strict total defect, but the relative slack of a
single letter tends to \(0\) with the state, so no uniform local
tax exists. Theorem 4.4 does not use these identities.

## Appendix D. Family exclusions

This appendix records the small-cycle censuses (Lemma 3.5,
Theorem 3.6, Lemma 3.7, Theorem 3.8) and the family-by-family
exhaustion used by Lemma 3.21a and Theorem 3.22. Each geometry is
killed by a next-square obstruction, by long odd-run growth
against a last-even one-step preimage, or by a finite exceptional window.

**Lemma 3.5 (two length-six exclusions).**
Neither \(OOOEOE\) nor \(OOOOEE\) is a cycle itinerary at any \(n\ge 2\).

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
`decide +kernel` evaluation behind `no_cycle_itinerary_oooeoe` and
`no_cycle_itinerary_ooooee` (Appendix A).

Now suppose \(OOOOEE\) is a cycle itinerary at \(n\ge 256\), and write
\(z=J^4(n)\) for the image after the prefix \(OOOO\). Lemma 3.4(iv)
gives \(J(z)<(n+1)^2\), and the preceding even letter gives
\(z<(J(z)+1)^2\), hence \(z<(n+1)^4\). Lemma 3.3 on \(OOOO\) gives
\(n^{81}\le 2^{130}z^{16}\), so
\(n^{81}<2^{130}(n+1)^{64}\), contradicting the tail inequality.

Finally suppose \(OOOEOE\) is a cycle itinerary at \(n\ge 256\). Write
\(z_3=J^3(n)\) and \(y=J(z_3)=\lfloor\sqrt{z_3}\rfloor\), so
\(z_3<(y+1)^2\). Lemma 3.3 on \(OOO\) gives
\(n^{27}\le 2^{38}z_3^8<2^{38}(y+1)^{16}\). Cubing yields
\(n^{81}<2^{114}(y+1)^{48}\). The last letters \(OE\) give the odd-preimage
bound \(y^3<(n+1)^4\). Write \(A=n+1\ge 257\). We claim
\((y+1)^3<2A^4\). If \(y\le A\), this is \((A+1)^3<2A^4\). If
\(y>A\), then \(y\ge 258\), so \(3y+1<y^2\) and hence
\((y+1)^3=y^3+3y^2+3y+1<A^4+4y^2\), while \(4y^2<A^4\) because
\(4y^3<4A^4\le yA^4\). Raising \((y+1)^3<2A^4\) to the sixteenth
power gives \((y+1)^{48}<2^{16}(n+1)^{64}\). Combining with the cubed
lower envelope produces again \(n^{81}<2^{130}(n+1)^{64}\). \(\square\)

**Theorem 3.6 (small-cycle census).**
No itinerary of length at most six is a cycle itinerary at any \(n\ge 2\).

*Proof.* Rotating a cycle itinerary by one letter moves the base point one
step along the trajectory and yields another cycle itinerary; every state of
the cycle is at least \(2\), because a trajectory that reaches \(1\) stays
at \(1\) and cannot return to a start \(n\ge 2\).

If every letter is odd, the start is odd, hence \(n\ge 3\), and the
odd branch strictly increases there: \(J(x)>x\) for odd \(x\ge 3\),
since \(x^3\ge(x+1)^2\). The trajectory ascends strictly and never returns.
Otherwise some letter is even, and a rotation ending just after that
letter produces an even-terminating cycle itinerary \(vE\) of the same
length based at a cycle state \(m\ge 2\). It therefore suffices to
exclude even-terminating cycle itineraries of length at most six.

By Theorem 3.2(i) a cycle itinerary is formally expanding. No
even-terminating itinerary of length one or two is expanding (\(2>3^0\) and
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
\(OOOEOE\), and \(OOOOEE\). Lemma 3.4(v) excludes \(O^5E\). The itinerary
\(EOOOOE\) rotates one step onto \(OOOOEE\), and \(OEOOOE\) rotates
two steps onto \(OOOEOE\); both are excluded by Lemma 3.5.

It remains to exclude \(OOEOOE\). Let this itinerary be a cycle itinerary at
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
Neither \(OOOOEOE\) nor \(OOOOOEE\) is a cycle itinerary at any \(n\ge 2\).

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
is the Lean `decide +kernel` evaluation behind
`no_cycle_itinerary_ooooeoe` and `no_cycle_itinerary_oooooee` (Appendix A).

Now suppose \(OOOOOEE\) is a cycle itinerary at \(n\ge 14\), and write
\(z=J^5(n)\) for the image after the prefix \(OOOOO\). Lemma 3.4(iv)
on the last even letter, together with the preceding even letter,
gives \(z<(n+1)^4\). Lemma 3.3 on \(OOOOO\) gives
\(n^{243}\le 2^{422}z^{32}\), so
\(n^{243}<2^{422}(n+1)^{128}\), contradicting the tail inequality.

Finally suppose \(OOOOEOE\) is a cycle itinerary at \(n\ge 14\). Write
\(z_4=J^4(n)\) and \(y=J(z_4)=\lfloor\sqrt{z_4}\rfloor\), so
\(z_4<(y+1)^2\). Lemma 3.3 on \(OOOO\) gives
\(n^{81}\le 2^{130}z_4^{16}<2^{130}(y+1)^{32}\). Cubing yields
\(n^{243}<2^{390}(y+1)^{96}\). The last letters \(OE\) give the odd-preimage
bound \(y^3<(n+1)^4\). Write \(A=n+1\ge 15\). The same comparison
\((y+1)^3<2A^4\) as in Lemma 3.5 holds at this smaller scale. Raising
to the thirty-second power gives
\((y+1)^{96}<2^{32}(n+1)^{128}\). Combining with the cubed lower
envelope produces again \(n^{243}<2^{422}(n+1)^{128}\). \(\square\)

**Theorem 3.8 (small-cycle census through length seven).**
No itinerary of length at most seven is a cycle itinerary at any \(n\ge 2\).

*Proof.* The reduction of Theorem 3.6 applies at every length: an
all-odd itinerary cannot return, and every mixed cycle itinerary rotates to an
even-terminating cycle itinerary based at a cycle state \(m\ge 2\).
Lengths at most six are Theorem 3.6. It remains to exclude
even-terminating cycle itineraries of length seven.

By Theorem 3.2(i) a cycle itinerary is formally expanding. The
even-terminating expanding length-seven words are exactly
\(O^6E\), \(EO^5E\), \(OEO^4E\), \(OOEO^3E\), \(O^3EO^2E\),
\(O^4EOE\), and \(O^5EE\). Lemma 3.4(v) excludes \(O^6E\). The itinerary
\(EO^5E\) rotates one step onto \(O^5EE\), and \(OEO^4E\) starts
\(OE\), so it cannot be a cycle minimum (Theorem 3.2(iii)) and
rotates two steps onto \(O^4EOE\); both leftovers are excluded by
Lemma 3.7.

It remains to exclude the cyclic class containing \(OOEO^3E\)
and \(O^3EO^2E\). At a cycle minimum \(m\), Theorem 3.2 forces
the orientation to start \(OO\) and end \(E\). The two possible
orientations in this class are exactly those two words; a rotation can
interchange them. In the first orientation, the internal even state is
followed by \(OOO\), so Lemma 3.4(ii), valid at \(m\ge3\),
contradicts the last-even preimage interval. In the second orientation,
the corresponding \(OO\) bootstrap applies at \(m\ge5\).
The remaining odd minimum \(m=3\) follows
\(3\to5\to11\to36\to6\): the \(E\) at \(36\) is realized,
but the next prescribed \(O\) is impossible at the even state \(6\).
Both minimum-based orientations are excluded. \(\square\)

**Theorem 3.12 (two-even leftover families).**
Let \(k\ge 6\) and \(n\ge 2\). Neither \(O^{k-2}EE\) nor
\(O^{k-3}EOE\) is a cycle itinerary at \(n\).


*Proof.* First, if \(n\ge 256\), then
\[
n^{3^{k-2}}>2^{G_{k-2}}(n+1)^{2^k}.
\]
The case \(k=6\) is the tail inequality of Lemma 3.5. If the display
holds at some \(k\ge 6\), cubing both sides produces
\[
n^{3^{k-1}}
>
2^{3G_{k-2}}(n+1)^{3\cdot 2^k}.
\]
The recurrence of Lemma 3.10 gives \(G_{k-1}=3G_{k-2}+2^{k-1}\), so
the desired comparison at length \(k+1\) reduces to
\(2^{2^{k-1}}<(n+1)^{2^k}\). Equivalently \(2<(n+1)^2\), which holds
for every \(n\ge 256\).

Now suppose \(O^{k-2}EE\) is a cycle itinerary at such an \(n\). Write
\(z=J^{k-2}(n)\). Lemma 3.9 with \(r=2\) gives \(z<(n+1)^4\).
Lemma 3.10 on the prefix \(O^{k-2}\) gives
\(n^{3^{k-2}}\le 2^{G_{k-2}}z^{2^{k-2}}\), hence
\(n^{3^{k-2}}<2^{G_{k-2}}(n+1)^{2^k}\), contradicting the tail.

Finally suppose \(O^{k-3}EOE\) is a cycle itinerary at such an \(n\).
Write \(z=J^{k-3}(n)\) and \(y=\lfloor\sqrt z\rfloor\), so
\(z<(y+1)^2\). Lemma 3.10 on \(O^{k-3}\) and cubing produce
\(n^{3^{k-2}}<2^{3G_{k-3}}(y+1)^{3\cdot 2^{k-2}}\). The last letters
\(OE\) give the odd-preimage bound \(y^3<(n+1)^4\). The comparison
\((y+1)^3<2(n+1)^4\) of Lemma 3.5 applies at this scale. Raising it
to the power \(2^{k-2}\) and using \(G_{k-2}=3G_{k-3}+2^{k-2}\)
recovers again \(n^{3^{k-2}}<2^{G_{k-2}}(n+1)^{2^k}\).

For \(2\le n<256\), the cases \(k=6\) and \(k=7\) are Lemmas 3.5
and 3.7. The remaining short words \(O^6EE\), \(O^5EOE\), and
\(O^6EOE\) fail to return on the same \(254\)-start window; this is
the Lean `decide +kernel` evaluation behind
`no_cycle_itinerary_two_even_ee` and `no_cycle_itinerary_two_even_eoe`
(Appendix A). Any longer leftover of either family begins with
seven consecutive odd letters, which Lemma 3.11 forbids on this
window. \(\square\)

**Theorem 3.13 (first-even transport).**
Let \(n\ge 2\). No minimum-based cycle itinerary at \(n\) has the form
\(O^aEO^bEE\) with \(a\ge 2\) and \(b\ge 4\), or the form
\(O^aEO^bEOE\) with \(a\ge 2\) and \(b\ge 3\).


*Proof.* Write \(y=J^{a+1}(n)\) for the state after the first even
letter. Minimum-basedness gives \(y\ge n\). In the first family the
remainder after that letter is \(O^bEE\) with \(b+2\ge 6\); in the
second it is \(O^bEOE\) with \(b+3\ge 6\). The trailing-even and
last-odd one-step preimages of those remainders are measured against the cycle
start \(n\). Combined with Lemma 3.10 at the remainder start \(y\),
the same algebra as in Theorem 3.12 produces
\[
y^{3^{\ell-2}}
<
2^{G_{\ell-2}}(n+1)^{2^\ell}
\le
2^{G_{\ell-2}}(y+1)^{2^\ell},
\]
where \(\ell\) is the remainder length. If \(y\ge 256\), the first
paragraph of Theorem 3.12 supplies the opposite inequality at \(y\).

If \(y<256\), then \(n\le y<256\). A gapped leftover of total
length at least \(17\) has \(a\ge 7\) or \(b\ge 7\), so either the
prefix or the remainder realizes seven consecutive odd letters,
contradicting Lemma 3.11. The finitely many short-gap words with
\(2\le a\le 6\) and \(b\le 6\) fail to be minimum-based cycle itineraries
on the window \(2\le n<256\); this is the Lean `decide +kernel`
evaluation behind `no_cycleMin_gapped_three_even_ee` and
`no_cycleMin_gapped_three_even_eoe` (Appendix A). \(\square\)

**Theorem 3.14 (three trailing evens).**
Let \(a\ge 6\) and \(n\ge 2\). The itinerary \(O^aEEE\) is not a cycle
word at \(n\).


*Proof.* Write \(z=J^a(n)\). Lemma 3.9 with \(r=3\) gives
\(z<(n+1)^8\). Lemma 3.10 then yields
\(n^{3^a}<2^{G_a}(n+1)^{2^{a+3}}\) on any such cycle itinerary. For
\(n\ge 128\) the opposite comparison
\[
n^{3^a}>2^{G_a}(n+1)^{2^{a+3}}
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
\(OOOOOOEEE\): at every such start the itinerary fails to return. The
same finite check is the Lean `decide +kernel` evaluation behind
`no_cycle_itinerary_ooooooeee` (Appendix A). For \(a\ge 7\) the prefix
contains seven consecutive odd letters, which Lemma 3.11 forbids
on this window. \(\square\)

**Theorem 3.15 (mixed bunched family \(EOEE\)).**
Let \(a\ge 5\) and \(n\ge 2\). The itinerary \(O^aEOEE\) is not a cycle
word at \(n\).


*Proof.* First let \(n\ge 4\), and write \(z=J^a(n)\),
\(y=\lfloor\sqrt z\rfloor\), and \(p=J(y)\). Lemma 3.9 with
\(r=2\) after the prefix \(O^aEO\) gives \(p<(n+1)^4\). The letter
after \(y\) is odd, so Lemma 3.10 at length one yields
\(y^3\le 4p^2<4(n+1)^8\). For \(n\ge 4\) one has
\(4(n+1)^8<(n+1)^9\), hence \(y<(n+1)^3\). The even one-step preimage at \(z\)
then gives \(z<(y+1)^2\le(n+1)^6\). Combined with Lemma 3.10,
any such cycle itinerary would satisfy
\[
n^{3^a}<2^{G_a}(n+1)^{6\cdot 2^a}.
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
\(a=6\), the itinerary fails to return; these are the Lean
`decide +kernel` evaluations behind `no_cycle_itinerary_three_even_eoee`
(Appendix A). For \(a\ge 7\) and \(n<256\), Lemma 3.11 applies. For
\(a\ge 6\) and \(n\ge 16\), the tail of the previous paragraph
applies. \(\square\)

**Theorem 3.16 (mixed bunched family \(EOOEE\)).**
Let \(a\ge 4\) and \(n\ge 2\). The itinerary \(O^aEOOEE\) is not a
cycle itinerary at \(n\).


*Proof.* First let \(n\ge 32\), and write \(z=J^a(n)\),
\(y=\lfloor\sqrt z\rfloor\), and \(p\) for the image after the
prefix \(O^aEOO\). Lemma 3.9 with \(r=2\) gives \(p<(n+1)^4\).
The two letters after \(y\) are odd, so Lemma 3.10 at length two
yields \(y^9\le 2^{10}p^4<2^{10}(n+1)^{16}\). For \(n\ge 32\) one
has \(2^{10}<(n+1)^2\), hence \(y<(n+1)^2\). The even one-step preimage at
\(z\) then gives \(z<(y+1)^2\le(n+1)^4\). Combined with
Lemma 3.10, any such cycle itinerary would satisfy
\[
n^{3^a}<2^{G_a}(n+1)^{2^{a+2}}.
\]
For \(n\ge 256\) and \(a\ge 4\), this is the opposite of the
shared tail of Theorem 3.12 at length \(k=a+2\).

For \(2\le n<256\), the cases \(a=4,5,6\) fail to return on that
window; this is the Lean `decide +kernel` evaluation behind
`no_cycle_itinerary_three_even_eooee` (Appendix A). For \(a\ge 7\),
Lemma 3.11 applies. \(\square\)

**Theorem 3.17 (mixed bunched family \(EOOOEE\)).**
Let \(a\ge 3\) and \(n\ge 2\). The itinerary \(O^aEOOOEE\) is not a
cycle itinerary at \(n\).


*Proof.* First let \(a\ge 4\) and \(n\ge 3\), and write
\(z=J^a(n)\), \(y=\lfloor\sqrt z\rfloor\), and \(p\) for the image
after the prefix \(O^aEOOO\). Lemma 3.9 with \(r=2\) gives
\(p<(n+1)^4\). The three letters after \(y\) are odd, so
Lemma 3.10 at length three yields
\(y^{27}\le 2^{38}p^8<2^{38}(n+1)^{32}\). For \(n\ge 3\) one has
\(2^{38}<(n+1)^{22}\), hence \(y<(n+1)^2\). The even one-step preimage at
\(z\) then gives \(z<(y+1)^2\le(n+1)^4\). Combined with
Lemma 3.10, any such cycle itinerary would satisfy
\[
n^{3^a}<2^{G_a}(n+1)^{2^{a+2}}.
\]
For \(n\ge 256\) and \(a\ge 4\), this is the opposite of the
shared tail of Theorem 3.12 at length \(k=a+2\), already used in
Theorem 3.16.

Now let \(a=3\) and \(n\ge 256\). The same two-even one-step preimage gives
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
that window; this is the Lean `decide +kernel` evaluation behind
`no_cycle_itinerary_three_even_eoooee` (Appendix A). For \(a\ge 7\),
Lemma 3.11 applies. \(\square\)

**Theorem 3.18 (mixed bunched family \(EEOE\)).**
Let \(a\ge 5\) and \(n\ge 2\). The itinerary \(O^aEEOE\) is not a
cycle itinerary at \(n\).


*Proof.* First let \(n\ge 4\), and write \(z=J^a(n)\) and \(y\)
for the last odd letter of \(O^aEEOE\). The suffix \(EOE\) is a
cycle suffix, so the last-odd cube of Theorem 3.15 gives
\(y^3<(n+1)^4\). The two letters between \(z\) and \(y\) are
even, so \(z<(y+1)^4\). For \(n\ge 4\) the successor comparison
\((y+1)^3<2(n+1)^4\) upgrades this to \(z<(n+1)^6\). Combined
with Lemma 3.10, any such cycle itinerary would satisfy the same
display as Theorem 3.15:
\[
n^{3^a}<2^{G_a}(n+1)^{6\cdot 2^a}.
\]
The opposite comparison is therefore the tail of Theorem 3.15:
it holds for \(a=5\) and \(n\ge 314\), and already for \(a=6\)
and \(n\ge 16\).

For \(2\le n<314\) and \(a=5\), and for \(2\le n<16\) and
\(a=6\), the itinerary fails to return; these are the Lean
`decide +kernel` evaluations behind `no_cycle_itinerary_three_even_eeoe`
(Appendix A). For \(a\ge 7\) and \(n<256\), Lemma 3.11 applies.
For \(a\ge 6\) and \(n\ge 16\), the tail of the previous
paragraph applies. \(\square\)

**Theorem 3.19 (mixed bunched family \(EOEOE\)).**
Let \(a\ge 4\) and \(n\ge 2\). The itinerary \(O^aEOEOE\) is not a
cycle itinerary at \(n\).


*Proof.* First let \(n\ge 32\), and write \(z=J^a(n)\),
\(w=\lfloor\sqrt z\rfloor\), and \(y\) for the last odd letter.
The suffix \(EOE\) again gives \(y^3<(n+1)^4\). The one-odd
envelope on \(w\) yields \(w^3\le 4s^2\), where \(s\) is the
image after \(O^aEO\). The last-odd one-step preimage and \(n\ge 32\) upgrade
this to \(w<(n+1)^2\), hence \(z<(w+1)^2\le(n+1)^4\). Combined
with Lemma 3.10, any such cycle itinerary would satisfy
\[
n^{3^a}<2^{G_a}(n+1)^{2^{a+2}}.
\]
For \(n\ge 256\) and \(a\ge 4\), this is the shared tail already
used in Theorem 3.16.

For \(2\le n<256\), the cases \(a=4,5,6\) fail to return on that
window; this is the Lean `decide +kernel` evaluation behind
`no_cycle_itinerary_three_even_eoeoe` (Appendix A). For \(a\ge 7\),
Lemma 3.11 applies. \(\square\)

**Theorem 3.20 (mixed bunched family \(EOOEOE\)).**
Let \(a\ge 3\) and \(n\ge 2\). The itinerary \(O^aEOOEOE\) is not a
cycle itinerary at \(n\).


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
cycle itinerary would satisfy the shared two-even tail of
Theorem 3.16.

Now let \(a=3\) and \(n\ge 256\). The prefix \(O^3\) against
\(z<(u+1)^2\) yields \(n^{27}<2^{38}(u+1)^{16}\), and the
two-odd plus last-odd geometry of the previous paragraph yields
\(u^{27}<2^{38}(n+1)^{32}\). These are the same two displays as
in the \(a=3\) case of Theorem 3.17, with \(u\) in place of
\(y\), and the same small/large split applies.

For \(2\le n<256\), the cases \(a=3,4,5,6\) fail to return on
that window; this is the Lean `decide +kernel` evaluation behind
`no_cycle_itinerary_three_even_eooeoe` (Appendix A). For \(a\ge 7\),
Lemma 3.11 applies. \(\square\)

**Theorem 3.21 (gapped leftovers as cycle itineraries).**
Let \(n\ge 2\). No cycle itinerary at \(n\) has the form \(O^aEO^bEE\)
with \(a\ge 2\) and \(b\ge 4\), or the form \(O^aEO^bEOE\) with
\(a\ge 2\) and \(b\ge 3\).


*Proof.* Every cycle itinerary has a minimum-based rotation. It is
therefore enough to check that every cyclic shift of either word
is an already-excluded cycle-minimum orientation.

Write \(w\) for the gapped word. In the first family,
\(\lvert w\rvert=a+b+3\). The rotation by \(k=0\) is the original
itinerary, excluded as a cycle minimum by Theorem 3.13. The rotation
by \(k=a+1\) is the bootstrap itinerary \(O^bEEO^aE\). That itinerary has
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

## Appendix E. Absolute return cells and parity obstructions

This appendix consolidates the short-return calculations used in
Section 3.11 and the precise limitations found when trying to extend
them. A prescribed word acts by the displayed branch functions even
when an intermediate parity is wrong. Its *guard* is the conjunction
of the required source parities at every letter. Statements about
prescribed endpoints must therefore be distinguished from statements
about actual Juggler trajectories.

### E.1. Exact short-return endpoints

**Proposition E.1 (root collapse and odd endpoints).** For positive
integers \(N,r,s\),
\[
\left\lfloor\left\lfloor N^{1/r}\right\rfloor^{1/s}\right\rfloor
=\left\lfloor N^{1/(rs)}\right\rfloor.
\]
Consequently
\[
F_{E^k}(x)=\lfloor x^{1/2^k}\rfloor,\qquad
F_{OE^k}(x)=\lfloor x^{3/2^{k+1}}\rfloor.
\]
If \(H=\lfloor x^{9/8}\rfloor\), then
\[
F_{OOE}(x)\in\{H-1,H\}.
\]
In particular an odd \(OOE\) endpoint equals \(Q(x^{9/8})\).
For positive odd \(x\), an odd \(OOEOE\) endpoint similarly equals
\(Q(x^{27/32})\).

*Proof.* For each integer \(j\ge0\), the nested root is at least
\(j\) if and only if \(N\ge j^{rs}\), proving root collapse.
Put \(u=\lfloor x^{3/2}\rfloor\). Then
\(F_{OOE}(x)=\lfloor u^{3/4}\rfloor\).
Concavity, or subadditivity of the \(3/4\) power, gives
\[
0\le x^{9/8}-u^{3/4}<1.
\]
The two possible floors follow; exactly one of two consecutive
integers is odd.

For \(u=F_{OOE}(x)\) and \(x\ge5\), we have \(u\ge6\) and
\(0\le x^{9/8}-u<2\). Concavity now gives
\[
0\le x^{27/32}-u^{3/4}
<\frac32u^{-1/4}<1,
\]
since \(u\ge6>81/16\). Taking the final floor again leaves fewer
than two units of total error. The odd-output conclusion follows.
The remaining odd sources are \(1\), which is fixed, and \(3\),
whose \(OOEOE\) endpoint is the even integer \(2\). \(\square\)

Endpoint compression does not determine the guard. For every odd
\(s\ge3\), the prescribed block
\[
s^4\overset O\longmapsto s^6\overset E\longmapsto s^3
\]
has odd endpoints, but the source of its \(E\) step is odd.
It lies in the threshold band with \(b=s^3\).
Likewise \(13\mapsto46\mapsto311\mapsto17\) has odd endpoints
and the stated \(OOE\) endpoint identity, but both hidden guards fail.

For completeness, a fixed prescribed word also has an exact
floor-loss identity. Let its branch exponents be \(\alpha_j\), its
successive states \(n_j=\lfloor n_{j-1}^{\alpha_j}\rfloor\), its
prefix products \(p_j=\prod_{i\le j}\alpha_i\), and
\[
q_j=p_k/p_j,\qquad
\epsilon_j=n_{j-1}^{\alpha_j}-n_j.
\]
Since \(n_{j-1}^{p_k/p_{j-1}}=(n_j+\epsilon_j)^{q_j}\),
telescoping gives
\[
x^{p_k}-n_k=\sum_{j=1}^k
\bigl((n_j+\epsilon_j)^{q_j}-n_j^{q_j}\bigr).
\]
If every nonempty proper prefix has \(p_j>p_k\), concavity gives the strict upper bound
\[
1+\sum_{j<k}q_jn_j^{q_j-1}.
\]
When the sum is at most \(1\), an odd final output is the odd
projection of \(x^{p_k}\). Each such fixed word eventually has
this property as \(x\) grows, because its finitely many negative
powers tend to zero. This supplies no uniform threshold for
words whose length grows, and does not certify internal parities.
This general fixed-word asymptotic statement remains a written proof.

### E.2. Euclidean return words retain the complete guard

For the rank rotation
\[
T(i)=
\begin{cases}
i+b,&0\le i<a,\\
i-a,&a\le i<a+b,
\end{cases}
\]
suppose the two branches execute chronological words \(A,B\).
Inducing on the prefix of length \(a\), when \(a>b\), gives
\[
(a,b;A,B)\longmapsto(a-b,b;A,AB).
\]
The first branch returns in one step; the second first leaves
the prefix and then returns. For \(b>a\), the prefix of length \(b\)
instead gives
\[
(a,b;A,B)\longmapsto(a,b-a;AB,B).
\]
When \(a=b\), every rank in the prefix of length \(a\) returns
by \(AB\) and is fixed by the induced rank map.
Iterating yields the accelerated formulas, for \(q\ge1\),
\[
(qb+r,b;A,B)\longmapsto(r,b;A,A^qB),\qquad 0\le r<b,
\]
\[
(a,qa+r;A,B)\longmapsto(a,r;AB^q,B),\qquad 0\le r<a.
\]
For example, in the first formula the ranks \(i\ge r\) traverse
\(i+b,\ldots,i+qb\) outside the retained prefix before returning
to \(i-r\). This also proves that the displayed words are first returns.

At each stage the length and letter-count identities are
\[
a|A|+b|B|=L,\qquad av(A)+bv(B)=(o,e),
\]
where \(v\) records the two original letter counts. Column addition
preserves the determinant \(1\) of the word-count matrix.
The return towers partition the original finite set: on each
permutation cycle choose the most recent retained rank while
traversing backwards. Every cycle meets the prefix, since rank
cycles are residue classes modulo \(d=\gcd(o,e)\) and each retained
prefix has at least \(d\) ranks. At termination there are \(d\)
towers, each of length \(L/d\); a primitive cycle has a single tower.

For the full guard \(P_W\), chronological composition is exactly
\[
P_{AB}(x)=P_A(x)\wedge P_B(F_A(x)).
\]
The tower partition therefore transfers every original parity
condition. Fully expanding this representation still gives \(L\)
tests across all retained bases. This is exact symbolic closure;
it does not provide a uniformly shorter arithmetic test for those
guards. The two subtractive rank returns and their word statistics are
formalized. The complete accelerated tower partition remains written;
the existing formal itinerary concatenation theorem
`follows_append` supplies the semantic composition law.

### E.3. An exact quotient form and its failed power substitution

**Proposition E.2 (three-candidate square carry).** Suppose
\(y\ge1\) and \(y^4\le N<(y+1)^4\). Set
\[
u=\operatorname{isqrt}(N),\quad c=u-y^2,\quad
d=\left\lfloor\frac{N-y^4}{2y^2}\right\rfloor,\quad h=\min(d,2y).
\]
Then \(0\le c\le2y\) and
\[
c=h-\kappa,\qquad \kappa\in\{0,1,2\}.
\]
Writing \(a=y^2+h\), choose \(\kappa=0\) if \(a^2\le N\),
\(\kappa=1\) if \((a-1)^2\le N<a^2\), and \(\kappa=2\)
otherwise. For odd \(OE\) endpoints \(x,y\), taking \(N=x^3\)
makes the hidden \(E\)-source guard equivalent to \(c\) being odd.

*Proof.* Write \(N=(y^2+c)^2+\epsilon\), where
\(0\le\epsilon\le2(y^2+c)\). Then
\[
d=c+\left\lfloor\frac{c^2+\epsilon}{2y^2}\right\rfloor\ge c.
\]
If \(c\le2y-1\), then \(c^2+\epsilon\le6y^2-1\), so
\(d-c\le2\). If \(c=2y\), clipping gives \(h=c\).
The adjacent square tests identify the unique correction.
Finally \(u=y^2+c\) is even exactly when \(c\) is odd. \(\square\)

The genuine block \(93\to896\to29\) attains the correction \(2\):
\(d=h=57\), whereas \(c=55\).

**Proposition E.3 (unbounded error of a particular substitution).**
For each odd integer \(s\ge3\), define
\[
\begin{aligned}
x&=s^8+8,& u&=s^{12}+12s^4,\\
v&=s^{18}+18s^{10}+54s^2-1,& z&=s^9+9s-1.
\end{aligned}
\]
These form an actual \(OOE\) block inside the threshold band
\(b=s^8\), with \(x,u,z\) odd and \(v\) even. Its suffix displacement is
\[
c_2=v-z^2=2z-27s^2.
\]
Define the actual and substituted quotients
\[
d_2=\left\lfloor\frac{u^3-z^4}{2z^2}\right\rfloor,\qquad
D=\left\lfloor\frac{x^{9/2}-z^4}{2z^2}\right\rfloor.
\]
Then
\[
D-d_2\in\{36s^2,36s^2+1\},\qquad
\min(D,2z)-c_2=27s^2.
\]
Thus replacing the eliminated integer \(u\) by its continuous
power cannot preserve Proposition E.2 with a uniformly bounded
additive correction.

*Proof.* The three adjacent-square certificates follow from
\[
x^3-u^2=48s^8+512,\qquad
(v+1)^2-u^3=216s^{12}+2916s^4,
\]
\[
(z+1)^2-v=27s^2+1,\qquad
v-z^2=2s^9+18s-27s^2-2.
\]
For \(s\ge3\), the first remainder lies strictly between \(0\) and
\(u\); the second lies strictly between \(0\) and \(v+1\).
The last two expressions are positive. These inequalities give
all three floors; the parities and
\(b\le x,u,z<b^2\le v<b^3\) follow directly.

Put \(R=48s^8+512\). The mean-value theorem bounds
\[
\Delta=\frac{x^{9/2}-u^3}{2z^2}
\quad\text{strictly between}\quad
\frac{3uR}{4z^2}\ \text{and}\ \frac{3(u+1)R}{4z^2}.
\]
Subtracting \(72s^2z^2\) from \(3uR/2\) gives
\[
P=336s^{12}+144s^{11}+3384s^4+1296s^3-72s^2>0.
\]
The corresponding upper excess is \(P+72s^8+768\), and
\[
P+72s^8+768<388s^{12}<2s^{18}<2z^2.
\]
For the first bound use \(144s^{11}\le48s^{12}\) and bound each
of the four remaining positive terms by \(s^{12}\).
It follows that \(36s^2<\Delta<36s^2+1\), proving the assertion
about the two floors. Since \(d_2\ge c_2\), it also follows that
\(D>2z\), giving the clipped difference. \(\square\)

The ideal endpoint is nevertheless within one integer:
\(\lfloor x^{9/8}\rfloor=z+1\).
Taylor's formula gives
\[
0<x^{9/8}-(s^9+9s)<\frac9{2s^7}<1.
\]
The ideal radicand lies outside the original suffix endpoint cell.
Thus Proposition E.3 tests the proposed substitution, rather than
misapplying Proposition E.2 to a radicand in that cell.
It refutes this bounded additive formula; it does not refute all
fixed-register rules or all rules for parity alone.

### E.4. The polynomial growth family has no infinite exact chain

**Theorem E.4 (finite consecutive family chains).** Let
\(X(r)=r^8+8\), for odd integers \(r\ge3\).
If there are \(k\) consecutive transitions
\(J^3(X(r_i))=X(r_{i+1})\) within this family, starting at \(r_0=r\),
then
\[
k\le\max\left(0,\left\lfloor\frac{\nu_2(r-1)-2}{2}\right\rfloor\right).
\]
Every immediate transition requires \(r\equiv1\pmod{48}\).
In particular, no infinite chain can remain in this exact
three-step family description.

*Proof.* Proposition E.3 makes a transition equivalent to
\[
s^8=r^9+9r-9.
\]
For odd \(r,s\), reducing modulo \(32\) gives
\(10(r-1)\equiv0\pmod{32}\), hence \(r\equiv1\pmod{16}\).
The residue \(r\equiv2\pmod3\) is impossible. If \(3\mid r\),
the right side has \(3\)-adic valuation \(2\), whereas an eighth
power has valuation divisible by \(8\). Thus \(r\equiv1\pmod3\).

If the destination \(s\) itself continues, both \(r,s\) are
\(1\pmod{16}\). Factoring the transition after subtracting \(1\) gives
\[
(s-1)(s+1)(s^2+1)(s^4+1)
=(r-1)(r^8+r^7+\cdots+r+10).
\]
The last factor on the right is \(2\pmod{16}\); the last three
factors on the left each have \(2\)-adic valuation \(1\). Therefore
\[
\nu_2(s-1)=\nu_2(r-1)-2.
\]
In a chain of \(k\ge1\) transitions the \(k\) source parameters
all have valuation at least \(4\). The first \(k-1\) valuation
drops give \(\nu_2(r-1)-2(k-1)\ge4\), which is the asserted bound.
The final destination need not continue, and no additional drop
has been assumed there. \(\square\)

For continuing destinations one also has
\(\nu_3(s-1)=\nu_3(r-1)+2\). If \(r=1+3j\), its right-hand
factor is \(18+108j+756j^2\equiv18\pmod{27}\); the other
three left-hand factors are prime to \(3\), since \(s\equiv1\pmod3\).
This additional identity is a written observation and is not needed
for the finite bound.

This excludes escape by endless exact concatenation of this family.
It says nothing about later re-entry, other growth patterns, or
general escape to infinity.
As separate finite computations, the six previously examined parameters
\[
3,\ 5,\ 11,\ 101,\ 10^6+1,\ 10^{20}+1
\]
reach \(1\) after respectively \(28,13,64,24,60,54\) steps.
Their peak decimal lengths are \(111,13,129,41,468,1480\).
The stored integer traces certify every edge by adjacent squares.
These six computations are not a proof about all family members.

### E.5. Retaining the exact first remainder repairs the short quotient

**Proposition E.5 (exact remainder transport).** Consider a prescribed
\(OOE\) block \(x\mapsto u\mapsto v\mapsto z\), with \(u\ge3\).
Set
\[
X=x^3,\quad R=X-u^2,\quad B=X-R=u^2,\quad t=\sqrt X,\quad\eta=t-u.
\]
The remainder record and proposed endpoint must satisfy
\[
B>0,\quad B\text{ is a square},\quad R\ge0,\quad R^2\le4B,\qquad
z^8\le B^3<(z+1)^8.
\]
These conditions certify \(u=\operatorname{isqrt}(X)\) and the
suffix endpoint. Define
\[
\Delta=\frac{t^3-u^3}{2z^2},\qquad C=\frac{3tR}{4z^2}.
\]
Then
\[
C-\Delta=\frac{\eta^2(t+2u)}{4z^2},\qquad
0\le C-\Delta<\frac56.
\]
Consequently, for the integer floors
\[
d=\left\lfloor\frac{u^3-z^4}{2z^2}\right\rfloor,\qquad
q=\left\lfloor\frac{t^3-z^4}{2z^2}-C\right\rfloor,
\]
we have \(d\in\{q,q+1\}\).

*Proof.* The initialized record gives \(0\le\eta<1\) and
\(R=(t-u)(t+u)\). Expansion proves the exact identity.
The endpoint cell gives \(z\ge2\) and \(z^2\ge u\):
otherwise \(u\ge z^2+1\), contradicting
\((z^2+1)^3>(z+1)^4\) for \(z\ge2\). For that comparison, the difference is
\[
z^3(z^3-4)+z(2z^3-3z-4)>0.
\]
It follows that
\[
0\le C-\Delta<\frac{3u+1}{4z^2}
\le\frac{3u+1}{4u}\le\frac56.
\]
The two possible floors are immediate. \(\square\)

The corrected \(q\) is signed and may a priori be \(-1\); the
relation with \(d\ge0\) guarantees \(q+1\ge0\).
There is an exact integer implementation. With \(K=2X-3R>0\),
\[
q=\left\lfloor
\frac{\operatorname{isqrt}(K^2X)-2z^4}{4z^2}
\right\rfloor. \tag{ER1}
\]
This uses
\(\lfloor(\alpha-a)/b\rfloor=\lfloor(\lfloor\alpha\rfloor-a)/b\rfloor\)
for integers \(a,b\), \(b>0\), and the identity
\(\lfloor K\sqrt X\rfloor=\operatorname{isqrt}(K^2X)\).
Negative numerators in (ER1) require floor division.

Put \(h=\min(q+1,2z)\) and \(N=z^2+h\). Proposition E.2 now gives
\[
v=N-\kappa,\qquad\kappa\in\{0,1,2,3\}.
\]
Indeed, for \(c=v-z^2<2z\), we have
\(c\le h\le d+1\le c+3\); if \(c=2z\), clipping gives \(h=c\).
The correction is the smallest \(j\in\{0,1,2,3\}\) for which
\[
(N-j)^4\le B^3.
\]
All candidates are positive, since \(N\ge z^2\ge4\).
For odd endpoints \(x,z\), the complete \(OOE\) guard is exactly
\[
R\text{ even},\qquad N-\kappa\text{ even}.
\]
Thus the absolute record \((x,z,R)\), a new exact square root in
(ER1), and at most four fourth-power comparisons recover both
hidden parities. This does not claim a computational speedup.

For the next word \(OOEOE\), the candidate intermediate endpoint
\(z_*=Q(x^{9/8})\) must first pass the eighth-power cell validation.
Then apply this prefix guard and the \(OE\) cell and guard at
\(z_*\). This yields one further exact composition. It does not
prove uniform arithmetic closure for arbitrarily long induced words.
Retaining the full remainder retains absolute information sufficient
to reconstruct \(u\); it is not a finite-valued summary.

### E.6. Fixed residues do not determine the hidden guard

**Proposition E.6 (a counterfamily for every fixed residue modulus).**
Even retaining the exact first remainder \(R=0\), no fixed finite
collection of residue classes of \(x,u,z\) and
\(\mathcal E=x^9-z^8\) determines the full \(OOE\) guard on its
geometric first-return domain. The two blocks below also share the
same full threshold and first-return section. This statement concerns
those specified summaries, not unrestricted arithmetic in full
absolute values and not a periodic-set invariant.

*Proof.* Let \(Q\ge2\) be any even integer, set \(c=Q-1\), and
choose a positive integer \(b\equiv3\pmod4\) with \(b^2>504c^5\). For \(d=1,-c\), set
\[
t_d=b^4+4d,\quad x_d=t_d^2,\quad u_d=t_d^3,
\]
\[
V_d=b^{18}+18db^{14}+126d^2b^{10}+420d^3b^6+630d^4b^2,
\]
\[
Z_d=b^9+9db^5+\frac{45d^2b-1}{2}.
\]
All these expressions are integers. The exact branches are
\[
O(x_d)=u_d,\quad
O(u_1)=V_1,\quad O(u_{-c})=V_{-c}-1,\quad
E(O(u_d))=Z_d.
\]
The first remainder is exactly zero in both cases.

To verify the floors, put \(A=b^4\), so \(A>8c+4\).
Taylor expansion through degree four gives
\[
(A+4d)^{9/2}=V_d+252d^5\xi^{-1/2},
\]
for \(\xi\) between \(A\) and \(A+4d\).
The remainder has the sign of \(d\), and its magnitude is less
than \(504c^5/b^2<1\), giving the two second images.
Expansion through degree two similarly gives
\[
(A+4d)^{9/4}
=b^9+9db^5+\frac{45d^2b}{2}
+\frac{15}{2}d^3\zeta^{-3/4}.
\]
Its remainder has magnitude less than
\(15c^3/b^3<15/64<1/2\), whereas the polynomial part is a
half-integer. Its floor is therefore \(Z_d\). Root collapse
identifies this with \(E(O(u_d))\).

The states \(x_d,u_d,Z_d\) are odd. The polynomial \(V_d\) is
odd, so the negative-\(d\) block has an even final \(E\) source
and is guard-valid, whereas the positive-\(d\) block fails that guard.
For \(Z_d\), oddness follows from
\(45d^2b-1\equiv2\pmod4\).

These blocks have the same geometric domain. Set \(T=t_{-c}>8\)
and \(B=T^2\). Then \(t_1<2T\), and
\[
B\le x_d,u_d,Z_d<B^2\le O(u_d)<B^3.
\]
For example \(u_1<8T^3<T^4\), and
\(O(u_1)^2\le t_1^9<512T^9<T^{12}\).
Also \(Z_1<T^3=u_{-c}\), so both blocks are first returns to
\[
D=[B,Z_1+1)\cap\mathbb N:
\]
their initial and final points belong to \(D\), and both
intermediate states lie outside it.

Finally
\[
t_1-t_{-c}=4Q,\qquad
Z_1-Z_{-c}=Q\left(9b^5+45b-\frac{45Qb}{2}\right).
\]
Thus \(x_d,u_d,Z_d,\mathcal E_d\) agree modulo \(Q\).
They also have the same exact valuation
\(\nu_2(\mathcal E_d)=3\): since \(t_d\equiv5\pmod8\),
\(x_d\equiv9\pmod{16}\), while \(Z_d^8\equiv1\pmod{16}\).
For any fixed finite list of moduli, choose an even common multiple
as \(Q\). The common data then give opposite guards, proving the
claim. \(\square\)

The formal witness specializes this construction, for any requested
modulus \(q>0\), to \(c=512q-1\) and \(b=c^3\). It verifies the
colliding record, including the exact aggregate valuation \(3\),
and both blocks' common threshold and first-return section. Even
supplying that exact threshold and section boundary to a classifier
of the stated record cannot distinguish the final source parities.
The general free-\(b\) argument above remains a written proof.

The two source values are different, and neither is asserted to
belong to a cycle. The absolute quotient and cell comparisons
in Section E.5 distinguish them. Adding a later intermediate parity
or remainder would also distinguish them.

The dyadic endpoint summary has a related limitation. For a
word of length \(L\ge1\), odd count \(o\), and odd endpoint \(y\),
\[
x^{3^o}-y^{2^L}\equiv x^{3^o}-1\pmod{2^{L+2}}.
\]
For an odd expanding closed return \(y=x>1\), its nonzero
aggregate has valuation \(\nu_2(x-1)\), because \(3^o-2^L\)
is odd. This is endpoint information, not the hidden source guards.
Likewise, an energy formed from squared differences of neighboring
wrong-parity indicators counts changes in those indicators. It can
vanish when every indicator is \(1\); it does not initialize their
correct value.

The analogous aggregate calculation on an actual return permutation
\(y_i=x_{\sigma(i)}\), with peaks \(v_i\) and displacements
\(c_i=v_i-y_i^2\), is only
\[
\sum_i c_i=\sum_i v_i-\sum_i x_i^2.
\]
It is not a zero-sum identity. Even bases restricted to distinct odd
integers admit all even-step cells by setting
\(v_i=x_{\sigma(i)}^2+1\); the omitted odd-prefix equations are essential.
Products of the complete cells similarly return to the existing
floor-defect identities unless a further estimate is supplied.
Theorem 3.39 uses the coupled periodic order and actual odd-prefix
cells to obtain a restriction beyond these bookkeeping identities.
The uniform wrong-parity conclusion remains open.


### E.7. Full arithmetic domains cannot preserve every OOE return

Write \(A=E\circ O\circ O\) for the prescribed three-step map, whether
or not its intermediate states realize the indicated parities. Proposition
E.1 and the growth argument used in Theorem 3.39 give

\[
0\le x^{9/8}-A(x)<2,\qquad A(x)>x\quad(x\ge5).
\tag{E7a}
\]

Consequently a nonempty set \(S\) of odd integers at least five would
give an infinite actual all-\(OOE\) trajectory if every \(x\in S\)
had \(O(x)\) odd, \(O(O(x))\) even, and \(A(x)\in S\).
The following restrictions concern this proposed invariant domain, rather
than an arbitrary trajectory.

**Proposition E.7 (eventually periodic domains).** Every odd residue
class modulo an even positive integer contains arbitrarily large
\(x\) for which \(O(x)\) is even. Hence no nonempty eventually
periodic set of odd integers has the displayed invariant-domain property.

*Proof.* Fix an even integer \(Q\ge2\), an odd residue
\(1\le a<Q\), and an integer \(h\ge1\). Put

\[
t=2Qh,\qquad x=t^8+a,\qquad
u=t^{12}+\frac{3a}{2}t^4.
\]

Then \(x\) is odd and congruent to \(a\) modulo \(Q\), while \(u\) is an even integer.
Direct expansion gives

\[
4(x^3-u^2)=3a^2t^8+4a^3>0,
\]
\[
4((u+1)^2-x^3)
=8t^{12}-3a^2t^8-4a^3+12at^4+4>0.
\]

For the last sign, \(a\le t^2\) implies
\(a^2t^8\le t^{12}\) and \(a^3\le t^6\le t^{12}\), leaving
at least \(t^{12}+12at^4+4\). Thus \(O(x)=u\), which prevents
the second O step. These sources grow without bound with \(h\). An infinite
eventually periodic odd domain contains a tail of one odd residue class
after refining its period to an even modulus. A nonempty finite domain
above four cannot be invariant because \(A(x)>x\). \(\square\)

**Proposition E.8 (one full polynomial value family).** Let \(P\) be a
polynomial of degree \(d\ge2\), with positive leading coefficient,
such that \(P(n)\) is a positive integer for every sufficiently large
integer \(n\). Fix an eventual value set
\(S_P=\{P(n):n\ge n_0\}\). At least one of every three sufficiently
large consecutive integer parameters \(n\) has
\(A(P(n))\notin S_P\).

*Proof.* Let \(\alpha=9/8\), let \(a\) be the leading coefficient of \(P\),
and use the increasing inverse branch of \(P\) near infinity to define

\[
w(t)=P^{-1}(P(t)^\alpha),\qquad
C=a^{(\alpha-1)/d}>0.
\]

Leading terms give \(w(t)\sim Ct^\alpha\). Differentiating the exact
identity \(P(w(t))=P(t)^\alpha\) first gives
\(w'(t)\sim C\alpha t^{\alpha-1}\), and a second differentiation
gives

\[
w''(t)=
\frac{\alpha(\alpha-1)P(t)^{\alpha-2}P'(t)^2
 +\alpha P(t)^{\alpha-1}P''(t)-P''(w(t))w'(t)^2}
 {P'(w(t))}
\sim\frac{9C}{64}t^{-7/8}.
\tag{E7b}
\]

Thus the derivative estimate follows from an exact differentiated
identity, without differentiating an unspecified error term.

If \(A(P(n))=P(s_n)\) with integer \(s_n\ge n_0\), then
\(s_n\sim Cn^\alpha\): sufficiently large outputs force the target parameter onto the increasing tail. The bound (E7a), the mean
value theorem, and \(P'(u)\sim adu^{d-1}\) yield

\[
0\le w(n)-s_n=O(n^{-\alpha(d-1)})=o(n^{-7/8}).
\tag{E7c}
\]

If the three parameters \(n,n+1,n+2\) all return into the family,
integrating (E7b) over the unit square and applying (E7c) gives

\[
s_{n+2}-2s_{n+1}+s_n
=\frac{9C}{64}n^{-7/8}(1+o(1)).
\]

For sufficiently large \(n\) this integer is strictly between zero and one,
a contradiction. \(\square\)

This theorem allows arbitrary integer target parameters \(s_n\);
it assumes no polynomial update rule. Its hypothesis is that the entire
eventual source value family is retained. It does not exclude an orbit
using only a sparse subsequence of parameters. Finite changes to the value
set have no effect, and a fixed arithmetic progression of parameters is
covered by replacing \(P(n)\) with \(P(qn+b)\), for integers \(q>0,b\).
A degree-one polynomial that is integer valued on a full integer tail has
integer slope and constant; if its value tail is odd, Proposition E.7
applies instead.

The valuation in Theorem E.4 is specific to consecutive transitions inside
that family. For example the actual return
\[
199\xrightarrow O2807\xrightarrow O148718\xrightarrow E385
\]
raises \(\nu_2(x-1)\) from one to seven. Neither the family valuation
nor Propositions E.7--E.8 establish a decreasing rank for every actual OOE
return. Existence of an infinite all-OOE trajectory remains open.


## Appendix F. Successive gaps and terminal return words

This appendix supplies the complete written proof of Theorem 3.40
and the terminal accounting of Proposition 3.41. Every application
retains the actual cycle states and all intermediate parity guards.

### F.1. A general floor-loss and paired-gap certificate

For a prescribed word of length \(L\ge1\) with positive integer source \(x\ge1\), let \(a_j=3\) for an
\(O\) letter and \(a_j=1\) for an \(E\) letter. Let \(p_j\) be its ideal prefix
exponents, \(p=p_L\), \(n_j\) its actual integer states, and
\(\varepsilon_j=n_{j-1}^{a_j/2}-n_j\in[0,1)\).
The exact square remainder is
\[
R_j=n_{j-1}^{a_j}-n_j^2,\quad 0\le R_j\le2n_j,\quad
\varepsilon_j=\frac{R_j}{\sqrt{n_j^2+R_j}+n_j}.
\]
Thus no remainder or intermediate parity has been replaced by an
independent random choice.

Assume every proper tail \(q_j=p/p_j\), \(j<L\), is below one.
Telescoping gives the exact identity
\[
e_W(x):=x^p-F_W(x)=
\sum_{j=1}^L\bigl[(n_j+\varepsilon_j)^{p/p_j}-n_j^{p/p_j}\bigr].
\]
If the proper states are at least \(m\ge1\), concavity implies
\[
0\le e_W(x)<K_W(m),\qquad
K_W(m)=1+\sum_{j<L}q_jm^{q_j-1}.
\tag{F1}
\]
This remains an absolute-loss estimate when \(p>1\), provided the
proper tails are below one. For the paired conclusion assume \(0<p<1\)
and two traces with sources \(z>w\ge m\) and proper states at least \(m\).
Then, with \(\kappa=p m^{p-1}\),
\[
0\le F_W(z)-F_W(w)<\kappa(z-w)+K_W(m).
\tag{F2}
\]
Consequently the sufficient certificate
\[
2\kappa+K_W(m)\le2
\tag{F3}
\]
forces strict contraction for every input gap at least two. If the
inputs and distinct outputs are odd, the even gap drops by at least two.
The trace hypotheses are supplied by actual cycle membership in every
application below.

### F.2. Two transfers through the first contracting word

**The floor-loss bound.**

For \(C=OOEOOEOE\), all seven proper prefix states satisfy \(n_j\ge x\)
when \(x\ge3\): \(O\) does not decrease a positive integer and
\(A(x)\ge x\), by \(O(O(x))\ge x^2\).
The seven proper tail exponents are
\[
\frac{81}{128},\frac{27}{64},\frac{27}{32},
\frac9{16},\frac38,\frac34,\frac{1}{2}.
\]
They are all below one. The concavity estimate in Section F.1 therefore yields
\[
0\le e_C(x):=x^\gamma-C(x)<1+U(x),\qquad
U(x)=\sum_j q_jx^{q_j-1}.
\]
At \(x\ge2^{24}\), the seven summands are bounded above respectively by
\[
\frac{81}{32768},\frac{27}{524288},\frac{27}{256},
\frac9{16384},\frac3{262144},\frac3{256},\frac1{8192}.
\]
Their sum is \(63121/524288<1/8\). Hence
\[
0\le e_C(x)<\frac98. \tag{F4}
\]
This is unconditional for the prescribed map; it does not discard
any guard in its subsequent application to actual cycle returns.

For \(z>w\ge2^{24}\), concavity now gives
\[
C(z)-C(w)
=z^\gamma-w^\gamma+e_C(w)-e_C(z)
<\gamma w^{-13/256}(z-w)+\frac98.
\]
Also
\[
\gamma w^{-13/256}<\frac{27}{64}.
\]
Indeed \(w^{13/256}\ge2^{39/32}>2^{6/5}>9/4\);
the last comparison follows by fifth powers from \(2^{16}>3^{10}\).
For \(d\ge2\),
\[
\frac{27}{64}d+\frac98<d,
\]
since \((37/64)d\ge37/32>9/8\).
Monotonicity of the prescribed branch maps supplies the lower bound
in the paired estimate above. This proves the strict gap contraction.

**Growing comparison words.**

For \(x\ge16\),
\[
A(x)>\frac78x^{9/8},\qquad B(x)\ge\frac78x^{3/4}.
\]
Here \(A(x)>x^{9/8}-2\) is the exact two-cell bound and
\(B(x)=\lfloor x^{3/4}\rfloor\).
All intermediate \(A\)-iterates stay at least \(x\). Consequently
\[
A^3B(x)\ge
\left(\frac78\right)^{907/256}x^{2187/2048}
>\frac{1}{2}x^{2187/2048}>x
\quad(x\ge2^{15}).
\tag{F5}
\]
The coefficient exceeds \(1/2\) because \(907/256<4\) and
\((7/8)^4>1/2\). The final comparison follows from
\(15\cdot139=2085>2048\).

Now set \(\alpha=9/8\), \(u=A(x)\), \(v=C(u)=A^3B(x)\).
For \(x\ge2^{24}\), both \(u,v\ge x\). Concavity and (F4) give
\[
0\le x^{\alpha\gamma^2}-D(x)
<2\gamma^2u^{\gamma^2-1}
 +\frac98\gamma v^{\gamma-1}+\frac98
<\frac{17}{4}.
\]
The exponent is \(\alpha\gamma^2=531441/524288\).
Since \(24\cdot7153/524288>1/4\) and \(2^{1/4}>9/8\),
\[
D(x)>\frac98x-\frac{17}{4}>x
\quad(x\ge2^{24}).
\tag{F6}
\]

**The forced first two batches.**

Order the retained set as \(Y=\{y_0<\cdots<y_{a+b-1}\}\).
Its lower \(a\) bases execute \(A\); its upper \(b\) bases execute \(B\).
The return sends rank \(i\) to \(i+b\) below \(a\), and to \(i-a\)
above it. Both counts are positive: \(A(x)>x\) and \(B(x)<x\)
throughout the present domain.

We have \(a>2b\). Otherwise the full return word has ideal exponent
at most
\[
(9/8)^{2b}(3/4)^b=(243/256)^b<1,
\]
and its prescribed floor composition cannot return a start \(>1\)
to itself.

Write \(a=qb+r\), \(0\le r<b\). Thus \(q\ge2\).
If \(r>0\), the maximal left batch has words \(A,A^qB\),
counts \(r,b\), and its upper branch strictly decreases rank.
If \(r=0\), its terminal return \(A^qB\) fixes the retained prefix.
For \(q\ge3\), (F5) makes \(A^qB(x)>x\), contradicting either case.
Therefore
\[
a=2b+r,\qquad 0<r<b,
\]
and the new pair is \(A,C\).

Write \(b=pr+s\), \(0\le s<r\).
If \(p\ge3\), the next lower word \(AC^p\) has ideal exponent at most
\[
(9/8)(243/256)^3=129140163/134217728<1.
\]
It cannot increase rank in a nonterminal return, or fix a terminal
prefix. If \(p=1\), the next strict left step makes
\((AC)C=D\) an upper branch that must decrease rank, contrary to
(F6). Finally \(p=2,s=0\) makes \(D\) the terminal fixed return,
also contrary to (F6). Hence
\[
b=2r+s,\qquad 0<s<r.
\tag{F7}
\]
Both right steps are genuine, with at least two retained bases.
This proof applies to normalized threshold cycles on this domain
before actual parity is imposed.

**The two genuine transfers.**

Initially
\[
w=y_{b-1}=B(t),\qquad z=y_b=A(m).
\]
A left induction step retains the prefix of length \(a\).
Its new largest base \(t_1=y_{a-1}\) satisfies \(A(t_1)=t\),
so its upper return \(AB(t_1)=w\). Its lower minimum image
is still \(z\). The next left step again gives the same pair.
Neither step supplies an additional independent gap.

After the maximal left batch the counts are \(r,b\).
At the first right step the boundary pair becomes
\[
(w_1,z_1)=(C(w),C(z))
 =(y_{b-r-1},y_{b-r}).
\]
At the second right step it becomes
\[
(w_2,z_2)=(C(w_1),C(z_1))
 =(y_{s-1},y_s).
\]
The indices exist by (F7). Every source and intermediate state
is part of a genuine return tower in the original cycle. In an
actual Juggler cycle, all four transferred endpoints and \(w,z\)
are odd, and both transferred gaps are positive even integers.

Put \(d_j=z_j-w_j\) and
\(\kappa=\gamma m^{-13/256}<27/64\).
Since every transferred source is at least \(m\), the paired estimate above gives
\[
d_1<\kappa d_0+\frac98,\qquad
d_2<\kappa d_1+\frac98.
\tag{F8}
\]
Each even positive gap drops by at least two. Thus \(d_0\ge6\).
Also
\[
2\le d_2<\kappa^2d_0+\frac98(1+\kappa),
\]
and therefore
\[
d_0>\frac{2-\frac98(1+\kappa)}{\kappa^2}
 \ge\frac{205}{512\kappa^2}
 =\frac{26240}{59049}m^{13/128}.
\]
This proves the gap bound in (SR1). Retaining \(\kappa\) gives the sharper expression
\[
d_0>
\frac{57344}{59049}m^{13/128}
-\frac{32}{27}m^{13/256}.
\]

### F.3. The next batch and the 65-letter return

The next word \(W=D^3C\) has ideal exponent \(\rho=3^{41}/2^{65}\). For every integer \(x\ge2^{128}\), we prove \(0\le x^\rho-W(x)<6/5\); for integers \(z>w\ge2^{128}\) with \(d=z-w\ge2\), we prove \(0\le W(z)-W(w)<\rho w^{\rho-1}d+6/5<d\).

**The next forced batch.**

Section F.2 leaves the pair \(D,C\) with counts \(r,s\), \(r>s>0\).
The ideal exponent of a complete return is
\(\delta^r\gamma^s>1\), since all floors lie below their ideal powers
and a cycle returns a start greater than one to itself.
Since \(\delta^3\gamma=\rho<1\), we must have \(r>3s\).

Write \(r=ks+u\), \(0\le u<s\). Thus \(k\ge3\).
The next upper word is \(D^kC\) when \(u>0\); when \(u=0\),
the terminal concatenation \(D^kC\) fixes the remaining ranks.

The comparison word \(V=D^4C\), with exponent \(\eta=\delta^4\gamma=3^{53}/2^{84}\), strictly grows on \(x\ge2^{128}\).
Here is a direct finite-word proof. Each nonempty proper prefix of
\(C\) has exponent at least \(\alpha\). Each nonempty proper prefix
of \(D=AC^2\) has exponent greater than \(\delta\).
It follows that every nonempty proper prefix of \(V\) has exponent
at least \(\delta>\eta\). Therefore all its 83 proper tails are below
one. Every actual prescribed state is at least one, so (F1) gives
\[
0\le x^\eta-V(x)<84.
\]
The exact rational comparisons
\[
\eta>1+\frac1{512},\qquad (9/8)^4<2
\]
give, for \(x\ge2^{128}\),
\[
V(x)>x^\eta-84>\frac98x-84>x.
\]
Also \(D(x)>x\) on this range by Section F.2. Monotonicity therefore
gives \(D^kC(x)\ge D^4C(x)>x\) for \(k\ge4\), contrary to either an
upper branch decreasing rank or a terminal fixed return.
Thus \(k=3\), and \(r>3s\) excludes \(u=0\). This proves \(r=3s+u,\ 0<u<s\).

**The exact error certificate.**

For \(W=D^3C\), every proper prefix exponent is at least
\(\delta>\rho\), by the same block calculation. All proper actual
states are at least the source \(x\ge2^{128}\): \(D\) grows, its
proper states stay above its source by the \(A,AC\) growth statements
in Section F.2, and the proper \(C\) states stay above their source.

Let \(p_j\) run through the 64 proper prefix exponents and put
\(q_j=\rho/p_j\). The exact dyadic majorant at \(m=2^{128}\) is
\[
\begin{aligned}
U_W(m)&:=\sum_{j=1}^{64}q_jm^{q_j-1}\\
&\le\sum_{j=1}^{64}
       \frac{q_j}{2^{\lfloor128(1-q_j)\rfloor}}\\
&=\frac{277910493483851358096413315698577150111783}{2^{140}}
 <\frac15.
\end{aligned}
\tag{F9}
\]
This is a finite rational identity obtained by expanding the prescribed
word \(D^3C\); the verifier records every prefix, tail and summand.
Equations (F1) and (F9) prove the claimed absolute-loss bound.

For the slope, the exact comparisons
\[
128(1-\rho)>\frac{10}{7},\qquad
2^{10}3^7>8^7
\]
imply \(m^{1-\rho}>2^{10/7}>8/3\), hence
\[
\kappa_W:=\rho m^{\rho-1}<\frac38.
\]
Since \(2(3/8)+6/5=39/20<2\), (F2) proves the claimed paired contraction.

**A third genuine transfer.**

The preceding two \(C\) transfers end at
\[
(w_2,z_2)=(y_{s-1},y_s).
\]
The next three left steps keep this exact boundary unchanged.
After them the retained counts are \(u,s\), with words \(D,W\).
Both seam points belong to the upper domain, because \(0<u<s\).
Its first right step is therefore genuine and gives
\[
(w_3,z_3)=(W(w_2),W(z_2))
          =(y_{s-u-1},y_{s-u}).
\tag{F10}
\]
All indices exist. Every intermediate is in a first-return tower of
the same original cycle; the sources and endpoints are at least \(m\).
All four seams are pairs of distinct odd cycle states.
Nothing in this step supplies a fourth or a terminal pair.

Write \(d_j=z_j-w_j\) and
\(\kappa_C=\gamma m^{-13/256}<1/64\).
The three valid inequalities are
\[
d_1<\kappa_Cd_0+\frac98,\quad
d_2<\kappa_Cd_1+\frac98,\quad
d_3<\kappa_Wd_2+\frac65.
\]
All four gaps are positive even integers, so \(d_0\ge8\). More generally,
\(n\) strict transfers between even natural gaps give
\(d_0\ge d_n+2n\), and hence \(d_0\ge2(n+1)\) if the final gap is
positive. This finite statement does not supply any additional valid
transfer. Moreover,
\[
2\le d_3<
\kappa_W\kappa_C^2d_0+
\frac98\kappa_W(1+\kappa_C)+\frac65.
\]
The remaining numerator has the exact lower bound
\[
\frac45-\frac98\frac38\frac{65}{64}
=\frac{7609}{20480}.
\]
Therefore
\[
\begin{aligned}
d_0&>\frac{7609}{20480\,\rho\gamma^2}m^\sigma\\
&>\frac{121744}{295245}m^\sigma
 >\frac25m^\sigma.
\end{aligned}
\]
The rational comparisons \(125/128<\rho<127/128\) give
\(7/64<\sigma<1/8\). This proves the gap bounds in (SR2).

### F.4. Transporting a seam gap to the maximum

The original exact cells from Theorem 3.39 are
\[
t^3+2\le[w(w+2)]^2,\qquad
M+2\le(t+1)^2,\qquad z^8\le m^9.
\]
The gaps at least six and eight give the respective integer restrictions
\[
t^3+2\le[(z-6)(z-4)]^2,\qquad
t^3+2\le[(z-8)(z-6)]^2.
\]
All factors are positive because \(w\ge m>0\).

For a common smooth consequence, suppose that \(m\ge2^{24}\),
\(0<\nu\le1/8\), and
\[
H:=z-w-1>\frac13m^\nu.
\]
Set
\[
X=m^{9/8},\qquad a_*=m^{3/2},\qquad
R=\frac13m^{3/8+\nu}.
\]
We have \(0<w+1=z-H\le X-H\). The elementary inequality
\((1-u)^{4/3}\le1-u\), \(0\le u\le1\), gives
\[
t<(w+1)^{4/3}\le(X-H)^{4/3}
\le X^{4/3}-X^{1/3}H<a_*-R.
\]
Here \(R\ge m^{3/8}/3\ge512/3>8\), and
\(R/a_*\le1/(3m)<1/4\). Hence
\[
R^2\le a_*R/4,\qquad 2a_*\le a_*R/4.
\]
All quantities being squared are positive, and
\[
\begin{aligned}
M&<(a_*-R+1)^2-2\\
 &=a_*^2-2a_*R+R^2+2a_*-2R-1\\
 &<a_*^2-\frac32a_*R
  =m^3-\frac{1}{2}m^{15/8+\nu}.
\end{aligned}
\tag{F11}
\]

For the two-transfer case \(d_0=z-w\ge6\), so
\[
H=d_0-1\ge\frac56d_0>
\frac{65600}{177147}m^{13/128}>\frac13m^{13/128}.
\]
Taking \(\nu=13/128\) proves (SR1).
For three transfers \(d_0\ge8\), and
\[
H\ge\frac78d_0>\frac7{20}m^\sigma>\frac13m^\sigma.
\]
Taking \(\nu=\sigma\in(7/64,1/8)\) proves (SR2) and (SR3).

An integer ceiling can be evaluated without real powers. In the first
case take the least even \(G\ge6\) with
\((59049G)^{128}>26240^{128}m^{13}\); in the second, take the least
even \(G\ge8\) with \((5G)^{64}>2^{64}m^7\).
Then \(d_0\ge G\). Let \(z_*\) be the greatest odd integer with
\(z_*^8\le m^9\), and \(T\) the greatest positive odd integer satisfying
\[
T^3+2\le[(z_*-G)(z_*-G+2)]^2.
\]
The necessary ceiling is \(M\le(T+1)^2-2\). The latter recipe uses
the clean \(7/64\) gap exponent, rather than the sharper \(\sigma\).
At the single illustrative input \(m=2^{128}+1\), it gives \(G=6554\).
This is a conditional arithmetic evaluation, not a periodic orbit.

### F.5. The terminal mixed-word passage

At a retained stage with words \(U,V\), exponents \(\lambda,\mu\),
and counts \(a,b\), the exact exponent invariant is
\[
\lambda^a\mu^b=\frac{3^o}{2^L}>1.
\]
Left and right substitutions preserve it:
\[
\lambda^{a-b}(\lambda\mu)^b
=\lambda^a\mu^b
=(\lambda\mu)^a\mu^{b-a}.
\]
For a primitive cycle the final two-base stage is \(\{m,v\}\), with
\[
U(m)=v,\qquad V(v)=m.
\]
The terminal word \(UV\) fixes \(m\), has ideal exponent
\(p=\lambda\mu=3^o/2^L>1\), and has exact loss
\[
e_{UV}(m)=m^p-m.
\tag{F12}
\]
Applying \(V\) also to \(m\) would be an off-domain prescribed
evaluation: periodicity supplies neither its cycle membership nor
its guard pattern. The upper point disappears when the section
becomes \(\{m\}\). Even strict contraction for every earlier selected
upper map would only decrease finitely many positive gaps; it would
not manufacture a surviving terminal pair.

To exclude this terminal return one needs an absolute-loss estimate
strictly below the positive excess \(m^p-m\), or a new incompatible
shared-cell constraint. Bounds on the difference of two losses do
not by themselves supply that absolute calibration. Equation (F12)
alone is a restatement of closure, not a new no-cycle result.

There is a more informative way to account for the terminal pair without
inventing an extra same-word return. At every induced stage there are
chronological words \(P,Q\) such that
\[
UV=P\,OE\,Q,\qquad VU=P\,EO\,Q.
\tag{F13}
\]
Initially \(U=A,\ V=B,\ P=O,\ Q=OE\), and direct concatenation verifies
both identities. A left substitution \((U,V)\mapsto(U,UV)\) changes
\(P\) to \(UP\) and keeps \(Q\). A right substitution
\((U,V)\mapsto(UV,V)\) keeps \(P\) and changes \(Q\) to \(QV\).
These rules prove (F13) by induction.


The same substitutions give an exact count invariant. Write
\(o(W),e(W)\) for the odd and even letter counts of a word. Then
\[
o(U)e(V)-o(V)e(U)=1.
\]
The initial vectors are \((2,1)\) and \((1,1)\); either substitution
adds one vector to the other and preserves the determinant. Thus both
count vectors are primitive. If
\(L=a|U|+b|V|\) and \(o=a\,o(U)+b\,o(V)\), the same integer change of
coordinates gives \(\gcd(a,b)=\gcd(L,o)\). Positive coprime section
counts reach \((1,1)\) by strict subtraction, since \(a+b\) decreases
until equality. The guard-preserving induction must accompany these
count identities; the identities alone do not construct an actual orbit.

At the final primitive two-base stage write the bases as \(\{m,v\}\),
so \(U(m)=v,\ V(v)=m\). They are the two smallest original cycle
states and hence adjacent. Their full-cycle words \(UV,VU\) first
apply the same \(P\). Common letters preserve adjacency inside the
ordered cubic-band cycle until their labels diverge. Thus \(P\)
sends \((m,v)\) to \((h,s)\), the largest odd source and smallest
even source. The differing words \(OE,EO\) then send that pair to
\[
(t,q)=(E(M),O(m)),
\]
and the common suffix \(Q\) sends \((t,q)\) back to \((m,v)\).
All these statements concern the actual two cycle traces, with every
guard and square remainder retained.

The mixed two-step passage itself strictly contracts for an actual
cubic-band cycle with odd \(m\ge3\). Indeed
\[
h<m^2,\qquad s\ge m^2+1,\qquad
t=\lfloor h^{3/4}\rfloor,\qquad
q=\lfloor(m^2)^{3/4}\rfloor.
\]
The extra unit in the lower bound for \(s\) uses its even parity and
the odd parity of \(m^2\). The normalized cycle order gives \(t<q\).
Since the derivative of \(x^{3/4}\) is below one for \(x\ge h\ge3\),
\[
0<q-t
<(m^2)^{3/4}-h^{3/4}+1
<m^2-h+1\le s-h.
\tag{F14}
\]
This closes the pair passage geometrically through the mixed block.
It does not give a net contraction of the complete passage:
the common prefix \(P\), which grows during left inductions, has
not been controlled by the previous right-transfer estimates.
Right-transfer words assemble \(Q\); the existing bounds control only
the factors already certified.

The exact ideal exponents make the missing comparison explicit:
\[
p_P\frac34p_Q=\frac{3^o}{2^L}>1.
\tag{F15}
\]
Therefore simply multiplying ideal powers cannot turn (F14) into
a contradiction. A successful gap proof needs an exact bound that
compares amplification through \(P\) with loss through the mixed
block and \(Q\). The local inequality (F14) is an elementary
floor-cell consequence; the new bookkeeping explains precisely
which part of the terminal argument it does and does not control.

### F.6. The limitation of a fixed-minimum certificate

Even if every inner loss were omitted optimistically, (F3) would
require \(p m^{p-1}\le1/2\). For a word with a proper prefix,
\(K_W(m)>1\), so it actually requires the strict inequality
\[
m>(2p)^{1/(1-p)}\qquad (1/2<p<1).
\tag{F16}
\]
As \(p\to1^-\), the logarithm of this threshold grows like
\((\log2)/(1-p)\). At any fixed \(m\), the slope
\(p m^{p-1}\to1\), so (F3) eventually fails even before its
positive inner-loss terms are added.

This is a rigorous limitation of the specified sufficient certificate.
It is not a counterexample to the true paired map inequality.
Correlations between the two traces could conceivably improve the
bound on \(e_W(w)-e_W(z)\).

The qualification matters: not every possible later cycle-selected
upper word has been proved to have exponent below one, or all its
proper tails below one. Close to termination, a word of ideal exponent
slightly above one can still decrease because of floors. One may not
silently impose the infinite ideal Euclidean itinerary on an actual
finite cycle.


## 7. Acknowledgments and use of AI

The author used large language models throughout the development of this
work, including drafting and revising the prose, proposing and developing
proof arguments, writing Lean formalizations, and designing and implementing
computations. The September 2026 review with OpenAI Codex checked the
mathematical claims and references, corrected the finite-window estimate,
revised the rotation-cell argument and several hypotheses, distinguished
formal proofs from numerical evidence, and prepared the document build and
independent numerical audit. AI assistance is not independent mathematical
validation. The explicit evidence boundaries in Section 1.2 and Appendix A
apply to these contributions. The author is responsible for the statements,
proofs, code, and final verification of this preprint.

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
15. G. Rhin, “Approximants de Padé et mesures effectives
    d'irrationalité,” in *Séminaire de Théorie des Nombres, Paris
    1985--86*, Progress in Mathematics 71, Birkhäuser, Boston, 1987,
    155--164.
    [doi:10.1007/978-1-4757-4267-1_11](https://doi.org/10.1007/978-1-4757-4267-1_11).
16. P. Cochin, “Five-Step Descent Certificates for the Juggler Map:
    Parity Statistics of Nested Floor Powers,” companion manuscript
    (Paper B), revision of 10 September 2026.
    [Source manuscript](https://github.com/sneakyweasel/btlab/blob/main/docs/theory/juggler_parity_discrepancy_note.md).
17. P. Cochin, “Fate Contagion and Termination Criteria for the Juggler
    Map,” companion manuscript (Paper C), revision of 9 September 2026.
    [Source manuscript](https://github.com/sneakyweasel/btlab/blob/main/docs/theory/juggler_fate_almost_all_note.md).

18. M. R. Herman, "Sur la conjugaison différentiable des difféomorphismes
    du cercle à des rotations," *Publ. Math. IHÉS* 49 (1979), 5--233,
    Theorem 3.1, p. 73.
    [doi:10.1007/BF02684798](https://doi.org/10.1007/BF02684798).
