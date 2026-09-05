---
title: Parity equidistribution of nested floor powers, with descent applications to the Juggler map
author: Philippe Cochin
date: 4 September 2026
subtitle: Working draft. Not submitted.
header-includes:
  - \AtBeginDocument{\author{Philippe Cochin \\ \texttt{philippe@cochin.fr}}}
---

## Abstract

For odd \(n\) set \(m=\lfloor n^{3/2}\rfloor\), \(v=\lfloor m^{3/2}\rfloor\),
and so on: the integer chains obtained by iterating \(x\mapsto\lfloor
x^{3/2}\rfloor\) and \(x\mapsto\lfloor\sqrt x\rfloor\) in a prescribed
pattern. We prove complete depth-4 parity equidistribution for
odd-rooted itineraries, with power savings: every pattern of depth at
most four over odd starts receives its expected share. The obstacle
at depth two and beyond is that the naive expansion of \(m^{3/2}\)
leaves the sawtooth \(\{n^{3/2}\}\) with an amplitude that grows like
\(n^{3/4}\), which defeats the classical van der Corput method. The
proof reorganizes the phase by an exact linearization —
\(m^{3/2}=\tfrac32mn^{3/4}-\tfrac12n^{9/4}+O(n^{-3/4})\) with a
one-signed remainder, a Taylor rewrite that keeps the integer \(m\)
linear with a smooth coefficient — and funnels the deeper patterns
into a single *kernel*: the exponential sum of the level-2 floor
defect \(\{\lfloor n^{3/2}\rfloor^{3/2}\}\) against the monomial
weight \(c=\tfrac{3k}4 n^{9/8}\). The fundamental obstruction inside that kernel is
the exact level-2 wave \(e(q\lfloor n^{3/2}\rfloor^{3/2})\) riding a
frozen floor; Lemma 5.2 bounds these mixed pieces by
\(|q|^{-1/6}P^{23/24+\varepsilon}\), uniformly enough for depth four,
and the central result (Theorem 5.3), \(K_c\ll P^{1-1/96+\varepsilon}\),
follows by double Weyl differencing over an exact carry-branch
decomposition and master identity. All thresholds are effective: no
divisor or gcd average occurs anywhere in the argument, so every
\(\varepsilon\) is a power of \(\log P\) --- Theorem 5.3 holds in
the form \(K_c\ll P^{1-1/96}\log^{3/4}P\) --- and the thirty-seven
threshold inequalities of the proof are solved individually in
Appendix A, giving \(P_0=8.9\cdot10^{13}\). The depth-\(\le3\) discrepancy
estimates (Theorems 4.4 and 4.7) are also proved on sub-dyadic
intervals of length \(\ge P^{1/2}\), with a slowly varying twist
attached (Section 3.5), which is the form a companion paper needs.
The kernel theorem itself remains a dyadic-block statement.

The sequences arise as the itineraries of the Juggler map
\(J(n)=\lfloor\sqrt n\rfloor\) (\(n\) even), \(\lfloor n^{3/2}\rfloor\)
(\(n\) odd), whose finite exact theory is developed in a companion
manuscript [22]. As a corollary, the class of starts carrying a
uniform power-envelope descent certificate of length at most five has
certificate density \(7/8\); the four-step subclass has certificate
density \(13/16\). An unconditional counting argument shows that parity
equidistribution at *all* depths would give density one to the set of
starts with some finite descent certificate. None of these is a
density of starts that reach \(1\), and no statement about the
Juggler conjecture itself is claimed. What is solved here is the first
genuinely nested layers of the parity process, not the infinite-depth
problem: the remaining obstacle is the level-3 kernel, where the
weight scale \(n^{27/16}\) exceeds \(n\); we state it as an open
problem and record precisely what blocks every method of this paper,
and what the depth-4 results do and do not buy for the termination
problem.

## 1. Introduction

Equidistribution questions for a *single* floor of a smooth function —
the Piatetski–Shapiro tradition — are classical and well developed.
This paper concerns the *composition* of floors:
\[
m=\lfloor n^{3/2}\rfloor,\qquad
v=\lfloor m^{3/2}\rfloor,\qquad
w=\lfloor m^{1/2}\rfloor,\qquad
z=\lfloor v^{3/2}\rfloor,\ \ldots
\]
and, specifically, the joint distribution of the *parities* along such
chains. Fix a pattern (an *itinerary word*) \(w_1w_2\cdots w_d\) over
the alphabet \(\{E,O\}\), where an \(O\) applies
\(x\mapsto\lfloor x^{3/2}\rfloor\) and an \(E\) applies
\(x\mapsto\lfloor\sqrt x\rfloor\). The question is whether the \(2^d\)
parity classes of the resulting chain equidistribute over odd starts
\(n\le N\), with a power saving. Odd starts have \(w_1=O\); the
theorems of this paper concern the \(O\)-rooted words. (Even starts
are a separate and easier problem: one square root drops the state to
scale \(\sqrt N\), and we make no claims about them.)

The difficulty is genuinely one of composition. Writing
\(\theta=\{n^{3/2}\}\), the naive expansion
\(m^{3/2}=n^{9/4}-\tfrac32\theta n^{3/4}+O(n^{-3/4})\) leaves a
sawtooth of *growing* amplitude \(n^{3/4}\) inside the phase. No
estimate for exponential sums with smooth monomial phases applies; the
phase is not smooth, and the sawtooth cannot be discarded. All results
in the single-floor literature stop before this point (Section 1.2).

Two ideas carry the paper.

1. **Exact linearization** (Lemma 4.3). The identity
   \(m^{3/2}=\tfrac32mn^{3/4}-\tfrac12n^{9/4}+E(n)\) with
   \(0\le E(n)\le\tfrac12n^{-3/4}\) eliminates the inner floor
   *exactly*: the integer \(m\) enters linearly, multiplied by a smooth
   coefficient, and the only non-smooth object left is \(m\) itself,
   which is handled by differencing and by an exact gap-cell
   decomposition. The identity is a Taylor rewrite, not a discovery;
   what carries the paper is the package built on it — one-signed
   remainders at every level, gap cells, the carry-branch
   decomposition, and a kernel with weight \(n^{9/8}\). Iterated along
   the chain, this is what makes depth \(\ge2\) accessible.

2. **The level-2 wave and the kernel theorem** (Lemma 5.2,
   Theorem 5.3). Every reorganization of the depth-4 pattern
   \(OOO*\) funnels into one object, the exponential sum of the
   level-2 floor defect
   \[
   K_c(P)=\sum_{\substack{n\sim P\\ n\ \mathrm{odd}}}
   e\bigl(c(n)\,\{\lfloor n^{3/2}\rfloor^{3/2}\}\bigr),
   \qquad c(n)=\tfrac{3k}4 n^{9/8}.
   \]
   After two Weyl differencings over an exact carry-branch
   decomposition, the master identity (Lemma 5.1) leaves no growing
   smooth part; what remains is bounded carries and, hardest, exact
   level-2 waves \(e(qY)\), \(Y=\lfloor n^{3/2}\rfloor^{3/2}\),
   possibly riding a frozen floor. The depth-2 nested-floor wave is
   the fundamental obstruction of the whole paper, and Lemma 5.2 is
   the result that overcomes it: a bound \(|q|^{-1/6}P^{23/24+\varepsilon}\)
   for these mixed pieces by a targeted third differencing, exactly
   depth-2 strength, which is what pins the kernel saving at
   \(1/96\). We then prove \(K_c(P)\ll P^{1-1/96+\varepsilon}\) for
   \(c=\tfrac{3k}4 n^{9/8}\), uniformly for \(1\le k\le P^{1/24}\)
   (Theorem 5.3). This is the hardest
   result of the paper, and Section 4 is written at full length —
   every estimate displayed with its constant — so that it can be
   checked without reference to anything outside this manuscript.

With the kernel theorem, depth-4 parity equidistribution for
odd-rooted itineraries is complete (Theorem 6.1): the eight
\(O\)-rooted length-4 words each receive their expected share with a
power saving. The same estimates, applied to one further letter, count
the two length-five contractors \(OOOEE\) and \(OOEOE\)
(Theorem 6.3), so the certified descent class has certificate density
\(7/8\) (Corollary 6.4). The leftover eighth is the expanding
length-five tree \(OOEOO\cup OOOEO\cup OOOO*\): the first two of those
itineraries are counted and do not contract, and \(OOOO*\) is the
level-3 kernel. Section 3.5 proves the depth-\(\le3\) theorems on
sub-dyadic intervals of length \(\ge P^{1/2}\) with a slowly varying
twist attached, the form in which the companion paper [24] uses them.
Theorem 5.3 is not localized.

The logical dependence of the counting theorems is
\[
\text{Lemma 5.2(i)}
\;\Longrightarrow\;
\text{Lemma 5.2(ii)}
\;\Longrightarrow\;
\text{Theorem 5.3}
\;\Longrightarrow\;
\text{Theorem 6.1}
\;\Longrightarrow\;
\text{Theorem 6.3 and Corollary 6.4}.
\]
The localization used by the companion [24] is a separate chain and
does not include Theorem 5.3:
\[
\text{Theorems 4.11--4.12 and Corollary 4.13 (Section 3.5)}
\;\Longrightarrow\;
\text{companion [24]}.
\]

The chains are not chosen at random: they are the itineraries of the
Juggler map
\[
J(n)=
\begin{cases}
\lfloor\sqrt n\rfloor,&n\ \text{even},\\
\lfloor n^{3/2}\rfloor,&n\ \text{odd},
\end{cases}
\]
introduced by Pickover [1] (OEIS A094683 [2]); universal arrival at
\(1\) is open. The map is niche; the nested-floor sums must stand on
their own, and the paper is organized so that they do. The exact
finite-itinerary calculus of \(J\) — the power envelope
\(J^{|w|}(n)^{2^{|w|}}\le n^{3^{\#O(w)}}\), the defect identity, and a
small-cycle census — is a companion manuscript [22]; here we use
only the contraction criterion (Proposition 3.1), whose short
induction is written out below. The dynamical payoff
of the counting theorems is a pair of *certified-descent densities*:
the set of starts guaranteed to drop below their starting value
within four steps has certificate density \(13/16\) (Corollary 4.9),
and the two length-five contractors raise that class to certificate
density \(7/8\) (Corollary 6.4). Equidistribution at all depths would
give the set of starts with *some* finite descent certificate density
one (Proposition 7.1). We state plainly what these corollaries are
not: they are not densities of starts that reach \(1\), and they do not
touch the Juggler conjecture, whose analogue of Terras's almost-all
theorem for Collatz [4, 5, 6] remains open; see Lagarias [3] for the
Collatz survey. A second companion paper [24] shows what the
termination problem needs from parity statistics — control at depth
of order \(\log\log n\), not at any fixed depth — and Section 8
records what the fixed-depth results of this paper do and do not
contribute to it.

Section 7 states the frontier precisely. The uncounted piece of the
leftover eighth is the \(OOOO*\) split, one nesting deeper than
Theorem 5.3, where the same kernel reappears with weight scale
\(n^{27/16}>n\) (Conjecture 7.3). Every method of this paper stops
below that scale. What survives is a clean model problem — the
amplitude-product sums \(\sum e(A(t)\{B(t)\})\) with
\(1\ll A'\ll A\) — for which a direct \(L^2\) computation in the
shift of the fractional argument gives square-root cancellation, up
to a \(\sqrt{\log}\) factor, for almost every shift
(Proposition 7.4). That average says nothing about the single
deterministic shift; the deterministic instance (Conjecture 7.5) is
open, and we record in three sentences why the obvious shortcuts
fail.

### 1.1 Verification

Every theorem below is a human proof from the stated classical
inequalities. No numerical computation is a proof step. A companion
repository records machine checks of the exact identities and a
row-by-row audit ledger
([paper_b_audit_ledger.md](paper_b_audit_ledger.md)); nothing in this
paper depends on it. Certificate densities are never densities of
starts that reach \(1\). The six-stage proof of Lemma 5.2(i) is the
author's reconstruction. The reduction of Lemma 5.2(ii) from (i),
and the preservation of the classes (D1), (D2), (D3) under the
third differencing, are written as a self-contained argument
(Claims A–H in the proof of Lemma 5.2).

The boundary between those three kinds of warrant is worth stating once
rather than reconstructing from the citations. *Human proof* means a
proof in this paper; *Lean* lists the identifiers the repository
declares, which are checks of identities, constants and thresholds, not
of any estimate; *classical* names the external result used as given.

| statement | human proof | Lean | classical input |
|---|---|---|---|
| Prop. 3.1 power envelope | companion [22] | in the companion, not here | — |
| Lem. 3.3 second-derivative test | quoted | — | van der Corput [11] |
| Lem. 3.4 discrepancy | quoted | — | Erdős–Turán [8] |
| Lem. 3.5 sawtooth expansion | quoted | — | Vaaler [10] |
| Lem. 3.7 shifted window | this paper | — | Lem. 3.5 |
| Lem. 3.8 two-term test | this paper | `c6_eleven_eighths_five_fourths`(+`_attained`) | Lem. 3.3 |
| Lem. 3.9 three-term sublevel | this paper | `step5b_curvature_inverse`, `step5b_curvature_norm`, `step5b_vector_transfer`, `step5b_c7_printed` | Lem. 3.3, 3.8 |
| Lem. 4.3 exact linearization | this paper | `lemma43_closed_form`, `lemma43_nonneg`, `lemma43_upper`, `lemma43_remainder_of_sqrt`, `carry_identity`, `carry_mem_zero_one` | Taylor |
| Thm. 4.4 nested discrepancy | this paper | — | Lem. 3.3–3.5, 4.3 |
| Thm. 4.7, 4.8 depth three | this paper | — | Thm. 4.4 |
| Thm. 4.11–4.13 localization | this paper | — | Thm. 4.4, 4.7 |
| Lem. 5.1 master identity | this paper | `lemma51_i_identity`, `lemma51_i_closed_form`, `lemma51_i_nonneg`, `lemma51_i_upper`, `lemma51_double_gap`, `lemma51_brackets_le_two`, `lemma51_master`, `carry_as_sawtooth`, `double_difference_product`, `fract_diff_level2`, `mvt_cube_explicit`, `mvt_sqrt_diff_explicit`, `second_difference_exists_xi`, `second_difference_two_sided` | mean value theorem |
| **Lem. 5.2(i), (ii), (iii)** | **this paper** | **none** | Lem. 3.3, 3.5, 3.7, 3.8 |
| Lem. 5.2b interpolant | this paper | `interpolant_assembly`, `interpolant_step_i`, `interpolant_step_ii_constant`, `gap_error_le_one`, `gap_error_one_attained`, `gap_error_not_halved_by_recentring` | — |
| **Thm. 5.3 kernel cancellation** | **this paper** | `step5b_curvature_norm`, `sublevel_raised_threshold` (Step 5b constants only; **no part of the assembly**) | Lem. 5.1, 5.2, 5.2b, 3.9 |
| Thm. 6.1 depth four | this paper | — | Thm. 5.3 |
| Thm. 6.3, Cor. 6.4 depth five | this paper | — | Thm. 5.3 |
| Threshold \(P_0\) (App. A) | computation, not a proof step | `row_5b_binding`, `step5b_c2_ceiling`, `step5b_c2_optimum_feasible`, `step5b_uniform_saturates` | rational arithmetic |
| Prop. 7.1 reduction | this paper | — | Hoeffding |
| Prop. 7.4 shift average | this paper | — | — |

Two rows carry the paper and are the ones to read first. Lemma 5.2 is
proved here and has **no** machine check of any kind; Theorem 5.3 has
two, and both are constants inside Step 5b rather than any step of the
assembly. Everything the repository verifies is an identity, a
constant, or a threshold — it has checked no estimate in this paper,
and a reader who treats the Lean column as corroboration of the
analysis will be misled. The remaining rows are stated so that this
one is unmistakable.

Two conventions in that column. Every identifier listed is declared
under `formal/Problems/` and reachable from the umbrella root
`Problems/Juggler.lean`; there is no root importing exactly this
paper's modules, so the reader who wants to build only these must
select them by hand from the five modules `MasterIdentity`,
`MeanValues`, `MonomialSplitting`, `PaperBAssembly` and
`ThresholdCertificate`. And `ring` appears once in
the text as the tactic that discharges an inversion, not as the name of
a theorem.

### 1.2 Related work

**Single floors.** The distribution of \(\lfloor n^c\rfloor\)
(\(c>1\), \(c\notin\mathbb N\)) in arithmetic progressions and among
primes goes back to Piatetski–Shapiro [12]; Leitmann [13] treated
general smooth \(\lfloor f(n)\rfloor\), and the prime exponent for
\(\lfloor n^c\rfloor\) has a long refinement history, e.g.
Rivat–Sargos [14] and Rivat–Wu [15]. All of these concern a single
floor of a smooth function; the analytic core is an exponential sum
with smooth monomial phase, estimated by van der Corput's method in
the form presented by Graham–Kolesnik [11].

**Digital and parity properties of \(\lfloor n^c\rfloor\).**
Mauduit–Rivat [16] established \(q\)-multiplicative equidistribution
along \(\lfloor n^c\rfloor\) for \(c\) in an explicit range,
Morgenbesser [17] proved the analogous statements for the sum of
digits of \(\lfloor n^c\rfloor\) in residue classes, and
Müllner–Spiegelhofer [23] proved normality of the Thue–Morse sequence
along \(\lfloor n^c\rfloor\) for \(1<c<3/2\). All of these estimate
sums of the shape \(\sum e(f(\lfloor n^c\rfloor))\) where \(f\) is a
*digital* (automatic or \(q\)-additive) function: the outer function
is handled by its own carry structure, and the analytic core is again
a smooth-phase sum over the single floor. Parity of
\(\lfloor n^{3/2}\rfloor\) — our depth-1 statement, Theorem 4.1 — is
the simplest instance of this circle and is classical; we include the
short proof to fix constants and notation. Our outer function is not
digital: it is a second convex power, and its fractional defect enters
later phases with polynomially growing amplitude, which is a different
regime.

**Compositions and generalized polynomials.** Two adjacent theories
compose floors and do not cover our sums. For compositions of *Beatty*
sequences \(\lfloor\alpha\lfloor\beta n\rfloor\rfloor\), the inner
floor error is bounded and the composition is again a
bounded-perturbation linear sequence, so the linear theory applies.
Bergelson–Leibman's generalized polynomials [7] — expressions built
from polynomials by iterated floors, sums, and products — admit a
complete distributional theory via nilmanifolds; but that theory is
confined to maps generated by *polynomials*, and \(n^{3/2}\) is not
one: no nilsystem models \(\{f(\lfloor g(n)\rfloor)\}\) for convex
non-polynomial powers \(f,g\), and the growing-amplitude sawtooth that
drives Sections 3–6 has no analogue there. We are unaware of a
published power-saving estimate for
\(\sum e(\xi\{f(\lfloor g(n)\rfloor)\})\)-type sums, or for the
fractional parts \(\{f(\lfloor g(n)\rfloor)\}\), with \(f,g\) convex
powers and growing \(\xi\).

**Arithmetic of Piatetski–Shapiro sequences.** Baker, Banks, Brüdern,
Shparlinski, and Weingartner [18] study squarefree values, prime
factors, and Carmichael numbers along \(\lfloor n^c\rfloor\);
Glasscock [21] studies linear equations whose unknowns range over
Piatetski–Shapiro sequences. These results intersect a
Piatetski–Shapiro sequence with other arithmetic sets; none composes
two floors.

**Beatty sequences.** For the linear case \(\lfloor\alpha n\rfloor\)
the discrepancy theory is governed by the continued fraction of
\(\alpha\) (three-distance/Ostrowski structure); see Abercrombie [19]
and, for character sums along Beatty sequences, Banks–Shparlinski
[20]. The linear case admits exact self-similar structure that the
convex case \(n^{3/2}\) does not.

**What is not covered.** We are unaware of a published
equidistribution or parity result for *nested* floor powers
\(\lfloor\lfloor n^{c}\rfloor^{d}\rfloor\) with \(c,d>1\), or of a
treatment of the level-2 defect sums \(K_c(P)\) of Section 4. We do
not make the novelty of this paper depend on that survey. What is new
here, independently of the literature, is a specific object and a
specific bound: the level-2 defect kernel
\(K_c(P)=\sum_{n\sim P\ \mathrm{odd}}e(c(n)\{\lfloor n^{3/2}\rfloor^{3/2}\})\)
with smooth weights of scale \(kP^{9/8}\), and the estimate
\(K_c(P)\ll P^{1-1/96+\varepsilon}\) uniformly for \(k\le P^{1/24}\)
(Theorem 5.3), resting on the mixed-piece bound for exact level-2
waves (Lemma 5.2). Both are falsifiable statements about explicit
sums. The obstruction they address is structural, not incremental:
after one floor the argument of the second floor is an integer
sequence, not a smooth function, and its fractional defect enters
later phases with growing amplitude. The individual devices are not
new — the linearization of Lemma 4.3 is a Taylor rewrite, and the
carry bookkeeping of Lemma 5.1 will be recognized by anyone who has
differenced \(\lfloor f(n)\rfloor\); what we believe is new is the
package (one-signed remainders, gap cells, the master identity, and
the kernel bound) and the results it yields. A literature check was
last refreshed in September 2026; we would welcome pointers to
anything missed.

**Dynamical context.** For the Collatz map, Terras [4] and Everett [5]
proved that almost every start has finite stopping time, and Tao [6]
proved that almost all orbits attain almost bounded values; Lagarias
[3] surveys the problem. These are methodological cousins — density
statements through parity-word counting — and motivate
Proposition 7.1; they prove nothing about \(J\), whose branches are
floor powers rather than affine maps.

**Standard tools.** The van der Corput estimates are used in the form
presented by Graham–Kolesnik [11]; see also Iwaniec–Kowalski [9,
Ch. 8]. The indicator expansions use Vaaler's extremal functions [10],
and the discrepancy bridge is the Erdős–Turán inequality in the form
of Kuipers–Niederreiter [8].

## 2. Exact linearization and the parity bridge

Throughout, \(n\) denotes an odd integer, \(e(t)=e^{2\pi it}\),
\(\{x\}\) the fractional part, and \(\psi(x)=(-1)^{\lfloor x\rfloor}\).
On a dyadic block \(n\in(P,2P]\) we write \(n\sim P\). For the chains,
\[
X=n^{3/2},\quad m=\lfloor X\rfloor,\quad \theta=X-m;\qquad
Y=m^{3/2},\quad v=\lfloor Y\rfloor,\quad \theta_2=Y-v;
\]
and on even \(m\), \(U=m^{1/2}\), \(w=\lfloor U\rfloor\),
\(\theta_w=U-w\). The same three letters are reused at later even
states (Theorem 4.8 at \(m\), Lemma 6.2 at \(v\)). An itinerary
word of depth \(d\) at \(n\) is the sequence of parities
\(\mathrm{word}_d(n)\) of \(n,J(n),\ldots,J^{d-1}(n)\). We write
\(\mathrm{word}(n)\) for the infinite itinerary, and say it has
prefix \(w\) when \(\mathrm{word}_{|w|}(n)=w\).

**Proposition 3.1 (power-envelope contraction; companion [22]).**
If the itinerary \(w\) is realized at \(n\ge2\) (the orbit's parities are
the letters of \(w\)) and \(3^{\#O(w)}<2^{|w|}\), then
\(J^{|w|}(n)<n\).

*Proof.* Write \(k=|w|\) and \(m=J^k(n)\). We first prove the
envelope \(m^{2^k}\le n^{3^{\#O(w)}}\), by induction on prefix
length. The empty prefix is \(n\le n\). Suppose a realized prefix
of length \(\ell\) with odd count \(o\) ends at \(x\) and satisfies
\(x^{2^\ell}\le n^{3^o}\), and the next letter is realized. If that
letter is even, then \(J(x)^2\le x\), so
\(J(x)^{2^{\ell+1}}=(J(x)^2)^{2^\ell}\le x^{2^\ell}\le n^{3^o}\). If
it is odd, then \(J(x)^2\le x^3\), so
\(J(x)^{2^{\ell+1}}=(J(x)^2)^{2^\ell}\le x^{3\cdot 2^\ell}
=(x^{2^\ell})^3\le(n^{3^o})^3=n^{3^{o+1}}\). This is the envelope
at \(w\). The exponent gap and \(n\ge2\) give
\(n^{3^{\#O(w)}}<n^{2^k}\), hence \(m^{2^k}<n^{2^k}\). Since
\(m\ge1\), one has \(m<n\). \(\square\)

The companion [22] develops the same envelope as a finite-itinerary
identity with an exact defect; only the contraction criterion is
used below. The induction is recorded here so that the criterion
does not depend on an unpublished text.

An itinerary \(w\) with \(3^{\#O(w)}<2^{|w|}\) is *contracting*; realizing a
contracting itinerary is a *descent certificate* of length \(|w|\).
Contracting words used below: \(E\), \(OE\), \(OOEE\), and the two
length-five words \(OOOEE\) and \(OOEOE\). Every even start realizes
\(E\), and every odd start with even image realizes \(OE\); those two
certificates cover all starts except the odd-to-odd class, which is
where the counting problem lives. Longer contracting itineraries exist
(length seven and eight); this paper makes no counting claims about
them.

**Lemma 3.2 (parity bridge).**
\(\lfloor x\rfloor\) is odd if and only if \(\{x/2\}\ge\tfrac12\).

*Proof.* Write \(x=\lfloor x\rfloor+\{x\}\) and split by the parity of
\(\lfloor x\rfloor\). \(\square\)

**Lemma 3.3 (van der Corput, second-derivative form [11]).**
Let \(f\) be twice differentiable on an interval of length \(M\), with
\(\lambda\le|f''|\le\alpha\lambda\) for some \(\alpha\ge1\). Then
\[
\Bigl|\sum e(f)\Bigr|\ll_\alpha M\lambda^{1/2}+\lambda^{-1/2},
\]
the sum over the integers of the interval.

The Weyl \(A\)-process used in Theorems 4.4 and 5.3 and in
Lemma 5.2 is the following form, applied to a unimodular sequence
on the odd integers of a block of length \(\asymp P\)
(equivalently, in the \(r\)-variable of Lemma 3.10, with shift
\(h\) in \(r\) equal to shift \(2h\) in \(n\)). For
\(1\le H\le P\),
\[
\Bigl|\sum a_n\Bigr|^2
\le\frac{2P^2}H+\frac{4P}H\sum_{1\le h<H}
\Bigl|\sum a_{n+2h}\overline{a_n}\Bigr|.
\]
This is the classical inequality
\(|\sum a_n|^2\le\tfrac{P+2H}H\sum_{|h|<H}(1-\tfrac{|h|}H)
\sum a_{n+h}\overline{a_n}\) with the even-shift restriction and
with the weights \(1-|h|/H\le1\) absorbed in the absolute
constants. Every later appeal to “the classical inequality” is
this display.

**Lemma 3.4 (Erdős–Turán [8]).**
The discrepancy of \(R\) points \(x_j\in\mathbb R/\mathbb Z\) against
an interval satisfies, for every \(H\ge1\),
\[
D\ll\frac RH+\sum_{h=1}^H\frac1h\Bigl|\sum_{j\le R}e(hx_j)\Bigr|.
\]

**Lemma 3.5 (Vaaler [10]).**
For every \(J\ge1\) there are trigonometric polynomials
\(V_J(t)=\sum_{0<|q|\le J}a_qe(qt)\) with
\(|a_q|\le\min(1,\tfrac2{|q|})\) and a nonnegative trigonometric
polynomial \(\Delta_J\ge0\) of degree \(J\) with constant term and
coefficients at most \(1/(J+1)\), such that the period-2 square wave satisfies
\(\psi(x)=V_J(x/2)+O(\Delta_J(x/2))\). For products,
\(|\psi_1\psi_2-V^{(1)}V^{(2)}|\le\Delta^{(1)}+\Delta^{(2)}
+\Delta^{(1)}\Delta^{(2)}\), and each error term is again a
nonnegative trigonometric polynomial of the same shape.

The class indicators below are products of half-wave factors
\(\tfrac12(1\pm\psi)\) evaluated along *formal* chains — chains whose
branches are dictated by the target itinerary, not by the orbit. The next
lemma is the exact identity that justifies this; it replaces any
appeal to sampled verification.

**Lemma 3.6 (branch consistency).**
Let \(d\ge1\) and let \(w=w_1\cdots w_d\) be an itinerary with \(w_1=O\).
For odd \(n\), define the formal chain \(x_1=n\) and, for
\(1\le t<d\),
\[
\xi_t=
\begin{cases}
x_t^{3/2},&w_t=O,\\
x_t^{1/2},&w_t=E,
\end{cases}
\qquad
x_{t+1}=\lfloor\xi_t\rfloor,
\]
and set \(\sigma_t=+1\) if \(w_t=E\), \(\sigma_t=-1\) if \(w_t=O\).
Then, for every odd \(n\),
\[
\prod_{t=1}^{d-1}\tfrac12\bigl(1+\sigma_{t+1}\,\psi(\xi_t)\bigr)
=\bigl[\mathrm{word}_d(n)=w\bigr].
\]

*Proof.* Induct on \(d\). For \(d=1\) both sides are \(1\). Let
\(\Pi_{d-1}\) be the product over \(t\le d-2\); by induction
\(\Pi_{d-1}=[\mathrm{word}_{d-1}(n)=w_1\cdots w_{d-1}]\). If
\(\Pi_{d-1}=0\), both sides vanish, since every factor lies in
\([0,1]\). If \(\Pi_{d-1}=1\), then the orbit realizes
\(w_1\cdots w_{d-1}\), and a second induction along the chain gives
\(x_t=J^{t-1}(n)\) for \(t\le d-1\): assuming \(x_t=J^{t-1}(n)\), the
true parity of \(x_t\) is \(w_t\), so \(J\) applies exactly the
\(w_t\)-branch and \(J^t(n)=\lfloor\xi_t\rfloor=x_{t+1}\). Hence
\(\xi_{d-1}\) is the true real image with
\(\lfloor\xi_{d-1}\rfloor=J^{d-1}(n)\), and the last factor
\(\tfrac12(1+\sigma_d\psi(\xi_{d-1}))\) equals \(1\) exactly when the
parity of \(J^{d-1}(n)\) is \(w_d\), else \(0\). \(\square\)

Each \(\psi(\xi_t)\) is defined for *every* odd \(n\), which is what
permits the unconditional Vaaler expansion of the product: off the
cylinder, the vanishing of an earlier factor kills the term, and on
the cylinder every factor computes the true letter.

The last three preliminaries are the remaining analytic tools of
Section 4: a finite Fourier expansion for sawtooth phases whose
coefficient may exceed \(1\); a second-derivative test for two-term
monomial phases in which the curvature transition — the short set
where the two curvatures cancel — receives a trivial bound; and a
sublevel splitting for three-term monomial phases, again with the
transition set destined for a trivial bound. No third- or
fourth-derivative exponential-sum test is used anywhere in this
paper: on the short cells of Section 4 those tests do not sum, and
the transition sets are cheaper to measure than to oscillate over.
A final remark fixes the parity reindexing once and for all.

**Lemma 3.7 (finite Fourier expansion with a shifted window).**
Let \(B\in\mathbb R\), and let \(T,J\) be integers with \(J\ge1\) and
\(T\ge8(1+|B|)\). There exist coefficients \((b_u)_{|u|\le T}\) with
\[
|b_u|\le\min\Bigl(2,\tfrac1{\pi|u+B|}\Bigr)
+\min\Bigl(2,\tfrac1{\pi|u|}\Bigr),
\qquad
\sum_{|u|\le T}|b_u|\le8+2\log(2+|B|+T),
\]
and coefficients \((v_q)_{0<|q|\le J}\) with
\(|v_q|\le\min(2,2\pi|B|)/|q|\), such that for every \(t\in\mathbb R\)
\[
\Bigl|e(-B\{t\})-\sum_{|u|\le T}b_ue(ut)
-\sum_{0<|q|\le J}v_qe(qt)\Bigr|
\le\min(2,2\pi|B|)\,\Delta_J(t)+\frac{8(1+|B|)}T,
\]
where \(\Delta_J\ge0\) is a trigonometric polynomial of degree \(J\)
with constant term and coefficients at most \(1/(J+1)\).

*Proof.* Write \(f(t)=e(-B\{t\})\) and
\(\sigma(t)=\tfrac12-\{t\}\), the sawtooth with jump \(+1\) at the
integers. The jump of \(f\) at the integers is \(1-e(-B)\), so
\(g:=f-(1-e(-B))\,\sigma\) is continuous, \(1\)-periodic, and
piecewise \(C^1\). Since \(|f|=1\), \(|\sigma|\le\tfrac12\), and
\(|1-e(-B)|=2|\sin\pi B|\le\min(2,2\pi|B|)\le2\), we have
\(|g|\le2\), hence \(|\hat g(0)|\le2\). For \(u\ne0\), direct
integration gives \(\hat f(u)=(1-e(-B))/(2\pi i(u+B))\) when
\(u+B\ne0\) and \(\hat\sigma(u)=1/(2\pi iu)\), so
\[
\hat g(u)=\frac{1-e(-B)}{2\pi i}
\Bigl(\frac1{u+B}-\frac1u\Bigr)
=-\frac{(1-e(-B))\,B}{2\pi i\,u(u+B)} .
\]
Two bounds follow. If \(\pi|u+B|\ge\tfrac12\), the first form gives
\(|\hat g(u)|\le\tfrac2{2\pi}\bigl(\tfrac1{|u+B|}+\tfrac1{|u|}\bigr)
=\tfrac1{\pi|u+B|}+\tfrac1{\pi|u|}\); if \(\pi|u+B|<\tfrac12\), then
\(|\hat g(u)|\le|\hat f(u)|+|1-e(-B)||\hat\sigma(u)|
\le1+\tfrac1{\pi|u|}\le2+\tfrac1{\pi|u|}\). In both cases (and when
\(u+B=0\), where \(|\hat f(u)|\le1\) directly)
\[
|\hat g(u)|\le\min\Bigl(2,\tfrac1{\pi|u+B|}\Bigr)
+\min\Bigl(2,\tfrac1{\pi|u|}\Bigr),
\]
and summing this over \(|u|\le T\) — at most four terms hit each of
the two caps, and the harmonic tails integrate to logarithms — gives
\(\sum_{|u|\le T}|\hat g(u)|\le8+2\log(2+|B|+T)\). The second form
gives, for \(|u|>T\ge8(1+|B|)\) (so \(|u+B|\ge|u|-|B|\ge|u|/2\)),
\[
|\hat g(u)|\le\frac{2|B|}{2\pi}\cdot\frac2{u^2}
=\frac{2|B|}{\pi u^2},
\qquad
\sum_{|u|>T}|\hat g(u)|\le\frac{4|B|}{\pi T}\le\frac{8(1+|B|)}T .
\]
The full series \(\sum_u|\hat g(u)|\) therefore converges, and since
\(g\) is continuous its Fourier series converges to \(g\) everywhere;
take \(b_u=\hat g(u)\) for \(|u|\le T\) and charge the tail to the
flat error. For the sawtooth part, Vaaler's theorem [10] provides a
trigonometric polynomial
\(V^*_J(t)=\sum_{0<|q|\le J}a^*_qe(qt)\) with \(|a^*_q|\le1/|q|\) and
\(|\sigma(t)-V^*_J(t)|\le\Delta_J(t)\) with \(\Delta_J\) as stated;
multiply by \(1-e(-B)\) and set \(v_q=(1-e(-B))a^*_q\). \(\square\)

When the lemma is applied with \(t=G(n)\) along a block, the
\(\Delta_J\)-term is a nonnegative majorant: its sum over the block
is \(P/(J+1)\) plus \(J\)-truncated mode sums of \(G\) with
coefficients \(\le1/(J+1)\), and the flat term contributes
\(8(1+|B|)P/T\). Both costs are displayed at each application below.

**Lemma 3.8 (two-term monomial test with a trivial transition bound).**
Let \(E\subset\mathbb Q\cap[-4,4]\) be a fixed finite set disjoint
from \(\{0,1,2,3\}\), let \(\alpha\ne\beta\) lie in \(E\), let
\(I\subseteq(P,2P]\), and let
\[
f(n)=a\,n^\alpha+b\,n^\beta+g(n),
\qquad
M:=\max\bigl(|a|P^{\alpha-2},\,|b|P^{\beta-2}\bigr)\le1,
\]
where the perturbation satisfies, for every \(n\in I\),
\[
|g''(n)|\le\rho\,\bigl(|a|n^{\alpha-2}+|b|n^{\beta-2}\bigr),
\qquad
|g'''(n)|\le\rho\,\bigl(|a|n^{\alpha-3}+|b|n^{\beta-3}\bigr),
\]
with \(\rho\le\rho_0(E)\) sufficiently small in terms of \(E\) alone.
Then
\[
\Bigl|\sum_{n\in I}e(f(n))\Bigr|
\ll_E |I|\,M^{1/2}+M^{-1/2}+(P/M)^{1/3}.
\]
(If \(M\le P^{-2}\) the third term exceeds \(|I|\) and the bound is
trivial; the content is the range \(M>P^{-2}\).)

*Proof.* Write \(A(n)=a\,\alpha(\alpha-1)\,n^{\alpha-2}\) and
\(B(n)=b\,\beta(\beta-1)\,n^{\beta-2}\), so that
\[
f''=A+B+g'',
\qquad
n\,f'''=(\alpha-2)A+(\beta-2)B+n\,g''' .
\]
On the block, \(|A(n)|\asymp_E|a|P^{\alpha-2}\) and
\(|B(n)|\asymp_E|b|P^{\beta-2}\). The ratio
\(|A/B|=|a\alpha(\alpha-1)/(b\beta(\beta-1))|\,n^{\alpha-\beta}\) is
strictly monotone in \(n\), so for any threshold \(K=K(E)\ge3\) the
block splits into at most three consecutive intervals: \(I_1\) where
\(|A/B|\ge K\), \(I_2\) where \(|A/B|\le1/K\), and a middle
\(I_0\). (If \(a\) or \(b\) vanishes, only \(I_1\) or \(I_2\) is
present and the argument shortens accordingly.)

On \(I_1\): \(|f''|\ge(1-\tfrac1K)|A|-|g''|\ge\tfrac12|A|
\gg_EM\)-scale, with \(\sup|f''|/\inf|f''|\le C(E)\); Lemma 3.3
gives \(\ll_E |I|M^{1/2}+M^{-1/2}\). Symmetrically on \(I_2\).

On \(I_0\), \(|A|\asymp_K|B|\). If \(A\) and \(B\) have the same
sign there, \(|f''|\ge|A|+|B|-|g''|\ge|A|\) and Lemma 3.3 applies
as before. If they have opposite signs, write \(B=-sA\) with
\(s=s(n)\in[1/K,K]\), monotone in \(n\). Then
\[
f''=A\,(1-s)+g'',
\qquad
n\,f'''=A\,\bigl((\alpha-2)-s(\beta-2)\bigr)+n\,g''' .
\]
The two affine functions \(s\mapsto1-s\) and
\(s\mapsto(\alpha-2)-s(\beta-2)\) have distinct zeros: \(s=1\) and
\(s=(\alpha-2)/(\beta-2)\ne1\) (here \(\alpha\ne\beta\) and
\(\beta\ne2\) are used). Hence
\[
c_6(E):=\min_{s>0}\ \max\bigl(|1-s|,\;|(\alpha-2)-s(\beta-2)|\bigr)>0.
\]
Since \(s(n)\) is monotone, the set where \(|1-s(n)|\ge c_6\) is the
complement of a single interval, so \(I_0\) splits into at most three
consecutive intervals: two on which \(|f''|\ge\tfrac12c_6|A|\) (after
absorbing \(g\) by \(\rho_0(E)\le c_6/8\)) — Lemma 3.3 as before —
and one transition interval \(J\) on which
\(|nf'''|\ge\tfrac12c_6|A|\) throughout, i.e.
\(|f'''|\ge c_8(E)\,M/P\) in normalized scale. On \(J\) the second
derivative is strictly monotone. Let \(V\in(0,M]\) be a parameter:
the set \(\{n\in J:|f''(n)|<V\}\) is a single interval of length at
most \(2V/(c_8M/P)\), which receives the trivial bound, and its at
most two flanking intervals carry \(|f''|\ge V\) of a single sign
with \(\sup|f''|\le C(E)M\), so Lemma 3.3 (applied at the piece's
own infimum) gives \(\ll_E|I|M^{1/2}+V^{-1/2}\) for each. Choosing
\(V=(c_8M/P)^{2/3}\) equalizes \(V^{-1/2}\) and the trivial cost at
\(\ll_E(P/M)^{1/3}\). Summing the \(O_E(1)\) contributions proves
the lemma. \(\square\)

The proof's only content is that the second and third derivatives of
a two-term monomial phase cannot both be small on the same
subinterval — the linear system with matrix
\(\bigl(\begin{smallmatrix}1&1\\ \alpha-2&\beta-2\end{smallmatrix}\bigr)\)
is invertible — so the transition set where the second-derivative
test fails is short, and *measuring* it costs less than any attempt
to oscillate over it: crucially, the transition cost \((P/M)^{1/3}\)
carries no factor \(|I|\), so it sums over many short cells. All
applications in Section 4 use exponent pairs from
\(E=\{\tfrac34,\tfrac54,\tfrac{11}8,\tfrac32,\tfrac{15}8\}\).

For that \(E\) the constant \(c_6\) is not merely positive but
computable in closed form: with \(p=\alpha-2\), \(q=\beta-2\), the two
V-shapes \(|1-s|\) and \(|p-qs|\) have distinct zeros \(1\) and
\(p/q\), so the minimum of their maximum is attained at a crossing and
is rational. Over the twenty ordered pairs of \(E\):

| \(\alpha\backslash\beta\) | \(\tfrac34\) | \(\tfrac54\) | \(\tfrac{11}8\) | \(\tfrac32\) | \(\tfrac{15}8\) |
|---|---|---|---|---|---|
| \(\tfrac34\) | — | \(\tfrac27\) | \(\tfrac5{13}\) | \(\tfrac12\) | \(1\) |
| \(\tfrac54\) | \(\tfrac29\) | — | \(\tfrac1{13}\) | \(\tfrac16\) | \(\tfrac59\) |
| \(\tfrac{11}8\) | \(\tfrac5{18}\) | \(\mathbf{\tfrac1{14}}\) | — | \(\tfrac1{12}\) | \(\tfrac49\) |
| \(\tfrac32\) | \(\tfrac13\) | \(\tfrac17\) | \(\tfrac1{13}\) | — | \(\tfrac13\) |
| \(\tfrac{15}8\) | \(\tfrac12\) | \(\tfrac5{14}\) | \(\tfrac4{13}\) | \(\tfrac14\) | — |

The minimum is \(c_6(E)=\tfrac1{14}\), attained only at
\((\alpha,\beta)=(\tfrac{11}8,\tfrac54)\) — there \(p=-\tfrac58\),
\(q=-\tfrac34\) and the crossing is at \(s=\tfrac{13}{14}\), where both
V-shapes equal \(\tfrac1{14}\). Consequently the admissible
perturbation size of this section may be taken to be the explicit
\(\rho_0(E)=c_6/8=\tfrac1{112}\), and every \(\ll_E\) in Lemma 3.8 is a
constant depending only on that number and on \(K\). Lean:
`c6_eleven_eighths_five_fourths` (the lower bound, for all \(s\)) and
`c6_eleven_eighths_five_fourths_attained` (sharpness).

One
corner of Section 4 (three curvature scales meeting on a zero-offset
branch) needs the three-term analogue, which we state directly as a
sublevel bound: there the transition set is measured once against a
global smooth model, and only the second-derivative test is ever
applied.

**Lemma 3.9 (three-term monomial sublevel splitting).**
Let \(E\) be as in Lemma 3.8 and let \(\alpha,\beta,\gamma\in E\) be
pairwise distinct, \(I\subseteq(P,2P]\), and
\[
f(n)=a\,n^\alpha+b\,n^\beta+c\,n^\gamma+g(n),
\qquad
S:=\max\bigl(|a|P^{\alpha-2},|b|P^{\beta-2},|c|P^{\gamma-2}\bigr)>0,
\]
with \(g\) satisfying the analogues of the perturbation bounds of
Lemma 3.8 for the second, third, *and fourth* derivatives, at some
\(\rho\le\rho_0\). There are constants
\(c_7=c_7(\alpha,\beta,\gamma)>0\) and \(C=C(\alpha,\beta,\gamma)\)
such that for every \(V\) with \(0<V\le c_7S/2\):

(i) the sublevel set
\(\Omega_V=\{n\in I:|f''(n)|\le V\}\) is a union of at most \(C(E)\)
intervals of total length
\[
|\Omega_V|\le C(E)\,\Bigl(\frac{PV}S+P\Bigl(\frac VS\Bigr)^{1/2}\Bigr);
\]

(ii) \(I\setminus\Omega_V\) is a union of at most \(C(E)\) intervals,
on each of which \(f''\) is single-signed with
\(V\le|f''|\le C(E)\,S\).
If one of \(a,b,c\) vanishes the claim reduces to Lemma 3.8; if two
vanish, to Lemma 3.3. The application in Theorem 5.3, Step 5b, uses
the three-term statement when a window mode is present and the
two-term reduction when \(w=0\).

*Proof.* Write \(A,B,C\) for the three curvature terms
\(a\alpha(\alpha-1)n^{\alpha-2}\) etc., so that
\[
f''=A+B+C+g'',\quad
nf'''=(\alpha{-}2)A+(\beta{-}2)B+(\gamma{-}2)C+ng''',
\]
\[
n^2f''''=(\alpha{-}2)(\alpha{-}3)A+(\beta{-}2)(\beta{-}3)B
+(\gamma{-}2)(\gamma{-}3)C+n^2g''''.
\]
The coefficient matrix is the Vandermonde-type matrix in the
distinct values \(\alpha{-}2,\beta{-}2,\gamma{-}2\) (rows \(1\),
\(x\), \(x(x{-}1)\)), hence invertible with inverse bounded in terms
of \(E\): at every point of \(I\),
\[
\max\bigl(|f''|,\,|nf'''|,\,|n^2f''''|\bigr)
\ge c_7(E)\max(|A|,|B|,|C|)\ge c_7(E)\,\tilde S,
\qquad\tilde S\asymp_ES,
\]
after absorbing \(g\) by \(\rho_0\le c_7/8\) (zero coefficients only
shorten the argument). The constant depends on the *triple*, not on the
ambient set: \(c_7=1/\lVert M^{-1}\rVert_\infty\), and since
\(\det M=\prod_{i<j}(x_j-x_i)\) with \(x=\alpha-2\) etc., it scales
as the square of the exponent gap. For an equally spaced triple of gap
\(\delta\) about \(x_0\),
\(\delta^2/c_7=x_0^2-2x_0+c\) with \(c\in[1.75,2]\) for
\(\delta\in[\tfrac18,\tfrac12]\). Writing \(c_7(E)\) for a
*uniform* constant over all triples of \(E\) would be weaker: over the
exponent inventory of this paper the minimum is \(1/259\), at
\((\tfrac98,\tfrac54,\tfrac{11}8)\). Each application below uses its
own triple's value.

The proof needs less than a single scalar. What it actually uses is that
the three tests are not *all* small, and that is a condition on a vector
\(c=(c_2,c_3,c_4)\), one constant per derivative order: if
\(\lvert T_j\rvert\le c_j\tilde S\) for \(j=2,3,4\) then
\(\lvert A_i\rvert\le\tilde S\sum_j\lvert M^{-1}\rvert_{ij}c_j\),
so any \(c\ge0\) with \(\lvert M^{-1}\rvert c\le1\) rowwise will do
(Lean `step5b_vector_transfer`). Only \(c_2\) enters the hypothesis
\(V\le c_2S/2\); \(c_3\) and \(c_4\) enter only through \(C\).
Appendix A.5 records what that buys, and what it costs. The ratios \(A/B\), \(B/C\), \(A/C\) are
monotone, so \(I\) splits into \(O_E(1)\) consecutive intervals on
each of which one fixed derivative order \(r\in\{2,3,4\}\) is good at
full scale throughout. On an \(r=2\) piece, \(\Omega_V\) is empty
(as \(V\le c_7S/2\)). On an \(r=3\) piece, \(|f'''|\ge c_7S/(2P)\)
makes \(f''\) strictly monotone, so \(\Omega_V\) meets it in a single
interval of length \(\le4PV/(c_7S)\). On an \(r=4\) piece,
\(|f''''|\ge c_7S/(4P^2)\) makes \(f'''\) strictly monotone, so
\(f''\) has at most one interior critical point and \(\Omega_V\)
meets the piece in at most two intervals; if \([x,y]\subseteq\Omega_V\),
the second-difference identity
\(f''(x)-2f''(\tfrac{x+y}2)+f''(y)=f''''(\xi)\,(y-x)^2/4\) forces
\((y-x)^2\le16V\cdot4P^2/(c_7S)\), i.e.
\(y-x\le8P\,(V/(c_7S))^{1/2}\). Summing the \(O_E(1)\) pieces gives
(i). For (ii): on the complement, \(f''\) is continuous with
\(|f''|\ge V\), hence single-signed on each maximal interval, and
\(|f''|\le|A|+|B|+|C|+|g''|\le C(E)S\). For the triple
\(\bigl(\tfrac54,\tfrac{11}{8},\tfrac32\bigr)\) of Theorem 5.3,
Step 5b, the inverse matrix is
\(\bigl(\begin{smallmatrix}10&68&32\\-24&-144&-64\\15&76&32\end{smallmatrix}\bigr)\);
the norm the argument needs — the \(\ell^\infty\) operator norm,
i.e. the maximal absolute row sum, since
\((A,B,C)^{\mathsf T}=M^{-1}(f'',nf''',n^2f'''')^{\mathsf T}\) — is
\(232\), and its \(\ell^1\) operator norm (maximal absolute column
sum) is \(288\). One may therefore take \(c_7=1/232\); we keep the
weaker value \(c_7=1/288\) used in Step 5b, which remains valid.
\(\square\)

The Step-5b triple is in fact the extremal one, so \(1/232\) serves as
a single explicit constant for the whole section. Over the ten triples
of \(E\) the norms \(\lVert M^{-1}\rVert_\infty\) are
\(\tfrac{113}{10}\) \((\tfrac34,\tfrac54,\tfrac{15}8)\) and
\((\tfrac34,\tfrac{11}8,\tfrac{15}8)\), \(\tfrac{113}9\), \(35\),
\(\tfrac{95}3\), \(\tfrac{95}2\), \(56\), \(\tfrac{149}2\),
\(\tfrac{181}3\), and \(232\) — the last being
\((\tfrac54,\tfrac{11}8,\tfrac32)\). Hence
\(c_7(E)=\tfrac1{232}\) is admissible uniformly in the triple, and the
absorption hypothesis of the lemma may be taken as the explicit
\(\rho_0\le c_7/8=\tfrac1{1856}\). Lean:
`step5b_curvature_inverse` (the inversion, by `ring`) and
`step5b_curvature_norm` (the \(\ell^\infty\) bound
\(\max(|A|,|B|,|C|)\le232\max(|f''|,|nf'''|,|n^2f''''|)\)), with
`step5b_c7_printed` recording that the manuscript's \(1/288\) follows a
fortiori. The step where the \(\ell^\infty\)/\(\ell^1\) confusion
originally arose is therefore now machine-checked.

The lemma is a measure statement, not an exponential-sum estimate:
in its one application (Theorem 5.3, Step 5b) the sublevel set
receives the trivial bound and the complement the second-derivative
test, with the parameter \(V\) chosen there.

**Lemma 3.10 (parity reindexing).**
All counting sums below run over odd \(n\). The substitution
\(n=2r+1\) maps a block interval of length \(L\) onto an interval of
length \(L/2\) and a phase \(f\) to \(f^*(r)=f(2r+1)\) with
\((f^*)^{(k)}(r)=2^kf^{(k)}(2r+1)\). Consequently:

(a) any two terms of a composite phase have the same curvature
*ratios* and the same *signs* in the \(r\)-variable as in the
\(n\)-variable, so every dominance margin and single-sign check
displayed below is invariant under the substitution;

(b) if \(\lambda\le|f''|\le\alpha\lambda\) on an interval of length
\(L\), then Lemma 3.3 applied in the \(r\)-variable (length \(L/2\),
curvature window \([4\lambda,4\alpha\lambda]\)) gives
\[
\Bigl|\sum_{n\in I,\ n\ \mathrm{odd}}e(f(n))\Bigr|
\ll_\alpha\tfrac L2\,(4\lambda)^{1/2}+(4\lambda)^{-1/2}
\le L\lambda^{1/2}+\lambda^{-1/2}:
\]
the \(n\)-variable display dominates the true reindexed bound, and
the same check for Lemma 3.8 replaces its conclusion by a smaller
quantity;

(c) sublevel and transition sets (Lemmas 3.8–3.9) are measured in
the \(n\)-line, and a set of total length \(\Lambda\) contains at
most \(\Lambda/2+C(E)\) odd integers, so trivial bounds displayed in
\(n\)-length dominate.

Every application of Lemmas 3.3 and 3.7–3.9 in Sections 3–6 is to be
read through this substitution; no displayed constant below needs
adjustment.

## 3. Depths one to three

For odd \(n\) write \(s(n)=\psi(n^{3/2})=(-1)^m\) and
\(S_O(N)=\sum_{n\le N,\ n\ \mathrm{odd}}s(n)\). Let \(M(N)\) be the
number of odd \(n\le N\) and
\(\operatorname{OO}(N)=\#\{n\le N:n\ \text{odd},\ J(n)\ \text{odd}\}\),
so \(S_O(N)=M(N)-2\operatorname{OO}(N)\). By Lemma 3.2, with
\(g(r)=\tfrac12(2r+1)^{3/2}\), \(s(2r+1)=-1\) iff
\(\{g(r)\}\ge\tfrac12\), and \(S_O(N)\) is (twice) an interval
discrepancy of the sequence \(\{g(r)\}\).

**Theorem 4.1 (depth one; classical).**
\(|S_O(N)|\ll N^{5/6}\).

*Proof.* This is the standard van der Corput estimate for the
monomial \(g\), included for completeness. \(g''(r)=\tfrac32
(2r+1)^{-1/2}\) is positive and decreasing. Partition \(1\le r<R\)
into dyadic blocks \([M,\min(2M,R))\); on a block
\(g''\asymp M^{-1/2}\), so for the \(h\)-th mode \(f=hg\) has
\(\lambda\asymp hM^{-1/2}\) and Lemma 3.3 gives
\(|\sum_{r\asymp M}e(hg(r))|\ll h^{1/2}M^{3/4}+h^{-1/2}M^{1/4}\).
Lemma 3.4 with \(H=\lfloor M^{1/6}\rfloor\) bounds the block's
discrepancy by \(\ll M^{5/6}\), and the dyadic sum is
\(O(R^{5/6})=O(N^{5/6})\). \(\square\)

**Corollary 4.2 (density of the odd-to-odd class).**
\(\bigl|\operatorname{OO}(N)-N/4\bigr|\ll N^{5/6}\). Equivalently,
the starts covered by the uniform one- or two-step certificates
(\(E\) and \(OE\)) have natural density \(3/4\).

This is a density of a certificate class, not of starts that reach
\(1\). Theorem 4.1 concerns consecutive source intervals; it supplies
no transfer theorem for orbit samples or sparse image sets, so it
cannot by itself control the odd-to-odd dynamics after the first step.
The rest of the paper does not transfer it; it attacks the nested sums
directly, by removing the inner floors exactly before any analytic
step.

**Lemma 4.3 (exact linearization and gap cells).**
(i) For every odd \(n\ge3\),
\[
m^{3/2}=\tfrac32\,m\,n^{3/4}-\tfrac12\,n^{9/4}+E(n),
\qquad
0\le E(n)\le\tfrac38\,(n^{3/2}-1)^{-1/2}\le\tfrac12\,n^{-3/4}.
\]
(ii) For \(h\ge1\) and odd \(n\), let \(g(n)=m(n+2h)-m(n)\) and
\(\delta(n)=(n+2h)^{3/2}-n^{3/2}\). Then
\[
g(n)=\lfloor\delta(n)\rfloor+\kappa(n),
\qquad
\kappa(n)=\bigl[\{n^{3/2}\}\ge1-\{\delta(n)\}\bigr]\in\{0,1\}.
\]

*Proof.* (i) Let \(f(t)=(X-t)^{3/2}\) on \([0,\theta]\), so
\(f(\theta)=m^{3/2}\). Then \(f'(t)=-\tfrac32(X-t)^{1/2}\) and
\(f''(t)=\tfrac34(X-t)^{-1/2}\). Taylor with Lagrange remainder at
\(0\) gives
\(f(\theta)=f(0)+f'(0)\theta+\tfrac12 f''(\xi)\theta^2
=X^{3/2}-\tfrac32X^{1/2}\theta
+\tfrac38(X-\xi)^{-1/2}\theta^2\) for some \(\xi\in(0,\theta)\).
Substituting \(\theta=X-m\) in the linear term yields
\(-\tfrac12X^{3/2}+\tfrac32mX^{1/2}=-\tfrac12n^{9/4}+\tfrac32mn^{3/4}\).
Since \(\theta\in[0,1)\) and \(f''>0\), the remainder
\(E(n)=\tfrac38(X-\xi)^{-1/2}\theta^2\) lies in
\(\bigl[0,\tfrac38(X-1)^{-1/2}\bigr]\), which is the bound of the
statement; and \((X-1)^{-1/2}\le\tfrac43X^{-1/2}\) already for
\(n\ge3\), whence \(E(n)\le\tfrac12 n^{-3/4}\). (ii)
\(g=\lfloor X+\delta\rfloor-\lfloor X\rfloor
=\lfloor\delta\rfloor+\lfloor\{X\}+\{\delta\}\rfloor\), and the last
floor is \(1\) precisely when \(\{X\}+\{\delta\}\ge1\)
(Lean `carry_identity`, `carry_mem_zero_one`). \(\square\)

*The remainder in closed form.* The mean value \(\xi\) is avoidable:
(i) is an algebraic identity in two square roots. Write
\(a=\sqrt m\) and \(b=\sqrt X=n^{3/4}\), so that
\(m^{3/2}=a^3\), \(mX^{1/2}=a^2b\), \(X^{3/2}=b^3\) and
\(\theta=b^2-a^2\). Then
\[
E=a^3-\tfrac32a^2b+\tfrac12b^3=\tfrac12(a-b)^2(2a+b),
\]
identically. Both printed bounds are immediate from this:
\(E\ge0\) because \(a,b\ge0\); and \(Ea\le\tfrac38\theta^2\)
--- i.e. \(E\le\tfrac38\theta^2m^{-1/2}\), which at
\(\theta<1\) is the stated
\(\tfrac38(n^{3/2}-1)^{-1/2}\) --- reduces after clearing
\((a-b)^2\) to \(4a(2a+b)\le3(a+b)^2\), i.e.
\((5a+3b)(a-b)\le0\), which holds because \(m\le X\). No Taylor
expansion and no mean value are needed, and the resulting bound is
sharper than the printed one at every \(n\), not merely
asymptotically. Machine-checked in
`formal/Problems/Juggler/PaperBAssembly.lean`
(`lemma43_closed_form`, `lemma43_nonneg`, `lemma43_upper`,
`lemma43_remainder_of_sqrt`).

The point of (i): the non-smooth integer \(m\) enters the phase
*linearly*, multiplied by a smooth coefficient; no fractional part of
growing amplitude survives. The naive expansion
\(m^{3/2}=n^{9/4}-\tfrac32\theta n^{3/4}+O(n^{-3/4})\) instead leaves
the sawtooth \(\theta\) with the growing amplitude \(n^{3/4}\), which
defeats the van der Corput method directly. For (ii), since
\(\delta\) is smooth and increasing with
\(\delta'\asymp hn^{-1/2}\), the level sets of
\(\lfloor\delta\rfloor\) partition a dyadic block \(n\in(P,2P]\) into
\(O(hP^{1/2})\) cells of length \(\asymp P^{1/2}/h\) on which the
integer part of the gap is constant.

**Theorem 4.4 (nested parity discrepancy).**
For every \(\varepsilon>0\) and every
\((a,b)\in\{0,1\}^2\setminus\{(0,0)\}\),
\[
\Bigl|\sum_{n\le N,\ n\ \mathrm{odd}}
\psi(n^{3/2})^{a}\,\psi(m(n)^{3/2})^{b}\Bigr|
\ll_\varepsilon N^{23/24+\varepsilon}.
\]
Consequently each of the four joint parity classes of
\((m,\lfloor m^{3/2}\rfloor)\) on odd \(n\le N\) has cardinality
\(\tfrac N8+O(N^{23/24+\varepsilon})\); in particular the odd-to-odd
cylinder refines one letter deeper than Theorem 4.1.

*Proof.* Work on dyadic blocks \(n\in(P,2P]\), odd, with truncations
\(J_1=J_2=P^{1/24}\) (wave modes), \(H=P^{1/12}\) (differencing), and
\(R=P^{1/4}\) (cell modes). All derivative tests are read through the
parity reindexing of Lemma 3.10; every constant below already
dominates the reindexed bound.

*Step 1 (wave expansion).* By Lemma 3.5 applied to each present
factor, \(\psi_1^a\psi_2^b\) differs from the product of the
truncated polynomials \(V^{(1)}V^{(2)}\) by at most
\(\Delta^{(1)}+\Delta^{(2)}+\Delta^{(1)}\Delta^{(2)}\), and each
error layer is a nonnegative trigonometric polynomial of degree
\(J_1\) resp. \(J_2\) with constant term and coefficients
\(\le1/(J+1)\). Summed over the block, a majorant layer costs its
constant term \(\le P/(2(J_1{+}1))\le P^{23/24}\) plus mode sums
\(\sum_{0<r\le2J_1}(J_1{+}1)^{-1}|\sum_ne(\tfrac r2n^{3/2})|\): each
inner sum has \(|(\tfrac r2X)''|\in[0.26,0.75]\,rP^{-1/2}\), single
sign, so Lemma 3.3 gives
\(\le1.4r^{1/2}P^{3/4}+2P^{1/4}\), and the weighted total is
\(\le2.4J_1^{1/2}P^{3/4}+2P^{1/4}\le3P^{19/24}\). The theorem is thus
reduced to bounds, uniform in the mode pair, for
\[
S_{i,j}(P)=\sum_{n\in(P,2P],\ n\ \mathrm{odd}}
e\bigl(\tfrac i2\,n^{3/2}+\tfrac j2\,m^{3/2}\bigr),
\qquad
|i|\le2J_1,\ 1\le|j|\le2J_2,
\]
with mode weights of total mass \(O(\log^2P)\); the \(j=0\) sums are
the depth-1 sums of Theorem 4.1. Replacing the summand by its
conjugate we may take \(j\ge1\).

*Step 2 (linearization).* By Lemma 4.3(i), replacing
\(\tfrac j2m^{3/2}\) by \(\tfrac{3j}4mn^{3/4}-\tfrac j4n^{9/4}\)
changes each summand by a phase of modulus
\(\le\tfrac j2E(n)\le\tfrac j4n^{-3/4}\), hence changes
\(S_{i,j}\) by at most
\(2\pi\tfrac j4\sum_{n\sim P}n^{-3/4}\le2jP^{1/4}\le4P^{7/24}\).
Call the linearized phase \(\Phi\).

*Step 3 (Weyl differencing).* For \(H=P^{1/12}\), the \(A\)-process
recorded after Lemma 3.3 gives
\[
|S_{i,j}|^2\le\frac{2P^2}H+\frac{4P}H
\sum_{1\le h<H}|T_h|,
\qquad
T_h=\sum_{\substack{n,\,n+2h\in(P,2P]\\ n\ \mathrm{odd}}}
e\bigl(\Phi(n{+}2h)-\Phi(n)\bigr).
\]

*Step 4 (the exact differenced phase).* Write \(\Delta f=
f(\cdot{+}2h)-f(\cdot)\), \(g(n)=m(n{+}2h)-m(n)\), and
\(m=n^{3/2}-\theta_n\). Exactly,
\[
\Phi(n{+}2h)-\Phi(n)
=\tfrac{3j}4\,g(n)\,(n{+}2h)^{3/4}
+\tfrac j2\,A_h(n)
-B_h(n)\,\theta_n
+\tfrac i2\,\Delta(n^{3/2}),
\]
with \(A_h=\tfrac32n^{3/2}\Delta(n^{3/4})-\tfrac12\Delta(n^{9/4})\)
and \(B_h=\tfrac{3j}4\Delta(n^{3/4})\). Taylor with third-order
remainders gives, for \(n\sim P\) and \(h\le H\),
\[
\Delta(n^{3/4})=\tfrac32hn^{-1/4}-\tfrac38h^2n^{-5/4}
+O(h^3P^{-9/4}),
\qquad
\Delta(n^{9/4})=\tfrac92hn^{5/4}+\tfrac{45}8h^2n^{1/4}
+O(h^3P^{-3/4}),
\]
so the two \(n^{5/4}\)-scale contributions of \(A_h\) cancel exactly
at leading order (both equal \(\tfrac94hn^{5/4}\)) and
\[
A_h=-\tfrac{27}8\,h^2n^{1/4}\bigl(1+O(hP^{-1})\bigr),
\qquad
|(\tfrac j2A_h)''|\le0.32\,jh^2P^{-7/4},
\]
\[
B_h\in[0.95,\,1.13]\,jh\,P^{-1/4},
\qquad
|(\tfrac i2\Delta(n^{3/2}))''|=\tfrac i2\,2h|X'''(\xi)|
\le0.38\,ihP^{-3/2}.
\]
The sawtooth term is *discarded*: \(|e(-B_h\theta_n)-1|\le2\pi B_h
\le7.1\,jhP^{-1/4}\) per term, so deleting it changes \(T_h\) by at
most \(3.6\,jhP^{3/4}\). This cost is charged in Step 7; it is
admissible only because \(jh\le2P^{1/24+1/12}=2P^{1/8}\), which is
the reason the truncation \(J_2\) and the differencing length \(H\)
cannot be enlarged in this argument.

*Step 5 (cells and the exact shift device).* Split \(T_h\) over the
level sets of \(\lfloor\delta\rfloor\),
\(\delta(n)=(n{+}2h)^{3/2}-n^{3/2}\): by (the argument of)
Lemma 4.3(ii) and \(\delta'\in(1.5,2.2)\,hP^{-1/2}\), at most
\(1.5hP^{1/2}+1\) cells of length in \([\tfrac23,0.95]P^{1/2}/h\).
On a cell \(g=G+\kappa\) with \(G=\lfloor\delta\rfloor\) frozen and
\(\kappa(n)=[\{n^{3/2}\}\ge\rho(n)]\), \(\rho=1-\{\delta(n)\}\)
smooth and monotone there. Vaaler-expand \(\kappa\) (one sawtooth
layer, Lemma 3.5) with modes \(e(rn^{3/2})\), \(0<|r|\le R\),
weights \(\le1/|r|\), majorant cost \(\le P/(R{+}1)+\)(\(R\)-mode
sums at coefficients \(\le1/(R{+}1)\))\(\le P^{3/4}+P^{7/8}\). The
moving endpoint costs nothing: since \(\rho(n)=1+G-\delta(n)\), the
coefficient's \(n\)-dependent piece contributes the exact smooth
phase \(r\delta(n)\), and
\(e(rn^{3/2}+r\delta(n))=e(r(n{+}2h)^{3/2})\) up to a unimodular
constant, so every \(r\)-term falls into one of the two smooth
families \(e(rn^{3/2})\), \(e(r(n{+}2h)^{3/2})\); the remaining
in-cell coefficient variation is exactly \(1\) per cell and one Abel
summation absorbs it at a factor \(\le2{+}2\pi\).

*Step 6 (second-derivative test per cell).* After Steps 4–5 the
phase on a cell is
\(\tfrac{3j}4G(n{+}2h)^{3/4}+\tfrac j2A_h+\tfrac i2\Delta(n^{3/2})\)
plus, for the \(r\)-pieces, \(rn^{3/2}\) or \(r(n{+}2h)^{3/2}\).

For \(r=0\): the main curvature is the single monomial term
\[
\Bigl(\tfrac{3j}4G(n{+}2h)^{3/4}\Bigr)''
=-\tfrac{9j}{64}\,G\,(n{+}2h)^{-5/4}
\in-[0.15,\,0.68]\,jh\,P^{-3/4},
\]
using \(G\in(3hP^{1/2}{-}1,\,4.3hP^{1/2})\) from (the mean value
bound for) \(\delta\) and \((n{+}2h)^{-5/4}\in(2^{-5/4},1]P^{-5/4}\).
Its competitors are dominated at displayed margins:
\(|(\tfrac j2A_h)''|/0.15jhP^{-3/4}\le2.2\,hP^{-1}\le2.2P^{-11/12}\)
and
\(|(\tfrac i2\Delta(n^{3/2}))''|/0.15jhP^{-3/4}
\le2.5\,(i/j)P^{-3/4}\le5P^{1/24-3/4}\), so the composite second
derivative is single-signed with in-cell ratio \(\le4.6\). Lemma 3.3
per cell (through Lemma 3.10) and summation over cells give
\[
\sum_{\text{cells}}\bigl(\ell_i\lambda^{1/2}+\lambda^{-1/2}\bigr)
\le0.83\,(jh)^{1/2}P^{5/8}+3.9\,(h/j)^{1/2}P^{7/8}.
\]

For \(r\ne0\): the mode curvature \(|(rX)''|\ge0.53|r|P^{-1/2}\)
dominates the full cell curvature \(\le0.68jhP^{-3/4}\) at ratio
\(\ge0.78\,|r|P^{1/4}/(jh)\ge0.39\,P^{1/8}\ge4\) for \(P\ge P_0\)
(here \(jh\le2P^{1/8}\) is used again), so the composite keeps the
mode's sign and, up to a factor \(\tfrac34\), its size. Lemma 3.3
per cell and the \(1/|r|\) weights give
\[
\sum_{0<|r|\le R}\frac1{|r|}
\Bigl(1.3|r|^{1/2}P^{3/4}
+1.5hP^{1/2}\cdot1.6|r|^{-1/2}P^{1/4}\Bigr)
\le5.2\,R^{1/2}P^{3/4}+13\,hP^{3/4}
\le6P^{7/8}+13P^{5/6}.
\]

*Step 7 (totals and assembly).* Collecting Steps 4–6,
\[
|T_h|\le C\bigl((jh)^{1/2}P^{5/8}+(h/j)^{1/2}P^{7/8}+P^{7/8}
+jhP^{3/4}\bigr)\log P
\le C'\,P^{7/8}(1+h^{1/2})\log P
\]
uniformly in the modes (for the last step:
\((jh)^{1/2}P^{5/8}\le2^{1/2}P^{1/16+5/8}\le P^{3/4}\) and
\(jhP^{3/4}\le2h^{1/2}\cdot(jh^{1/2})P^{3/4}
\le2h^{1/2}P^{1/24+1/24+3/4}\le2h^{1/2}P^{7/8}\), using
\(j\le2P^{1/24}\), \(h^{1/2}\le P^{1/24}\)). Hence
\[
|S_{i,j}|^2\le\frac{2P^2}H
+\frac{4P}H\cdot C'\log P\sum_{h<H}P^{7/8}(1+h^{1/2})
\le2P^{23/12}+6C'P^{15/8}H^{1/2}\log P
\ll P^{23/12+\varepsilon}
\]
at \(H=P^{1/12}\), so \(|S_{i,j}|\ll P^{23/24+\varepsilon}\). Summing
mode weights (\(O(\log^2P)\)), the majorant and truncation costs of
Steps 1 and 5 (\(\le P^{23/24}+3P^{19/24}+P^{7/8}\) per layer), and
dyadic blocks gives the theorem. \(\square\)

The exponent \(23/24\) is deliberately unoptimized; every stage has
slack. The proof above is the undecorated instance of Lemma 5.2(i)
below, which reruns the same six stages with three classes of
decorations riding along; the reader who has checked this proof has
checked the skeleton of that one.

**Proposition 4.5 (OE-branch third letter).**
For \(a\in\{0,1\}\),
\[
\Bigl|\sum_{n\le N,\ n\ \mathrm{odd}}\bigl((-1)^m\bigr)^a\,
\psi\bigl(m^{1/2}\bigr)\Bigr|\ll_\varepsilon N^{7/8+\varepsilon},
\]
and consequently
\(\#\mathrm{OEO}(N),\ \#\mathrm{OEE}(N)=N/8+O(N^{7/8+\varepsilon})\).
Together with Theorem 4.4 this completes depth 3 for odd-rooted itineraries: each of
\(OOO\), \(OOE\), \(OEO\), \(OEE\) has density \(1/8\) among odd starts with a power
saving.

*Proof.* Taylor expansion of \((X-\theta)^{1/2}\) with both correction
terms one-signed gives
\[
m^{1/2}=n^{3/4}+D_1(n),
\qquad
-\tfrac12X^{-1/2}-\tfrac18(X-1)^{-3/2}\le D_1\le0 .
\]
\(D_1\) is decaying, so replacing \(\tfrac l2m^{1/2}\) by
\(\tfrac l2n^{3/4}\) inside a Vaaler mode costs
\(\ll l\sum_{n\sim P}n^{-3/4}\ll lP^{1/4}\), absorbable at
\(l\le2P^{1/24}\). The mode sums are then pure:
\(\sum_{n\sim P}e(\tfrac i2n^{3/2}+\tfrac l2n^{3/4})\) with
\(l\ne0\). For \(i\ne0\), \(\varphi''\asymp|i|P^{-1/2}\) is
single-signed and Lemma 3.3 gives
\(\ll i^{1/2}P^{3/4}+i^{-1/2}P^{1/4}\); for \(i=0\),
\(\varphi''\asymp lP^{-5/4}\) gives
\(\ll l^{1/2}P^{3/8}+l^{-1/2}P^{5/8}\). Vaaler majorants, truncation
tails, and dyadic assembly are as in Theorem 4.4, and every bound is
\(\ll P^{7/8}\) after summing mode weights. Branch consistency is
Lemma 3.6: the \((1+(-1)^m)/2\) factor vanishes exactly on odd \(m\),
where the true chain takes the \(3/2\)-power branch. \(\square\)

**Lemma 4.6 (fourth-letter linearization).**
For every odd \(n\ge3\),
\[
v^{1/2}=n^{9/8}+D(n),
\qquad
-\tfrac34\,n^{-3/8}-n^{-9/8}\le D(n)\le0 .
\]

*Proof.* Two applications of the Lemma 4.3(i) pattern. With
\(f(t)=(Y-t)^{1/2}\) on \([0,\theta_2]\):
\(v^{1/2}=m^{3/4}-\tfrac12\theta_2m^{-3/4}-E_2\),
\(0\le E_2\le\tfrac18(Y-1)^{-3/2}\). With \(f(t)=(X-t)^{3/4}\) on
\([0,\theta]\): \(m^{3/4}=n^{9/8}-\tfrac34\theta n^{-3/8}-E_3\),
\(0\le E_3\le\tfrac3{32}(X-1)^{-5/4}\). Every term is nonpositive
after the leading one, and
\(\tfrac12m^{-3/4}+E_3+E_2\le n^{-9/8}\) for \(n\ge3\). \(\square\)

Unlike the depth-2 layer, *every* non-smooth term now has decaying
amplitude: the cumulative phase cost of replacing
\(\tfrac k2v^{1/2}\) by the smooth \(\tfrac k2n^{9/8}\) over a dyadic
block is \(\ll kP^{5/8}\), negligible against the target.

**Theorem 4.7 (triple parity discrepancy).**
For every \(\varepsilon>0\) and every
\((a,b,c)\in\{0,1\}^3\setminus\{(0,0,0)\}\),
\[
\Bigl|\sum_{n\le N,\ n\ \mathrm{odd}}
\psi(n^{3/2})^{a}\,\psi(m^{3/2})^{b}\,\psi(v^{1/2})^{c}\Bigr|
\ll_\varepsilon N^{23/24+\varepsilon}.
\]
Consequently each of the eight sign classes of
\((\psi(n^{3/2}),\psi(m^{3/2}),\psi(v^{1/2}))\) on odd \(n\le N\) has
cardinality \(\tfrac N{16}+O(N^{23/24+\varepsilon})\).

*Proof.* The \(c=0\) cases are Theorem 4.4 and Theorem 4.1. For
\(c=1\), wave-expand all present sign factors as in Step 1 of
Theorem 4.4, with truncations \(J_1=J_2=J_3=P^{1/24}\), and bound
\[
S_{i,j,k}(P)=\sum_{n\in(P,2P],\ n\ \mathrm{odd}}
e\bigl(\tfrac i2n^{3/2}+\tfrac j2m^{3/2}+\tfrac k2v^{1/2}\bigr)
\]
uniformly for \(|i|\le2J_1\), \(|j|\le2J_2\), \(1\le|k|\le2J_3\). By
Lemma 4.6, replacing \(\tfrac k2v^{1/2}\) by \(\tfrac k2n^{9/8}\)
costs \(\ll|k|P^{5/8}\le P^{2/3}\), before any differencing.

If \(j=0\), the remaining sum is a single smooth exponential sum with
phase \(\tfrac i2n^{3/2}+\tfrac k2n^{9/8}\). Both curvature terms are
positive for positive modes, and for mixed signs with \(|i|\ge1\) the
first dominates by \(P^{3/8-1/24}\); Lemma 3.3 gives
\(\ll P^{5/8}\) for \(i=0\) and \(\ll|i|^{1/2}P^{3/4}+P^{1/4}\)
otherwise, both \(\ll P^{23/24}\).

If \(j\ne0\), the phase is exactly the Theorem 4.4 phase plus the
smooth passenger \(\tfrac k2n^{9/8}\). Steps 2–6 run verbatim; the
passenger modifies the smooth part of the differenced phase by
\(\tfrac k2[(n{+}2h)^{9/8}-n^{9/8}]\), whose second derivative
\(\ll|k|hP^{-15/8}\) is smaller than the retained cell curvature
\(jhP^{-3/4}\) and the \(r\)-mode curvature \(|r|P^{-1/2}\) by powers
of \(P\). Every sign-dominance check of Theorem 4.4 holds with these
margins. \(\square\)

**Theorem 4.8 (the OE\*\* splits).**
\[
\#\mathrm{OEOE}(N),\ \#\mathrm{OEOO}(N)
=\tfrac N{16}+O\bigl(N^{7/8+\varepsilon}\bigr),
\qquad
\#\mathrm{OEEE}(N),\ \#\mathrm{OEEO}(N)
=\tfrac N{16}+O\bigl(N^{13/16+\varepsilon}\bigr).
\]
Together with Theorems 4.4 and 4.7 this proves every depth-4
itinerary word class except \(OOO*\).

*Proof.* On the \(OE\) branch \(m\) is even and \(w=\lfloor
U\rfloor\), \(U=m^{1/2}\). The \(w\)-level linearization is Lemma
4.3(i) verbatim with base \(U\): since \(Um^{1/4}=m^{3/4}\) exactly,
\[
w^{3/2}=m^{3/4}-\tfrac32\,m^{1/4}\,\theta_w+E,
\qquad 0\le E\le\tfrac38(U-1)^{-1/2},
\]
and \(m^{3/4}=n^{9/8}\) up to one-signed corrections of scale
\(n^{-3/8}\). For a Vaaler mode \(k\ne0\), the phase is therefore
\(\varphi_1(n)-B(n)\theta_w(n)\) up to absorbable errors, with
\(\varphi_1=\tfrac i2n^{3/2}+\tfrac j2n^{3/4}+\tfrac k2n^{9/8}\) and
\(B=\tfrac{3k}4n^{3/8}(1+O(n^{-3/2}))\): a *single growing sawtooth*
of amplitude \(\asymp kn^{3/8}\) riding \(\theta_w=\{m^{1/2}\}\),
whose underlying integer increments once every \(\asymp\tfrac43
n^{1/4}\) steps. Truncations: \(J_1=J_2=J_3=P^{1/8}\).

*Drift-1 intervals.* \(B'\asymp kn^{-5/8}\), so \(B\) drifts by at
most \(1\) on intervals \(I\) of length \(L_0=P^{5/8}/k\); there are
\(\asymp kP^{3/8}\) of them. On \(I\), expand
\(e(-B\{U\})=\sum_ra_r(B)e(rU)\) (Fourier in \(U\), Vaaler truncation
\(|r+B|\le T=P^{5/16}\)); the coefficients satisfy
\(|a_r(B)|\le\min(1,|r+B|^{-1})\) with window mass \(O(\log T)\), and
their \(n\)-dependence through \(B(n)\) has total variation \(O(1)\)
per interval, removed by one partial summation per mode.

*Mode sums.* Smoothing \(rU\to rn^{3/4}\) costs \(kP^{5/8}\) in
total. Writing \(r=-B_0+t\), \(|t|\le T\), the curvature of the mode
phase is
\[
\varphi''=\tfrac{27k}{128}n^{-7/8}
-\tfrac3{16}\bigl(t+\tfrac j2\bigr)n^{-5/4}+\tfrac{3i}8n^{-1/2}.
\]
For \(i\ne0\) the last term dominates and Lemma 3.3 gives
\(\ll i^{1/2}P^{3/4}+i^{-1/2}kP^{5/8}\) after summing intervals. For
\(i=0\), \((T+J_2)P^{-5/4}\ll kP^{-7/8}\) because
\(T=P^{5/16}\ll kP^{3/8}\) for every \(k\ge1\), so
\(\lambda\asymp kn^{-7/8}\) is single-signed; Lemma 3.3 per
interval and summation over \(\asymp kP^{3/8}\) intervals give
\(S_k\ll k^{1/2}P^{13/16+\varepsilon}\). With Vaaler weights \(1/k\),
\(\sum_{k\le J_3}k^{-1/2}P^{13/16}=J_3^{1/2}P^{13/16}=P^{7/8}\),
balanced against the truncation error \(P/J_3=P^{7/8}\) at
\(J_3=P^{1/8}\). Total \(\ll P^{7/8+\varepsilon}\).

*OEE branch.* The fourth letter needs \(\psi(w^{1/2})\), and
\(w^{1/2}=U^{1/2}-\tfrac12\theta_wU^{-1/2}
-\tfrac18\theta_w^2(U-\xi)^{-3/2}\) has *decaying* amplitudes only,
with \(U^{1/2}=m^{1/4}\to n^{3/8}\) likewise. The pure modes
\(e(\tfrac l2n^{3/8})\) have \(\lambda\asymp lP^{-13/8}\), giving
\(l^{1/2}P^{3/16}+l^{-1/2}P^{13/16}\); the mixed cases sit in the
dominance hierarchy \(iP^{-1/2}\gg jP^{-5/4}\gg lP^{-13/8}\) with all
three second derivatives of the same sign. Total
\(\ll N^{13/16+\varepsilon}\). \(\square\)

**Corollary 4.9 (certified-descent density \(13/16\)).**
The three uniform certificate classes
\[
E,\qquad OE,\qquad OOEE
\]
are disjoint, and
\[
\#\{n\le N:\mathrm{word}(n)\ \text{has prefix }E\}
=\bigl\lfloor\tfrac N2\bigr\rfloor,
\]
\[
\bigl|\#\{n\le N:\mathrm{word}(n)\ \text{has prefix }OE\}-\tfrac N4\bigr|
\ll N^{5/6},
\]
\[
\bigl|\#\{n\le N:\mathrm{word}(n)\ \text{has prefix }OOEE\}-\tfrac N{16}\bigr|
\ll_\varepsilon N^{23/24+\varepsilon}.
\]
Hence the class of starts with a certified descent within four
steps has cardinality
\[
\tfrac N2+\tfrac N4+\tfrac N{16}+O(N^{23/24+\varepsilon})
=\tfrac{13N}{16}+O(N^{23/24+\varepsilon}).
\]
No other depth-\(\le4\) word class is used. In particular this is
not a census of \(E\)-rooted itineraries of length \(\ge2\), and it is
not a census of every \(O\)-rooted itinerary of length four (the
classes \(OOO*\) are Theorem 6.1, and they are non-contracting at
this depth).

*Proof.* Every even start realizes \(E\), so the first count is
elementary. The \(OE\) count is Corollary 4.2. For \(OOEE\),
Lemma 3.6 gives
\(\#OOEE=\tfrac18\sum_{n\le N\ \mathrm{odd}}
(1-\psi_1)(1+\psi_2)(1+\psi_3)\) with
\(\psi_1=\psi(n^{3/2})\), \(\psi_2=\psi(m^{3/2})\),
\(\psi_3=\psi(v^{1/2})\); expanding gives the main term \(N/16\)
and seven sign sums bounded by Theorem 4.7. Every \(OOEE\) start
descends within four steps by Proposition 3.1: \(3^2<2^4\). The
three classes are disjoint because they are distinct prefixes.
\(\square\)

The certificate density \(13/16\) is the exact ceiling of this one-growing-layer
machinery: an itinerary contracts iff \(3^{o}<2^{\ell}\), the method so far
proves letters at positions 1–3 of any itinerary plus further letters along
even branches only, and the contracting minimal words with all odd
letters at positions \(\le2\) are exactly \(E\), \(OE\), and \(OOEE\).
Completing depth 4 over odd starts requires the \(OOO*\) split — a second
growing layer, where the fourth-letter phase coefficient
\(W\asymp kn^{9/8}\) crosses integers within single steps and no
drift-1 interval exists. Sections 5 and 6 close that split. The
\(OOO*\) words are non-contracting at depth 4, so the four-step
certified density remains \(13/16\); the next increment is the two
length-five contractors of Theorem 6.3.

### 3.5 Localization to sub-dyadic intervals and slow twists

Theorems 4.4 and 4.7 are stated on dyadic blocks. Two applications
outside this paper need them on shorter intervals and with a slowly
varying phase attached: the contagion recursion of the companion
paper [24] counts the \(OOEEE\) starts landing in a prescribed even
block, which is a statement about the interval
\(I(m')=[m'^{32/9},(m'+1)^{32/9})\) of length \(\asymp P^{23/32}\) at
scale \(P=m'^{32/9}\), and the fifth letter enters through a Fourier
expansion whose modes \(e(\tfrac\ell2n^{9/16})\) multiply the depth-4
sign products. This subsection proves both theorems in that
generality. The proofs are the proofs of Theorems 4.4 and 4.7 with the
number of summands \(Y\) in place of \(P\) wherever the number of
summands enters, and the point of writing them out is to exhibit the
terms that do *not* scale with \(Y\) — there are three, all of size
at most \(P^{7/16}\) — and to show that the twist is removed by one
partial summation after the differencing.

Throughout, \(I\subseteq(P,2P]\) is an interval of length \(Y\) (so
\(I\) contains \(Y/2+O(1)\) odd integers), and a *slow twist* is
\(g(n)=\tfrac\ell2n^{9/16}\) with an integer \(\ell\), \(|\ell|\le P^{1/24}\).
For \(n\in(P,2P]\),
\[
|g'(n)|\le\tfrac9{32}|\ell|P^{-7/16},\qquad
|g''(n)|\le\tfrac{63}{512}|\ell|P^{-23/16}\le0.13\,P^{1/24-23/16}.
\tag{4.5}
\]

**Lemma 4.10 (removing a slow twist after differencing).** Let
\(a_n\) be complex numbers on an interval \(I\) and \(w(n)=e(\gamma(n))\)
with \(\gamma\) real and differentiable on \(I\). Then
\[
\Bigl|\sum_{n\in I}a_nw(n)\Bigr|
\le\bigl(1+2\pi\,\mathrm{TV}_I(\gamma)\bigr)\max_{I'}\Bigl|\sum_{n\in I'}a_n\Bigr|,
\]
the maximum over the initial sub-intervals \(I'\) of \(I\), where
\(\mathrm{TV}_I(\gamma)=\int_I|\gamma'|\). In particular, for
\(\gamma=\Delta_{2h}g=g(\cdot+2h)-g\) with \(g\) a slow twist,
\(h\le P^{1/12}\) and \(|I|\le P\),
\(\mathrm{TV}_I(\gamma)\le2h\,|I|\sup|g''|\le0.26\,P^{1/24+1/12+1-23/16}=0.26\,P^{-5/16}\).

*Proof.* Abel summation: with \(A(x)=\sum_{n\in I,\,n\le x}a_n\),
\(\sum_{n\in I}a_nw(n)=\sum_n A(n)\bigl(w(n)-w(n+1)\bigr)+A(\max I)w(\max I)\),
and \(\sum_n|w(n)-w(n+1)|\le2\pi\sum_n|\gamma(n+1)-\gamma(n)|\le2\pi\,\mathrm{TV}_I(\gamma)\).
The second claim is \(|(\Delta_{2h}g)'|\le2h\sup|g''|\) and (4.5).
\(\square\)

**Theorem 4.11 (nested parity discrepancy on sub-dyadic intervals,
with a slow twist).** For every \(\varepsilon>0\) there is \(P_0\)
such that for all \(P\ge P_0\), every interval \(I\subseteq(P,2P]\) of
length \(Y\ge P^{1/2}\), every \((a,b)\in\{0,1\}^2\setminus\{(0,0)\}\)
and every slow twist \(g\),
\[
\Bigl|\sum_{n\in I,\ n\ \mathrm{odd}}
\psi(n^{3/2})^{a}\,\psi(m^{3/2})^{b}\,e(g(n))\Bigr|
\ \le\ Y\,P^{-1/24+\varepsilon}.
\]

*Proof.* We run Steps 1–7 of Theorem 4.4 over \(I\) and record each
cost as *proportional* (to the number of summands, hence to \(Y\)) or
*absolute* (independent of it).

*Step 1.* The majorant layers are nonnegative and the twist is
unimodular, so the expansion is unchanged: each layer costs its
constant term \(\le Y/(2(J_1+1))\le\tfrac12YP^{-1/24}\) (proportional)
plus the mode sums \(\sum_{0<r\le2J_1}(J_1+1)^{-1}|\sum_{n\in I}e(\tfrac r2n^{3/2})|\);
Lemma 3.3 on \(I\) gives each inner sum
\(\le1.4r^{1/2}YP^{-1/4}+2P^{1/4}\), and the weighted total is
\(\le2.6J_1^{1/2}YP^{-1/4}+4P^{1/4}=2.6\,YP^{-11/48}+4P^{1/4}\)
(proportional plus absolute). The theorem reduces to the twisted mode
sums
\[
S^{g}_{i,j}(I)=\sum_{n\in I,\ n\ \mathrm{odd}}
e\bigl(\tfrac i2n^{3/2}+\tfrac j2m^{3/2}+g(n)\bigr),
\qquad|i|\le2J_1,\ 1\le|j|\le2J_2,
\]
with mode weights of total mass \(O(\log^2P)\); the \(j=0\) sums are
the depth-1 sums \(\sum_{n\in I}e(\tfrac i2n^{3/2}+g(n))\), \(i\ne0\),
whose phase has curvature in \([0.53,0.75]|i|P^{-1/2}\) up to the twist's
\(\le0.13P^{1/24-23/16}\) — a relative perturbation
\(\le0.25P^{1/24-15/16}\) — so Lemma 3.3 gives
\(\le1.4|i|^{1/2}YP^{-1/4}+2P^{1/4}\).

*Step 2.* Linearization changes each summand by a phase of modulus
\(\le\tfrac j4n^{-3/4}\): total \(\le2\pi\cdot\tfrac j4\cdot\tfrac Y2P^{-3/4}\le jYP^{-3/4}\le2YP^{1/24-3/4}\)
(proportional).

*Step 3.* The \(A\)-process for a sum of \(Y/2+O(1)\) unimodular terms
with \(H=P^{1/12}\le Y\):
\[
|S^g_{i,j}(I)|^2\le\frac{2Y^2}H+\frac{4Y}H\sum_{1\le h<H}|T^g_h|,
\qquad
T^g_h=\sum_{\substack{n,\,n+2h\in I\\ n\ \mathrm{odd}}}
e\bigl(\Phi(n{+}2h)-\Phi(n)+\Delta_{2h}g(n)\bigr).
\]
By Lemma 4.10, \(|T^g_h|\le(1+1.7P^{-5/16})\max_{I'}|T_h(I')|\), where
\(T_h(I')\) is the *untwisted* differenced sum over an initial
sub-interval \(I'\) of \(I\). The twist has now been removed; it
remains to bound \(T_h(I')\) for every sub-interval \(I'\subseteq I\)
by an expression that is nondecreasing in \(|I'|\), and to evaluate
it at \(|I'|=Y\).

*Step 4.* The exact differenced phase is unchanged. Discarding the
sawtooth term costs \(\le7.1jhP^{-1/4}\) per summand, i.e.
\(\le3.6jhY'P^{-1/4}\) on \(I'\) (proportional).

*Step 5.* The level sets of \(\lfloor\delta\rfloor\) cut \(I'\) into
at most \(1.5hY'P^{-1/2}+2\) cells: the full cells have length in
\([\tfrac23,0.95]P^{1/2}/h\) as before, and at most two end cells are
partial. The Vaaler layer for \(\kappa\) costs its constant term
\(\le Y'/(R+1)\le Y'P^{-1/4}\) plus the \(R\)-mode sums at
coefficients \(\le1/(R+1)\); per cell and mode Lemma 3.3 gives
\(\ell\lambda_r^{1/2}+\lambda_r^{-1/2}\) with \(\lambda_r\ge0.53|r|P^{-1/2}\),
and summing over cells and modes,
\[
\le1.2\,R^{1/2}Y'P^{-1/4}+\bigl(1.5hY'P^{-1/2}+2\bigr)\cdot5.5\,P^{1/4}R^{-1/2}
=1.2\,Y'P^{-1/8}+8.3\,hY'P^{-3/8}+11\,P^{1/8}
\]
(two proportional terms and one absolute). The exact shift device is
pointwise and unchanged.

*Step 6.* For \(r=0\) the per-cell test gives, over the cells meeting
\(I'\),
\[
\sum_{\text{cells}}\bigl(\ell_i\lambda^{1/2}+\lambda^{-1/2}\bigr)
\le0.83\,(jh)^{1/2}Y'P^{-3/8}+3.9\,(h/j)^{1/2}Y'P^{-1/8}+5.2\,(jh)^{-1/2}P^{3/8},
\]
the last term being the two partial end cells. For \(r\ne0\) the
same per-cell bounds with the mode curvature, summed against the
\(1/|r|\) weights, give
\(\le5.2\,Y'P^{-1/8}+13\,hY'P^{-1/4}+17\,P^{1/4}\), the last term
again from the end cells. All sign-dominance checks are pointwise and
unchanged.

*Step 7.* Collecting, for every sub-interval \(I'\) of length \(Y'\),
\[
|T_h(I')|\le C\,Y'P^{-1/8}(1+h^{1/2})\log P+C'P^{3/8},
\]
nondecreasing in \(Y'\) (the absolute constant \(C'\) collects
\(5.2(jh)^{-1/2}P^{3/8}\), \(17P^{1/4}\), \(11P^{1/8}\) and the
Step-1 term \(4P^{1/4}\)). Hence
\[
|S^g_{i,j}(I)|^2\le\frac{2Y^2}H+\frac{4Y}H\sum_{h<H}\Bigl(CYP^{-1/8}(1+h^{1/2})\log P+C'P^{3/8}\Bigr)(1+1.7P^{-5/16})
\le Y^2P^{-1/12}\bigl(3+8C\log P\bigr)+5C'YP^{3/8}.
\]
For \(Y\ge P^{1/2}\), \(YP^{3/8}\le Y^2P^{-1/8}\le Y^2P^{-1/12}\), so
\(|S^g_{i,j}(I)|\ll YP^{-1/24}\log^{1/2}P\). Summing the mode weights
(\(O(\log^2P)\)) and adding the proportional and absolute costs of
Steps 1–2 gives the theorem, the absolute costs being
\(\le4P^{1/4}\le YP^{-1/4}\). \(\square\)

**Theorem 4.12 (triple parity discrepancy on sub-dyadic intervals,
with a slow twist).** For every \(\varepsilon>0\) there is \(P_0\)
such that for all \(P\ge P_0\), every interval \(I\subseteq(P,2P]\) of
length \(Y\ge P^{1/2}\), every \((a,b,c)\in\{0,1\}^3\setminus\{(0,0,0)\}\)
and every slow twist \(g\),
\[
\Bigl|\sum_{n\in I,\ n\ \mathrm{odd}}
\psi(n^{3/2})^{a}\,\psi(m^{3/2})^{b}\,\psi(v^{1/2})^{c}\,e(g(n))\Bigr|
\ \le\ Y\,P^{-1/24+\varepsilon}.
\]

*Proof.* The \(c=0\) cases are Theorem 4.11 and its depth-1 case. For
\(c=1\), wave-expand as in Theorem 4.7 and bound the twisted mode sums
\(S^g_{i,j,k}(I)\), \(1\le|k|\le2J_3\). Lemma 4.6 replaces
\(\tfrac k2v^{1/2}\) by \(\tfrac k2n^{9/8}\) at a per-summand cost
\(\le\tfrac k2(\tfrac34n^{-3/8}+n^{-9/8})\), total
\(\le2.4\,|k|YP^{-3/8}\le5\,YP^{1/24-3/8}\) (proportional).

If \(j=0\) the sum is a single smooth exponential sum with phase
\(\tfrac i2n^{3/2}+\tfrac k2n^{9/8}+g(n)\). For \(i\ne0\) the first
term's curvature \(\ge0.53|i|P^{-1/2}\) dominates the second
(\(\le0.14|k|P^{-7/8}\le0.14P^{1/24-7/8}\)) and the twist
(\(\le0.13P^{1/24-23/16}\)) by powers of \(P\), and Lemma 3.3 gives
\(\le1.4|i|^{1/2}YP^{-1/4}+2P^{1/4}\). For \(i=0\) the passenger's
curvature \(\ge0.07|k|P^{-7/8}\) dominates the twist by
\(P^{-23/16+7/8-1/24}=P^{-7/12}\), and Lemma 3.3 gives
\(\le0.27|k|^{1/2}YP^{-7/16}+3.8|k|^{-1/2}P^{7/16}\): one proportional
term and the absolute *pure passenger* term \(3.8P^{7/16}\), which is
\(\le3.8\,YP^{-1/16}\) for \(Y\ge P^{1/2}\).

If \(j\ne0\), the phase is the Theorem 4.11 phase plus the smooth
passenger \(\tfrac k2n^{9/8}\). After the differencing of Step 3 and
the removal of the twist by Lemma 4.10, the passenger contributes
\(\tfrac k2[(n{+}2h)^{9/8}-n^{9/8}]\) to the smooth part of the
differenced phase, with second derivative \(\le0.15|k|hP^{-15/8}\),
smaller than the retained cell curvature \(0.15jhP^{-3/4}\) and the
\(r\)-mode curvature \(0.53|r|P^{-1/2}\) by the factors
\(P^{1/24-9/8}\) and \(P^{1/24+1/12-11/8}\); every sign-dominance
check of Steps 4–6 holds with these margins, and Step 7 is unchanged.
\(\square\)

The threshold \(Y\ge P^{1/2}\) is where the three absolute terms —
the two partial end cells (\(5.2P^{3/8}\)), the pure passenger
(\(3.8P^{7/16}\)) and the majorant end cells (\(17P^{1/4}\)) — fall
below the main saving \(YP^{-1/24}\); nothing else in either proof
uses the length of the block except through the number of summands.
The twist enters only through Lemma 4.10 (after differencing) and
through curvature comparisons in which it loses by a power of \(P\);
any \(g\) with \(|g''|\le P^{-4/3}\) on the block would do, and the
class \(\tfrac\ell2n^{9/16}\), \(|\ell|\le P^{1/24}\), is the one the
application needs.

**Corollary 4.13 (the \(OOEEE\) production on even blocks).** For
\(m'\ge2\) let \(I(m')=[m'^{32/9},(m'+1)^{32/9})\) and
\[
\mathcal O(m')=\{n\ \text{odd}\in I(m'):\ \mathrm{word}_5(n)=OOEEE,\ J^5(n)=m'\},
\]
where \(\mathrm{word}_5(n)\) is the itinerary of the first five steps of
\(n\) under \(J\). Then every \(n\in\mathcal O(m')\) has
\(J^4(n)\in[m'^2,(m'+1)^2)\) even, and
\[
|\mathcal O(m')|=\tfrac1{16}\#\{n\ \text{odd}\in I(m')\}
+O_\varepsilon\bigl(|I(m')|\,m'^{-4/27+\varepsilon}\bigr).
\]

*Proof.* Put \(P=m'^{32/9}\) and \(Y=|I(m')|=\tfrac{32}9m'^{23/9}(1+O(1/m'))\asymp P^{23/32}\ge P^{1/2}\).
Along \(OOEEE\) the states are \(n\) (odd), \(m\) (odd), \(v\) (even),
\(\lfloor v^{1/2}\rfloor\) (even), \(J^4(n)=\lfloor\sqrt{\lfloor v^{1/2}\rfloor}\rfloor=\lfloor v^{1/4}\rfloor\)
(even), and \(J^5(n)=\lfloor\sqrt{J^4(n)}\rfloor\); so \(J^5(n)=m'\)
forces \(J^4(n)\in[m'^2,(m'+1)^2)\). Three elementary facts:

(a) *Nesting at the fifth letter.* For odd \(n\ge3\),
\(0\le n^{9/16}-v^{1/4}\le n^{-15/16}\): the upper bound is
\(v\le n^{9/4}\); the lower one follows from
\(v\ge(n^{3/2}-1)^{3/2}-1\ge n^{9/4}-\tfrac32n^{3/4}-1\) and the mean
value theorem for \(u\mapsto u^{1/4}\), using \(v\ge\tfrac12n^{9/4}\).
Hence \(\lfloor v^{1/4}\rfloor=\lfloor n^{9/16}\rfloor\) unless
\(\{n^{9/16}\}<n^{-15/16}\).

(b) *The exceptional set is small.* By Lemma 3.4 (Erdős–Turán) with
\(H=\tfrac49P^{7/16}\) and the Kusmin–Landau bound
\(|\sum_{n\in I\ \mathrm{odd}}e(hn^{9/16})|\ll P^{7/16}/h\) (the phase
\(h(2k{+}1)^{9/16}\) has monotone derivative \(\tfrac98h(2k{+}1)^{-7/16}\in(0,\tfrac12]\)),
\[
\#\{n\ \text{odd}\in I:\ \{n^{9/16}\}<n^{-15/16}\}\ll YP^{-15/16}+YP^{-7/16}+P^{7/16}\ll YP^{-1/16}.
\]

(c) *The fifth letter as a Fourier series.* With \(J=\lfloor P^{1/24}\rfloor\),
Lemma 3.5 gives coefficients \(b_q\), \(0<|q|\le J\), \(|b_q|\ll1/|q|\),
and a majorant \(\Delta_J\) of degree \(J\) with coefficients
\(\le1/(J+1)\), such that
\(|\psi(y)-\sum_qb_qe(qy/2)|\le2\Delta_J(y/2)\) for all real \(y\);
and by Kusmin–Landau,
\(|\sum_{n\in I\ \mathrm{odd}}e(\tfrac q2n^{9/16})|\ll P^{7/16}/|q|\) for
\(0<|q|\le J\), so
\(\sum_{n\in I}\Delta_J(\tfrac12n^{9/16})\ll YP^{-1/24}+P^{7/16}\log P\).

Now, off the exceptional set of (a), \(n\in I(m')\) gives
\(\lfloor n^{9/16}\rfloor\in[m'^2,(m'+1)^2)\), so for such \(n\) with
\(\mathrm{word}_5(n)=OOEEE\) the value \(J^5(n)=m'\) is automatic;
therefore \(|\mathcal O(m')|\) differs from
\(\#\{n\ \text{odd}\in I:\ \mathrm{word}_5(n)=OOEEE\}\) by at most the
exceptional count of (b). By Lemma 3.6 the indicator of \(OOEEE\) on
odd \(n\) is \(\tfrac1{16}(1-\psi_1)(1+\psi_2)(1+\psi_3)(1+\psi_4)\)
with \(\psi_4=\psi(v^{1/4})\), each factor enforcing the branch on
which the next is the true letter. Expanding, the main term is
\(\tfrac1{16}\#\{n\ \text{odd}\in I\}\); the seven sign sums without
\(\psi_4\) are Theorem 4.12 with \(g=0\); for the eight with
\(\psi_4\), replace \(\psi(v^{1/4})\) by \(\psi(n^{9/16})\) (they agree
off the exceptional set, by (a)), expand by (c), and bound each
twisted sum \(\sum_n\psi_1^a\psi_2^b\psi_3^c\,e(\tfrac q2n^{9/16})\)
by Theorem 4.12 when \((a,b,c)\ne0\) and by the Kusmin–Landau bound of
(c) when \((a,b,c)=0\); the coefficient sums are \(O(\log P)\). Every
error is \(\ll YP^{-1/24+\varepsilon}+P^{7/16}\log P\ll YP^{-1/24+\varepsilon}\),
and \(P^{-1/24}=m'^{-4/27}\). \(\square\)

The corollary is what the contagion recursion of [24] consumes: for
a backward-closed set \(A\ni m'\), every member of \(\mathcal O(m')\)
lies in \(A\), with log-mass at least \(\tfrac1{9m'}(1-O(m'^{-4/27+\varepsilon}))\),
and the recursion gains the term \(\tfrac19g(9t/32)\), raising the
contagion exponent from \(0.4050\) to \(0.4922\). Nothing in this
subsection is used in Sections 5–7.

## 4. The level-2 wave and the kernel theorem

The reader should hold one object in mind through this section: the
exact level-2 wave \(e(qY)\), \(Y=\lfloor n^{3/2}\rfloor^{3/2}\), a
depth-2 nested-floor phase, possibly multiplied by a frozen floor of
the same depth. It is the fundamental obstruction of the paper. The
kernel theorem (Theorem 5.3) is organized so that, after two
differencings and an exact bookkeeping of carries, *everything* that
is not a standard second-derivative test is such a wave, and
Lemma 5.2 — stated and proved first, as a standalone result with its
own differencing — bounds it with exactly depth-2 strength,
\(|q|^{-1/6}P^{23/24+\varepsilon}\). The exponent \(1-1/96\) of the
kernel theorem is nothing but that depth-2 strength propagated
through two differencings; any improvement of Lemma 5.2 improves the
kernel theorem proportionally, and no other part of the argument is
close to its limit.

Every reorganization of the \(OOO*\) phase funnels into one object:
for the monomial weight \(c(n)=\tfrac{3k}4 n^{9/8}\) on \(n\sim P\),
\[
K_c(P)=\sum_{\substack{n\sim P\\ n\ \mathrm{odd}}}
e\bigl(c(n)\,\{\lfloor n^{3/2}\rfloor^{3/2}\}\bigr).
\]
This section proves the kernel bound at full length: every estimate
that the proof uses is displayed, with its dependence on the mode
\(k\), the differencing shifts \(h_1,h_2,h_3\), the branch offset
\(j\), and the expansion frequencies made explicit, and with
numerical constants displayed at each of the sign-critical
dominance checks. Two structural facts shape the proof and are
worth stating in advance. First, the hardest pieces of the
decomposition are exact level-2 waves \(e(qY)\), possibly riding a
frozen floor; a frozen-coefficient model \(e(sX)\) with
\(s\asymp qP^{3/4}\) would silently discard the sawtooth
\(-\tfrac32qX^{1/2}\theta\) of the same amplitude hidden in
\(Y=(X-\theta)^{3/2}\), so the waves are treated exactly — by the
same exact linearization that proves Theorem 4.4 — and the honest
bound is \(q^{-1/6}P^{23/24+\varepsilon}\) (Lemma 5.2): the wave is
a depth-2 object and receives exactly depth-2 strength, which is
what pins the kernel saving at \(\delta=\tfrac1{96}\). Second, the
offset-branch pieces of Step 5 carry a factor \((k|j|)^{1/2}\), and
\((k|j|)^{1/2}P^{15/16}\le P^{23/24}\) exactly on the standing range
\(k\le P^{1/24}\): the two bottlenecks meet at the endpoint, which
is why the theorem is uniform in \(k\) on that range and why the
range cannot be enlarged by this assembly.

The next lemma collects the exact reductions behind the treatment:
the kernel phase is the level-2 local floor defect; the second
difference of the level-2 integer obeys an exact floor identity; on
an explicit carry-branch decomposition that second difference is a
smooth function with a frozen floor; and the doubly differenced
kernel phase decomposes exactly into four bounded pieces — the
master identity — with no growing smooth part left to estimate.

**Lemma 5.1 (level-2 defect, double gap, branch freeze, and the master identity).**
Fix shifts \(d_1=2h_1\), \(d_2=2h_2\) and write \(\Delta_1\),
\(\Delta_2\), \(\Delta\Delta\) for the corresponding difference
operators in \(n\), and \(W=\Delta_1Y\), \(W'=\Delta_2Y\).

(i) For odd \(n\ge3\),
\[
\tfrac34\,v^{1/2}\theta_2
=\tfrac12\bigl(m^{9/4}-v^{3/2}\bigr)-R,
\qquad 0\le R\le\tfrac3{16}\,v^{-1/2}.
\]
Hence for \(c=\tfrac{3k}4v^{1/2}\) the kernel phase \(c\,\theta_2\)
equals \(\tfrac k2(Y^{3/2}-v^{3/2})\) up to \(kR\ll kP^{-9/8}\) per
term: the kernel is the exponential sum of the level-2 local floor
defect.

(ii) Exactly, with \(g_2=\Delta_1v\),
\[
\Delta_2g_2=\lfloor\Delta\Delta Y\rfloor+\kappa''+\Delta_2\kappa_2,
\qquad
\kappa_2=\bigl[\theta_2\ge1-\{W\}\bigr],\quad
\kappa''=\bigl[\{W\}\ge1-\{\Delta\Delta Y\}\bigr],
\]
and every carry is a difference of unit sawtooths:
\(\bigl[\{A\}+\{B\}\ge1\bigr]=\{A\}+\{B\}-\{A{+}B\}\)
for all reals \(A,B\) (both sides equal \(\{A\}+\{B\}-\{A+B\}\):
the left side because \(\{A\}+\{B\}\in[0,2)\) and
\(\{A+B\}=\{A\}+\{B\}-\lfloor\{A\}+\{B\}\rfloor\)).

(iii) Write \(b_1=\lfloor\Delta_1X\rfloor\),
\(b_2=\lfloor\Delta_2X\rfloor\), \(b_{12}=\lfloor\Delta_{12}X\rfloor\)
(shift \(d_1{+}d_2\)) — each constant on runs of length
\(\asymp P^{1/2}/h\) — and let
\(\boldsymbol\kappa=(\kappa_1,\kappa_2,\kappa_{12})\in\{0,1\}^3\) be
the level-1 carries, so that the shifted values of \(m\) are
\(m+\beta_1\), \(m+\beta_2\), \(m+\beta_{12}\) with
\(\beta_i=b_i+\kappa_i\). On each \(b\)-run intersection and carry
branch,
\[
\Delta\Delta Y=F_{\boldsymbol\kappa}(m),
\qquad
F_{\boldsymbol\kappa}(m)=(m{+}\beta_{12})^{3/2}
-(m{+}\beta_1)^{3/2}-(m{+}\beta_2)^{3/2}+m^{3/2}
\]
exactly. The net offset
\(j=\beta_{12}-\beta_1-\beta_2\)
satisfies \(|j|\le3\) for \(h_1h_2\le P^{1/2}/3\), and \(F\) splits
exactly into an offset term and a genuine second difference: for
some \(\xi_1\) between \(0\) and \(j\) and some
\(\xi_2\in(0,\beta_1+\beta_2)\),
\[
F_{\boldsymbol\kappa}(m)
=\tfrac32\,j\,(m+\beta_1+\beta_2+\xi_1)^{1/2}
+\tfrac34\,\beta_1\beta_2\,(m+\xi_2)^{-1/2}.
\]
Consequently, with \(G:=F_{\boldsymbol\kappa}\circ X\),
\[
\tfrac32|j|P^{3/4}\le\Bigl|\tfrac32j(\cdot)^{1/2}\Bigr|
\le2.6\,|j|P^{3/4},
\qquad
1.4\,h_1h_2P^{1/4}\le\tfrac34\beta_1\beta_2(\cdot)^{-1/2}
\le15\,h_1h_2P^{1/4},
\]
\[
|G'(n)|\le2|j|P^{-1/4}+20\,h_1h_2P^{-3/4}<1,
\qquad
|G''(n)|\le2|j|P^{-5/4}+25\,h_1h_2P^{-7/4},
\]
so \(\lfloor G(n)\rfloor\) is constant on runs of length
\(\ge\tfrac1{22}\min\bigl(P^{1/4}/(|j|{+}1),\,P^{3/4}/(h_1h_2)\bigr)\).
The branch indicator is a finite union of arcs in the single
variable \(\theta\) with slowly moving endpoints (drifts
\(\le1.5hP^{-1/2}\) per step): exactly the moving-endpoint pattern of
Step 4 of Theorem 4.4, absorbed by the same exact shift device at
\(O(\log P)\) mode-mass cost.

(iv) *(Master identity.)* With
\(\kappa_2=[\theta_2\ge1-\{W\}]\), \(\kappa_2'=[\theta_2\ge1-\{W'\}]\)
the level-2 carries at the two shifts, and \(\kappa''\),
\(\Delta_2\kappa_2\) as in (ii), the doubly differenced kernel phase
decomposes exactly:
\[
\Delta\Delta(c\,\theta_2)
=(\Delta\Delta c)\,\theta_2
+(\Delta_2c)(n{+}d_1)\,\bigl(\{W\}-\kappa_2\bigr)
+(\Delta_1c)(n{+}d_2)\,\bigl(\{W'\}-\kappa_2'\bigr)
+c_{11}\,\bigl(\{\Delta\Delta Y\}-\kappa''-\Delta_2\kappa_2\bigr),
\]
where \(c_{11}\) is the doubly shifted weight. Every bracket is
bounded by \(2\) in absolute value: no unbounded smooth part
survives the differencing.

*Proof.* (i) Taylor of \((v+\theta_2)^{3/2}\) at \(v\), with
\(Y^{3/2}=m^{9/4}\); as in Lemma 4.3(i) the mean value is avoidable,
and the remainder has a closed form. Write \(a=\sqrt v\),
\(b=\sqrt Y\), so \(\theta_2=b^2-a^2\) and \(m^{9/4}=b^3\). Then
\[
\tfrac34 a\,(b^2-a^2)
=\tfrac12\bigl(b^3-a^3\bigr)-R,
\qquad
R=\tfrac14(b-a)^2(2b+a),
\]
identically; \(R\ge0\) by inspection, and
\(Ra\le\tfrac3{16}\theta_2^2\) reduces to
\((a+3b)(a-b)\le0\), which holds because \(v\le Y\). At
\(\theta_2<1\) that is the printed
\(R\le\tfrac3{16}v^{-1/2}\), and it is nearly sharp: sampling odd
\(n\le10^7\) gives \(R\sqrt v\) up to \(0.1867\) against
\(\tfrac3{16}=0.1875\) (Lean `lemma51_i_closed_form`,
`lemma51_i_nonneg`, `lemma51_i_upper`, `lemma51_i_identity`).
(ii) The gap identity of Lemma 4.3(ii) applied
twice — to \(Y\) at shift \(d_1\), then to the real sequence
\(n\mapsto W(n)\) at shift \(d_2\), with \(\Delta_2W=\Delta\Delta Y\);
the sawtooth form of the carry is the displayed elementary identity.
(iii) The corner identities are Lemma 4.3(ii)
at the three shifts, and the offset bound follows from
\(|\Delta\Delta X|\le4h_1h_2\sup|X''|=3h_1h_2P^{-1/2}<1\). For the
split, group
\(F=\bigl[(m{+}\beta_1{+}\beta_2{+}j)^{3/2}-(m{+}\beta_1{+}\beta_2)^{3/2}\bigr]
+\bigl[(m{+}\beta_1{+}\beta_2)^{3/2}-(m{+}\beta_1)^{3/2}
-(m{+}\beta_2)^{3/2}+m^{3/2}\bigr]\): the first bracket is
\(\tfrac32j(\cdot)^{1/2}\) by the mean value theorem, the second is
\(\beta_1\beta_2\,f''(m+\xi_2)\) for \(f=x^{3/2}\) by the double mean
value theorem. The displayed numerical bounds use
\(m\in(P^{3/2}{-}1,2^{3/2}P^{3/2}]\),
\(\beta_i\in[3h_iP^{1/2}{-}1,\,3\sqrt2\,h_iP^{1/2}{+}1]\)
(from \(\Delta_iX=2h_iX'(\xi)\) and (E1) below), and
\(G'=F'(X)X'\), \(G''=F''(X)X'^2+F'(X)X''\) with
\(F'=\tfrac34j(\cdot)^{-1/2}-\tfrac38\beta_1\beta_2(\cdot)^{-3/2}\),
\(F''=-\tfrac38j(\cdot)^{-3/2}+\tfrac9{16}\beta_1\beta_2(\cdot)^{-5/2}\).

*The bound on \(G''\) is not term by term.* Writing \(n=s^4\), so that
\(X=s^6\), \(X'=\tfrac32s^2\), \(X''=\tfrac34s^{-2}\), the two
\(\beta_1\beta_2\) contributions to
\(G''=F''(X)X'^2+F'(X)X''\) are
\[
\tfrac9{16}\cdot\tfrac94=\tfrac{81}{64}
\quad\text{and}\quad
-\tfrac38\cdot\tfrac34=-\tfrac9{32},
\qquad
\tfrac{81}{64}-\tfrac9{32}=\tfrac{63}{64},
\]
of *opposite sign*. With \(\beta_1\beta_2\le19h_1h_2P\) the combined
coefficient gives \(\tfrac{63}{64}\cdot19=18.7\le25\); bounding the
two separately gives \(\tfrac{99}{64}\cdot19=29.4\), which exceeds
the printed \(25\). The displayed bound is correct, but only through
that cancellation, and the same happens for the \(j\)-terms
(\(-\tfrac{27}{32}+\tfrac9{16}=-\tfrac9{32}\), against the printed
\(2\)). Lean `Gsecond_beta_cancellation`,
`Gsecond_naive_bound_fails`.

The run-length constant is \(22=2+20\): with
\(M=\max\bigl((|j|{+}1)P^{-1/4},h_1h_2P^{-3/4}\bigr)\) the two parts
of the \(G'\) bound are \(\le2M\) and \(\le20M\), so
\(|G'|\le22M\) and the level sets of \(\lfloor G\rfloor\) have
length \(\ge1/(22M)\), which is the displayed minimum. The regrouping,
the offset bound \(|j|\le3\), the \(\beta\)-product bound and all
four derivative estimates are machine-checked in
`formal/Problems/Juggler/BranchFreeze.lean`, and the two mean values that
produce \(\xi_1\) and \(\xi_2\) are supplied in
`formal/Problems/Juggler/MeanValues.lean`, so (iii) is unconditional.

Two of the three ingredients need no analysis at all, because
\(x^{3/2}\) has *explicit* mean values in root coordinates. For the
first, with \(a=\sqrt A\) and \(b=\sqrt{A+j}\),
\[
b^3-a^3=\tfrac32(b^2-a^2)\,c,
\qquad
c=\tfrac23\,\frac{a^2+ab+b^2}{a+b},
\]
and \(a\le c\le b\) reduces to \((2b+a)(b-a)\ge0\) and
\((2a+b)(a-b)\le0\); so \(\xi_1=c^2-A\) is an exact witness
(`mvt_cube_explicit`). The *inner* step of the second is the
**arithmetic mean of the square roots**: \(F'(A{+}B)-F'(A)=BF''(\eta)\)
holds identically with \(\sqrt\eta=\tfrac12(\sqrt A+\sqrt{A+B})\)
(`mvt_sqrt_diff_explicit`). Only the outer step uses a genuine mean value
theorem, applied to \(g(t)=F(t{+}\beta_2)-F(t)\); rationalising its
increment gives the two-sided form the inventory actually uses,
\[
\tfrac34\,\frac{\beta_1\beta_2}{\sqrt{m{+}\beta_1{+}\beta_2}}
\ \le\ \Delta\Delta\ \le\
\tfrac34\,\frac{\beta_1\beta_2}{\sqrt m},
\]
and hence \(\xi_2\) itself, as
\(\sqrt{m+\xi_2}=\tfrac34\beta_1\beta_2/\Delta\Delta\)
(`second_difference_two_sided`, `second_difference_exists_xi`).
Throughout, \(x^{3/2}\) is written \(x\sqrt x\), so no real-power
machinery is needed. On \(20{,}000\) samples the witness \(\xi_2\)
sits between \(0.32\) and \(0.52\) of \(\beta_1+\beta_2\),
comfortably interior. On \(300\) sampled \((P,n,h_1,h_2)\) the printed ranges
are comfortable except the offset lower bound, which is nearly attained:
the ratio to \(|j|P^{3/4}\) runs over \([1.510,2.514]\) against the
printed \([1.5,2.6]\).
(iv) By (ii) and the definitions:
\(\Delta_1\theta_2=\Delta_1Y-\Delta_1v=W-(\lfloor W\rfloor+\kappa_2)
=\{W\}-\kappa_2\) (Lemma 4.3(ii) applied to \(Y\)), likewise
\(\Delta_2\theta_2=\{W'\}-\kappa_2'\), and
\(\Delta\Delta\theta_2=\Delta\Delta Y-\Delta_2g_2
=\{\Delta\Delta Y\}-\kappa''-\Delta_2\kappa_2\) by (ii). Substitute
these into the exact product rule
\[
\Delta\Delta(cf)=c_{11}\,\Delta\Delta f
+(\Delta_2c)(n{+}d_1)\,\Delta_1f
+(\Delta_1c)(n{+}d_2)\,\Delta_2f
+(\Delta\Delta c)\,f,
\]
which is verified by expanding both sides over the four base points
\(n\), \(n{+}d_1\), \(n{+}d_2\), \(n{+}d_1{+}d_2\).

All of (i), (ii) and (iv) are machine-checked in
`formal/Problems/Juggler/MasterIdentity.lean`: the carry sawtooth
(`carry_as_sawtooth`), the substitution
\(\{y{+}w\}-\{y\}=\{w\}-\kappa\) that drives every step of (iv)
(`fract_diff_level2`), the double-gap identity of (ii)
(`lemma51_double_gap`), the four-point product rule
(`double_difference_product`), the master identity itself
(`lemma51_master`), and the bracket bound
(`lemma51_brackets_le_two`). These were previously supported only by the
probe's 60-digit sampling on random odd \(n\); they are exact, so they
are now proved rather than sampled. \(\square\)

One warning, essential to the organization: \(\lfloor\Delta\Delta
Y\rfloor\) itself is *not* frozen. The level-1 carry toggles at
essentially every step and shifts \(\Delta\Delta Y\) by
\(\tfrac32j_1m^{1/2}\), a jump of size \(\asymp P^{3/4}\). The branch
decomposition of (iii), which carries the flicker inside the
indicator over the eight carry branches, is therefore forced: no
decomposition conditioning on the *values* of the level-1 gaps
produces sets on which the second difference is smooth.

### Standing estimates

All estimates of this section take place on a dyadic block
\(n\in(P,2P]\), \(n\) odd, under the standing constraints
\[
\text{(C1)}\quad kh_1h_2\le P^{1/8},
\qquad
\text{(C2)}\quad h_1h_2\le P^{1/2}/3,
\qquad
\text{(C3)}\quad 1\le k\le P^{1/24},
\qquad
\text{(C4)}\quad h_1,\,h_2\le P^{1/24}.
\]
(C1)--(C3) do not by themselves bound the individual shifts: the
product constraints permit one of \(h_1,h_2\) to be as large as
\(\asymp P^{1/2}\). The decoration class (D1) and the third-differencing
reduction of Lemma 5.2(ii) need \(h_1+h_2\le 2P^{1/24}\), which is
(C4). Theorem 5.3 takes \(H_1=P^{1/48}\) and \(H_2=P^{1/24}\), so
(C4) holds there. Every displayed constant below is valid for
\(P\ge P_0\) with an absolute \(P_0\). All sums run over odd \(n\),
and every derivative test below is read through the parity
reindexing of Lemma 3.10: margins and signs are invariant, and each
displayed test bound dominates its reindexed value, so no constant
needs adjustment. The base derivatives are
\[
\text{(E1)}\quad
X'=\tfrac32n^{1/2}\in(1.5,2.13]\,P^{1/2},\quad
X''=\tfrac34n^{-1/2}\in[0.53,0.75)\,P^{-1/2},
\]
\[
\phantom{\text{(E1)}}\quad
-X'''=\tfrac38n^{-3/2}\in[0.13,0.375)\,P^{-3/2},\quad
X''''=\tfrac9{16}n^{-5/2}\le0.57\,P^{-5/2},
\]
and \(m=X-\theta\in(P^{3/2}-1,\,2.83\,P^{3/2}]\). Every gap is a
mean value: for any shift \(2h\),
\[
\text{(E2)}\quad
\Delta X=2hX'(\xi)\in(3hP^{1/2},\,4.3hP^{1/2}),
\qquad
\beta:=\lfloor\Delta X\rfloor+\kappa
\in(3hP^{1/2}-1,\,4.3hP^{1/2}+1),
\]
so that every level-1 gap integer at shift \(2h\) is
\(\asymp hP^{1/2}\) with the displayed constants. For the monomial
weight \(c=\tfrac{3k}4n^{9/8}\) of Theorem 5.3,
\[
\text{(E3)}\quad
c'=\tfrac{27}{32}kn^{1/8},\quad
c''=\tfrac{27}{256}kn^{-7/8},\quad
c'''=-\tfrac{189}{2048}kn^{-15/8},\quad
c''''=\tfrac{2835}{16384}kn^{-23/8},
\]
\[
\text{(E4)}\quad
\Delta_ic=2h_ic'(\xi)\in(1.68,1.85)\,kh_iP^{1/8},
\qquad
\Delta\Delta c=4h_1h_2c''(\xi)\in(0.22,0.43)\,kh_1h_2P^{-7/8}.
\]
On the level-2 side, with \(\beta_i\) as in Lemma 5.1(iii),
\[
\text{(E5)}\quad
W=\Delta_1Y\in(4.4,11)\,h_1P^{5/4},
\qquad
\bigl|(W\circ\text{cell})'\bigr|
=\bigl|W_1'(m)\,X'\bigr|\in(2.2,10.4)\,h_1P^{1/4},
\]
where \(W_1(m)=(m+\beta_1)^{3/2}-m^{3/2}\), so \(\{W\}\) is a *fast*
sawtooth (its argument moves by \(\gg1\) per step), while \(\theta\),
\(\{\Delta_iX\}\), and \(\{\Delta\Delta Y\}\) are slow. The branch
bounds of Lemma 5.1(iii) give, per branch with offset \(j\),
\[
\text{(E6)}\quad
\bigl|(cF)''\bigr|
=\tfrac{945}{512}\,k|j|\,n^{-1/8}\,(1+O(P^{-1/4}))
+O\bigl(kh_1h_2P^{-5/8}\bigr).
\]
The first summand is the offset monomial \(c\cdot\tfrac32j\,m^{1/2}
=\tfrac98kj\,\nu^{15/8}\), differentiated in \(\nu\) with \(j\)
frozen. The second is the zero-offset scale: on a cell the gaps
\(\beta_i\) are frozen, and Lemma 5.2b computes the local curvature
exactly as \(-\tfrac{135}{1024}\,k\beta_1\beta_2\nu^{-13/8}\), which
is \(\asymp kh_1h_2\nu^{-5/8}\) and *negative*. (A model that
differentiates the moving gaps \(\Delta_iX(\nu)\) produces a
different, positive leading coefficient \(\tfrac{243}{128}\) and is
not the local \(f''\).) Finally, the
run and cell inventories: level-1 gap cells at shift \(2h\) number
at most \(1.5hP^{1/2}+1\) with lengths in
\([\tfrac23,\,0.95]\,P^{1/2}/h\), and the frozen-floor runs of
\(\lfloor F_{\boldsymbol\kappa}(X)\rfloor\) number at most
\(22(|j|+1)P^{3/4}\) by the derivative bound of Lemma 5.1(iii).

Throughout, "\(A\) is dominated by \(B\) at margin \(P^{-\rho}\)"
means \(\sup|A|/\inf|B|\le CP^{-\rho}\) with the displayed \(C\):
the composite second derivative then keeps the sign and, up to the
factor \(1+CP^{-\rho}\), the size of \(B\), so Lemma 3.3 applies at
\(B\)'s scale.

The symbol \(P^\varepsilon\) is used only for factors of the form
\(C(\varepsilon)(\log P)^{O(1)}\). The number of Fourier/Vaaler
expansion layers that produce those logarithms is three
(the pieces \(M_2\), \(M_3\), \(M_4\) of the master identity),
independent of \(P\) and of \(k,h_1,h_2,t\). Each layer contributes
\(O(\log P)\) mode mass; there is no further nesting of expansions
whose depth would grow with \(P\). Implied constants in every
\(\ll_\varepsilon\) of Sections 4--6 depend on \(\varepsilon\) and on
(C1)--(C4) only: on those ranges they do not grow with \(k\),
\(h_i\), or \(t\). The threshold \(P_0\) is independent of
\(\varepsilon\) (Appendix A.3) and of \(k,h_i,t\); it is carried by
the Lemma 3.9 comparison \(W\le c_7S/2\).

Every numerical margin in this section is claimed only for
\(P\ge P_0\), and \(P_0\) is **effective**: Appendix A solves
each of the thirty-seven printed threshold inequalities of
Sections 4--6 separately and takes the maximum,
\[
P_0=8.9\cdot10^{13},
\]
attained at the Lemma 3.9 hypothesis \(W\le c_7S/2\) in
Theorem 5.3, Step 5b. Two features of that number should be said
here. First, \(P_0\) does not depend on \(\varepsilon\).
No divisor sum, gcd sum or large-sieve average occurs anywhere in
Sections 3--6, so every \(\ll_\varepsilon\) in those sections is
a power of \(\log P\) and nothing else; the mode masses are
\(O(\log^3P)\) and the two Weyl steps halve the exponent twice,
giving the \(\varepsilon\)-free form
\(K_c(P)\ll P^{1-1/96}(\log P)^{3/4}\) of Theorem 5.3
(Appendix A.3). The threshold at which \(\log^AP\) is absorbed
into \(P^{\varepsilon}\) is a statement about \(\varepsilon\),
not about the proof, and is not part of \(P_0\).

Second, the comparisons stratify sharply, and one of them is the
whole story. The Lemma 3.7 / Lemma 5.2 window hypotheses first
hold together on the printed majorants at a moderate threshold (of
size \(3\cdot10^5\)); every inequality in the paper except the three
Lemma 3.9 balance comparisons of Steps 5a and 5b holds from
\(2.9\cdot10^{10}\) on.
The comparison \(W\le c_7S/2\) then adds three and a half orders of
magnitude on its own: until it holds, a three-term zero of
\(\Phi''\) can keep the sublevel \(\Omega_W\) of length
\(\Theta(P)\) on a dyadic block, and the printed length
\(P^{89/96}\) is the bound of Lemma 3.9, not a claim that the
sublevel is short at small \(P\). Its two ingredients are
\(c_7=1/232\), exactly \(1/\lVert M^{-1}\rVert_\infty\) for the
Vandermonde-type matrix \(M\) of Lemma 3.9 at the exponent triple of
Step 5b and hence not improvable there, and the interpolant error
\(E\) of Lemma 5.2b (Appendix A.5);
the earlier reading \(c_7=1/288\) and the earlier normalisation
\(V=3S^{1/2}P^{-11/24}\) together put \(P_0\) at
\(5.8\cdot10^{23}\). The interpolant error of Step 5b is
\(O(P^{-5/6})\) with leading coefficient \(0.11\), and is not
absorbed into a smaller constant. The constants are not asserted
to be sharp.

The proof of the kernel theorem classifies the differenced pieces
into four classes; three are handled by standard tests, and the
fourth — an exact level-2 wave \(e(qY)\), possibly riding a frozen
floor — is the genuinely new difficulty. We isolate it as a
standalone lemma with its own differencing, so that it can be
checked independently. The checkable objects, in order, are:
Lemma 5.1 (exact identities); Lemma 5.2(i) (differenced wave);
Lemma 5.2(ii) from (i) (Claims A–H); Lemma 5.2b (frozen-shape
interpolant: local \(f''\) versus global \(\Lambda\)); Theorem 5.3
Step 5a (offset composite); Theorem 5.3 Step 5b (three regimes,
the middle band citing Lemma 5.2b and Lemma 3.9); Theorem 6.1
Step E (frozen-shape total phase
\(\Delta\Delta(\tfrac k2 m^{9/4})-\Delta\Delta(c\theta_2)\),
composites \(\tfrac{243}{512}\) and \(\tfrac{1095}{1024}\)).
No later section re-derives these.

**Lemma 5.2 (level-2 waves: the mixed-piece bound).**
Assume (C1)–(C4), write \(\mathcal D=\{0,d_1,d_2,d_1{+}d_2\}\), and
call a *decoration* any sum \(\rho\) of at most nine terms of the
classes

- (D1) \(q'\,\Delta_{2h}\Delta_{2h'}Y(n{+}d')\) with
  \(|q'|\le 4P^{1/24}\), \(1\le h'\le2P^{1/24}\),
  \(d'\in\mathcal D\);
- (D2) \(-\Delta_{2h}\bigl(c\,\lfloor
  F_{\boldsymbol\kappa}(X)\rfloor\bigr)(n)\), with
  \(F_{\boldsymbol\kappa}\) a branch function of Lemma 5.1(iii),
  offset \(|j|\le3\);
- (D3) a smooth \(\varphi\) with
  \(|\varphi''|\le6kh_1h_2h\,P^{-13/8}\) and
  \(|\varphi'''|\le6kh_1h_2P^{-13/8}\), where \(2h\) is the shift
  of part (i);

here \(2h\) is the shift of part (i), and in part (ii) the
decorations are read after the differencing there. Then, for sums
over \(n\in(P,2P]\), \(n\) odd:

(i) *(differenced wave)* for all integers \(u,h\ge1\) with
\(h\le P^{1/8}\), \(uh\le P^{1/2}\), and \(d\in\mathcal D\),
\[
V:=\Bigl|\sum_n
e\bigl(u\,\Delta_{2h}Y(n{+}d)+\rho(n)\bigr)\Bigr|
\;\ll\;
\Bigl((uh)^{1/2}P^{5/8}+(h/u)^{1/2}P^{7/8}+P^{7/8}
+P^{1/24}(uh)^{-1/2}P^{7/8}+R_0^{1/2}P^{3/4}\Bigr)
P^{\varepsilon};
\]

The fifth term is Stage 5's dominant-mode sum over the Stage-2
families, \(3R_0^{1/2}P^{3/4}\log P\); it is the only term carrying the
Stage-2 truncation, which is why Appendix A.6 weighs \(R_0\) against
\(P^{23/24}\) and not against the other four. At \(R_0=P^{5/16}\) it is
\(P^{29/32}\); at the \(R_0=P^{1/4}\) of an earlier draft it read
\(P^{7/8}\) and was absorbed by the third term, which is why it did not
appear before.

(ii) *(waves)* for all integer coefficients \((q_d)_{d\in\mathcal D}\)
with \(|q_d|\le 4P^{1/24}\) and total frequency
\(t:=\sum_{d\in\mathcal D}q_d\) obeying \(0<|t|\le3P^{1/24}\), all
\(\varepsilon_0\in\{0,1\}\), and smooth \(\varphi\) with
\(|\varphi'''|\le3kh_1h_2P^{-13/8}\),
\[
U:=\Bigl|\sum_n
e\Bigl(\sum_{d\in\mathcal D}q_d\,Y(n{+}d)
-\varepsilon_0\,c(n)\lfloor F_{\boldsymbol\kappa}(X(n))\rfloor
+\varphi(n)\Bigr)\Bigr|
\;\ll\;|t|^{-1/6}\,P^{23/24+\varepsilon}.
\]

(iii) *(widened decoration budget)* the conclusion of (i) continues to
hold when at most two of the (D1) terms of \(\rho\) carry, in place of
\(|q'|\le4P^{1/24}\), the widened budget
\[
|q'|\,h'\ \le\ P^{1/2},
\qquad
h'\ \le\ P^{1/24},
\tag{D1$'$}
\]
provided \(uhh'\ge72\) for each such term. For fixed \(u\) and \(h'\)
the shifts violating that are \(h<72/(uh')\), at most \(72\) positive
integers per widened term.

Part (ii) is the mixed-piece bound proper: level-2 waves
\(e(qY)\), possibly riding a frozen floor. Part (i) is the engine
that (ii)'s targeted differencing feeds, and is also used directly
for the \(\{W\}\)-content of the kernel proof. The exponent
\(\tfrac{23}{24}\) is not an accident: written exactly, the wave
\(e(qY)\) is the depth-2 object of Theorem 4.4, and part (ii)
recovers exactly the depth-2 strength — no more. A model of \(U\)
as \(e(sX)\) with a frozen real coefficient \(s\asymp tP^{3/4}\)
would discard the sawtooth \(-\tfrac32tX^{1/2}\theta\) of amplitude
\(\asymp tP^{3/4}\) inside \(tY=t(X-\theta)^{3/2}\); no such
shortcut is taken anywhere below.

*Proof of (ii) from (i).* Eight claims. No appeal is made to
“the same treatment”, “absorbed”, or “inside the budget” except
as a pointer to a displayed comparison in the claim that uses it.

*Claim A (conjugate).* Replacing the summand by its conjugate
replaces \((q_d)\) by \((-q_d)\) and \(t\) by \(-t\). Henceforth
\(t\ge1\). The classes (D1)--(D3) are unchanged (they are
absolute-value conditions).

*Claim B (telescoping, with signs).* Fix \(e_1\in\mathcal D\) with
\(q_{e_1}\ne0\). For each \(d\in\mathcal D\),
\[
Y(n{+}d)=Y(n{+}e_1)+\sigma_{d,e_1}\,
\Delta_{|d-e_1|}Y\bigl(n{+}\min(d,e_1)\bigr),
\]
where \(\sigma_{d,e_1}=+1\) if \(d>e_1\), \(\sigma_{d,e_1}=-1\) if
\(d<e_1\), and \(\sigma_{e_1,e_1}=0\). (If \(d>e_1\) this is the
definition of \(\Delta_{d-e_1}\); if \(d<e_1\) then
\(Y(n{+}d)-Y(n{+}e_1)=-\bigl(Y(n{+}e_1)-Y(n{+}d)\bigr)
=-\Delta_{e_1-d}Y(n{+}d)\).) Therefore, exactly,
\[
\sum_{d\in\mathcal D}q_d\,Y(n{+}d)
=t\,Y(n{+}e_1)
+\sum_{d\ne e_1}q_d\sigma_{d,e_1}\,
\Delta_{|d-e_1|}Y\bigl(n{+}\min(d,e_1)\bigr).
\]
Each difference of elements of \(\mathcal D=\{0,d_1,d_2,d_1{+}d_2\}\)
lies in \(\{\pm d_1,\pm d_2,\pm(d_1{+}d_2)\}\), so
\(|d-e_1|\in\{2h_1,2h_2,2(h_1{+}h_2)\}\) and
\(h':=|d-e_1|/2\in\{h_1,h_2,h_1{+}h_2\}\). By (C4),
\(h'\le h_1{+}h_2\le2P^{1/24}\). Each
\(\min(d,e_1)\) lies in \(\mathcal D\). Each coefficient
\(q':=q_d\sigma_{d,e_1}\) satisfies \(|q'|=|q_d|\le4P^{1/24}\).
There are at most three nonzero seeds.

*Claim C (the \(A\)-process).* Let \(H_3:=\lceil t^{1/3}P^{1/12}\rceil\).
The recorded \(A\)-process after Lemma 3.3, applied to the
unimodular sequence of odd \(n\in(P,2P]\) (at most \(P\) terms;
using \(P\) in place of the true count \(P/2+O(1)\) only enlarges
the right-hand side), gives
\[
|U|^2
\le\frac{2P^2}{H_3}
+\frac{4P}{H_3}\sum_{1\le h_3<H_3}
\bigl|V_{h_3}\bigr|,
\]
where
\[
V_{h_3}
=\sum_n
e\bigl(t\,\Delta_{2h_3}Y(n{+}e_1)+\rho_{h_3}(n)\bigr)
\]
and \(\rho_{h_3}\) is the increment of the remaining phase at
shift \(2h_3\), written out in Claim E. (The recorded display
sums \(1\le h<H\); we have renamed the index \(h_3\).)

*Claim D (the parameters of (i) are admissible).* The hypothesis
gives \(t\le3P^{1/24}\). (The individual bound \(|q_d|\le4P^{1/24}\)
would give only \(16P^{1/24}\), and that is not a harmless slack: it
would put the shift comparison below at \(16^{12}=2.8\cdot10^{14}\)
and make it the largest threshold in the paper. The total-frequency
bound is the one to carry, and Step 4 of Theorem 5.3 --- the only
place (ii) is invoked --- supplies it, because the wave modes come
one per expansion layer from three layers at truncation
\(J_2=P^{1/24}\), so \(|t|\le3J_2\).) Write
\(x:=t^{1/3}P^{1/12}\), so \(H_3=\lceil x\rceil\). Claim C sums
over \(1\le h_3<H_3\), hence \(h_3\le\lceil x\rceil-1\le x\)
(the integer \(\lceil x\rceil-1\) never exceeds \(x\)). In
particular \(h_3\le t^{1/3}P^{1/12}\le3^{1/3}P^{7/72}\) with
\(3^{1/3}<1.45\). Two comparisons for the shift range of (i):
\[
\frac7{72}<\frac18,
\qquad
1.45\,P^{7/72}\le P^{1/8}
\quad\text{once}\quad
P\ge1.45^{36}.
\]
The threshold is \(1.45^{36}=1.1\cdot10^{6}\), comfortably under
\(P_0\). The exponent gap here is \(\tfrac18-\tfrac7{72}=\tfrac1{36}\),
so whatever constant stands in front of \(P^{7/72}\) is paid at the
thirty-sixth power; that is why the sharp \(t\) matters and why an
earlier draft, which used \(16^{1/3}\) and checked the result against
a standing \(P_0\) "of size \(10^{24}\)", silently carried a threshold
of \(2.8\cdot10^{14}\). Thus every index in the Claim C sum satisfies
\(1\le h_3\le P^{1/8}\) for \(P\ge P_0\). (The averaging length
itself obeys \(H_3\le x+1\le3P^{7/72}\) once
\(1\le0.48P^{7/72}\), i.e. once \(P^{7/72}\ge3\), which holds
for \(P\ge3^{72/7}<10^6\); Claim G uses only
\(H_3\le2x\), which follows from \(x\ge1\).) The product range
of (i) is \(th_3\le tx=t^{4/3}P^{1/12}\). Substituting
\(t\le3P^{1/24}\) gives
\(t^{4/3}P^{1/12}\le3^{4/3}P^{1/18+1/12}
=4.33\,P^{5/36}\), and
\(4.33P^{5/36}\le P^{1/2}\) once \(4.33\le P^{13/36}\), i.e. once
\(P\ge58\), again far under \(P_0\). Hence every
\(V_{h_3}\) in the Claim C sum is an instance of (i) with
\((u,h)=(t,h_3)\), provided \(\rho_{h_3}\) is a legal
decoration.

*Claim E (class membership of \(\rho_{h_3}\)).* Expanding the
increment of Claim B, the frozen-floor term, and \(\varphi\),
\[
\rho_{h_3}
=
\sum_{d\ne e_1}
q_d\sigma_{d,e_1}\,
\Delta_{2h_3}\Delta_{|d-e_1|}Y\bigl(n{+}\min(d,e_1)\bigr)
-\varepsilon_0\,\Delta_{2h_3}\bigl(c\lfloor F_{\boldsymbol\kappa}(X)\rfloor\bigr)
+\Delta_{2h_3}\varphi.
\]
This is a sum of at most five terms (three of type (D1), one of
type (D2), one of type (D3)), inside the budget of nine.

- (D1). Each summand is \(q'\,\Delta_{2h}\Delta_{2h'}Y(n{+}d')\)
  with \(2h=2h_3\) the shift of this invocation of (i),
  \(q'=q_d\sigma_{d,e_1}\), \(|q'|\le4P^{1/24}\),
  \(h'=|d-e_1|/2\le2P^{1/24}\), and \(d'=\min(d,e_1)\in\mathcal D\).
  This is the printed class (D1).
- (D2). The middle term is exactly the printed class (D2) at the
  shift \(2h\) of (i), with the same branch function
  \(F_{\boldsymbol\kappa}\) and the same offset \(|j|\le3\). If
  \(\varepsilon_0=0\) the term is absent.
- (D3). The input \(\varphi\) of (ii) is produced, in every
  application in this paper, with
  \(|\varphi'''|\le3kh_1h_2P^{-13/8}\) (the kernel's smooth
  remnants satisfy \(|c''|\le0.11kP^{-7/8}\) and
  \(|(\Delta_ic)''|\le0.19kh_iP^{-15/8}\), both far smaller).
  Then
  \[
  \bigl|(\Delta_{2h_3}\varphi)''\bigr|
  \le2h_3\sup|\varphi'''|
  \le6kh_1h_2h_3P^{-13/8}.
  \]
  This is *exactly* the (D3) second-derivative budget at the shift
  \(h=h_3\) of this invocation, and it is the sharp form Stage 6
  needs. It must not be relaxed to a budget of the shape
  \(3kh_1h_2P^{-5/8}\): that is larger by a factor \(P/(2h_3)\)
  --- at \(h_3\le P^{1/8}\), a factor \(\ge\tfrac12P^{7/8}\) ---
  and Stage 6 cannot dominate it. Indeed
  \(3kh_1h_2P^{-5/8}\big/\bigl(0.35uhP^{-3/4}\bigr)
  =8.6\,kh_1h_2P^{1/8}/(uh)\), which by (C1) reaches
  \(8.6P^{1/4}\) at \(uh=1\); at any \(uh\le8.6P^{1/4}\) such a
  \(\varphi''\) could cancel the Stage-4 curvature outright, and
  Lemma 3.3 at that scale would not apply. The third derivative of
  the increment satisfies
  \(\bigl|(\Delta_{2h_3}\varphi)'''\bigr|
  \le2\sup|\varphi'''|
  \le6kh_1h_2P^{-13/8}\), which is the printed (D3)
  third-derivative budget. (The printed \(6\) rather than \(3\)
  is exactly this factor of two: (D3) is closed under one
  difference of an input that starts at \(3\).) Thus
  \(\Delta_{2h_3}\varphi\) is of class (D3).

No other terms appear. In particular this reduction does not
introduce a large-\(u\) first-differenced wave; those, when they
sit on the same piece as a \(t\ne0\) wave in Theorem 5.3, are
treated in Step 4 of that theorem, after this lemma.

*Claim F (invoke (i)).* By Claims D and E, part (i) applies to
each \(V_{h_3}\) and gives
\[
|V_{h_3}|
\ll
\Bigl(
(th_3)^{1/2}P^{5/8}
+(h_3/t)^{1/2}P^{7/8}
+P^{7/8}
+P^{1/24}(th_3)^{-1/2}P^{7/8}
\Bigr)P^{\varepsilon}.
\]
The fourth term is the (D1) run-boundary remainder of Stage 6; it
is part of the printed bound of (i), not an extra cost smuggled
through the average.

*Claim G (the \(H_3\)-average).* Substitute Claim F into Claim C.
Write \(S_1,S_2,S_3,S_4\) for the four contributions to
\((4P/H_3)\sum_{h_3<H_3}|V_{h_3}|\), and use the crude bounds
\(\sum_{h_3<H_3}h_3^{1/2}\le H_3\cdot H_3^{1/2}=H_3^{3/2}\) and
\(\sum_{h_3<H_3}h_3^{-1/2}\le H_3\cdot1=H_3\) (the second is the
worst case \(h_3=1\) on every term; a tighter integral
\(2H_3^{1/2}\) is available and is not needed). Then, with
\(H_3\le2t^{1/3}P^{1/12}\),
\[
\begin{aligned}
\frac{2P^2}{H_3}
&\le2t^{-1/3}P^{2-1/12}
=2t^{-1/3}P^{23/12},\\
S_1
&\le4t^{1/2}H_3^{1/2}P^{13/8}\,P^{\varepsilon}
\le6t^{2/3}P^{5/3}\,P^{\varepsilon}
=6\,(tP^{-1/4})\,t^{-1/3}P^{23/12}\,P^{\varepsilon}\\
&\le96P^{1/24-1/4}\,t^{-1/3}P^{23/12}\,P^{\varepsilon},\\
S_2
&\le4t^{-1/2}H_3^{1/2}P^{15/8}\,P^{\varepsilon}
\le6t^{-1/3}P^{23/12}\,P^{\varepsilon},\\
S_3
&=4P^{15/8}\,P^{\varepsilon}
=4\,(t^{1/3}P^{-1/24})\,t^{-1/3}P^{23/12}\,P^{\varepsilon}\\
&\le11P^{1/72-1/24}\,t^{-1/3}P^{23/12}\,P^{\varepsilon},\\
S_4
&\le4P^{1/24}t^{-1/2}P^{15/8}\,P^{\varepsilon}
=4t^{-1/2}P^{23/12}\,P^{\varepsilon}
=4t^{-1/6}\cdot t^{-1/3}P^{23/12}\,P^{\varepsilon}.
\end{aligned}
\]
The identities used here are
\(1/24+13/8=5/3\), \(5/3-23/12=-1/4\),
\(1/24+15/8=23/12\), \(15/8+1/24=23/12\),
and \(1/24+15/8=23/12\). The exponent contributed by
\(H_3^{1/2}\) is \(1/24\), not \(1/12\): the bound
\(H_3\le2t^{1/3}P^{1/12}\) enters each of \(S_1,S_2\) under a
square root, giving \(H_3^{1/2}\le\sqrt2\,t^{1/6}P^{1/24}\).
Each prefactor is \(O(1)\) on
\(t\ge1\), \(P\ge P_0\): \(96P^{-5/24}\to0\),
\(P^{1/72-1/24}=P^{-1/36}\to0\), and \(4t^{-1/6}\le4\).
Hence
\(|U|^2\ll t^{-1/3}P^{23/12+\varepsilon}\).

Only two of the five contributions survive with an \(O(1)\)
prefactor — the \(A\)-process head \(2P^2/H_3\) and \(S_2\), of
constants \(2\) and \(4\sqrt2\le6\) — so the balance is exact and
explicit:
\[
|U|^2\le\bigl(8+o(1)\bigr)\,t^{-1/3}P^{23/12+\varepsilon},
\qquad
|U|\le\bigl(2.83+o(1)\bigr)\,t^{-1/6}P^{23/24+\varepsilon}.
\]
The choice \(H_3=\lceil t^{1/3}P^{1/12}\rceil\) is exactly the one
that equalizes those two terms; any other exponent in \(H_3\) makes
one of them dominate and loses the \(23/24\).

*Claim H (square root).* Taking square roots,
\(|U|\ll t^{-1/6}P^{23/24+\varepsilon}\), which is (ii).
The implied constant depends on \(\varepsilon\) and on
(C1)--(C4) only. \(\square\) of the reduction.

The six stages below prove (i). They are used as a black box by
Claims F--H; the only decoration information those claims need is
Claim E together with the printed fourth term of (i).

*Proof of (i).* Six stages; write \(\nu=n+d\) (a shift of the block
by at most \(d_1{+}d_2\le P^{1/2}\), harmless in every estimate) and
\(\Delta=\Delta_{2h}\).

*Stage 1 (the \(m\)-linear form).* By Lemma 4.3(i) at the bases
\(\nu\) and \(\nu{+}2h\),
\[
u\,\Delta Y
=u\,A_h(\nu)
+\tfrac{3u}2\,g(\nu)\,(\nu{+}2h)^{3/4}
-\tfrac{3u}2\,\theta_\nu\,\Delta(\nu^{3/4})
+u\,\Delta E,
\]
with \(g=m(\nu{+}2h)-m(\nu)\), \(|u\Delta E|\le uP^{-3/4}\) (total
cost over the block \(\le2\pi uP^{1/4}\le2\pi P^{3/4}\)), and
\[
A_h(\nu)=\tfrac32\nu^{3/2}\Delta(\nu^{3/4})
-\tfrac12\Delta(\nu^{9/4})
=-\tfrac{27}8h^2\nu^{1/4}\bigl(1+O(hP^{-1})\bigr):
\]
the two \(\nu^{5/4}\)-scale contributions cancel exactly at leading
order (both equal \(\tfrac94h\nu^{5/4}\)), leaving
\(|uA_h''|\le0.64\,uh^2P^{-7/4}\). The sawtooth coefficient is
\[
B(\nu):=\tfrac{3u}2\,\Delta(\nu^{3/4})
=\tfrac94\,uh\,\xi^{-1/4}\in(1.89,2.25]\,uhP^{-1/4}.
\]

*Stage 2 (gap cells and the exact shift device).* Split into the
level sets of \(\lfloor\delta_h\rfloor\),
\(\delta_h(\nu)=(\nu{+}2h)^{3/2}-\nu^{3/2}\): at most
\(1.5hP^{1/2}+1\) cells of length in
\([\tfrac23,\,0.95]\,P^{1/2}/h\) (E1). On a cell \(g=G+\kappa\) with
\(G=\lfloor\delta_h\rfloor\) frozen and
\(\kappa=[\theta_\nu\ge1-\{\delta_h\}]\); Vaaler-expand \(\kappa\)
at truncation \(R_0=P^{5/16}\) (majorant cost
\(\le4P/R_0=4P^{11/16}\)). The exponent \(5/16\) is not free choice:
Stage 5 below pays \(R_0^{1/2}\) for it and Step 5b(a) pays \(R_0\),
while the fifth-letter window of Theorem 6.3 needs \(R_0\) *large*.
Appendix A.6 solves the four competing sites; \(5/16\) is the value
at which all four hold below \(P_0\), and \(1/4\) --- the exponent an
earlier draft used --- is not. \(R_0\) is the truncation of *this*
expansion. It is reused as the Lemma 3.7 mode truncation \(J\) in
Stage 3(s1) below, and again in Step 5b(a), where the modes counted
are Stage 2's own and the identification \(J=R_0\) is deliberate; the
per-window Lemma 3.7 truncation of Step 3a is a separate parameter,
chosen there as \(P^{1/4}\), and is not affected by the value of
\(R_0\).
The moving endpoint costs nothing: as in Theorem 4.4, Step 4, the
endpoint's smooth part contributes the exact phase
\(r\delta_h(\nu)\), and
\(e(r\nu^{3/2}+r\delta_h(\nu))=e(r(\nu{+}2h)^{3/2})\), so every
\(r\)-term falls into the two smooth families \(e(r\nu^{3/2})\),
\(e(r(\nu{+}2h)^{3/2})\), \(0<|r|\le R_0\), with weights
\(\le1/|r|\); the in-cell variation of the coefficient is exactly
\(1\) and one Abel summation absorbs it at a factor \(\le2{+}2\pi\).

*Stage 3 (the \(\theta\)-sawtooth).* Two regimes.
(s1) If \(uh\le P^{3/16}\) then \(|B|\le2.25P^{-1/16}<\tfrac12\) for
\(P\ge P_0\): Lemma 3.7 with \(T=P^{1/2}\), \(J=R_0\)
(hypothesis \(T\ge8(1+|B|)\): \(P^{1/2}\ge9\) for \(P\ge P_0\))
expands
\(e(-B_0\{\nu^{3/2}\}\dots)\) per window (here one window: the total
drift of \(B\) is \(\le0.6uhP^{-1/4}\le0.6P^{-1/16}<1\)) into the
same two mode families at coefficient factor
\(\min(2,2\pi|B|)\le14.2P^{-1/16}\) (the constant is
\(2\pi\cdot2.25=14.14\), not \(14\)), mass \(O(\log P)\), flat
cost \(\le12P^{1/2}\), majorant
\(\le14.2P^{-1/16}\cdot4P^{11/16}\).
(s2) If \(P^{3/16}<uh\le P^{1/2}\) then \(|B|\le2.25P^{1/4}\) and
\(B\) drifts by at most \(1\) on windows of length
\(\ge P^{5/4}/(0.6uh)\ge1.2P^{3/4}\): at most \(0.6P^{1/4}+1\)
windows. Per window Lemma 3.7 at the centre \(B_0\)
(\(T=P^{1/2}\ge8(1+2.25P^{1/4})\) for \(P\ge P_0\), since
\(P^{1/4}\ge19\); flat cost \(\le8(1{+}2.25P^{1/4})P^{1/2}
\le19P^{3/4}\) in total, once \(P\ge4096\)) produces modes \(e(w\nu^{3/2})\) whose
coefficients decay as
\(\min(2,\tfrac1{\pi|w+B_0|})+\min(2,\tfrac1{\pi|w|})\); the
window-boundary cost is, using \(uh>P^{3/16}\),
\(\le(0.6P^{1/4}{+}1)\,(0.35\,uh)^{-1/2}P^{3/8}
\le1.1\,P^{1/4-3/32+3/8}=1.1\,P^{17/32}\le P^{5/8}\). Modes with
\(|w|\) in the collision window are treated in Stage 5.

*Stage 4 (the main curvature, \(r=w=0\)).* On a cell the remaining
phase is \(\tfrac{3u}2G(\nu{+}2h)^{3/4}+uA_h+(\text{smooth
decorations})\), with second derivative
\[
-\tfrac9{32}\,uG\,(\nu{+}2h)^{-5/4}
\in-[0.35,\,1.20]\,uh\,P^{-3/4}
\qquad(\text{E2}),
\]
single-signed with in-cell ratio \(\sup/\inf\le3.5\): the second
derivative of \(\tfrac{3u}2G(\nu{+}2h)^{3/4}\) is the single term
\(\tfrac{3u}2G\cdot\tfrac34\cdot(-\tfrac14)(\nu{+}2h)^{-5/4}\), with
\(G\) frozen and bounded by (E2). The competitor
\(uA_h''\) has ratio
\(\le0.64uh^2P^{-7/4}/(0.35uhP^{-3/4})\le1.9hP^{-1}\le1.9P^{-7/8}\);
decoration competitors are bounded in Stage 6. Lemma 3.3 per cell
and summation give
\[
\sum_{\text{cells}}
\Bigl(\ell_i\lambda^{1/2}+\lambda^{-1/2}\Bigr)
\le1.1\,(uh)^{1/2}P^{5/8}
+2.6\,(h/u)^{1/2}P^{7/8},
\]
the first because the cells partition the block, so
\(\sum_i\ell_i\lambda_i^{1/2}\le P\lambda_{\max}^{1/2}
=(1.20)^{1/2}(uh)^{1/2}P^{5/8}=1.096\,(uh)^{1/2}P^{5/8}\), and the
second because there are at most \(1.5hP^{1/2}+1\) cells, giving
\(1.5\cdot(0.35)^{-1/2}=2.536\) plus a lower-order term. These are the
two main terms of (i).

*Stage 5 (nonzero modes and collisions).* A mode \(w\ne0\) (or
\(r\ne0\); identical treatment with weight \(1/|r|\)) adds the phase
\(w\nu^{3/2}\) of curvature \(\ge0.53|w|P^{-1/2}\).
If \(0.53|w|P^{-1/2}\ge4\cdot1.20uhP^{-3/4}\), i.e.
\(|w|\ge9.1\,uhP^{-1/4}\), the mode curvature dominates at margin
\(\ge4\): Lemma 3.3 over the full block gives
\(\le1.4|w|^{1/2}P^{3/4}+1.4|w|^{-1/2}P^{1/4}\), and the
coefficient-weighted sums are
\(\le3R_0^{1/2}P^{3/4}\log P=3P^{29/32}\log P\) (families of Stage 2,
regime (s1)) and \(\le CP^{7/8}\log P\) (regime (s2) tails). If
\(|w|\le0.11\,uhP^{-1/4}\) the main curvature dominates at margin
\(\ge4\) and the mode rides along at Stage 4's scale, weight
summable to \(O(\log P)\). In the remaining collision window
\(0.11\,uhP^{-1/4}\le|w|\le9.1\,uhP^{-1/4}\) (nonempty only in
regime (s2)), the two curvatures can cancel: there the phase is the
two-term monomial
\(a\nu^{3/4}+w\nu^{3/2}\) with \(a=\tfrac{3u}2G\asymp uh P^{1/2}\)
plus perturbations already shown \(\rho_0\)-small, and Lemma 3.8
with \((\alpha,\beta)=(\tfrac34,\tfrac32)\) applies per window. The
range of \(M\) is pinned from below by the \(\nu^{3/4}\) scale alone,
which never degenerates: by (E1),
\(\delta_h=3h\xi^{1/2}\in(3hP^{1/2},\,4.25hP^{1/2}]\), so
\(G=\lfloor\delta_h\rfloor>3hP^{1/2}-1\) and
\[
|a|P^{-5/4}=\tfrac32uG\,P^{-5/4}
>uhP^{-3/4}\Bigl(4.5-\tfrac{1.5}{hP^{1/2}}\Bigr)
\ge4.4\,uhP^{-3/4}
\qquad(P\ge P_0),
\]
while \(|a|P^{-5/4}\le6.37\,uhP^{-3/4}\) and
\(|w|P^{-1/2}\in[0.11,9.1]uhP^{-3/4}\) on the band. Hence
\[
M\in[4.4,\ 9.1]\,uhP^{-3/4},
\qquad
M\le9.1\,P^{-1/4}\le1
\quad(P\ge7000),
\]
using \(uh\le P^{1/2}\) for the last two. (The \(\nu^{3/4}\) curvature
carries a factor \(G\asymp hP^{1/2}\), so \(M\) cannot be small on
this band; an earlier draft printed the far weaker
\(M\in[0.03,11]uhP^{-3/4}\), which cost a factor \(12\) in the second
sum below and \(5\) in the third.) Then:
\[
\le C_E\bigl(|I_w|M^{1/2}+M^{-1/2}+(P/M)^{1/3}\bigr)
\quad\text{per window.}
\]
Summing over the at most \(0.6P^{1/4}{+}1\) windows — the transition
cost \((P/M)^{1/3}\) carries no window-length factor, which is why
it sums — with the \(O(\log P)\) collision-band coefficient mass:
\[
\sum_w|I_w|M^{1/2}=P\,M^{1/2}\le3.1\,(uh)^{1/2}P^{5/8},\qquad
\sum_wM^{-1/2}\le0.77P^{1/4}\cdot0.48\,(uh)^{-1/2}P^{3/8}
\le0.37\,(uh)^{-1/2}P^{5/8},
\]
\[
\sum_w(P/M)^{1/3}
\le0.77P^{1/4}\cdot0.611\,(uh)^{-1/3}P^{7/12}
=0.47\,(uh)^{-1/3}P^{5/6}\le0.47\,P^{5/6-1/16}=0.47\,P^{37/48},
\]
the windows numbering at most \(0.6P^{1/4}+1\le0.77P^{1/4}\)
(\(P\ge1200\)), the first sum using that the windows partition the
block, and the last using \(uh>P^{3/16}\) in regime (s2). The
collision-band total is
\(\le C\bigl((uh)^{1/2}P^{5/8}+P^{37/48}\bigr)\log P\le
CP^{7/8}\log P\), with \(\tfrac{37}{48}<\tfrac78\).

*Stage 6 (decorations).* Each class is dominated at a displayed
margin against the Stage-4 curvature
\(\ge0.35uhP^{-3/4}\).

- (D1). On the branch decomposition of Lemma 5.1(iii) at the shift
  pair \((h_3\text{-role }h,\,h')\): the arcs are absorbed by the
  shift device (log mass); the \(b\)-run boundaries add
  \(\le1.5(h{+}2h')P^{1/2}+2\) cells, at boundary cost
  \(\le1.5(h{+}2h')P^{1/2}(0.35uh)^{-1/2}P^{3/8}
  \le2.6(h/u)^{1/2}P^{7/8}+5.1\,h'(uh)^{-1/2}P^{7/8}\).
  The second term is the printed fourth term of (i): since
  \(h'\le2P^{1/24}\), it is
  \(\le11\,P^{1/24}(uh)^{-1/2}P^{7/8}\). When (i) is invoked from
  (ii), Claim G averages this term at the worst-case \(h_3=1\),
  giving \(S_4\le4t^{-1/6}\,t^{-1/3}P^{23/12}P^{\varepsilon}\).
  The \(\theta\)-coefficient of the decoration is
  \(\le|q'|\bigl(2|j'|P^{-1/4}+20hh'P^{-3/4}\bigr)
  \le24P^{1/24-1/4}+160P^{1/24+1/8+1/24-3/4}
  =24P^{-5/24}+160P^{-13/24}\).
  This is \(O(P^{-5/24})\), hence \(\lvert B\rvert\le1\) for
  \(P\ge P_0\); Lemma 3.7 at \(T=P^{1/2}\) applies either way
  (even a constant-size leftover would satisfy
  \(T\ge8(1+\lvert B\rvert)\)). The modes are expanded in the
  Stage-2 families. Its smooth curvature has ratio
  \(\le|q'|\bigl(2|j'|P^{-5/4}+25hh'P^{-7/4}\bigr)
  /(0.35uhP^{-3/4})\le69P^{1/24-1/2}+572P^{1/24+1/24-1}
  \le P^{-1/4}\): dominated.
- (D2). Write
  \(\Delta(c\lfloor F\rfloor)
  =(\Delta c)\lfloor F\rfloor+c_+\Delta\lfloor F\rfloor\)
  with \(c_+=c(\cdot{+}2h)\).
  (a) \((\Delta c)\lfloor F\rfloor=(\Delta c)F-(\Delta c)\{F\}\):
  the smooth part has curvature
  \(\le\bigl((\Delta c)F\bigr)''\le7kh|j|P^{-9/8}
  +28khh_1h_2P^{-13/8}\), ratio to the main curvature
  \(\le20k|j|P^{-3/8}/u\le60P^{1/24-3/8}\): dominated. The sawtooth
  part has coefficient
  \(\Delta c\in(1.68,1.85)\,khP^{1/8}\), handled per windows of
  drift \(\le1\): at most \(2khP^{1/8}{+}1\) windows, at boundary
  cost
  \(\le2khP^{1/8}(0.35\,uh)^{-1/2}P^{3/8}
  \le3.4\,k\,(h/u)^{1/2}P^{1/2}\). Per window, Lemma 3.7 at
  \(T=P^{1/2}\) yields modes \(e(q''(F\circ X))\) whose index obeys
  \(|q''|\le|B_0|+J\) with the *truncation* \(J=R_0=P^{5/16}\) of
  Stage 2 — not the window parameter \(T\) — so that
  \(|q''|\le1.85khP^{1/8}+P^{5/16}\le2.85P^{5/16}\) by (C3) and
  \(h\le P^{1/8}\) (here \(R_0\) is the larger of the two, which it
  was not at \(R_0=P^{1/4}\)), and the curvature is
  \[
  \le\bigl(1.85khP^{1/8}{+}R_0\bigr)\cdot3|j|P^{-5/4}
  \le2.85P^{5/16}\cdot6P^{-5/4}
  =17.1P^{-15/16},
  \]
  ratio to the main curvature
  \(\le48.9P^{-3/16}\): dominated for \(P\ge P_0\), with room
  \(0.12\) against the margin \(\tfrac14\).  That is the sharp
  statement, and it is the one to quote: weakening it to
  \(49P^{-1/16}\), as an earlier draft did, is true but useless ---
  a constant of \(49\) on a gap of \(\tfrac1{16}\) does not clear
  \(\tfrac14\) until \(10^{36}\).
  (Substituting \(T\) for \(J\) here would give only \(9P^{-3/4}\),
  whose ratio \(26/(uh)\) is not \(o(1)\) at \(uh=O(1)\);
  \(17.1/0.35=48.9\) fixes the constant either way.) The flat cost is, per point,
  \(8(1{+}B_0)/T\), so in total
  \(\le8\bigl(1{+}1.85khP^{1/8}\bigr)P^{1/2}
  \le8P^{1/2}+15\,khP^{5/8}\le23\,P^{1/24+1/8+5/8}
  =23\,P^{19/24}\), using \(h\le P^{1/8}\) and (C3); this sits inside
  the Step 6 budget \(P^{23/24}\) from \(P\ge23^{6}=1.5\cdot10^{8}\).
  (It is *not* below \(P^{7/8}\), which an earlier draft printed:
  the gap \(\tfrac78-\tfrac{19}{24}=\tfrac1{12}\) would make that
  claim wait until \(23^{12}=2.2\cdot10^{16}\).)
  (b) \(c_+\Delta\lfloor F\rfloor\): by the gap identity applied to
  the sequence \(F\circ X\),
  \(\Delta\lfloor F\rfloor=\lfloor\Delta F\rfloor+\kappa_F\).
  \(\Delta F\) has total drift
  \(\le P\cdot2h\sup|(F\circ X)''|\le P\cdot2h(2|j|P^{-5/4}
  +25h_1h_2P^{-7/4})\le13hP^{-1/4}+50h\,h_1h_2P^{-3/4}<1\), so
  \(\lfloor\Delta F\rfloor\) takes at most two values, on at most
  two intervals; per value the phase \(-q_0c_+\) (\(|q_0|\le
  2{+}6hP^{-1/4}\le3\)) has curvature \(\le0.4kP^{-7/8}\), ratio
  \(\le1.2kP^{-1/8}/(uh)\le1.2P^{1/24-1/8}\): dominated. The carry
  \(\kappa_F=\{F\}+\{\Delta F\}-\{F{+}\Delta F\}\) is a sum of unit
  sawtooths in slow variables (all drifts \(<1\) per step): Lemma
  3.5 at truncation \(P^{1/8}\) (majorant \(\le3\cdot4P^{7/8}\))
  gives modes \(e(q''(F\circ X))\)-type of curvature
  \(\le P^{1/8}\cdot3|j|P^{-5/4}\le9P^{-9/8}\), ratio
  \(\le26P^{-3/8}\): dominated.
- (D3). The class budget is \(|\varphi''|\le6kh_1h_2h\,P^{-13/8}\),
  which is what Claim E delivers for \(\Delta_{2h_3}\varphi\). The
  ratio to the Stage-4 curvature is
  \[
  \frac{6kh_1h_2h\,P^{-13/8}}{0.35uhP^{-3/4}}
  =\frac{18\,kh_1h_2P^{-7/8}}u
  \le18P^{1/8-7/8}=18P^{-3/4},
  \]
  using (C1) in the form \(kh_1h_2\le P^{1/8}\) and \(u\ge1\):
  dominated. Only the second-derivative budget is used; the
  third-derivative budget is carried so that (D3) is closed under one
  further difference. It is essential that the budget be the
  differenced one: a second derivative of size \(3kh_1h_2P^{-5/8}\)
  --- the shape an *undifferenced* smooth remnant would have --- is
  larger by \(P/(2h)\) and is *not* dominated (Claim E).

*The wide (D3) class: what is and is not covered.* The narrowing of
(D3) above is not cosmetic, and it is worth recording exactly where the
wider class — \(|\varphi''|\le3kh_1h_2P^{-5/8}\), the shape an
*undifferenced* smooth remnant would have — stands. Write
\(\Phi_2=3kh_1h_2P^{-5/8}\).

*Regime A: \(\Phi_2\le\tfrac14\cdot0.35uhP^{-3/4}\)*, i.e.
\(uh\ge34.3\,kh_1h_2P^{1/8}\). Here the decoration is dominated and
Stage 6 applies verbatim; nothing changes.

*Regime B: \(uh<34.3\,kh_1h_2P^{1/8}\le34.3P^{1/4}\)* by (C1). Here
\(\varphi''\) may cancel the Stage-4 curvature and \(\varphi'''\) may
exceed \(\lambda_{\mathrm{main}}'\), so neither the second- nor the
third-derivative test is available on a cell; and \(\Phi\) is not a
monomial combination, so Lemmas 3.8–3.9 do not apply either. What
replaces them is the *frozen* \(G\). Since \(\delta_h\) is continuous
and increasing, \(G=\lfloor\delta_h\rfloor\) increases by exactly \(1\)
at each cell boundary, so \(f''\) carries a sawtooth of amplitude
\(\tfrac9{32}u(\nu{+}2h)^{-5/4}\in[0.118,0.282]\,uP^{-5/4}\) that no
continuous \(\varphi''\) can follow, and \(f'\) jumps by
\(\tfrac98u(\nu{+}2h)^{-1/4}\in[0.946,1.125]\,uP^{-1/4}\) at each
boundary. Two consequences, both elementary:

- the cells are *flat*: at the sawtooth curvature scale the phase
  departs from linear by
  \(\le0.282\,uP^{-5/4}\ell^2\le0.26\,uP^{-1/4}h^{-2}\), which is
  \(<1\) throughout regime B once \(h\ge3\); so the second-derivative
  test is the wrong tool there and Kusmin–Landau is the right one;
- the cell frequencies are *spread*: across the \(\ge1.24hP^{1/2}\)
  cells, \(f'\) sweeps at least \(1.17\,uhP^{1/4}\) full periods.

If the \(\lVert f'_i\rVert\) inherit that spread, then
\(\sum_i\min\bigl(\ell,(2\lVert f'_i\rVert)^{-1}\bigr)\ll
hP^{1/2}\log P\le P^{5/8}\log P\) by \(h\le P^{1/8}\) — comfortably
inside the third printed term \(P^{7/8}\) of (i). Numerically this is
what happens. Taking \(\varphi=\tfrac{27}{10}\nu^{5/4}\), which lies in
the wide class at \(u=h=k=h_1=h_2=1\) and cancels the smooth part of the
Stage-4 curvature exactly, the block sums at
\(P=2\cdot10^3,8\cdot10^3,3.2\cdot10^4,1.28\cdot10^5,5.12\cdot10^5\) are
\(36,\,12,\,220,\,479,\,385\), against \(P^{1/2}=45,\dots,716\) and a
\(P^{7/8}\) larger by a further factor \(P^{3/8}\); the cells are flat
(\(\mathrm{amp}\cdot\ell^2\approx3\cdot10^{-3}\)) and \(f'\) sweeps
\(19\) to \(37\) periods.

*Closing regime B.* Write \(t=\{\delta_h(\nu)\}\in[0,1)\) on a cell and
\(q(\nu)=\tfrac98u(\nu{+}2h)^{-1/4}\in[0.946,1.125]\,uP^{-1/4}\), so that
\[
f'(\nu)=\Psi(\nu)-q(\nu)\,t,
\qquad
\Psi:=\tfrac{27}8uh\nu^{1/4}+uA_h'+\varphi' .
\]
The decoration enters only through \(\Psi\); the term \(-qt\) comes from the
frozen \(G\) and no choice of \(\varphi\) can remove it. Since \(t\) sweeps
\([0,1)\) across each cell, \(f'\) sweeps an interval of length \(\asymp q\)
there unless \(\Psi'\) cancels the sweep, and that dichotomy is the whole
argument. Put \(D_i:=\Psi'-q/\ell\) on cell \(i\).

*(a) \(|D_i|\ge q/(2\ell)\).* Then \(f'\) is monotone on the cell and sweeps an
interval of length \(\ge q/2\). Split the cell by dyadic \(\lVert f'\rVert\):
the \(j\)-th piece has length \(\ll2^{-j}\ell\) and Kusmin–Landau bounds its
sum by \(\ll2^{j}/q\); balancing at \(2^{j}=(\ell q)^{1/2}\) gives a cell total
\(\ll(\ell/q)^{1/2}\le1.01\,(uh)^{-1/2}P^{3/8}\). Summing over the
\(\le1.5hP^{1/2}{+}1\) cells,
\[
\ll1.6\,(h/u)^{1/2}P^{7/8},
\]
which is exactly the second printed term of (i). Case (a) is closed.

*(b) \(|D_i|<q/(2\ell)\).* Then \(\Psi'\asymp q/\ell\asymp uhP^{-3/4}\), so
\(\varphi''\) must sit within \(O(uhP^{-3/4})\) of \(\tfrac12uhP^{-3/4}\), which
by \(|\varphi''|\le\Phi_2\) confines this case to
\(uh\le6\,kh_1h_2P^{1/8}\). Here \(f'\) is nearly constant on each cell, equal
to \(\alpha_i:=\Psi(\nu_i)\) up to \(O(q)\), and \(\alpha_{i+1}-\alpha_i
=\Psi'\ell\asymp q\): the cell frequencies advance by \(\asymp uP^{-1/4}\) per
cell. The cell sums are \(\ll\min(\ell,\lVert\alpha_i\rVert^{-1})\), and
\(\Psi\) is monotone here, sweeping \(V\asymp uhP^{1/4}\) periods over the
block. Counting the samples in each period,
\[
\sum_i\min\bigl(\ell,\lVert\alpha_i\rVert^{-1}\bigr)
\ll hP^{1/2}\log P+V\ell
\ll P^{5/8}\log P+1.1\,uP^{3/4},
\]
using \(h\le P^{1/8}\). The first term is inside the third printed term of (i)
with room. The second is \(\le P^{7/8}\) precisely when \(u\le0.9P^{1/8}\).

So regime B closes outright for \(u\le P^{1/8}\), and case (a) closes for every
\(u\). What remains is the sliver
\[
P^{1/8}<u\le 6\,kh_1h_2P^{1/8}/h
\quad\text{inside case (b)},
\]
where the argument above yields only the crude \(V\ell\): it charges a full cell
to each of the \(V\) crossings of \(\Psi\) through \(\mathbb Z\). That is
certainly lossy — those \(V\) cells carry different constant terms and should
not add coherently — but making the saving explicit needs a bound on how often
\(\lVert\alpha_i\rVert\) is small, i.e. the classical
\(\sum_{i<N}\min(\ell,\lVert iq\rVert^{-1})\) estimate for the *slowly varying*
difference \(q\), and that is not carried out here.

*The sliver is a narrow-class problem.* Case (b) looks like the wide class but
is not. Its defining condition \(|D_i|<q/(2\ell)\) reads
\(\Psi'\in\bigl(\tfrac{q}{2\ell},\tfrac{3q}{2\ell}\bigr)\), and with
\(q/\ell=\tfrac{27}{16}uh\nu^{-3/4}\) and
\(\Psi'=\tfrac{27}{32}uh\nu^{-3/4}+\varphi''\) this pins
\[
0\;<\;\varphi''\;<\;\tfrac{27}{16}\,uh\nu^{-3/4}
\qquad\text{throughout case (b)} .
\]
So in the only case left open, \(|\varphi''|\) is at most \(4.8\) times the
Stage-4 curvature \(0.35uhP^{-3/4}\): the wide budget
\(\Phi_2=3kh_1h_2P^{-5/8}\), larger by \(P/(2h)\), is *never* attained there.
The wide class collapses to a narrow one exactly where it mattered.

Two consequences follow at once. First, \(\Psi\) is strictly increasing with
\(\Psi'\in[0.84,2.53]uh\nu^{-3/4}\), so the cell frequencies
\(\alpha_i=\Psi(\nu_i)\) form a strictly increasing sequence with gaps
\[
\alpha_{i+1}-\alpha_i\in[0.562,\,1.688]\,uP^{-1/4},
\]
of bounded ratio \(3\). Second, in the extreme sub-case \(\Psi'\equiv q/\ell\)
one has \(\Psi'=q\,\delta_h'\), hence \(\alpha_i=\Psi(\nu_i)\approx qG_i+\)const
with \(G_i\) consecutive integers: an approximate arithmetic progression of
difference \(q\asymp uP^{-1/4}\). The residual is therefore exactly the
classical sum \(\sum_{i<N}\min(\ell,\lVert iq\rVert^{-1})\), for a difference
that drifts by \(19\%\) across the block (because
\(q=\tfrac98u(\nu{+}2h)^{-1/4}\)); that drift is what prevents the progression
from locking onto a rational, and it is the saving the crude \(V\ell\) throws
away.

*The sliver, measured.* Maximising over the free linear term as before, at
\(h=1\) and \(u\) up to the top of the sliver:
\[
\begin{array}{r|rr|rr|r}
P & u & \text{case (b)} & \text{case (a)} & \text{printed (i)} & \text{(b)}/\text{(i)}\\\hline
8\cdot10^{3} & 1 & 192 & 397 & 5478 & 0.035\\
8\cdot10^{3} & 13 & 234 & 193 & 4315 & 0.054\\
3.2\cdot10^{4} & 1 & 475 & 1035 & 18154 & 0.026\\
3.2\cdot10^{4} & 7 & 546 & 403 & 13788 & 0.040\\
3.2\cdot10^{4} & 13 & 544 & 413 & 13536 & 0.040
\end{array}
\]
The ratio to the printed bound stays near \(0.04\) across the whole sliver and
falls with \(P\). At \(P=3.2\cdot10^{4}\), \(u=13\) the crude \(V\ell\) is
\(34\,214\) against an actual \(544\): the period-counting step is lossy there by
a factor \(63\), which is the whole of the remaining gap.
*Numerical check of the whole regime.* The decoration is free to carry a linear
term, so the honest test is to maximise over it; on the natural grid that
maximum is a discrete Fourier transform of \(e(f(n))\). At
\(u=h=k=h_1=h_2=1\), the optimum over all class-(D3) linear shifts, for the
undecorated phase and for the two extremal decorations
\(\varphi=\pm\tfrac{27}{10}\nu^{5/4}\) (which cancel the Stage-4 curvature and
the drift of \(f'\) respectively), is
\[
\begin{array}{r|rrr|rr}
P & \text{none} & \text{curvature} & \text{drift} & P^{7/8} & \text{worst}/P^{7/8}\\\hline
8\cdot10^{3} & 169 & 192 & 397 & 2601 & 0.152\\
3.2\cdot10^{4} & 383 & 475 & 1035 & 8750 & 0.118\\
1.28\cdot10^{5} & 792 & 958 & 2536 & 29431 & 0.086
\end{array}
\]
The worst case grows like \(P^{0.67}\) and its ratio to \(P^{7/8}\) *decreases*;
the drift-cancelling decoration is the stronger of the two, as the analysis
above predicts, and neither approaches the printed bound.

*Totals.* Stages 1–6 bound \(V\) by
\[
C\Bigl((uh)^{1/2}P^{5/8}+(h/u)^{1/2}P^{7/8}+P^{7/8}
+P^{1/24}(uh)^{-1/2}P^{7/8}
+k\,(h/u)^{1/2}P^{1/2}\Bigr)\log^3P.
\]
The last term is \(\le P^{1/24}(h/u)^{1/2}P^{1/2}\), and
\(P^{1/24+1/2}=P^{13/24}<P^{7/8}=P^{21/24}\), so it is
absorbed by the second printed term of (i). The (D1)
run-boundary term \(P^{1/24}(uh)^{-1/2}P^{7/8}\) is kept in
the printed bound of (i); it is \(\le P^{11/12}\) for
\(uh\ge1\), and \(11/12<23/24\). This is (i).

*Costs collected.* Each class contributes to \(V\) as follows,
all times \(P^{\varepsilon}\).

| Class | Bound contributed to \(V\) | Absorbed by |
|---|---|---|
| Stage 1 remainder \(u\Delta E\) | \(P^{3/4}\) | \(P^{7/8}\) |
| Stage 2 majorant / shift device | \(P^{3/4}\) | \(P^{7/8}\) |
| Stage 3 (s1) sawtooth | \(P^{3/4}\) | \(P^{7/8}\) |
| Stage 3 (s2) windows / collision | \((uh)^{1/2}P^{5/8}+P^{7/8}\) | (i) |
| Stage 4, \(r=w=0\) | \((uh)^{1/2}P^{5/8}+(h/u)^{1/2}P^{7/8}\) | (i) |
| Stage 5, non-collision modes | \(P^{7/8}\) | (i) |
| (D1) curvature | dominated at \(P^{-1/4}\) | Stage 4 |
| (D1) run boundaries | \((h/u)^{1/2}P^{7/8}+h'(uh)^{-1/2}P^{7/8}\) | printed (i); Claim G |
| (D2)(a) smooth / sawtooth | dominated; \(P^{7/8}\) flat | Stage 4; (i) |
| (D2)(b) gap / carry | dominated; \(P^{7/8}\) majorant | Stage 4; (i) |
| (D3) | dominated at \(P^{-3/4}\) | Stage 4 |

No decoration class is used later unless it appears in this
table.

*Proof of (iii).* The budget \(|q'|\le4P^{1/24}\) enters Stages 1--6
in exactly two places, both in Stage 6's (D1) bullet: the smooth
curvature ratio and the \(\theta\)-coefficient. Everything else there
depends on \(h'\) and not on \(|q'|\) --- in particular the
run-boundary cost
\(2.6(h/u)^{1/2}P^{7/8}+5.1h'(uh)^{-1/2}P^{7/8}\), whose second term is
the fourth printed term of (i) and is unchanged because
\(h'\le P^{1/24}\) still holds under (D1\('\)).

*Curvature ratio.* Against the Stage-4 curvature \(0.35uhP^{-3/4}\),
using \(2|j'|\le6\), \(6/0.35\le18\), \(25/0.35\le71.5\) and
\(|q'|h'\le P^{1/2}\) in both summands,
\[
\frac{|q'|\bigl(2|j'|P^{-5/4}+25hh'P^{-7/4}\bigr)}{0.35uhP^{-3/4}}
\ \le\ \frac{18}{uhh'}+\frac{72}u\,P^{-1/2}.
\]
The second summand is \(o(1)\) for \(P\ge P_0\); the first is
\(\le\tfrac14\) once \(uhh'\ge72\), which is the stated hypothesis.
Stage 6 then dominates at margin \(\ge4\), as in the printed case.

*\(\theta\)-coefficient, and the window inventory it forces.* By
(D1\('\)), \(|j'|\le3\), \(h'\ge1\) and \(h\le P^{1/8}\),
\[
|q'|\bigl(2|j'|P^{-1/4}+20hh'P^{-3/4}\bigr)
\ \le\ \frac{6P^{1/4}}{h'}+20hP^{-1/4}\ \le\ 7P^{1/4}.
\]
This is not \(O(P^{-5/24})\), so the decoration's sawtooth is expanded
by the large-\(B\) treatment of Stage 3(s2) and not by the small-\(B\)
one of (s1). Each line below is that treatment's with \(2.25\)
replaced by \(7\). The hypothesis \(T=P^{1/2}\ge8(1+|B|)\) reads
\(P^{1/4}\ge56.14\), i.e. \(P\ge9.9\cdot10^{6}\). Since \(B\) is
monotone on the dyadic block its drift is at most \(\sup|B|\), giving
at most \(7P^{1/4}+1\) windows on which \(B\) moves by \(\le1\). The
boundary charge at the Stage-4 curvature is
\[
(7P^{1/4}{+}1)(0.35uh)^{-1/2}P^{3/8}\ \le\ 13.5\,(uh)^{-1/2}P^{5/8},
\]
which needs no lower bound on \(uh\): Stage 3(s2) may simplify its own
using \(uh>P^{3/16}\) because (s2) *is* that regime, whereas a widened
decoration is large independently of the main mode and can occur while
the main sawtooth sits in (s1). It is dominated by the fourth printed
term of (i), since \(\tfrac58<\tfrac1{24}+\tfrac78\). The flat cost is
\(8(1{+}|B|)P^{1/2}\le64P^{3/4}\) in total. The modes are the (s2)
families, with weights
\(\min(2,\tfrac1{\pi|w+B_0|})+\min(2,\tfrac1{\pi|w|})\) and index
\(|w|\le|B_0|+R_0\le2R_0\) for \(P\ge P_0\), because
\(7P^{1/4}\le P^{5/16}\) once \(P\ge7^{16}=3.3\cdot10^{13}\); Stage 5
therefore pays at most \(\sqrt2\) more on its dominant sum and a factor
\(7/0.6\le12\) on its (s2) tails, both absorbed by
\(P^{\varepsilon}\). \(\square\)

*Checklist for (ii) from (i).* Claims A–H are the verification.
In order: conjugate (A); telescoping with signs \(\sigma_{d,e_1}\)
(B); the recorded \(A\)-process \(2P^2/H_3+4P/H_3\sum|V|\) (C);
admissible range \(h_3\le P^{1/8}\) and \(th_3\le P^{1/2}\) (D);
class membership of \(\rho_{h_3}\), five terms, (D3) closed under
one difference from an input with \(|\varphi'''|\le3kh_1h_2P^{-13/8}\)
(E); invoke the printed (i), fourth term included (F); average,
five displayed comparisons, worst-case \(h_3=1\) on the (D1)
remainder (G); square root (H). Collision windows of (i) are only
the band \(0.11\,uhP^{-1/4}\le\lvert w\rvert\le9.1\,uhP^{-1/4}\) of
Stage 5, and only in regime (s2). On a cell the integer
\(G=\lfloor\delta_h\rfloor\) is held frozen; the smooth remainder
\(A_h\) does not differentiate a frozen gap. Lemma 3.9 is not used
in (i) or (ii); it is used only on the global interpolant \(\Phi\)
of Lemma 5.2b. Every \(k,h_1,h_2\) dependence passes through
(C1)--(C4). \(\square\)

The balance to keep in mind: with the trivial bound
\(|V_{h_3}|\le P\), part (ii)'s differencing returns nothing beyond
the choice of \(H_3\); the content of the lemma is that the floor,
coefficient, and carry bookkeeping of Stages 3–6 survives the
targeted differencing with the Stage-4 curvature intact. What is
*not* available is the frozen-coefficient shortcut: per frozen run
the run length \(P^{1/4}\) is shorter than
\(\lambda^{-1/2}\asymp(uh)^{-1/2}P^{3/8}\) for small \(uh\), and the
run-boundary cost \((h/u)^{1/2}P^{7/8}\), summed against the
\(H_3\)-average, is exactly what pins the final exponent at
\(\tfrac{23}{24}\).

The remaining object that Theorem 5.3 must not confuse with
Lemma 5.2 is the *zero-offset anchor*: the phase
\(c(G_F-J_F)\) on a branch with \(j=0\). On a cell the integers
\(\beta_1,\beta_2,J_F\) are frozen, so
\((cG_F)''=c''G_F+2c'G_F'+cG_F''\) is computed with those
integers held constant while \(X(\nu)\) and \(c(\nu)\) move. The
interpolant used on the whole block is the same frozen-shape
formula with the smooth gap values \(\Delta_iX(\nu)\) substituted
as numbers, not differentiated. The next lemma records that
computation, so that Step 5b is only a classification of scales.

**Lemma 5.2b (frozen-shape interpolant on a zero-offset piece).**
Assume (C1)–(C4), \(j=0\), and the *middle-band wave bound*
\[
u\ \le\ 186\,kh_2P^{1/8},
\qquad
u'\ \le\ 186\,kh_1P^{1/8}.
\tag{C5}
\]
(C5) is not implied by (C1)–(C4): Lemma 5.2(i) admits \(uh_1\le P^{1/2}\),
hence \(u\) as large as \(P^{1/2}\), and at that size the first error term
below is \(\tfrac9{16}P^{-3/4}\), larger than the stated bound by a
factor \(P^{7/24}\). It *is* the middle-band condition of Step 5b:
\(\mu\le60\lambda_0\) with
\(\mu=0.84\max(uh_1,u'h_2)P^{-3/4}\) and
\(\lambda_0\le2.6\,kh_1h_2P^{-5/8}\) gives
\(\max(uh_1,u'h_2)\le\tfrac{60\cdot2.6}{0.84}kh_1h_2P^{1/8}
=185.7\,kh_1h_2P^{1/8}\), opened to \(186\). Keeping the shifts
visible, rather than passing to the cruder
\(u,u'\le186P^{5/24}\) through \(kh_i\le P^{1/12}\), is what lets
the two error terms below combine before they are converted. Work on a common-refinement piece of
the gap cells of both shifts, the frozen-floor runs of
\(\lfloor F_{\boldsymbol\kappa}(X)\rfloor\), and the sawtooth windows
already counted, so that the integers \(G_1\), \(G_2\),
\(\beta_1\), \(\beta_2\), and \(J_F=\lfloor F_{\boldsymbol\kappa}(X)\rfloor\)
are constant. Write \(G_F=F_{\boldsymbol\kappa}\circ X\). The remaining
phase on the piece has second derivative
\[
f''
=-\tfrac9{32}\Bigl(uG_1(\nu{+}2h_1)^{-5/4}
+u'G_2(\nu{+}2h_2)^{-5/4}\Bigr)
+2c'G_F'+c\,G_F''+c''(G_F-J_F)
+wX''+O(\rho_0),
\]
where the \(O(\rho_0)\) collects decorations already shown small
against the scales of Lemma 3.8, and the chain rule uses *frozen*
\(\beta_i\):
\[
G_F'=F'(X)\,X',\qquad
G_F''=F''(X)\,(X')^2+F'(X)\,X'',
\]
with, from Lemma 5.1(iii) at \(j=0\),
\[
F'(m)=-\tfrac38\beta_1\beta_2\,m^{-3/2},\qquad
F''(m)=\tfrac9{16}\beta_1\beta_2\,m^{-5/2}
\]
up to the relative \(O(\beta/m)=O(P^{-1})\) of the mean-value
\(\xi\). Define the *frozen-shape interpolant* \(\Lambda\) by
substituting the smooth gap values
\(\tilde\beta_i(\nu)=\Delta_iX(\nu)\) and
\(\delta_{h_i}(\nu)=(\nu{+}2h_i)^{3/2}-\nu^{3/2}\) for those
frozen integers *as values only*. The \(\nu\)-derivatives of
\(\tilde\beta_i\) are not introduced:
\[
\begin{aligned}
\Lambda(\nu)
&=-\tfrac9{32}u\,\delta_{h_1}(\nu)\,(\nu{+}2h_1)^{-5/4}
-\tfrac9{32}u'\,\delta_{h_2}(\nu)\,(\nu{+}2h_2)^{-5/4}\\
&\qquad
+2c'(\nu)\,\widetilde F'(X(\nu))\,X'(\nu)
+c(\nu)\,\widetilde G''(\nu)
+\tfrac12 c''(\nu)
+wX''(\nu),
\end{aligned}
\]
where \(\widetilde F'(m)=-\tfrac38\tilde\beta_1\tilde\beta_2\,m^{-3/2}\)
and \(\widetilde G''\) is the frozen-shape formula for \(G_F''\)
evaluated at \(\tilde\beta_i\). Then, for \(P\ge P_0\),
\[
\lvert f''-\Lambda\rvert
\le\tfrac9{32}(u{+}u')P^{-5/4}
+\lvert c''\rvert
+0.57\,k(h_1{+}h_2)P^{-9/8}
\le52.9\,k(h_1{+}h_2)P^{-9/8}+0.11P^{-5/6}
\le106\,P^{-25/24}+0.11P^{-5/6}.
\]
The second term is the leading interpolant error and is not
absorbed into a smaller multiple of \(P^{-5/6}\). Moreover
\(\Lambda=\Phi''+r\), where
\[
\Phi(\nu)
=a\,\nu^{5/4}+b\,\nu^{11/8}+w\,\nu^{3/2},
\qquad
a=-\tfrac{27}{10}(uh_1+u'h_2),\quad
b=-\tfrac{405}{176}\,kh_1h_2,
\]
the exponents \(\bigl(\tfrac54,\tfrac{11}8,\tfrac32\bigr)\) lie in
\(E\) and are pairwise distinct, and \(r\) obeys the \(\rho_0(E)\)
bounds of Lemma 3.9. If \(w=0\), drop the third term. The local
frozen curvature of the anchor itself is
\[
2c'G_F'+c\,G_F''
=-\tfrac{135}{1024}\,k\beta_1\beta_2\,\nu^{-13/8}
\bigl(1+O(P^{-1/4})\bigr),
\]
and therefore
\[
\lambda_0
:=\bigl\lvert\bigl(c(G_F-J_F)\bigr)''\bigr\rvert
\in[0.35,\,2.6]\,kh_1h_2P^{-5/8}
\]
on the standing range: the summand \(c''(G_F-J_F)\) is
\(O(kP^{-7/8})\) and sits in the \(O(P^{-1/4})\) relative error.

*Proof.* There are three replacements of a frozen integer by a
smooth gap of the same scale, and each moves its argument by at
most \(1\).

(i) By the gap identity \(G_i=\lfloor\delta_{h_i}\rfloor+\kappa_i\)
with \(\kappa_i\in\{0,1\}\), so
\(\lvert G_i-\delta_{h_i}\rvert=\lvert\kappa_i-\{\delta_{h_i}\}\rvert\le1\)
— *not* merely \(<2\), which would double the constant below. The
bound \(1\) is sharp and cannot be halved by recentring
\(\Lambda\) (Lean `gap_error_le_one`, `gap_error_one_attained`,
`gap_error_not_halved_by_recentring`): \(\kappa_i=1\) exactly when
\(\{\nu^{3/2}\}+\{\delta_{h_i}\}\ge1\), so both values of
\(\kappa_i\) occur, and a global shift of the interpolant that
halves the error for one doubles it for the other. Hence the wave
terms differ from \(\Lambda\) by at most
\(\tfrac9{32}(u{+}u')P^{-5/4}\), and by (C5) this is
\(\le\tfrac9{32}\cdot186\,k(h_1{+}h_2)P^{1/8-5/4}
=52.3125\,k(h_1{+}h_2)P^{-9/8}\) --- the *same shape* as the third
term, which is why the two are added before converting. Together
they are \(52.8795\le52.9\,k(h_1{+}h_2)P^{-9/8}\le105.8\), i.e.
\(\le106\,P^{-25/24}\) by \(k(h_1{+}h_2)\le2P^{1/12}\) from
(C3) and (C4).

(ii) \(\lvert\beta_i-\tilde\beta_i\rvert\le1\), so
\(\lvert\beta_1\beta_2-\tilde\beta_1\tilde\beta_2\rvert
\le\lvert\beta_1\rvert+\lvert\tilde\beta_2\rvert
\le4.3(h_1{+}h_2)P^{1/2}+1\). The frozen-shape second derivative is
linear in that product with coefficient
\(\tfrac{135}{1024}k\nu^{-13/8}\), so the difference is at most
\(\tfrac{135}{1024}\cdot4.3\;k(h_1{+}h_2)P^{1/2}P^{-13/8}
=0.567\,k(h_1{+}h_2)P^{-9/8}\), printed as \(0.57\) --- not \(0.6\),
which would push the sum in (i) past \(52.9\): this is the
third displayed term. (An earlier draft carried \(8\) here ---
fourteen times the true value --- and \(219\) in place of
\(106\) above.)

(iii) \(\lvert G_F-J_F\rvert<1\), and \(\Lambda\) replaces this
fractional part by \(\tfrac12\) only in the already-expanded
\(c''\)-term. The difference is at most \(\lvert c''\rvert
\le0.11kP^{-7/8}\le0.11P^{-5/6}\). This replacement is *not*
made in the phase \(c(G_F-J_F)\): substituting \(J_F\mapsto
G_F-\tfrac12\) there would collapse the anchor to \(c/2\) and
destroy the curvature.

Steps (i)--(iii) and the assembly are machine-checked in
`formal/Problems/Juggler/PaperBAssembly.lean` (`interpolant_step_i`,
`interpolant_step_ii_constant`, `interpolant_assembly`), with the power
identities \(P^{1/8}P^{-5/4}=P^{-9/8}\) and
\(P^{1/12}P^{-9/8}=P^{-25/24}\) as hypotheses.

These are all the differences between \(f''\) and \(\Lambda\).
In particular \(\Lambda\) is not \((cF_{\mathrm{sm}})''\) for
\(F_{\mathrm{sm}}=\tfrac34(\Delta_1X)(\Delta_2X)X^{-1/2}\). That
composite differentiates the moving gaps and is a different
function.

It remains to match leading monomials. Mean-value expansion
gives \(\delta_h(\nu)=3h\,\xi^{1/2}\) with
\(\xi\in(\nu,\nu{+}2h)\), hence
\(\delta_h(\nu)\,(\nu{+}2h)^{-5/4}
=3h\,\nu^{-3/4}\bigl(1+O(hP^{-1})\bigr)\) and
\[
-\tfrac9{32}u\,\delta_{h_1}(\nu)\,(\nu{+}2h_1)^{-5/4}
=-\tfrac{27}{32}uh_1\,\nu^{-3/4}\bigl(1+O(h_1P^{-1})\bigr).
\]
This is \(\Phi''\) of \(a\nu^{5/4}\), because
\(a\cdot\tfrac54\cdot\tfrac14=-\tfrac{27}{32}\).

For the anchor, keep \(\beta_1,\beta_2\) frozen and expand the
chain rule at \(c=\tfrac{3k}4\nu^{9/8}\),
\(X=\nu^{3/2}\). Then \(G_F=\tfrac34\beta_1\beta_2X^{-1/2}
=\tfrac34\beta_1\beta_2\nu^{-3/4}\) at leading order,
\(G_F'=-\tfrac9{16}\beta_1\beta_2\nu^{-7/4}\), and
\(G_F''=\tfrac{63}{64}\beta_1\beta_2\nu^{-11/4}\), so
\[
\begin{aligned}
c''G_F
&=\tfrac{81}{1024}\,k\beta_1\beta_2\nu^{-13/8},\\
2c'G_F'
&=-\tfrac{972}{1024}\,k\beta_1\beta_2\nu^{-13/8},\\
c\,G_F''
&=\tfrac{756}{1024}\,k\beta_1\beta_2\nu^{-13/8}.
\end{aligned}
\]
The sum is \(-\tfrac{135}{1024}\,k\beta_1\beta_2\nu^{-13/8}\).
(The term \(\tfrac12 c''\) in \(\Lambda\) is \(O(kP^{-7/8})\) and
is absorbed in \(r\).) Substituting the interpolating values
\(\tilde\beta_i=3h_i\nu^{1/2}(1+O(hP^{-1}))\) converts the
product \(\beta_1\beta_2\) into \(9h_1h_2\nu\), and the curvature
becomes \(-\tfrac{1215}{1024}kh_1h_2\nu^{-5/8}\). This is
\(\Phi''\) of \(b\nu^{11/8}\), because
\[
b\cdot\tfrac{11}8\cdot\tfrac38
=-\tfrac{405}{176}\cdot\tfrac{33}{64}
=-\tfrac{1215}{1024}.
\]
The window mode is exactly \(wX''=\tfrac34w\nu^{-1/2}\). Write
\(r=\Lambda-\Phi''\), so that Lemma 3.9 is applied to
\(\Phi+g\) with \(g''=r\). The remainder \(r\) is the sum of the
mean-value errors \(O(hP^{-1})\) on the two leading monomials
and the leftover \(\tfrac12 c''\). In the middle band of Step 5b
one has \(S\ge0.35\,kh_1h_2P^{-5/8}\) (and \(S\ge0.35P^{-5/8}\)
whenever \(kh_1h_2\ge1\)). The three ratios Lemma 3.9 needs are
then, for \(P\ge P_0\),
\[
\frac{\lvert r\rvert}{S}
\le C_1P^{-1/4},\qquad
\frac{P\lvert r'\rvert}{S}
\le C_2P^{-1/4},\qquad
\frac{P^2\lvert r''\rvert}{S}
\le C_3P^{-1/4},
\]
with absolute \(C_1,C_2,C_3\) coming from
\(\lvert\tfrac12 c''\rvert\le0.053kP^{-7/8}\),
\(\lvert\tfrac12 c'''\rvert\le0.047kP^{-15/8}\),
\(\lvert\tfrac12 c''''\rvert\le0.044kP^{-23/8}\),
and the wave remainders \(O(uh^2\nu^{-7/4})\) which are
\(O(P^{-35/24})\) on the printed inventory. Each ratio is
therefore \(\le\rho_0(E)=c_7/8=1/2304\) for \(P\ge P_0\).
(The worst standing cell is \(kh_1h_2=1\); larger products
only enlarge \(S\).)

The range of \(\lambda_0\) is the same leading term against
\(\beta_i\in(3h_iP^{1/2}-1,\,4.3h_iP^{1/2}+1)\) and
\(\nu\in(P,2P]\): the product \(\beta_1\beta_2\nu^{-13/8}\)
runs through \([2.92,18.5]\,h_1h_2P^{-5/8}\), and
\(\tfrac{135}{1024}\approx0.132\) converts this to
\([0.38,2.44]\), opened to \([0.35,2.6]\) for the
\(O(P^{-1/4})\) and the \(\pm1\) in the \(\beta\)-bounds.
\(\square\)

The global monomial \(\nu^{11/8}\) appears only after
\(\tilde\beta_1\tilde\beta_2\sim\nu\) is substituted. On a single
frozen run the curvature is a multiple of \(\nu^{-13/8}\), i.e.
the second derivative of a \(\nu^{3/8}\) phase. Lemma 3.9 is
applied to the *global* model \(\Phi\), whose second derivative
tracks \(\Lambda\); the local \(f''\) stays within the interpolant
error of that model, which is the only comparison the sublevel
argument uses.

### Architecture of the proof of Theorem 5.3

The proof is long, and its length is bookkeeping rather than depth: one
reduction, one identity, one hard lemma, and a classification. This
table is the map. Nothing in it is proved here; every row points at the
statement that does the work.

| # | component | input | output | consumed by |
|---|---|---|---|---|
| — | Lemma 5.1(i) | exact Taylor of \(m^{9/4}\) at \(v\) | kernel phase \(=\) level-2 local floor defect, error \(kR\ll kP^{-9/8}\) | the definition of \(K_c\) |
| — | Lemma 5.1(ii) | \(\lbrack\{A\}+\{B\}\ge1\rbrack=\{A\}+\{B\}-\{A+B\}\) | every carry is a difference of unit sawtooths | Step 3(3b), (3d) |
| — | Lemma 5.1(iii) | branch functions \(F_{\boldsymbol\kappa}\), offset \(\lvert j\rvert\le3\) | branch decomposition; smooth-per-branch, frozen floor \(J_F\) | Steps 3(3e), 5 |
| — | Lemma 5.1(iv) | (i)–(iii) | master identity \(\varphi_2=M_1+M_2+M_3+M_4\) | Step 2 |
| 1 | Step 1 | \(A\)-process twice, \(H_1=P^{1/48}\), \(H_2=P^{1/24}\) | \(K_c\) reduced to \(T_2\); (C1)–(C4) hold with room \(P^{-1/48}\) | Steps 2–6 |
| 2 | Step 2 | Lemma 5.1(iv), estimate (E4) | \(M_1\) deleted at cost \(2.7P^{1/4}\); \(M_2,M_3,M_4\) remain | Step 3 |
| 3 | Step 3 | Lemma 3.7 (sawtooth windows), Lemma 3.5 at \(J_2=P^{1/24}\) (carries) | every piece \(=\) anchor \(+\) waves \(+\) differenced waves \(+\) (D3)-smooth | Steps 4–5 |
| 4 | Step 4 | pieces with total wave frequency \(t\ne0\), \(\lvert t\rvert\le3P^{1/24}\) | \(\ll\lvert t\rvert^{-1/6}P^{23/24+\varepsilon}\); \(t=0\) collapses exactly to (D1) | Step 6; \(t=0\) to Step 5 |
| — | Lemma 5.2(i) | \(u,h\ge1\), \(h\le P^{1/8}\), \(uh\le P^{1/2}\), decoration \(\rho\) | \(V\)-bound \(\ll((uh)^{1/2}P^{5/8}+(h/u)^{1/2}P^{7/8}+\cdots)P^{\varepsilon}\) | Lemma 5.2(ii); Steps 3(3a), 4, 5b |
| — | Lemma 5.2(ii) | \(\lvert q_d\rvert\le4P^{1/24}\), \(0<\lvert t\rvert\le3P^{1/24}\) | \(\ll\lvert t\rvert^{-1/6}P^{23/24+\varepsilon}\) | Step 4 |
| — | Lemma 5.2(iii) | up to two (D1) terms with \(\lvert q'\rvert h'\le P^{1/2}\), and \(uhh'\ge72\) | the bound of (i) at the widened budget | Step 4, leftover modes |
| 5a | Step 5a | offset branches \(j\ne0\) | \(\le1.8P^{23/24+\varepsilon}\); anchor curvature \(\lambda_a\in[1.30,1.43]k\lvert j\rvert P^{-1/8}\) | Step 6 |
| 5b | Step 5b | zero-offset branches \(j=0\) | \(\ll P^{15/16+\varepsilon}\) | Step 6 |
| 6 | Step 6 | all of the above | \(\lvert T_2\rvert\ll P^{23/24+\varepsilon}\), hence \(\lvert K_c\rvert\ll P^{1-1/96+\varepsilon}\) | Theorem 6.1 |

Two structural facts the table is meant to make visible.

*Where the exponent comes from.* The saving \(\tfrac1{96}
=\tfrac14\cdot\tfrac1{24}\) is inherited, not produced: it is the
depth-2 strength \(P^{23/24}\) of Lemma 5.2(ii) passed back through
the two differencings of Step 1. Every other estimate in the proof is
arranged to reach that exponent and no further; improving the wave
bound improves \(\delta\) proportionally, and improving anything else
improves nothing.

*Where the threshold comes from.* \(P_0\) is not distributed across
the proof. Of the thirty-seven displayed inequalities, thirty-six hold
from \(2.9\cdot10^{10}\) or below; the binding one is the comparison
\(W\le c_7S/2\) inside Step 5b's middle band (Appendix A). That single
row is why Lemma 3.9's constant \(c_7=1/232\) is proof-critical and
why the middle band is the part of the argument to check first.

**Step 5b in detail.** It is the only step that splits, and the only
one where several curvature scales meet. Write
\(\lambda_0\in[0.35,2.6]\,kh_1h_2P^{-5/8}\) for the frozen anchor
curvature and \(\mu=0.84\max(uh_1,u'h_2)P^{-3/4}\) for the strongest
differenced-wave scale present.

| regime | condition | tool | output |
|---|---|---|---|
| anchor-dominant | \(60\mu\le\lambda_0\) | Lemma 3.3 per run at \(\lambda_0\) | \(\le1.7(kh_1h_2)^{1/2}P^{11/16}+40(h_1h_2/k)^{1/2}P^{9/16}\) |
| mode-dominant | \(\mu\ge60\lambda_0\) | Lemma 5.2(i), anchor as decoration | \(\ll((uh_1)^{1/2}P^{5/8}+(h_1/u)^{1/2}P^{7/8}+P^{7/8})P^{\varepsilon}\) |
| middle band | \(\tfrac1{60}\le\mu/\lambda_0\le60\) | Lemma 5.2b, then Lemma 3.9 | transition set measured once, trivial bound; **binds \(P_0\)** |

The middle band is the only place in the paper where the composite
second derivative can cross zero inside a cell, and the only consumer
of the three-term form of Lemma 3.9. It is also where condition (C5)
of Lemma 5.2b is discharged: (C5) does *not* follow from (C1)–(C4),
and the middle-band inequality \(\mu\le60\lambda_0\) is exactly what
supplies it.

**Theorem 5.3 (kernel cancellation).**
Let \(c(n)=\tfrac{3k}4 n^{9/8}\) with \(1\le k\le P^{1/24}\). Then
\[
K_c(P)\ll P^{1-1/96+\varepsilon},
\]
uniformly in \(k\). The cancellation in Step 5a uses the exact
ratio of this monomial's derivatives; a two-sided scale
\(c^{(r)}\asymp kP^{9/8-r}\) would not determine the composite.

*Proof.* Work on a dyadic block \(n\sim P\), odd.

*Step 1 (double Weyl differencing).* Set \(H_1=P^{1/48}\),
\(H_2=P^{1/24}\). The \(A\)-process recorded after Lemma 3.3,
applied twice, gives
\[
|K_c|^2\le\frac{2P^2}{H_1}+\frac{4P}{H_1}
\sum_{h_1=1}^{H_1}|T_1(h_1)|,
\qquad
|T_1|^2\le\frac{2P^2}{H_2}+\frac{4P}{H_2}
\sum_{h_2=1}^{H_2}|T_2(h_1,h_2)|,
\]
with \(T_2=\sum_ne(\varphi_2)\),
\(\varphi_2=\Delta\Delta(c\,\theta_2)\). For all
\(h_1\le H_1\), \(h_2\le H_2\), \(k\le P^{1/24}\):
\(kh_1h_2\le P^{1/24+1/48+1/24}=P^{5/48}\le P^{1/8}\), so
(C1)–(C4) hold with room \(P^{-1/48}\) on (C1) (and (C4) is
\(P^{1/48},P^{1/24}\le P^{1/24}\)). We prove
\[
|T_2|\ll P^{23/24+\varepsilon}
\quad\text{uniformly in }h_1,h_2,k;
\]
then \(|T_1|\ll P^{1-1/48+\varepsilon}\) and
\(|K_c|\ll P^{1-1/96+\varepsilon}\), the three savings balancing
exactly at the chosen \(H_1,H_2\).

*Step 2 (master identity; the trivial piece).* By Lemma 5.1(iv),
exactly,
\[
\varphi_2=\underbrace{(\Delta\Delta c)\,\theta_2}_{M_1}
+\underbrace{(\Delta_2c)(n{+}d_1)(\{W\}-\kappa_2)}_{M_2}
+\underbrace{(\Delta_1c)(n{+}d_2)(\{W'\}-\kappa_2')}_{M_3}
+\underbrace{c_{11}(\{\Delta\Delta Y\}-\kappa''
-\Delta_2\kappa_2)}_{M_4}.
\]
By (E4), \(|M_1|\le0.43\,kh_1h_2P^{-7/8}\), so
\(|e(M_1)-1|\le2.7\,kh_1h_2P^{-7/8}\) and deleting \(M_1\) changes
\(T_2\) by at most \(2.7\,kh_1h_2P^{1/8}\le2.7\,P^{1/4}\) by (C1).
No growing smooth part remains: every other bracket is bounded
by \(2\).

*Step 3 (the expansion inventory).* The three remaining pieces are
expanded as follows; all truncations, masses, and error costs are
displayed here once and summed in Step 6.

(3a) *\(M_2\), sawtooth part \((\Delta_2c)(n{+}d_1)\{W\}\).* The
coefficient \(B(n)=\Delta_2c(n{+}d_1)\in(1.68,1.85)kh_2P^{1/8}\)
drifts by \(|B'|\le0.22kh_2P^{-7/8}\) per step: freeze it on at most
\(2kh_2P^{1/4}{+}1\) windows on which it moves by \(\le P^{-1/8}\)
(residual cost
\(\sum_n|e((B{-}B_0)\{W\})-1|\le6.3P^{-1/8}\cdot P=6.3P^{7/8}\)).
Per window, Lemma 3.7 at the centre \(B_0\) with
\(T=P^{1/2}/(2h_1)\), \(J=P^{1/4}\)
(hypothesis \(T\ge8(1+|B|)\):
\(P^{1/2}/(2h_1)\ge\tfrac12 P^{23/48}\) and
\(8(1+|B|)\le15\,kh_2P^{1/8}\le15P^{10/48}\), so the inequality
holds for \(P\ge P_0\)): flat cost in total
\(\le8(1{+}1.85kh_2P^{1/8})\cdot2h_1P^{1/2}
\le16h_1P^{1/2}+30\,kh_1h_2P^{5/8}\le46P^{3/4}\) by (C1); the
majorant \(\Delta_J\)-part costs \(\le2\cdot4P/J=8P^{3/4}\) plus
\(J\)-mode sums at coefficients \(\le1/(J{+}1)\); modes \(e(uW)\)
with mass \(\le C\log P\) and \(u\le1.85kh_2P^{1/8}+P^{1/2}/(2h_1)\),
so that \(uh_1\le1.85P^{1/4}+P^{1/2}/2\le P^{1/2}\): every mode is a
Lemma 5.2(i) object at shift \(h_1\le P^{1/48}\). Window boundaries
cost \(\le2kh_2P^{1/4}\cdot3.4P^{3/8}\le7P^{17/24}\).

(3b) *\(M_2\), carry part \((\Delta_2c)(n{+}d_1)\kappa_2\).* Here
\(\kappa_2\in\{0,1\}\) is an integer, so exactly
\(e(-(\Delta_2c)\kappa_2)=1+\kappa_2\bigl(e(-\Delta_2c)-1\bigr)\):
the large coefficient never multiplies a sawtooth inside an
exponential. The factor \(e(-\Delta_2c(n{+}d_1))\) is a smooth phase
with \(|(\Delta_2c)''|\le2h_2\sup|c'''|\le0.19kh_2P^{-15/8}\):
class (D3). The weight \(\kappa_2=\{Y\}+\{W\}-\{Y{+}W\}\)
(Lemma 5.1(ii)) is expanded *additively* as real numbers, each unit
sawtooth by finite Fourier (Lemma 3.5) at truncation
\(J_2=P^{1/24}\), coefficients \(\le1/(\pi|q|)\), majorant cost
\(\le4P/J_2=4P^{23/24}\) per layer plus \(J_2\)-mode averages. Since
\(Y{+}W=Y(n{+}d_1)\) exactly, the resulting modes are \(e(qY(n))\),
\(e(qY(n{+}d_1))\) — Lemma 5.2(ii) objects — and \(e(qW)\) —
Lemma 5.2(i) objects.

(3c) *\(M_3\), sawtooth and carry.* The same two expansions as
(3a)–(3b), with the roles of the shifts exchanged:
\(B(n)=\Delta_1c(n{+}d_2)\in(1.68,1.85)\,kh_1P^{1/8}\) and
Lemma 3.7 at \(T=P^{1/2}/(2h_2)\). The window hypothesis is
\(T\ge\tfrac12 P^{11/24}=\tfrac12 P^{22/48}\) (since
\(h_2\le P^{1/24}\)) against
\(8(1+|B|)\le15\,kh_1P^{1/8}\le15P^{9/48}\), so it holds for
\(P\ge P_0\) with more room than (3a). Modes \(e(uW')\) satisfy
\(uh_2\le1.85\,kh_1h_2P^{1/8}+P^{1/2}/2\le P^{1/2}\) by (C1) and
are Lemma 5.2(i) objects at shift \(h_2\le P^{1/24}\). Window
boundaries cost
\(\le2kh_1P^{1/4}\cdot3.4P^{3/8}\le7P^{11/16}\). The carry
expansion is identical to (3b) at truncation \(J_2=P^{1/24}\),
and produces \(e(qY(n{+}d_2))\) and \(e(qW')\).

(3d) *\(M_4\), carries.* \(\kappa''=\{W\}+\{\Delta\Delta Y\}
-\{W{+}\Delta\Delta Y\}\) with \(W{+}\Delta\Delta Y=W(n{+}d_2)\)
exactly, and \(\Delta_2\kappa_2=\kappa_2(n{+}d_2)-\kappa_2(n)\) with
each \(\kappa_2\) expanded as in (3b) at its base. The smooth
factors \(e(\mp c_{11})\) have \(|c''|\le0.11kP^{-7/8}\): class
(D3). New mode species: \(e(q\{\Delta\Delta Y\}\)-content\()\) —
slow modes, treated in Step 5 — and \(e(qY(n{+}d))\) for
\(d\in\{0,d_2,d_1{+}d_2\}\), \(e(qW(n{+}d_2))\): Lemma 5.2 objects
again.

(3e) *\(M_4\), the anchor.* The factor
\(e(c_{11}\{\Delta\Delta Y\})\) is never expanded away. On the
branch decomposition of Lemma 5.1(iii) (arcs absorbed by the exact
shift device at \(O(\log P)\) mass and \(4P^{11/16}\) majorant, as in
Theorem 4.4, Step 4), \(\{\Delta\Delta Y\}=G-J_F\) with
\(G=F_{\boldsymbol\kappa}(X{-}\theta)\) and
\(J_F=\lfloor G\rfloor\) frozen on the runs of (E6). The anchor
phase \(c_{11}(G-J_F)\) is present in **every** final piece; its
curvature scale (E6) is what orders the whole classification of
Step 5.

After (3a)–(3e), every final piece of \(T_2\) has the exact form
\[
e\Bigl(\ \underbrace{c_{11}(G-J_F)}_{\text{anchor}}
+\underbrace{\textstyle\sum_iq_iY(n{+}e_i)}_{\text{waves},\
e_i\in\mathcal D}
+\underbrace{u\,W\text{- and }u'W'\text{-modes}}_{\text{differenced
waves}}
+\underbrace{\text{slow modes}+\varphi}_{\text{(D3)-smooth}}\Bigr)
\]
with at most one mode from each expansion layer (three layers), and
piece weights whose total mass is \(O(\log^3P)\) beyond the
displayed majorant and flat costs.

*Step 4 (pieces with wave content: Lemma 5.2(ii)).* Let
\(t=\sum_iq_i\) be the total wave frequency,
\(|t|\le3J_2\le3P^{1/24}\), inside the coefficient budget of
Lemma 5.2(ii).

If \(t\ne0\): split the phase of the piece into the printed
Lemma 5.2(ii) content and the leftover first-differenced modes.

*Printed content.* The \(Y\)-wave, the frozen-floor anchor, and
the (D3) content are exactly an instance of Lemma 5.2(ii).
Claims A–H give \(\ll|t|^{-1/6}P^{23/24+\varepsilon}\) for a
piece that carries only that content. The carry-expansion modes
of (3b)–(3d) have \(|q|\le J_2=P^{1/24}\) and become printed
(D1) decorations after the differencing of Claim C
(\(|q'|\le P^{1/24}\le4P^{1/24}\), \(h'\in\{h_1,h_2\}\le P^{1/24}\)
by (C4)); they are already covered by Claims E–H.

*Leftover modes.* The same piece may also carry first-differenced
modes \(uW\) and \(u'W'\) from Steps (3a) and (3c). Those modes
are not in the printed statement of (ii), and their coefficients
need not obey \(|q'|\le4P^{1/24}\). After the \(A\)-process of
Claim C they become
\[
u\,\Delta_{2h_3}W
=u\,\Delta_{2h_3}\Delta_{d_1}Y,
\qquad
u'\,\Delta_{2h_3}W'
=u'\,\Delta_{2h_3}\Delta_{d_2}Y,
\]
which have the algebraic shape of (D1) decorations with
coefficients \(q'=u,u'\) and second shifts \(h'=h_1,h_2\), and which
Lemma 5.2(iii) covers. From
(3a),
\(u\le1.85kh_2P^{1/8}+P^{1/2}/(2h_1)\) and
\(uh_1\le P^{1/2}\); likewise \(u'h_2\le P^{1/2}\) from (3c).
The second-shift bounds \(h_1,h_2\le P^{1/24}\) still hold, so both
satisfy (D1\('\)), and Lemma 5.2(iii) applies with
main coefficient \(t\) and shift \(h_3\): its good-shift condition
reads \(th_3h_i\ge72\), and it supplies the Stage-6 comparisons, the
\((s2)\) window inventory for the enlarged sawtooth, and the mode
accounting.

The *bad* set for the \(u\)-mode is
\(h_3<72/(th_1)\). It contains at most \(72\) positive
integers (since \(t\ge1\) and \(h_1\ge1\)). The bad set for
the \(u'\)-mode likewise contains at most \(72\) integers.
Their union has at most \(144\) elements. On those \(h_3\)
use the trivial bound \(|V_{h_3}|\le P\). The recorded
\(A\)-process charges
\[
\frac{4P}{H_3}\cdot144\cdot P
=576\,\frac{P^2}{H_3}
\le576\,t^{-1/3}P^{23/12},
\]
which is a constant multiple of the target of Claim G (the
same first-term comparison \(P^2/H_3\le t^{-1/3}P^{23/12}\)).
On the complementary good set Lemma 5.2(iii) gives the bound of
(i), and Claims F–H average it exactly as for a printed decoration.

Thus every \(t\ne0\) piece, with or without leftover
first-differenced modes, is
\(\ll|t|^{-1/6}P^{23/24+\varepsilon}\).
The weight sum is
\[
\sum_{t\ne0}\ \sum_{q_1+q_2+q_3=t}
\frac1{\pi^3\max(1,|q_1|)\max(1,|q_2|)\max(1,|q_3|)}
\,|t|^{-1/6}
\ll\sum_{t\ge1}\frac{\log^2(2{+}t)}{t^{7/6}}\ll1,
\]
so the total wave-piece contribution is
\(\ll P^{23/24+\varepsilon}\).

If \(t=0\): the wave content collapses exactly to differenced
waves — e.g. \(q(Y(n{+}d_2)-Y(n))=q\,W'(n)\) — i.e. to
(D1)-type resonant decorations of the remaining piece; these are
handled in Step 5. This exactness is the reason no near-resonant
analysis is ever needed for the wave frequencies: the resonant
combination is an identity, not an approximation.

*Step 5 (pieces without wave content: the anchor classes).*
The remaining pieces carry the anchor, at most two differenced-wave
modes \(u\,W\), \(u'W'\) (including the resonant remnants of
Step 4, which by Lemma 5.1(iii) are smooth-per-branch with
\(\theta\)-coefficients \(O(P^{-5/24})\)), slow modes, and (D3)-smooth content.
Split by the anchor branch type.

**(5a) Offset branches (\(j\ne0\)).** The anchor curvature is,
by (E6) and the window-centre composite,
\[
\lambda_a=\tfrac{729}{512}\,k|j|\,n^{-1/8}\,(1+O(P^{-1/8}))
\ \in\ [1.30,\,1.43]\,k|j|P^{-1/8},
\]
where \(\tfrac{729}{512}=\tfrac{945}{512}-\tfrac{27}{64}\), by the
following algebra. The smooth part of the anchor on an offset
branch is
\(cF=\tfrac{3k}4\nu^{9/8}\cdot\tfrac32j(m{+}\beta_1{+}\beta_2{+}\xi_1)^{1/2}
=\tfrac98\,kj\,\nu^{15/8}\,(1+O(P^{-1/4}))\) (Lemma 5.1(iii) and
\(m=\nu^{3/2}-\theta\)), with second derivative
\(\tfrac98\cdot\tfrac{15}8\cdot\tfrac78\,kj\,\nu^{-1/8}
=\tfrac{945}{512}\,kj\,\nu^{-1/8}\) up to the same relative error.
The window-centre mode carries \(u=-B(n_0)\), where
\(B=c\,\partial_mF
=\tfrac{3k}4\nu^{9/8}\cdot\tfrac34j\,m^{-1/2}
=\tfrac9{16}\,kj\,\nu^{3/8}\,(1+O(P^{-1/4}))\) is the
\(\theta\)-sawtooth coefficient of the anchor (the \(\theta\)-linear
term of \(cF(X-\theta)\)), so its curvature contribution is
\(uX''=-\tfrac9{16}\cdot\tfrac34\,kj\,\nu^{-1/8}
=-\tfrac{27}{64}\,kj\,\nu^{-1/8}\). The two terms have ratio
\(\tfrac{945}{512}:\tfrac{27}{64}=4.375\), so the composite is
single-signed at the displayed scale. Every competitor is dominated at a displayed
margin: differenced-wave modes
\(\le0.84\,uh_1P^{-3/4}\le0.51P^{-1/4}\) (since \(uh_1\le0.6P^{1/2}\)),
ratio \(\le0.34P^{-1/8}\) against \(\lambda_a\ge1.30P^{-1/8}\);
resonant (D1) content \(\le6\,|q'|P^{-5/4}\) with
\(|q'|\le4P^{1/24}\), ratio \(\le20P^{1/24-5/4+1/8}=20P^{-13/12}\);
slow modes
\(\le3J_2|j|P^{-5/4}\), ratio \(\le8P^{1/24-9/8}\); (D3) content,
ratio \(\le3h_1h_2P^{-1/2}\le P^{-1/4}\). The \(\theta\)-sawtooth of
the anchor has coefficient \(\tfrac9{16}k|j|P^{3/8}\)-scale with
per-step drift \(\tfrac{27}{128}k|j|\nu^{-5/8}\le0.22k|j|P^{-5/8}<1\).
Its total drift over the block is
\(\tfrac9{16}(2^{3/8}{-}1)k|j|P^{3/8}\le0.17k|j|P^{3/8}\), so there are at
most \(0.17k|j|P^{3/8}{+}1\) windows, each of length at least
\(1/B'(P)=\tfrac{128}{27}P^{5/8}/(k|j|)\ge4.7P^{5/8}/(k|j|)\), at
window-boundary cost
\(\le0.17k|j|P^{3/8}\cdot0.88(k|j|)^{-1/2}P^{1/16}
\le0.15(k|j|)^{1/2}P^{7/16}\). Off the collision band, window modes
\(w\) are dominated at margin \(\ge4\) either way and ride along or
are estimated by Lemma 3.3 at their own scale with \(1/|w{+}B_0|\)
weights (\(\ll P^{7/8}\log P\) in total); on the collision band
\(|wX''|\in[\tfrac14,4]\lambda_a\), Lemma 3.8 with
\((\alpha,\beta)=(\tfrac{15}8,\tfrac32)\) and
\(M\in[1.30,\,5.75]\,k|j|P^{-1/8}\) gives
\(\le C_E(|I_w|M^{1/2}+M^{-1/2}+(P/M)^{1/3})\) per window; summed
over the at most \(0.17k|j|P^{3/8}{+}1\) windows with the
\(O(\log P)\) band mass,
\[
\sum_w|I_w|M^{1/2}=P\,M^{1/2}\le2.4\,(k|j|)^{1/2}P^{15/16},\qquad
\sum_wM^{-1/2}\le0.15\,(k|j|)^{1/2}P^{7/16},
\]
\[
\sum_w(P/M)^{1/3}
\le0.17k|j|P^{3/8}\cdot0.92\,(k|j|)^{-1/3}P^{3/8}
=0.16\,(k|j|)^{2/3}P^{3/4}\le0.33\,P^{1/36+3/4},
\]
so the band total is \(\ll(k|j|)^{1/2}P^{15/16}\log P\).
The main estimate is Lemma 3.3 per frozen run at scale
\(\lambda_a\): run lengths \(\ge\tfrac1{22}P^{1/4}/(|j|{+}1)\)
(Lemma 5.1(iii)), and
\(\lambda_a^{-1/2}\le0.88(k|j|)^{-1/2}P^{1/16}\ll\) run length, so
\[
\sum_{\text{runs}}\bigl(\ell\lambda_a^{1/2}+\lambda_a^{-1/2}\bigr)
\le1.2\,(k|j|)^{1/2}P^{15/16}
+20\,(|j|{+}1)|j|^{-1/2}k^{-1/2}P^{13/16}.
\]
Summed over the eight carry branches and \(|j|\le3\) with the
\(O(\log^3P)\) piece masses:
\(\ll(k)^{1/2}P^{15/16+\varepsilon}
\le1.8\,P^{1/48}P^{15/16+\varepsilon}=1.8\,P^{23/24+\varepsilon}\)
at \(k\le P^{1/24}\) — the absorbed \((k|j|)^{1/2}\) loss, exactly
at the bottleneck.

**(5b) Zero-offset branches (\(j=0\)).** Lemma 5.2b gives the
local frozen curvature
\(\lambda_0\in[0.35,\,2.6]\,kh_1h_2P^{-5/8}\)
(leading coefficient \(\tfrac{135}{1024}\) in
\(k\beta_1\beta_2\nu^{-13/8}\), converted by
\(\beta_i\asymp h_iP^{1/2}\)). Runs of length
\(\ge\tfrac1{22}P^{3/4}/(h_1h_2)\). Let
\(\mu=0.84\max(uh_1,u'h_2)P^{-3/4}\) be the strongest
differenced-wave scale present. Three regimes.

- *Anchor-dominant* (\(60\mu\le\lambda_0\)): Lemma 3.3 per run at
  \(\lambda_0\), all else dominated at margin \(\ge20\):
  \(\le1.7(kh_1h_2)^{1/2}P^{11/16}
  +40\,(h_1h_2/k)^{1/2}P^{9/16}\).
- *Mode-dominant* (\(\mu\ge60\lambda_0\), i.e.
  \(uh_1\ge60\,kh_1h_2P^{1/8}\)-form): Lemma 5.2(i) with the
  undifferenced anchor as decoration: its run boundaries number
  \(\le22h_1h_2P^{1/4}\le22P^{5/16}\), which uses the Theorem 5.3
  shift caps \(h_1\le H_1=P^{1/48}\), \(h_2\le H_2=P^{1/24}\) (so
  \(h_1h_2\le P^{1/16}\)) and *not* (C4) alone, under which
  \(h_1h_2\le P^{1/12}\) would give only \(22P^{1/3}\), cost
  \(\le22P^{5/16}\cdot3.4(uh_1)^{-1/2}P^{3/8}\le75P^{11/16}\); its
  smooth part is dominated at margin \(\ge20\) by hypothesis. On a
  zero-offset branch the anchor's \(\theta\)-coefficient is
  \(B=c\,\partial_m F=-\tfrac38 c\,\beta_1\beta_2\,m^{-3/2}
  =-\tfrac9{32}k\beta_1\beta_2\nu^{-9/8}\bigl(1+O(P^{-1/4})\bigr)\).
  With \(\beta_i\in(3h_iP^{1/2}-1,\,4.3h_iP^{1/2}+1)\) this is
  \(\lvert B\rvert\le5.3\,kh_1h_2P^{-1/8}\le5.3\) by (C1), opened
  to \(\lvert B\rvert\le6\). The sawtooth is of constant size, not
  sub-unit. Lemma 3.7 still applies in a single window at
  \(T=P^{1/2}\), because \(T\ge8(1+\lvert B\rvert)\) is
  \(P^{1/2}\ge56\) for \(P\ge P_0\); there is no large-\(B\)
  window inventory. (The offset-scale amplitude
  \(kh_1h_2P^{3/8}\) does not occur at \(j=0\).) Centre modes
  \(w\) are treated as in Lemma 5.2(i), Stage 5. Total
  \(\ll\bigl((uh_1)^{1/2}P^{5/8}+(h_1/u)^{1/2}P^{7/8}
  +P^{7/8}\bigr)P^{\varepsilon}\).
- *Middle band* (\(\tfrac1{60}\le\mu/\lambda_0\le60\); coefficient
  mass \(O(1)\) per layer): here up to three curvature scales meet,
  and this is the one place in the paper where the composite second
  derivative can cross zero *inside* cells. Since the cells are
  short (\(\asymp P^{1/2}/h\)) while the third-derivative scale is
  tiny, no inverse-power van der Corput term may be summed per
  cell; instead the transition set is measured once, against a
  global smooth model, and receives the trivial bound
  (Lemma 3.9).

  *Inventory.* In this band
  \(0.84\,uh_1P^{-3/4}=\mu\le60\lambda_0\le160\,kh_1h_2P^{-5/8}\)
  forces \(u\le200\,kh_2P^{1/8}\le200\,P^{5/24}\), and likewise
  \(u'\le200\,kh_1P^{1/8}\le200\,P^{5/24}\). The phase's second
  derivative \(f''\) is smooth on the common refinement of the gap
  cells of both shifts (at most \(1.5(h_1{+}h_2)P^{1/2}+2\le
  3.1P^{13/24}\)), the anchor runs (\(\le22h_1h_2P^{1/4}\le
  22P^{3/8}\)), and the sawtooth windows already counted: in total
  at most \(N\le3.5P^{13/24}\) pieces, for \(P\ge P_0\). On each
  piece,
  \[
  f''=-\tfrac9{32}\Bigl(uG_1(\nu{+}2h_1)^{-5/4}
  +u'G_2(\nu{+}2h_2)^{-5/4}\Bigr)
  +\bigl(c_{11}(G_F-J_F)\bigr)''+wX''+O(\rho_0\text{-small}),
  \]
  with \(G_1,G_2,J_F\) (and the \(\beta_i\) inside \(G_F\)) frozen
  integers. This is the local \(f''\) of Lemma 5.2b.

  *Interpolant.* Invoke Lemma 5.2b: the frozen-shape interpolant
  \(\Lambda\) (values of \(\Delta_iX\) substituted, not
  differentiated) satisfies
  \(\lvert f''-\Lambda\rvert\le106P^{-25/24}+0.11P^{-5/6}=:E\)
  and \(\Lambda=\Phi''+r\) with
  \(a=-\tfrac{27}{10}(uh_1+u'h_2)\) and
  \(b=-\tfrac{405}{176}\,kh_1h_2\). The raised threshold
  \(W=V+E\) below is read from that two-term majorant.

  The scale is
  \[
  S
  =\max\bigl(\lvert uh_1+u'h_2\rvert P^{-3/4},\,
  kh_1h_2P^{-5/8},\,\lvert w\rvert P^{-1/2}\bigr),
  \]
  and the middle-band constraints give
  \(0.35P^{-5/8}\le S\le380\,P^{-1/2}\): the lower bound is
  \(\lambda_0\) when \(kh_1h_2\ge1\), and for the upper bound,
  \(\lvert uh_1{+}u'h_2\rvert\le2\max(uh_1,u'h_2)=2\mu P^{3/4}/0.84\)
  with \(\mu\le60\lambda_0\le60\cdot2.6\,kh_1h_2P^{-5/8}\), so the
  first entry of \(S\) is at most
  \(2\cdot156/0.84=372\,kh_1h_2P^{-5/8}\le372\,P^{-1/2}\) by
  \(kh_1h_2\le P^{1/8}\) from (C1) (opened to \(380\)); the third
  entry is the collision-band restriction \(\lvert wX''\rvert\ll
  P^{-1/2}\). (The factor \(2\) from the sum and the \(1/0.84\) from
  the definition of \(\mu\) are both needed: \(160\) alone would give
  \(300\), which does not cover the sum.) If \(w=0\), drop the third
  term of \(\Phi\) and apply Lemma 3.8 (or Lemma 3.3 if only
  one of \(a,b\) is present).

  *Splitting.* Choose \(V:=\tfrac1{12}S^{1/2}P^{-11/24}\), so that
  \(V/S\le0.15P^{-7/48}\) and, at the lower end
  \(S\ge0.35P^{-5/8}\), \(V\ge0.049P^{-37/48}\). Lemma 3.9 is
  applied not at \(V\) but at the *raised* threshold
  \[
  W:=V+E,\qquad
  E:=\sup\lvert f''-\Lambda\rvert\le106P^{-25/24}+0.11P^{-5/6},
  \]
  whose only hypothesis is \(W\le c_7S/2\). Off
  \(\Omega_W=\{\lvert\Lambda\rvert\le W\}\) one has
  \(\lvert\Lambda\rvert\ge W>E\), so \(f''\) carries the sign
  of \(\Lambda\) there and \(\lvert f''\rvert\ge W-E=V\) (Lean
  `sublevel_raised_threshold`). No
  separate comparison \(V\ge10\lvert f''-\Lambda\rvert\) is
  needed. That factor \(10\) was margin, and demanding it was
  actively harmful: it forced \(V\) to be *large* exactly where
  \(V\le c_7S/2\) wants it small, so the two comparisons pulled
  against each other and pinned \(\kappa\) near \(\tfrac13\).
  At the exact \(c_7=1/232\) of Lemma 3.9 (the \(\ell^\infty\)
  operator norm, Lean `step5b_curvature_norm`), \(W\le c_7S/2\)
  holds from \(P\ge8.9\cdot10^{13}\); the interpolant error alone
  would allow \(5.7\cdot10^{12}\), and the balance between the two
  is what now fixes \(\kappa\). At that threshold \(V\) and \(E\)
  take \(60\%\) and \(40\%\) of the budget \(c_7S/2\), and
  \(E\) itself splits \(54{:}46\) between its two terms. Both halves
  of \(E\) are therefore load-bearing --- which they were not under
  the old comparison, where \(V\ge10E\) made \(E\) irrelevant to
  the binding inequality and the \(219\) cost nothing.

  Writing \(V=\kappa S^{1/2}P^{-11/24}\): the piece-boundary cost
  carries \(\kappa^{-1/2}\), while \(W\le c_7S/2\) pushes the
  threshold up as \(\kappa\) grows. With the raised threshold these
  no longer conflict --- both the threshold and the non-vacuity point
  \(P_1\) of Appendix A.5 fall together as \(\kappa\) decreases,
  until near \(\kappa=\tfrac1{12}\) the boundary term turns
  \(P_1\) around. We take that value: it gives
  \(P_0=8.9\cdot10^{13}\) and \(P_1=5.0\cdot10^{19}\), against
  \(3.8\cdot10^{16}\) and \(2.1\cdot10^{21}\) for the earlier
  \(\kappa=\tfrac13\) with the factor \(10\), and
  \(1.3\cdot10^{23}\) for \(\kappa=3\). The exponent
  \(89/96\) does not depend on \(\kappa\). Until
  \(W\le c_7S/2\) holds, a three-term zero of \(\Phi''\) can
  keep \(\Omega_W\) of length \(\Theta(P)\) on a dyadic block. The length bound below is that of Lemma 3.9,
  not a claim that the sublevel is short at small \(P\);
  interval counts remain \(O_E(1)\). By Lemma 3.9 the set
  \(\Omega_W=\{\nu:|\Lambda(\nu)|\le W\}\) is a union of at most
  \(C(E)\) intervals of total length
  \(\le C(E)\,P(W/S)^{1/2}\le0.44\,C(E)\,P^{89/96}\) (using
  \(W/S\le0.19P^{-7/48}\) for \(P\ge P_0\)), and on its
  complement \(f''\) is single-signed per interval with
  \(V\le|f''|\le C(E)S+E\). The three costs:
  \[
  \text{transition (trivial):}\quad\le0.44\,C(E)\,P^{89/96};
  \]
  \[
  \text{piece boundaries:}\quad
  \le(N{+}C(E))\,V^{-1/2}
  \le3.5P^{13/24}\cdot4.51P^{37/96}+O_E(P^{37/96})
  \le15.8\,P^{89/96};
  \]
  \[
  \text{good pieces (Lemma 3.3):}\quad
  \sum\ell\,(1.1\,C(E)S)^{1/2}
  \le C'(E)\,P\cdot(380)^{1/2}P^{-1/4}
  \le21\,C'(E)\,P^{3/4}.
  \]
  The middle band therefore totals
  \(\le C(E)\,P^{89/96}\log P=O_E\bigl(P^{89/96+\varepsilon}\bigr)\),
  which is the form Step 6 uses. The sharper reading
  \(\le P^{15/16}\) would need \(C(E)\log P\le P^{1/96}\), i.e.
  \(\ln P\ge96\ln\ln P\), which first holds near \(P=10^{274}\); at
  \(P_0=8.9\cdot10^{13}\) one has \(\ln P=32.1\) against
  \(P^{1/96}=1.40\), so that reading is **not** available at \(P_0\).
  Nothing downstream depends on it: Step 6 carries \(P^{\varepsilon}\)
  and \(\tfrac{89}{96}<\tfrac{15}{16}\).

In all three regimes the \(j=0\) pieces total
\(\ll P^{15/16+\varepsilon}\ll P^{23/24}\).

*Step 6 (assembly).* Additive costs: the \(M_1\) deletion
(\(2.7P^{1/4}\)); majorants (\(\le3\) sawtooth layers at
\(4P/J_2=4P^{23/24}\) each, plus \(8P^{3/4}\), \(46P^{3/4}\), and
the displayed window residuals \(\le7P^{7/8}\)); flat costs
(\(\le46P^{3/4}\) per layer). Multiplicative costs: mode masses over
at most three expansion layers plus the shift devices,
\(O(\log^3P)=P^{\varepsilon}\). Piece totals: Step 4,
\(\ll P^{23/24+\varepsilon}\); Step 5a,
\(\le1.8P^{23/24+\varepsilon}\); Step 5b,
\(\ll P^{15/16+\varepsilon}\); slow modes and (D3) remnants,
\(\ll P^{7/8+\varepsilon}\). Hence
\(|T_2|\ll P^{23/24+\varepsilon}\), and by Step 1
\[
|T_1|^2\le2P^{2-1/24}+CP^{1+23/24+\varepsilon}
\ \Rightarrow\ |T_1|\ll P^{1-1/48+\varepsilon},
\qquad
|K_c|^2\le2P^{2-1/48}+CP^{2-1/48+\varepsilon},
\]
so \(|K_c|\ll P^{1-1/96+\varepsilon}\). Exponents deliberately
unoptimized. \(\square\)

Two remarks on the constants. First, the \(k\)-range is sharp for
this assembly: the class-(5a) loss \((k|j|)^{1/2}P^{15/16}\) meets
the wave-piece bottleneck \(P^{23/24}\) exactly at \(k=P^{1/24}\),
which is why the theorem is uniform on the original range with no
\(k\)-explicit statement needed. Second, the exponent
\(\tfrac1{96}=\tfrac14\cdot\tfrac1{24}\) traces entirely to the
depth-2 strength \(P^{23/24}\) of the exact level-2 waves
(Lemma 5.2(ii)); any improvement of the wave bound improves
\(\delta\) proportionally.

## 5. Depth-four equidistribution

**Theorem 6.1 (the OOO\* splits; complete depth-4 parity equidistribution for odd-rooted itineraries).**
For \(w\in\{OOOE,OOOO\}\),
\[
\#\{n\le N\ \text{odd}:\ \mathrm{word}_4(n)=w\}
=\tfrac N{16}+O\bigl(N^{1-1/96+\varepsilon}\bigr).
\]
Hence every length-4 itinerary word class of *odd* starts — the
eight words with first letter \(O\) — satisfies
\(\#\{n\le N\}=2^{-4}N+O(N^{1-\delta_w})\) with explicit
\(\delta_w>0\): depth-4 parity equidistribution over odd starts is
complete. (E-rooted words, i.e. even starts, are a different and
easier problem — one square root drops the state to scale
\(\sqrt N\) — and are not treated in this paper.)

*Proof.* *Step A (expansion; the mode ranges).* The class indicator
expands (Lemma 3.6, then Lemma 3.5 at truncation \(J_3=P^{1/96}\),
majorant cost \(4P/J_3=4P^{1-1/96}\) per layer) into mode sums
\[
S_{ijk}=\sum_{\substack{n\sim P\\ n\ \mathrm{odd}}}
e\bigl(\tfrac i2X+\tfrac j2Y+\tfrac k2v^{3/2}\bigr),
\qquad
|i|\le2P^{1/96},\quad|j|\le2P^{1/96},\quad1\le|k|\le2P^{1/96},
\]
with weights \(\le\min(1,2/|i|)\min(1,2/|j|)\min(1,2/|k|)\) of total
mass \(O(\log^3P)\). The \(k=0\) sums are Theorems 4.1 and 4.4.
Conjugating, take \(k\ge1\); then every displayed sign below is as
written.

*Step B (the depth-4 identity).* Three applications of the Taylor
pattern of Lemma 4.3(i), taken to second order, give the exact
identity (odd \(n\ge5\))
\[
v^{3/2}=-\tfrac5{64}n^{27/8}+\tfrac9{32}mn^{15/8}
-\tfrac{45}{64}m^2n^{3/8}+\tfrac{15}{64}vn^{9/8}
+\tfrac{45}{32}vmn^{-3/8}-\tfrac9{64}vm^2n^{-15/8}
+\mathrm{err},
\]
\(|\mathrm{err}|\le\tfrac34n^{-9/8}\) (discarding \(\mathrm{err}\)
costs \(\le2\pi\cdot\tfrac k2\cdot\tfrac34P^{-9/8}\cdot P
=\tfrac{3\pi k}4P^{-1/8}\le4.8\,P^{-11/96}<1\) for
\(P\ge7.6\cdot10^{5}\)): the fourth-letter
phase is a polynomial of degree \((2,1)\) in the integer pair
\((m,v)\) with smooth coefficients. Substituting \(m=X-\theta\) in
the \(v\)-coefficients, the total smooth \(v\)-coefficient is
*exactly*
\[
c(\nu):=\tfrac k2\Bigl(\tfrac{15}{64}+\tfrac{45}{32}
-\tfrac9{64}\Bigr)\nu^{9/8}=\tfrac{3k}4\,\nu^{9/8},
\]
the monomial weight of Theorem 5.3, and the \(v\theta\)- and
\(v\theta^2\)-cross coefficients are
\(\le\tfrac{45}{64}k\nu^{-3/8}+\tfrac9{32}k\nu^{-3/8}\le
1.2k\nu^{-3/8}\) and \(\le\tfrac9{128}k\nu^{-15/8}\): sub-unit and
decaying. The pure-\(m\) part is
\(\mu_1m+\mu_2m^2\) with \(\mu_1=\tfrac9{64}k\nu^{15/8}\),
\(\mu_2=-\tfrac{45}{128}k\nu^{3/8}\), and the pure-smooth part
\(-\tfrac5{128}k\nu^{27/8}+\mu_1X+\mu_2X^2\).

*Step C (double differencing; corner exactness).* Apply Step 1 of
Theorem 5.3 (\(H_1=P^{1/48}\), \(H_2=P^{1/24}\); now
\(kh_1h_2\le2P^{1/96+1/48+1/24}\le P^{1/8}\), so (C1)–(C4) hold) to
the whole mode phase. On each level-1 carry branch of
Lemma 5.1(iii), the four corner values obey the exact relations
\[
m(n{+}d)=m+\beta_d,
\qquad
\theta(n{+}d)=\theta+\delta_d(\nu)-\beta_d
\qquad(d\in\mathcal D),
\]
with \(\beta_d\) frozen integers and \(\delta_d\) smooth: the
doubly differenced phase on a branch is an exact function
\(\Phi(\nu,\theta)\) of \(\nu\) and the *single* sawtooth
\(\theta=\{X\}\). Two consequences are used repeatedly. First, the
\(\theta^2\)-contents of the four corners cancel exactly in the
\((+,-,-,+)\) pattern, so
\(|\partial_\theta^2\Phi|\le3k h_1h_2P^{-13/8}+4|\Delta\Delta\mu_2|
\le P^{-1}\): no quadratic sawtooth survives, and
\(e(\Phi)=e(\Phi(\nu,0)+B(\nu)\theta)(1+O(P^{-1}))\) with
\(B=\partial_\theta\Phi(\nu,0)\). Second, the wave and kernel
contents are exactly those of Theorem 5.3 with \(c=\tfrac{3k}4\nu^{9/8}\):
the \(v\)-linear part contributes \(\Delta\Delta(c\,\theta_2)\)
(the master identity, Steps 2–3 of Theorem 5.3) plus
\(\Delta\Delta(cY)\)-content whose wave frequencies join Step 4's
bookkeeping.

*Step D (passenger inventory).* Every phase content beyond the bare
kernel is listed here with its range and its check.

- *The \(\tfrac i2X\)-passenger*, \(|i|\le2P^{1/96}\):
  \(\Delta\Delta(\tfrac i2X)\) is smooth with second derivative
  \(\le\tfrac i2\cdot4h_1h_2\sup|X''''|\le2.3\,ih_1h_2P^{-5/2}
  \le P^{-9/4}\): class (D3), dominated by every retained scale at
  margin \(\le P^{-3/2}\).
- *The \(\tfrac j2Y\)-passenger*, \(|j|\le2P^{1/96}\):
  \(\Delta\Delta(\tfrac j2Y)\) is exactly four waves
  \(\pm\tfrac j2Y(n{+}d)\), \(d\in\mathcal D\), with total frequency
  \(0\). In Step 4 of Theorem 5.3 it shifts each wave coefficient
  \(q_d\) by at most \(P^{1/96}\), keeping
  \(|q_d|\le3P^{1/24}+P^{1/96}\le4P^{1/24}\) — inside
  Lemma 5.2(ii)'s coefficient budget — and leaves \(t\) unchanged;
  its \(t=0\) remnants are differenced waves that shift the
  \(u\)-coefficients of Step 5 by \(\le P^{1/96}\), harmless against
  the budget \(uh_1\le0.6P^{1/2}\).
- *The pure-\(m\) passengers* \(\mu_1m+\mu_2m^2\): on a branch,
  by corner exactness,
  \(\Delta\Delta(\mu m)=(\Delta\Delta\mu)m
  +(\Delta_2\mu)\beta_1+(\Delta_1\mu)\beta_2+\mu_{11}j\) and
  \(\Delta\Delta(\mu m^2)=(\Delta\Delta\mu)m^2
  +(\Delta_2\mu)(2\beta_1m{+}\beta_1^2)
  +(\Delta_1\mu)(2\beta_2m{+}\beta_2^2)
  +\mu_{11}\bigl(2jm+\beta_{12}^2{-}\beta_1^2{-}\beta_2^2\bigr)\),
  \(j\) the branch offset. The \(\theta\)-coefficients that arise
  from \(m=X-\theta\) in these terms are
  \(|\Delta\Delta\mu_1|\le0.92kh_1h_2P^{-1/8}\le P^{-1/48}\),
  \(|2(\Delta_2\mu_2)\beta_1|\le2.3kh_1h_2P^{-1/8}\le3P^{-1/48}\),
  and \(|2j\mu_2|\)-content, which joins \(B(\nu)\) below; all
  sub-unit ones are expanded in the slow-mode families at
  \(O(\log P)\) mass. The smooth parts join the two anchor families
  and are accounted in Step E.
- *The \(v\theta\)-crosses*: writing \(v=Y-\theta_2\) and
  linearizing \(Y=m^{3/2}\) once more by Lemma 4.3(i), the crosses
  decompose into \(\nu^{15/8}\)-scale \(\theta\)-sawtooth content
  (joining \(B(\nu)\)), a \(\theta\theta_2\)-product with
  coefficient \(\le1.2k\nu^{-3/8}\) (deleted at cost
  \(\le31kP^{5/8}\le P^{2/3}\)), and decaying remainders.

*Step E (the two sign-critical composites, rerun).* The passengers
change the two composites of Step 5 of Theorem 5.3. Both are
recomputed here from the *frozen-shape* model of Lemma 5.2b, not
from the moving-\((m,v)\) interpolant of \(\tfrac k2\nu^{27/8}\).
The identity that organises the difference is Lemma 5.1(i):
\[
\tfrac k2\,v^{3/2}
=\tfrac k2\,m^{9/4}-c\,\theta_2-kR,
\qquad
c=\tfrac{3k}4\,v^{1/2},
\]
with \(\lvert kR\rvert\ll kP^{-9/8}\) discarded as in Step B. The
differenced total phase is therefore
\(\Delta\Delta(\tfrac k2 m^{9/4})-\Delta\Delta(c\theta_2)\) plus
the Step D passengers. On a piece the integers
\(\beta_i\), \(J_F\) are held frozen; \(X(\nu)\) and the smooth
weights move; the values of \(\Delta_iX\) may be substituted for
the \(\beta_i\) as *values only*.

*Offset branches (\(j\ne0\)).* The frozen-shape offset content of
\(\Delta\Delta(\tfrac k2 m^{9/4})\), with \(m=X\) as a value, is
the same monomial as in Theorem 5.3,
\(\tfrac98 kj\nu^{15/8}\), with curvature
\(\tfrac{945}{512}kj\nu^{-1/8}\). The frozen kernel anchor
\((c(G_F-J_F))''\), now including the \(-J_Fc''\) term that
Lemma 5.2b isolates as part of \(c''(G_F-J_F)\) only after the
fractional part is taken, is
\(\tfrac{27}{16}kj\nu^{-1/8}=\tfrac{864}{512}kj\nu^{-1/8}\).
The difference — the surviving total-phase offset — is
\[
\bigl(\tfrac{945}{512}-\tfrac{864}{512}\bigr)kj\nu^{-1/8}
=\tfrac{81}{512}\,kj\nu^{-1/8}.
\]
This is \(J_Fc''\) at leading order: after the master identity
cancels \(c_{11}F_{\boldsymbol\kappa}\) against \(\Delta\Delta(cY)\),
what remains of the growing smooth offset is the frozen integer
times \(c''\). The total \(\theta\)-coefficient on the piece is
\[
B=\tfrac{27}{32}\,kj\,\nu^{3/8}\,(1+O(P^{-1/4})),
\]
one and a half times the bare-kernel value \(\tfrac9{16}kj\nu^{3/8}\)
(not the moving-gap value \(\tfrac{45}{32}\)). The window-centre
mode therefore carries
\(u_0X''=-\tfrac{27}{32}\cdot\tfrac34\,kj\,\nu^{-1/8}
=-\tfrac{81}{128}\,kj\,\nu^{-1/8}
=-\tfrac{324}{512}\,kj\,\nu^{-1/8}\), and the composite is
\[
\Bigl(\tfrac{81}{512}-\tfrac{324}{512}\Bigr)kj\,\nu^{-1/8}
=-\tfrac{243}{512}\,kj\,\nu^{-1/8},
\]
single-signed, with
\(\lambda_a'\in[0.40,\,0.52]\,k|j|P^{-1/8}(1+O(P^{-1/8}))\).
The competitors of Step 5a, now read against
\(\lambda_a'\ge0.40\,k|j|P^{-1/8}\ge0.40P^{-1/8}\), remain dominated
for \(P\ge P_0\): differenced-wave modes
\(\le0.84\,uh_1P^{-3/4}\le0.51P^{-1/4}\), ratio
\(\le1.3P^{-1/8}\); resonant (D1) content, ratio
\(\le13P^{-9/16}\); slow modes
\(\le3J_2|j|P^{-5/4}\), ratio
\(\le9P^{-13/12}\); (D3) content, ratio
\(\le4h_1h_2P^{-1/2}/(0.40P^{-1/8})\le3P^{-1/8}\). The window count
grows by \(\tfrac{27/32}{9/16}=\tfrac32\), so at most
\(1.8\,k|j|P^{3/8}+1\) windows; the collision-band Lemma 3.8 sum
is then \(\le3.0\,(k|j|)^{1/2}P^{15/16}\log P\). Run lengths are
unchanged, and
\[
\sum_{\mathrm{runs}}\bigl(\ell\lambda_a'^{1/2}+\lambda_a'^{-1/2}\bigr)
\le1.4\,(k|j|)^{1/2}P^{15/16}
+34\,(|j|{+}1)|j|^{-1/2}k^{-1/2}P^{13/16}.
\]
Summed over the eight branches and \(\lvert j\rvert\le3\) with the
\(O(\log^3P)\) piece masses:
\(\ll k^{1/2}P^{15/16+\varepsilon}\le P^{1/48}P^{15/16+\varepsilon}
=P^{23/24+\varepsilon}\) already at the kernel's \(k\le P^{1/24}\);
the actual range \(k\le2P^{1/96}\) sits strictly inside.
The inverse-power term remains \(P^{13/16}\).

*Zero-offset branches (\(j=0\)).* The same frozen-shape difference,
after \(\beta_1\beta_2\sim9h_1h_2\nu\), has leading curvature
\[
\lambda_0'
=\tfrac{1095}{1024}\,kh_1h_2\,\nu^{-5/8}
\in[0.60,\,1.25]\,kh_1h_2P^{-5/8}.
\]
The three-regime split of Step 5b is
read at this scale. The thresholds (factor \(60\)) are
scale-free. In the anchor-dominant regime, Lemma 3.3 per run gives
\(\le2.0(kh_1h_2)^{1/2}P^{11/16}
+30\,(h_1h_2/k)^{1/2}P^{9/16}\).
In the mode-dominant regime the undifferenced-anchor decoration
is the same as in Step 5b. The \(j=0\) \(\theta\)-coefficient of
the *total* phase is \(O(1)\), of the same species as the
kernel's zero-offset \(B\) (constant size, \(\lvert B\rvert\le6\)):
Lemma 3.7 applies in a single window at \(T=P^{1/2}\)
(hypothesis \(T\ge8(1+\lvert B\rvert)\) holds for
\(\lvert B\rvert\le6\)). In the middle band the frozen-shape
interpolant of Lemma 5.2b is reused with the kernel-anchor
leading \(-\tfrac{1215}{1024}kh_1h_2\nu^{-5/8}\) replaced by
\(-\tfrac{1095}{1024}kh_1h_2\nu^{-5/8}\), so
\(\Phi=a\nu^{5/4}+b'\nu^{11/8}+w\nu^{3/2}\) with
\(a=-\tfrac{27}{10}(uh_1+u'h_2)\) and
\(b'=-\tfrac{365}{176}\,kh_1h_2\). The \(\rho_0(E)\) bounds
are unchanged, and
\[
S
\le\max\bigl(60\lambda_0',\,\lambda_0',\,\lvert w\rvert P^{-1/2}\bigr)
\le80\,P^{-1/2}
\]
by (C1) and \(\lvert w\rvert\le2\). The same choice
\(V=\tfrac1{12}S^{1/2}P^{-11/24}\) and the same raised threshold
\(W=V+E\) satisfy \(W\le c_7S/2\) at \(c_7=1/232\) from
\(P\ge1.6\cdot10^{13}\) -- a lower threshold than Step 5b's,
because \(S\) is larger here: at the lower end
\(S\ge0.60P^{-5/8}\) one has \(V/S\le0.11P^{-7/48}\) and
\(V\ge0.064P^{-37/48}\), against the interpolant error
\(106P^{-25/24}+0.11P^{-5/6}\). Transition length and
piece-boundary costs are as in Step 5b (the same exponents;
the smaller \(S\) enlarges \(V/S\) by a constant, still
\(O(P^{-7/48})\)). Good pieces cost
\(\le P\cdot(80)^{1/2}P^{-1/4}\le9P^{3/4}\). The middle band
therefore remains \(\ll P^{15/16+\varepsilon}\).

The passengers of Step D are inside these estimates: the
\(\tfrac i2X\)-term is (D3) as listed; the \(\tfrac j2Y\)-term
shifts each \(q_d\) by at most \(P^{1/96}\), keeping
\(\lvert q_d\rvert\le4P^{1/24}\) and \(uh_1\le0.6P^{1/2}\); the
pure-\(m\) smooth pieces are already in
\(\Delta\Delta(\tfrac k2 m^{9/4})\) and do not add a further
relative \(O(1)\) to \(\lambda_a'\) or \(\lambda_0'\); the
sub-unit \(\theta\)-coefficients of those pieces are among the
slow modes already bounded.

*Step F (assembly).* With the inventory of Step D and the
composites of Step E, Steps 2–6 of Theorem 5.3 give
\(|T_2|\ll P^{23/24+\varepsilon}\) uniformly in \((i,j,k)\) on the
stated ranges, hence \(S_{ijk}\ll P^{1-1/96+\varepsilon}\). Summing
the mode weights (\(O(\log^3P)\)), the majorant costs
(\(\le4P^{1-1/96}\) per layer, three layers), and dyadic blocks
gives the theorem. \(\square\)

The four-step certified class remains \(13/16\): \(OOO*\) does not
contract (\(3^3>2^4\)). The next two contracting itineraries are
\(OOOEE\) and \(OOEOE\) (\(3^3<2^5\)). Neither is a third growing
layer. After \(OOOE\) the fifth letter is a decaying nest plus one
slow sawtooth of coefficient \(n^{3/16}<n\); after \(OOEO\) it is
a single growing sawtooth of coefficient \(n^{9/16}<n\), of the
same species as Theorem 4.8. Theorem 6.3 counts both cylinders.

## 6. Depth-five contractors

**Lemma 6.2 (fifth-letter identities).**
Let \(n\ge5\) be odd, and write \(z=\lfloor v^{3/2}\rfloor\),
\(U=v^{1/2}\), \(w=\lfloor U\rfloor\), and \(\theta_w=\{U\}\)
(the same letters as in Theorem 4.8, now at the \(v\)-level).

(i) *(\(OOOE*\) smoothing.)*
\[
z^{1/2}
=n^{27/16}-\tfrac98 n^{3/16}\,\theta+D_5,
\qquad
\lvert D_5\rvert
\le\tfrac34\,m^{-3/8}+\tfrac12\,v^{-3/4}+\tfrac9{128}\,(X-1)^{-7/8}
+\tfrac3{32}(Y-1)^{-5/4}+\tfrac18(v^{3/2}-1)^{-3/2}.
\]
The second term is \(O(n^{-27/16})\), and the last three are
\(O(n^{-21/16})\), \(O(n^{-45/16})\) and \(O(n^{-81/16})\); the
leading remainder is \(O(n^{-9/16})\).

(ii) *(\(OOEO*\) linearization.)*
\[
w^{3/2}
=n^{27/16}-\tfrac98 n^{3/16}\,\theta
-\tfrac32\,v^{1/4}\,\theta_w+D_5',
\]
with
\(\lvert D_5'\rvert
\le\tfrac34\,m^{-3/8}+\tfrac38(U-1)^{-1/2}
+\tfrac9{128}(X-1)^{-7/8}+\tfrac3{32}(Y-1)^{-5/4}\).

*Proof.* (i) Three applications of the Lemma 4.3(i) pattern.
With \(f(t)=(v^{3/2}-t)^{1/2}\) on \([0,\theta_z]\),
\(\theta_z=\{v^{3/2}\}\):
\(z^{1/2}=v^{3/4}-\tfrac12\theta_z v^{-3/4}-E_z\) and
\(0\le E_z\le\tfrac18(v^{3/2}-1)^{-3/2}\).
With \(f(t)=(m^{3/2}-t)^{3/4}\) on \([0,\theta_2]\):
\(v^{3/4}=m^{9/8}-\tfrac34\theta_2 m^{-3/8}-E_2\) and
\(0\le E_2\le\tfrac3{32}(Y-1)^{-5/4}\).
With \(f(t)=(X-t)^{9/8}\) on \([0,\theta]\):
\(m^{9/8}=n^{27/16}-\tfrac98\theta n^{3/16}
+\tfrac9{128}\theta^2(X-\xi)^{-7/8}\)
for some \(\xi\in(0,\theta)\). Hence
\(D_5=\tfrac9{128}\theta^2(X-\xi)^{-7/8}-\tfrac34\theta_2m^{-3/8}-E_2
-\tfrac12\theta_zv^{-3/4}-E_z\), and the triangle inequality with
\(\theta,\theta_2,\theta_z<1\) gives the displayed bound term by
term. (The two Lagrange remainders \(E_2,E_z\) are of orders
\(n^{-45/16}\) and \(n^{-81/16}\); they are displayed rather than
absorbed into the coefficients \(\tfrac34\) and \(\tfrac12\), which
have no slack when \(\theta_2\) or \(\theta_z\) is close to \(1\).)
The leftover sawtooth has coefficient \(n^{3/16}\).

(ii) Lemma 4.3(i) at base \(U\), using
\(U\,v^{1/4}=v^{3/4}\) exactly:
\(w^{3/2}=v^{3/4}-\tfrac32 v^{1/4}\theta_w+E\) with
\(0\le E\le\tfrac38(U-1)^{-1/2}\). The chain
\(v^{3/4}\to n^{27/16}\) is the second and third steps of (i), so
\(D_5'=E-\tfrac34\theta_2m^{-3/8}-E_2+\tfrac9{128}\theta^2(X-\xi)^{-7/8}\),
and the bound follows term by term. Two sawtooths remain, of
coefficients \(n^{3/16}\) on \(\theta\) and \(n^{9/16}\) on
\(\theta_w\). \(\square\)

**Theorem 6.3 (two length-five splits; not a census of depth five).**
\[
\#\mathrm{OOOEE}(N),\;\#\mathrm{OOOEO}(N)
=\tfrac N{32}+O\bigl(N^{1-1/96+\varepsilon}\bigr),
\qquad
\#\mathrm{OOEOE}(N),\;\#\mathrm{OOEOO}(N)
=\tfrac N{32}+O\bigl(N^{43/48+\varepsilon}\bigr).
\]
Of these four words only \(OOOEE\) and \(OOEOE\) contract. The
expanding tree \(OOOO*\) is not estimated: it is the level-3
kernel of Conjecture 7.3. All estimates below are for
\(P\ge P_0=8.9\cdot10^{13}\), the effective threshold of Appendix A
--- but only because Stage 2 of Theorem 5.3 is run at
\(R_0=P^{5/16}\). The fifth-letter window below is opened at
\(T=R_0\) against a sawtooth coefficient
\(\lvert C\rvert\le1.30\,P^{19/96}\), and both of its requirements ---
the Lemma 3.7 hypothesis \(T\ge8(1+\lvert C\rvert)\) and the flat
cost \(8(1+\lvert C\rvert)/T\le P^{-1/96}\) per point --- have a
margin of only \(T/P^{19/96}\). At \(R_0=P^{1/4}\) that margin is
\(P^{5/96}\), and the two requirements first hold at
\(2.55\cdot10^{19}\) and \(1.81\cdot10^{24}\): both far above
\(P_0\), the second by ten orders. At \(R_0=P^{5/16}\) the margin is
\(P^{11/96}\) and they hold from \(7.5\cdot10^{8}\) and
\(5.5\cdot10^{9}\). Appendix A.6 records the trade in full.

*Proof.* \(OOOE*\). By Lemma 3.6 the class indicators are the
\(OOOE\) indicator of Theorem 6.1 times
\(\tfrac12\bigl(1\pm\psi(z^{1/2})\bigr)\). Vaaler-expand the fifth
wave at truncation \(J_5=2P^{1/96}\) (majorant
\(4P/J_5=2P^{1-1/96}\) per block). Lemma 6.2(i) replaces
\(\tfrac l2 z^{1/2}\) by
\(\tfrac l2 n^{27/16}-\tfrac{9l}{16}n^{3/16}\theta\). The
remainder costs
\(\lvert l\rvert\cdot P\cdot P^{-9/16}\ll P^{1/96+7/16}=P^{43/96}\),
inside \(P^{1-1/96}\). Write
\(C=\tfrac{9l}{16}n^{3/16}\), so
\(\lvert C\rvert\le2P^{19/96}\) on \(\lvert l\rvert\le2P^{1/96}\).
Lemma 3.7 with \(T=R_0=P^{5/16}\) satisfies
\(T\ge8(1+\lvert C\rvert)\) for \(P\ge P_0\), since
\(8\lvert C\rvert/T\le11P^{-11/96}\), which is below \(1\) from
\(P\ge7.5\cdot10^{8}\). The produced modes are
\(e(uX)\) with \(\lvert u\rvert\le P^{5/16}\). These are
first-letter monomials of the shape already estimated in the
proof of Lemma 5.2(i) — the families \(e(r\nu^{3/2})\) with
truncation \(R_0=P^{5/16}\), which is exactly why Stage 2 is run at
that truncation — and are not decorations of class
(D1). (The coefficient budget \(\lvert q'\rvert\le4P^{1/24}\) of
Lemma 5.2(ii) is the kernel's own \(Y\)-wave range after
differencing; it is not a slot for \(X\)-modes.)

Write \(I_{\mathrm{tot}}\) for the combined first-letter index:
Theorem 6.1's own \(\lvert i\rvert\le2P^{1/96}\) plus the
fifth-letter \(\lvert u\rvert\le P^{5/16}\). Then
\(\lvert I_{\mathrm{tot}}\rvert\le2P^{5/16}\). Theorem 6.1
Steps D–E apply at this range.

- *The \(\tfrac i2X\)-passenger.*
  \(\Delta\Delta(\tfrac i2 X)\) has second derivative
  \(\le2.3\,\lvert i\rvert h_1h_2P^{-5/2}\). At
  \(\lvert i\rvert\le2P^{5/16}\) and \(h_1h_2\le P^{1/16}\) this is
  \(O(P^{-34/16})\), inside class (D3)
  (\(\lvert\varphi''\rvert\le6kh_1h_2h\,P^{-13/8}\)) by
  \(P^{-34/16}/P^{-26/16}=P^{-1/2}\). The fifth-letter chirp
  \(\tfrac l2 n^{27/16}\), after the same double difference, is
  likewise (D3):
  \(h_1h_2\cdot l\cdot P^{27/16-4}=O(P^{1/16+1/96-37/16})\).
- *The \(\tfrac j2Y\)-passenger.* The fifth letter does not
  enlarge \(j\) or the \(Y\)-wave frequencies. The bound
  \(\lvert q_d\rvert\le3P^{1/24}+P^{1/96}\le4P^{1/24}\) is
  unchanged.
- *The sign-critical composites.* An \(X\)-mode is smooth, so it
  does not enter the frozen \(\theta\)-coefficient \(B\). The
  offset composite \(\tfrac{243}{512}\) and the zero-offset
  curvature \(\tfrac{1095}{1024}kh_1h_2\nu^{-5/8}\) are therefore
  the values of Theorem 6.1 Step E. The (D3) curvature of the new
  modes is dominated at the ratios already displayed there
  (\(\le 3P^{-1/8}\) against \(\lambda_a'\ge0.40P^{-1/8}\)).
- *The Lemma 5.2(i) budget.* Modes with \(\lvert u\rvert\le P^{5/16}\)
  are a subset of the family already bounded by
  \(3R_0^{1/2}P^{3/4}\log P=3P^{29/32}\log P\), which is inside
  \(P^{23/24}\) with \(P^{5/96}\) to spare. Collision-band
  mass stays \(O(\log P)\).
- *The flat cost of Lemma 3.7.* Per point
  \(8(1+\lvert C\rvert)/T\le11P^{19/96-5/16}=11P^{-11/96}\); over
  a block \(\le11P^{1-11/96}\), inside Theorem 6.1's
  \(P^{1-1/96}\) budget from \(P\ge5.5\cdot10^{9}\). This is the
  requirement that binds hardest on \(R_0\): at \(R_0=P^{1/4}\) the
  same line reads \(11P^{1-5/96}\), which does not clear
  \(P^{1-1/96}\) until \(1.8\cdot10^{24}\).

Theorem 6.1 therefore applies to every fifth-letter decorated
\(OOOE*\) mode sum, uniformly in \(\lvert l\rvert\le2P^{1/96}\).
Hence
\(\#\mathrm{OOOEE}(N),\;\#\mathrm{OOOEO}(N)
=N/32+O(N^{1-1/96+\varepsilon})\).

\(OOEO*\). By Lemma 3.6, the two class indicators are
\[
\tfrac1{16}\bigl(1-\psi(X)\bigr)\bigl(1+\psi(Y)\bigr)
\bigl(1-\psi(U)\bigr)\bigl(1\pm\psi(w^{3/2})\bigr).
\]
Vaaler-expand the four waves. The fifth-letter \(k=0\) sums are
the depth-4 class \(OOEO\), bounded by Theorem 4.7. For
\(k\ne0\), Lemma 6.2(ii) writes the fifth-letter phase as
\(\tfrac k2 n^{27/16}-C\theta-B\theta_w\) with
\(B=\tfrac{3k}4 v^{1/4}\asymp kn^{9/16}\) and
\(C=\tfrac{9k}{16}n^{3/16}\), up to the decaying \(D_5'\). The
remainder costs
\(\lvert k\rvert\cdot P\cdot P^{-9/16}\ll P^{5/48+7/16}=P^{13/24}\)
at the fifth-letter truncation \(P^{5/48}\) used below, inside
\(P^{43/48}\). The leading sawtooth is of the
same species as Theorem 4.8, now riding
\(\theta_w=\{v^{1/2}\}\).

*Drift-1 intervals.* \(B'\asymp kn^{-7/16}\), so \(B\) drifts by
at most \(1\) on intervals \(I\) of length
\(L_B=P^{7/16}/k\); there are \(\asymp kP^{9/16}\) of them. On
\(I\), expand \(e(-B\{U\})\) by the same shifted-window Fourier
expansion as in Theorem 4.8 (Fourier in \(U\), Vaaler
truncation \(\lvert r+B\rvert\le T_w\) with \(T_w=P^{1/4}\)):
the coefficients satisfy
\(\lvert a_r(B)\rvert\le\min(1,\lvert r+B\rvert^{-1})\) with
window mass \(O(\log T_w)\), and their \(n\)-dependence through
\(B(n)\) has total variation \(O(1)\) per interval, removed by
one partial summation per mode. The window is legal for the
sign check below:
\(T_w=P^{1/4}\ll kP^{9/16}\) for every \(k\ge1\); the majorant
is \(P/T_w=P^{3/4}\).

At frequency \(\ell=-B+t\), \(\lvert t\rvert\le T_w\), the
combined phase is
\(-\tfrac{3k}4 v^{3/4}+t\,v^{1/2}\) plus the original
\(\tfrac k2 n^{27/16}-C\theta\). Linearizing \(v^{3/4}\) and
\(v^{1/2}\) by Lemma 6.2, the \(\theta\)-coefficients from the
two expansions cancel at the window centre up to a residual
\(C_{\mathrm{net}}=\tfrac{9k}{32}n^{3/16}\): the contribution
of \(-\tfrac{3k}4 v^{3/4}\) is
\(\tfrac{27k}{32}n^{3/16}\), and
\(\tfrac{27k}{32}-\tfrac{9k}{16}=\tfrac{9k}{32}\). One slow
\(\theta\)-sawtooth remains. Expand
\(e(C_{\mathrm{net}}\theta)\) on the same intervals, again by
the shifted-window device of Theorem 4.8
(\(C_{\mathrm{net}}\) drifts by \(P^{-3/8}\ll1\) on each \(I\);
window \(T_\theta=P^{1/8}\ll kP^{3/16}\); majorant \(P^{7/8}\)).
The window-centre \(X\)-mode of this last expansion has
curvature \(\tfrac{27k}{128}n^{-5/16}\). The leading
\(n^{27/16}\) coefficient of the combined phase is
\(\tfrac k2-\tfrac{3k}4=-\tfrac k4\), of curvature
\(-\tfrac{297k}{1024}n^{-5/16}\). Hence
\[
\lambda_2
=\Bigl(-\tfrac{297k}{1024}+\tfrac{27k}{128}
+O\bigl(T_w n^{-9/16}\bigr)
+O\bigl(J_* n^{-3/16}\bigr)\Bigr)n^{-5/16},
\]
with leading combination
\(-\tfrac{297}{1024}+\tfrac{216}{1024}=-\tfrac{81}{1024}\ne0\).
The \(t\)-error is
\(O(P^{1/4-9/16})=O(P^{-5/16})\) and the \(J_*\)-error, at the
truncation \(J_*=P^{5/48}\) used below, is
\(O(P^{5/48-3/16})=O(P^{-1/12})\). Both are smaller than the
leading coefficient, so \(\lambda_2\) is single-signed and
\(\lambda_2\asymp kn^{-5/16}\). By Lemma 3.10(a) the curvature
ratios and signs are invariant under \(n=2r+1\); Lemma 3.10(b)
says the \(n\)-variable van der Corput display dominates the
reindexed bound.

Lemma 3.3 on each \(I\):
\(L_B\lambda_2^{1/2}+\lambda_2^{-1/2}
\ll k^{-1/2}P^{9/32}+k^{-1/2}P^{5/32}\).
Times \(\asymp kP^{9/16}\) intervals:
\(S_k\ll k^{1/2}P^{27/32+\varepsilon}\). Balance
\(J_*^{1/2}P^{27/32}=P/J_*\) at \(J_*=P^{5/48}\) gives
\(P^{43/48}\). Dyadic blocks sum to
\(N^{43/48+\varepsilon}\). \(\square\)

**Corollary 6.4 (certified-descent density \(7/8\)).**
The five uniform certificate classes
\[
E,\qquad OE,\qquad OOEE,\qquad OOOEE,\qquad OOEOE
\]
are disjoint, and
\[
\bigl|\#\{n\le N:\mathrm{word}(n)\ \text{has prefix }OOOEE\}
-\tfrac N{32}\bigr|
\ll_\varepsilon N^{1-1/96+\varepsilon},
\]
\[
\bigl|\#\{n\le N:\mathrm{word}(n)\ \text{has prefix }OOEOE\}
-\tfrac N{32}\bigr|
\ll_\varepsilon N^{43/48+\varepsilon}.
\]
Hence the class of starts with a certified descent within five
steps has cardinality
\[
\tfrac N2+\tfrac N4+\tfrac N{16}+\tfrac N{32}+\tfrac N{32}
+O\bigl(N^{1-1/96+\varepsilon}\bigr)
=\tfrac{7N}8+O\bigl(N^{1-1/96+\varepsilon}\bigr).
\]
No other depth-\(\le5\) word class is used. In particular this
is not a census of every \(O\)-rooted itinerary of length five: the
classes \(OOOO*\) remain open, and \(OOEOO\), \(OOOEO\) are
counted by Theorem 6.3 but do not contract.

*Proof.* The first three counts are Corollary 4.9. The new
cylinders are Theorem 6.3. Every \(OOOEE\) or \(OOEOE\) start
descends within five steps by Proposition 3.1: \(3^3<2^5\).
The five classes are disjoint because they are distinct
prefixes. The error is the worse of the two fifth-letter
exponents. \(\square\)

## 7. The Terras-style reduction and the frontier

The depth-by-depth counting assembles into a conditional
Terras-style statement, and the reduction is unconditional:

**Proposition 7.1 (equidistribution implies density-one descent).**
Let \(d\ge1\) and suppose that for every *\(O\)-rooted* itinerary
word \(w\) of length \(d\),
\[
\bigl|\#\{n\le N:\mathrm{word}_d(n)=w\}-2^{-d}N\bigr|\le E_d(N).
\]
Let \(N_d\) be the number of length-\(d\) words with no contracting
prefix. Then the starts with no contracting prefix of length \(\le d\)
number at most
\[
\frac{N_d}{2^{d}}\,N+N_d\,E_d(N),
\]
and \(N_d\le 2^de^{-cd}\) with
\(c=2\bigl(\tfrac{\log2}{\log3}-\tfrac12\bigr)^2>0.0342\).
Every other start \(n\ge2\) satisfies \(J^t(n)<n\) for some
\(t\le d\) with the uniform power-envelope certificate of
Proposition 3.1. Consequently, if \(E_d(N)=O_d(N^{1-\delta_d})\) with
\(\delta_d>0\) for every \(d\), the set of starts admitting a finite
descent certificate has natural density \(1\).

*Proof.* Every \(E\)-rooted word has a contracting prefix at length
one (\(3^0<2\)), so the starts with no contracting prefix of length
\(\le d\) all realize an \(O\)-rooted itinerary of length \(d\). An
itinerary \(w\) of length \(d\) has a contracting prefix iff
\(3^{o_t}<2^t\) for some \(t\le d\), where \(o_t\) counts odd letters
among the first \(t\); so the words to be counted are exactly those
whose lattice path \((t,o_t)\) satisfies \(3^{o_t}\ge2^{t}\)
throughout. That condition depends on nothing but \((t,o_t)\), so
\(N_d\) is a two-line dynamic program over the triangle
\(0\le o\le t\le d\), exact in integers. Each surviving class has at
most \(2^{-d}N+E_d(N)\) members by the \(O\)-rooted hypothesis, and
multiplying by \(N_d\) gives the count. For the closed form, drop
every constraint but \(t=d\): the endpoint condition is
\(o_d\ge\beta d\) with \(\beta=\log2/\log3\), and Hoeffding's
inequality gives
\(\#\{o_d\ge\beta d\}\le2^{d}e^{-2(\beta-1/2)^2d}\). The
density-one statement follows by letting \(d\to\infty\) slowly with
\(N\) (any \(d(N)\to\infty\) with \(N_dE_d(N)/N\to0\)). \(\square\)

The exact count is worth carrying rather than the closed form,
because Hoeffding is lossy in exactly the range the paper certifies:

| \(d\) | \(N_d\) | endpoint only | \(2^d\) | \(N_d/2^d\) | \(e^{-cd}\) | certificate density |
|---:|---:|---:|---:|---:|---:|---:|
| \(4\) | \(3\) | \(5\) | \(16\) | \(0.1875\) | \(0.8718\) | \(0.8125\) |
| \(5\) | \(4\) | \(6\) | \(32\) | \(0.1250\) | \(0.8425\) | \(0.8750\) |
| \(6\) | \(8\) | \(22\) | \(64\) | \(0.1250\) | \(0.8141\) | \(0.8750\) |
| \(8\) | \(19\) | \(37\) | \(256\) | \(0.0742\) | \(0.7601\) | \(0.9258\) |
| \(12\) | \(226\) | \(794\) | \(4096\) | \(0.0552\) | \(0.6627\) | \(0.9448\) |
| \(16\) | \(2114\) | \(6885\) | \(65536\) | \(0.0323\) | \(0.5778\) | \(0.9677\) |
| \(24\) | \(286581\) | \(1271626\) | \(16777216\) | \(0.0171\) | \(0.4392\) | \(0.9829\) |

The ratio \(e^{-cd}2^{d}/N_d\) is \(6.7\) at \(d=5\), \(11.4\) at
\(d=10\), \(43.6\) at \(d=40\) and \(1.3\cdot10^{4}\) at \(d=1600\).
It grows without bound, and the reason is not the exponential rate.
The rate is essentially untouched: the sharp value is
\(\rho=\min_{\theta}\tfrac12\bigl((3/2)^{\theta}+2^{-\theta}\bigr)
=0.965907\), i.e. \(-\log\rho=0.034688\) against Hoeffding's
\(c=0.034285\), a difference of one part in eighty. What Hoeffding
discards is a polynomial factor, and it is a large one:
\[
\frac{N_d}{2^{d}}\ \sim\ C\,\rho^{d}\,d^{-3/2},
\qquad C\approx11 ,
\]
the \(d^{-1/2}\) being the cost of staying nonnegative under the
zero-drift tilt and the further \(d^{-1}\) the cost of the tilted
endpoint, which sits at height \(\asymp\sqrt d\) rather than at the
origin. Over any range a depth-\(d\) theorem could occupy, that
polynomial factor is the whole story: the *observed* per-letter rate
\(-d^{-1}\log(N_d/2^d)\) is \(0.1696\) at \(d=24\), \(0.0635\) at
\(d=200\) and still \(0.0401\) at \(d=1600\), against an asymptote of
\(0.0347\) it approaches only logarithmically slowly. (The value at
\(d=200\), \(N_{200}/2^{200}=3.06\cdot10^{-6}\), is the figure recorded
independently in the theorem ledger.) What changes in
Proposition 7.1 is therefore the operative constant, in both terms: at
\(d=5\) the error term carries \(N_5=4\) rather than \(2^5=32\), and at
\(d=16\) it carries \(2114\) rather than \(65536\).

The \(d=5\) row is a cross-check rather than a new number. The four
surviving words are \(OOOOO\), \(OOOOE\), \(OOOEO\) and \(OOEOO\), so
the certificate density available at depth five is \(1-4/32=7/8\) ---
which is Corollary 6.4's figure, reached here by counting words rather
than by counting contractors. The \(d=6\) row is \(7/8\) again: all
eight children of those four words survive, so depth six buys nothing
without depth five first. The two words of the open \(OOOO*\) split
are half of the depth-five obstruction and, by the same table, half of
the depth-six one.

Sections 3–5 prove the hypothesis at every depth \(d\le4\), so the
conclusion of Proposition 7.1 is unconditional for those depths.
Corollary 6.4 raises the certified class to certificate density \(7/8\) without
counting every depth-5 word. The first open counting case is the
\(OOOO*\) split. It has an exact shape, one nesting deeper than
Theorem 5.3. Write
\(Z=v^{3/2}\), \(z=\lfloor Z\rfloor\), \(\theta_3=Z-z\); after four
odd letters the fifth is the parity of \(\lfloor z^{3/2}\rfloor\).

**Lemma 7.2 (level-3 kernel reformulation).**
For odd \(n\ge5\),
\[
\tfrac12\bigl(v^{9/4}-z^{3/2}\bigr)-\tfrac34\,z^{1/2}\theta_3=R_3,
\qquad
0\le R_3\le\tfrac3{16}\,z^{-1/2}.
\]
Consequently the fifth-letter phase is, up to \(kR_3\ll kn^{-27/16}\)
per term, the exponential sum of the level-3 local floor defect, with
coefficient \(\varrho=\tfrac{3k}4z^{1/2}\asymp kn^{27/16}\): Lemma 5.1(i)
with \((m,v)\) replaced by \((v,z)\).

*Proof.* Taylor of \((z+\theta_3)^{3/2}\) at \(z\), with
\(Z^{3/2}=v^{9/4}\). \(\square\)

For smooth \(\varrho\) with \(\varrho\asymp kP^{27/16}\) and
\(\varrho'\asymp kP^{11/16}\) on \(n\sim P\) (the \(z^{1/2}\)-shaped
family), define
\[
K_3(P)=\sum_{\substack{n\sim P\\ n\ \mathrm{odd}}}
e\bigl(\varrho(n)\,\{\lfloor\lfloor
n^{3/2}\rfloor^{3/2}\rfloor^{3/2}\}\bigr).
\]

**Conjecture 7.3 (level-3 kernel cancellation).**
\(K_3(P)\ll P^{1-\delta}\) for some \(\delta>0\), uniformly over the
family above with \(k\le P^{\varepsilon}\).

The boundary between Theorem 5.3 and Conjecture 7.3 is quantitative
and sharper than a derivative count. The smooth model iterates: where
Theorem 5.3 used two Weyl differencings against
\(Y''\asymp P^{1/4}\gg1>P^{-3/4}\asymp Y'''\), the level-3 model
\(n^{27/8}\) has \(G'''\asymp P^{3/8}\gg1>P^{-5/8}\asymp G^{(4)}\)
and predicts three. But the prediction does not descend to the nested
floors. The kernel weight now has \(\varrho'\asymp kP^{11/16}\gg1\), so no
drift-1 interval exists for any expansion of the weight itself; the
branch decomposition of Lemma 5.1(iii) has no analogue at the
\(v\)-level, because \(v\) jumps by \(\asymp n^{5/4}\) per step and
the branch set is a *product* of two carry lattices, not a copy of
one; and the forced inner linearization
\(v^{3/2}=m^{9/4}-\tfrac32m^{3/4}\theta_2+E_2\) trades \(\theta_3\)
for a sawtooth family at coefficient scale \(kn^{45/16}\), *above*
the \(9/4\) threshold where every method of this paper stops.

What survives at the frontier is a model problem and one theorem
about it. Its objects carry script letters --- \(\mathcal S\) for the
sum, \(\mathcal A\) for the amplitude, \(\mathcal B\) for the phase ---
to keep them clear of the \(S\) of Lemma 3.9 and the curvature triple
\(A,B,C\) of the same lemma, which are unrelated. Stripping every
problem-specific structure (carries, defects, nesting) from \(K_3\)
leaves the *amplitude-product* sums
\[
\mathcal S=\sum_{t\le L}e\bigl(\mathcal A(t)\,\{\mathcal B(t)\}\bigr),
\qquad
1\ll \mathcal A'\ll \mathcal A,
\]
with smooth monomial-type \(\mathcal A,\mathcal B\) (the instance above has
\(\mathcal A\asymp P^{27/16}\), \(\mathcal A'\asymp P^{11/16}\)). For \(\mathcal A'\ll1\)
partial summation makes the amplitude a tame passenger and the
classical single-floor machinery applies; for \(\mathcal A'\gg1\) we
know of no nontrivial deterministic bound by any method. What can be
proved is an \(L^2\) identity in the shift, a one-page computation
that uses no harmonic analysis:

**Proposition 7.4 (shift-averaged \(L^2\) bound).**
Let \(\mathcal A_1<\cdots<\mathcal A_L\) be reals with
\(|\mathcal A_t-\mathcal A_{t'}|\ge \mathcal A'_{\min}|t-t'|\) for some \(\mathcal A'_{\min}\ge1\), and
let \(x_1,\ldots,x_L\) be arbitrary reals. For
\(\mathcal S_\lambda=\sum_{t\le L}e\bigl(\mathcal A_t\{x_t+\lambda\}\bigr)\),
\[
\Bigl|\int_0^1|\mathcal S_\lambda|^2\,d\lambda-L\Bigr|
\le\frac4\pi\,\frac L{\mathcal A'_{\min}}\,(\log L+1).
\]
Consequently, for any \(\eta\in(0,1)\), Markov's inequality
gives
\[
|\mathcal S_\lambda|
\le\sqrt{\frac L\eta
\Bigl(1+\frac4\pi\,\frac{\log L+1}{\mathcal A'_{\min}}\Bigr)}
\]
outside a shift set of measure at most \(\eta\). This is
square-root cancellation times \(\sqrt{\log L}\) in general, and
genuine square-root cancellation when \(\mathcal A'_{\min}\gg\log L\) — which
holds in the instance above, where \(\mathcal A'_{\min}\asymp P^{11/16}\).

*Proof.* Expand the square; the diagonal gives \(L\). For
\(t\ne t'\), the function
\(\varphi(\lambda)=\mathcal A_t\{x_t+\lambda\}-\mathcal A_{t'}\{x_{t'}+\lambda\}\) is
piecewise linear with *real* slope \(\mathcal A_t-\mathcal A_{t'}\), with jumps at
\(1-\{x_t\}\) and \(1-\{x_{t'}\}\). Those two points cut \([0,1)\)
into three intervals, but the first and the last carry the same linear
branch --- their constants differ by exactly the slope --- so on the
circle there are two arcs, not three, and on each
\(|\int e(\varphi)\,d\lambda|\le1/(\pi|\mathcal A_t-\mathcal A_{t'}|)\).
Summing,
\(\sum_{t\ne t'}2/(\pi \mathcal A'_{\min}|t-t'|)
\le(4/\pi)(L/\mathcal A'_{\min})(\log L+1)\). For the second display, the
measure of \(\{|\mathcal S_\lambda|^2>\tau\}\) is at most
\(\tau^{-1}(L+(4/\pi)(L/\mathcal A'_{\min})(\log L+1))\); take
\(\tau=(L/\eta)(1+(4/\pi)(\log L+1)/\mathcal A'_{\min})\). \(\square\)

Two cautions. The amplitude separation \(\mathcal A'\gg1\) — the very
property that defeats every character expansion, since a Fourier
window centred at the amplitude drifts by \(\mathcal A'\) harmonics per step
— is what makes the shift *average* trivial; but an average over
shifts says nothing about the single shift \(\lambda=0\), which is
the deterministic sum. Proposition 7.4 does not make the level-3
kernel "generically cancelling" in any sense that bears on
Conjecture 7.3; it only locates the conjecture's difficulty as a
specific-point problem inside a metric statement.

**Conjecture 7.5 (the pure amplitude-product model).**
\(|\mathcal S|\le L^{1-\delta}\) for some \(\delta>0\), for smooth
monomial-type \(\mathcal A,\mathcal B\) with \(1\ll \mathcal A'\ll \mathcal A\) as above.

Three structural facts locate the difficulty of the
de-randomization. No second averaging variable exists: amplitude
separation forces any two sample points with \(|\mathcal A(p)-\mathcal A(q)|\le1\) to
coincide, and every family average available in the application
re-enters either the differenced-kernel class or the
amplitude-product class itself. The inverse theory is self-similar:
any concentration or discrepancy inverse for \(\mathcal A\{\mathcal B\}\bmod1\) is a
statement about \(\sum e(j\mathcal \mathcal A\{\mathcal \mathcal B\})\) — the same class with amplitude
\(j\mathcal \mathcal A\) — so the class is closed under its own inverse theorems and
no bootstrapping is possible. And the metric statement does not
transfer: \(|dS_\lambda/d\lambda|\le2\pi \mathcal A_{\max}L\) almost
everywhere, so \(\mathcal S_\lambda\) decorrelates at shift scale
\(1/\mathcal A_{\max}\), and an almost-all-\(\lambda\) theorem leaves
\(\asymp\eta \mathcal A_{\max}\) exceptional cells among
\(\asymp \mathcal A_{\max}\) — no measure argument pins \(\lambda=0\). The
deterministic content of Conjecture 7.5 is a
specific-point-in-metric-theory problem: a class whose known
successes all use special arithmetic.

Two analytic shortcuts around Conjecture 7.3 fail at recorded
points, and we state them once: composing gap cells across two
levels fails because on a cell where the first-level gap is constant
the second-level gap still takes a new value at essentially every
point, so no usable sub-cell survives; and reindexing by the image
\(m\) strips one nesting level but introduces a fiber indicator of
density \(\asymp m^{-1/3}\), whose sawtooth requires savings beyond
the exponent \(1/3\) while the engine saves only \(1/24\).

The open question, stated once:

> It is open whether almost every odd-to-odd start has a finite
> descent certificate. By Proposition 7.1 that would follow from
> all-depth parity equidistribution, which is now a theorem through
> depth four for odd-rooted itineraries. The certified class through
> length five has certificate density \(7/8\). The first open
> counting case is the \(OOOO*\) kernel of Conjecture 7.3, whose
> deterministic model instance is Conjecture 7.5.

## 8. Relation to the Juggler map

The companion paper [24] reduces the termination problem to one
statement about parity words and makes precise which statistics it
needs. That paper's results bear on the program of this one in two
opposite directions, and we record both.

Two localization facts, stated so they cannot be confused.

1. Section 3.5 proves the depth-\(\le3\) discrepancy estimates
   (Theorems 4.11 and 4.12) on sub-dyadic intervals of length
   \(\ge P^{1/2}\) with a slow twist. Corollary 4.13 is the only
   localization this paper supplies to [24].
2. Theorem 5.3 is a dyadic-block statement. A localized kernel
   theorem on intervals of length \(P^{23/32}\) is not proved, and
   the strongest even-block productions that would need it
   (\(OOOEEE\), \(OOEOEE\)) remain unavailable.

*What each new depth buys.* Every new certificate class enters the
contagion recursion of [24] as a production: a word \(w\) of fair
probability \(P_w\) landing at scale \(x^{e_w}\) contributes
\((P_w/e_w)\,g(e_wt)\), provided its cylinder is counted on the
preimage intervals of the landing points — intervals of length
\(x^{1-e_w}\), which is why Section 3.5 localizes Theorems 4.4 and 4.7
to sub-dyadic intervals. Through Corollary 4.13 the \(OOEEE\)
production on even blocks raises the contagion exponent from
\(\lambda^{**}=0.4480\) to \(\lambda^{***}=0.5392\), the rate threshold
of the almost-all reformulation from \(0.552\) to \(0.461\), and the
least depth constant of its conditional theorems from \(20\) to
\(18\). Those are the dividends of the depth-\(\le3\) localization.
A localized form of the kernel theorem (Theorem 5.3 on intervals of
length \(P^{23/32}\), which we have not proved; the scaling
architecture is the same, with per-window absolute costs at most
\(P^{7/16}\)) would add the words \(OOOEEE\) and \(OOEOEE\) and give
\(0.5561\); the level-3 kernel of Conjecture 7.3 would give more.
Each depth also raises the certificate density of Corollaries 4.9 and
6.4 and the constants of the Tao-type reduction. These are the
quantitative dividends of the program, and they are real. The
strongest of them that this paper actually proves for [24] is the
depth-\(\le3\) localization, not a localized Theorem 5.3.

*What no depth can buy.* The frontier statement of [24] is that the
odd starts in \((y,2y]\) whose orbit is still above a fixed floor after
\(C\log_2\log y\) steps number at most \(y(\log y)^{-e}\) for some
\(e>0.508\), where \(C\ge19\). Its weakest sufficient condition is an
exponential moment of the odd count on live starts — a statement
about the tilted average of parity words of length \(\asymp\log\log y\),
which is insensitive to bias at any \(o(\log\log y)\) initial depths
and to any single cylinder unless it is over-populated by an
exponential factor. Consequently: (i) no fixed-depth theorem, this
paper's or any other, is necessary for that statement — the depth-5
split of Conjecture 7.3 is irrelevant to it; (ii) no cylinder
statement of bounded depth is sufficient for it, because a word
measure fair to depth \(k\) and all-\(O\) afterwards satisfies every
depth-\(\le k\) statement and violates the bound; and (iii) along the
per-cylinder route, an analytic method whose saving exponent loses a
factor \(2^{c}\) per depth reaches the required depth only if
\(cC<1\), i.e. \(c<1/19\), whereas Weyl differencing loses \(c\ge1\)
(this paper's chain \(\tfrac1{24}\to\tfrac1{96}\) from depth three to
four is \(c=2\)). The differencing machinery of Sections 3–6 cannot
therefore be iterated to the termination frontier, however far the
kernel program is pushed; what would be needed is a saving uniform in
the depth up to a factor \(2^{d/19}\), or a direct treatment of the
exponential moment, neither of which this paper offers.

The honest summary is the one the abstract gives: this paper solves
the first genuinely nested layers of the parity process of nested
floor powers — depth four completely, depth five for the two
contractors — with a bound whose critical piece is the level-2 wave;
it identifies the level-3 kernel as the next analytic object; and
through the depth-\(\le3\) localization of Section 3.5 it supplies
constants to the termination reduction of [24]. It does not localize
Theorem 5.3, and it does not approach the infinite-depth problem
that the termination question is.

![The theorem flow of the paper. The exact finite-itinerary calculus of the companion manuscript feeds the contraction certificates; the discrepancy calculus with the kernel theorem counts every O-rooted itinerary class through depth four and the two length-five contractors (certified-descent density 7/8), leaving the level-3 kernel — and with it almost-all descent — open.](figures/juggler_frontier.png){width=100%}

A repository accompanies the paper
([https://github.com/sneakyweasel/balanced_ternary/](https://github.com/sneakyweasel/balanced_ternary/)).
It is not required to read or check any proof. Lean certificates cover
the exact floor identities; the module
`research.juggler_sequence.paper_b_audit` and the companion
[paper_b_audit_ledger.md](paper_b_audit_ledger.md) record numerical
and exponent checks. Those are not proofs and are not an independent
verification of Lemma 5.2.

## Appendix A. The threshold \(P_0\)

Every numerical margin of Sections 4--6 is claimed for
\(P\ge P_0\). This appendix makes \(P_0\) effective. Each printed
threshold inequality is solved separately for the least \(P\) beyond
which it holds, and \(P_0\) is the maximum. The computation is
machine-checked in `src/research/juggler_sequence/p0_certificate.py`,
which also generates the table below; the probe and the paper therefore
cannot drift apart.

The probe solves each row by bisection in floating point, which was the
only inexact step in an otherwise exact chain. It is no longer a link in
that chain. Every exponent in the paper lies in
\(\tfrac1{96}\mathbb Z\), so the substitution \(P=t^n\) turns each
row into a *polynomial* inequality in \(t\), with no real powers at
all, and **all thirty-seven rows are proved that way** in
`formal/Problems/Juggler/ThresholdCertificate.lean` (32 theorems: the
window-boundary and \(\lambda_0\)-range rows each split in two). Each
carries its substitution and a rational threshold \(t_0\) at or just
above the true crossing, so the certified thresholds are slightly
conservative. The largest is the binding row --- `row_5b_binding`, at
\(t=1.96\), i.e. \(P\ge1.96^{48}=1.07\cdot10^{14}\) against the
bisected \(8.9\cdot10^{13}\), a loss of under \(20\%\). Two
irrational constants are replaced by rational bounds, both recorded:
\(\sqrt{0.35}\ge0.5916\) in the boundary row, and
\(\tfrac1{12}\sqrt{0.35}\le0.04931\) in the binding one.

### A.1 The certificate

| threshold | site | least $P$ |
|---|---|---|
| P^(1/72-1/24) <= 1 | Claim G | always |
| 16 h1 P^(1/2) + 30 k h1 h2 P^(5/8) <= 46 P^(3/4) | Thm 5.3 St.3(a) | always |
| linearization remainder P^(43/96) <= P^(1-1/96) | Thm 6.3 | always |
| P^(1/2) >= 8(1+\|B\|) with \|B\| < 1/2 | Thm 4.1 St.3(s1) | $144$ |
| 4.5 - 1.5/(h P^(1/2)) >= 4.4 at h = 1 | Thm 4.1 St.5 | $225$ |
| P^(1/2) >= 8(1+6) = 56 | Thm 5.3 St.5b (j=0) | $3.1\cdot10^{3}$ |
| 8(1+2.25P^(1/4))P^(1/2) <= 19 P^(3/4) | Thm 4.1 St.3(s2) | $4.1\cdot10^{3}$ |
| 41 P^(5/36) <= P^(1/2) | Claim C | $2.9\cdot10^{4}$ |
| [0.38,2.44] with its corrections inside [0.35,2.6] | Lemma 5.2b | $6.4\cdot10^{4}$ |
| P^(7/72) >= 3 | Claim C | $8.1\cdot10^{4}$ |
| 72 t^(-1) P^(-1/2) <= 1/4 at t = 1 | Thm 5.3 St.6(D1) | $8.3\cdot10^{4}$ |
| P^(1/2) >= 8(1 + 2.25 P^(1/4)) | Thm 4.1 St.3(s2) | $1.2\cdot10^{5}$ |
| window boundaries <= 1.1 P^(17/32) <= P^(5/8) | Thm 4.1 St.3(s2) | $1.5\cdot10^{5}$ |
| 0.6 P^(1/4) + 1 <= 0.65 P^(1/4) | Thm 4.1 St.3(s2) | $1.6\cdot10^{5}$ |
| P^(1/2)/(2h1) >= 8(1+\|B\|): 0.5 P^(23/48) >= 15 P^(10/48) | Thm 5.3 St.3(a) | $2.8\cdot10^{5}$ |
| P^(1/2)/(2h2) >= 8(1+\|B\|): 0.5 P^(22/48) >= 15 P^(9/48) | Thm 5.3 St.3(b) | $2.8\cdot10^{5}$ |
| 1.45 P^(7/72) <= P^(1/8): shift range of (i) | Claim D | $6.4\cdot10^{5}$ |
| (3 pi k/4) P^(-1/8) <= 1 at k <= 2 P^(1/96) | Thm 6.1 St.B | $7.5\cdot10^{5}$ |
| P^(1/2) >= 8(1 + 7 P^(1/4)) | Thm 5.3 St.6(D1) | $9.9\cdot10^{6}$ |
| wave remainder 200 P^(-35/24) vs S: 571 P^(-5/6) <= rho_0 | Thm 5.3 St.5b | $1.7\cdot10^{7}$ |
| beta-substitution error 2.31 P^(-1/2) <= rho_0 | Thm 5.3 St.5b | $1.8\cdot10^{7}$ |
| cells + anchor runs + windows <= 3.5 P^(13/24) | Thm 5.3 St.5b | $5.1\cdot10^{7}$ |
| mode/cell curvature ratio 0.39 P^(1/8) >= 4 | Thm 4.1 St.2 | $1.2\cdot10^{8}$ |
| flat cost 23 P^(19/24) inside the P^(23/24) budget | Thm 5.3 St.3(a) | $1.5\cdot10^{8}$ |
| every competitor ratio <= 1/4 (margin 4) | Thm 5.3 St.5a | $4.3\cdot10^{8}$ |
| Lemma 3.7 window T = R_0 >= 8(1 + \|C\|) | Thm 6.3 | $7.4\cdot10^{8}$ |
| 3 R_0^(1/2) P^(3/4) = 3 P^(29/32) <= P^(23/24) | Thm 5.3 St.5 | $1.4\cdot10^{9}$ |
| P^2\|c''''/2\|/S <= rho_0: (0.044/0.35) P^(-1/4) | Thm 5.3 St.5b | $3.0\cdot10^{9}$ |
| 96 P^(-5/24) <= 1 | Claim G | $3.3\cdot10^{9}$ |
| P\|c'''/2\|/S <= rho_0: (0.047/0.35) P^(-1/4) | Thm 5.3 St.5b | $3.9\cdot10^{9}$ |
| flat cost 8(1+\|C\|)/R_0 <= P^(-1/96) per point | Thm 6.3 | $5.5\cdot10^{9}$ |
| \|c''/2\|/S <= rho_0: (0.053/0.35) P^(-1/4) | Thm 5.3 St.5b | $6.2\cdot10^{9}$ |
| 2.25 P^(-1/16) < 1/2 | Thm 4.1 St.3(s1) | $2.8\cdot10^{10}$ |
| \|q''\| curvature ratio 48.9 P^(-3/16) <= 1/4 | Thm 5.3 St.5b(a) | $3.0\cdot10^{11}$ |
| E alone <= c_7 S/2 (the floor as kappa -> 0) | Thm 5.3 St.5b | $5.7\cdot10^{12}$ |
| W = V + E <= c_7 S/2 at S >= 0.60 P^(-5/8) | Thm 5.3 St.5a | $1.6\cdot10^{13}$ |
| W = V + E <= c_7 S/2 at S >= 0.35 P^(-5/8) | Thm 5.3 St.5b | $8.9\cdot10^{13}$ |

\[
P_0=8.9\cdot10^{13},
\]
attained at the Lemma 3.9 hypothesis \(W\le c_7S/2\) of Theorem 5.3,
Step 5b. Three rows hold for every \(P\ge1\) and are listed for
completeness rather than because they constrain anything.

### A.2 The stratification

The thresholds are not spread out; they cluster and then jump.
Thirty-three of the thirty-seven hold from \(2.9\cdot10^{10}\) on, and
that value is set by a single soft inequality
(\(2.25P^{-1/16}<\tfrac12\) in Stage 3(s1) of Theorem 4.1, which merely
names the regime). Of the remaining four, one is the \(q''\) curvature
ratio of Step 5b(a) at \(3.0\cdot10^{11}\) --- the price of
\(R_0=P^{5/16}\), and still two and a half orders below \(P_0\)
(A.6) --- and the other three are the Lemma 3.9 balance comparisons of
Steps 5a and 5b, which alone carry \(P_0\) up by three and a half
orders of magnitude.

\(W\le c_7S/2\) is a *hypothesis* of Lemma 3.9, not an optimisation: it
is what makes \(\Omega_W\) empty on the \(r=2\) pieces. Its size is
fixed by \(c_7=1/\lVert M^{-1}\rVert_\infty=1/232\) at the Step 5b
exponent triple (Lean `step5b_curvature_norm`), which is exact and so
not improvable there (A.5), and by the normalisation \(\kappa\) of
\(V=\kappa S^{1/2}P^{-11/24}\), which is free:

| \(\kappa\) | \(P_0\) | \(P_1\) (A.5) | boundary coefficient |
|---|---|---|---|
| \(\tfrac13\) | \(5.8\cdot10^{16}\) | \(1.4\cdot10^{21}\) | \(7.9\) |
| \(\tfrac18\) | \(3.5\cdot10^{14}\) | \(6.6\cdot10^{19}\) | \(12.9\) |
| \(\tfrac1{12}\) (used here) | \(8.9\cdot10^{13}\) | \(5.0\cdot10^{19}\) | \(15.8\) |
| \(\tfrac1{16}\) | \(4.4\cdot10^{13}\) | \(6.3\cdot10^{19}\) | \(18.2\) |
| \(\tfrac1{20}\) | \(2.9\cdot10^{13}\) | \(9.4\cdot10^{19}\) | \(20.4\) |

Both columns fall together until \(\kappa=\tfrac1{12}\), where the
piece-boundary term turns \(P_1\) around; that is the operating point.
As \(\kappa\to0\) the threshold tends to \(5.7\cdot10^{12}\), the point
at which the interpolant error alone satisfies \(E\le c_7S/2\). The
exponent \(89/96\) does not depend on \(\kappa\) at all.

*A near miss, recorded because it nearly cost a factor three.* Claim D
of Lemma 5.2(ii)\(\to\)(i) must place every index of the Claim C sum
inside the shift range of (i), i.e. \(h_3\le P^{1/8}\), from
\(h_3\le t^{1/3}P^{1/12}\). The exponent gap
\(\tfrac18-\tfrac7{72}=\tfrac1{36}\) is small, so whatever constant
stands in front is paid at the thirty-sixth power, and the choice of
bound on \(t\) decides the row:
\[
|t|\le16P^{1/24}\ \Rightarrow\ 16^{12}=2.8\cdot10^{14},
\qquad
|t|\le3P^{1/24}\ \Rightarrow\ 3^{12}=5.3\cdot10^{5}.
\]
The first is what the individual bound \(|q_d|\le4P^{1/24}\) gives over
the four elements of \(\mathcal D\); the second is the total-frequency
bound that Theorem 5.3, Step 4 --- the only place (ii) is invoked ---
actually supplies, since the wave modes arrive one per expansion layer
from three layers at truncation \(J_2=P^{1/24}\). Lemma 5.2(ii)
therefore carries \(|t|\le3P^{1/24}\) as a hypothesis, and the row is
\(6\cdot10^{5}\) rather than \(2.8\cdot10^{14}\). Had it been the
latter it would have been the binding row of the whole paper, and
\(P_0\) would have been \(2.8\cdot10^{14}\) --- larger by \(3.15\) than
the value above, for no analytic reason whatever. This is the sharpest
illustration in the paper of the rule that governs Appendix A: on a gap
of \(g\), a constant \(c\) costs \(c^{1/g}\), so a constant is only
harmless when the gap is wide.


### A.3 \(P_0\) does not depend on \(\varepsilon\)

No divisor sum, gcd sum or large-sieve average occurs anywhere in
Sections 3--6. Every \(\ll_\varepsilon\) in those sections is therefore
a power of \(\log P\), and the powers can be counted. The mode masses
are \(O(\log^3P)\) over at most three expansion layers, so
\(\lvert T_2\rvert\ll P^{23/24}\log^3P\); the two Weyl steps of
Theorem 5.3 each halve the exponent of the log,
\[
\lvert T_1\rvert\ll P^{1-1/48}\log^{3/2}P,
\qquad
K_c(P)\ll P^{1-1/96}\log^{3/4}P,
\]
and Theorem 6.3 costs a further \(\log^3P\) from its own truncations,
giving \(\#\mathrm{OOOEE}(N)=\tfrac N{32}
+O\bigl(N^{1-1/96}(\log N)^{15/4}\bigr)\). These forms carry no
\(\varepsilon\), and \(P_0\) is the same for all of them.

The threshold at which \(\log^AP\) would be *absorbed* into
\(P^{\varepsilon}\) is a different quantity and is not part of
\(P_0\): for \(\varepsilon=1/96\) it is \(1.5\cdot10^{190}\) at
\(A=3/4\) and beyond \(10^{300}\) at \(A=15/4\). Sections 4--6 carry the
\(P^{\varepsilon}\) rather than spending it, so those numbers never
enter. The same remark disposes of the \(P^{15/16}\) reading in
Step 5b: it would need \(C(E)\log P\le P^{1/96}\), first true near
\(10^{274}\), and Step 6 uses only \(89/96<15/16\).

### A.4 What the certificate is not

It is not a proof. It certifies that the inequalities the paper prints
are true beyond the stated threshold; it does not certify that they are
the right inequalities, and it inherits every modelling choice made in
reducing a displayed estimate to a predicate in \(P\). Two of its
inputs are conservative substitutes for statements the paper leaves in
\(O(\cdot)\) form --- the \(\tilde\beta\)-substitution error, bounded
here by the \(\pm1\) of the gap floor at \(0.68P^{-1/2}\) rather than
by the printed \(O(hP^{-1})\), and the wave remainder
\(O(uh^2\nu^{-7/4})\), bounded at \(200P^{-35/24}\) on the printed
inventory. Both clear \(\rho_0\) by more than nine orders of magnitude,
so neither choice affects \(P_0\).

Nor does \(P_0\) answer every question one might ask of a threshold. It
is the point beyond which the proof's inequalities hold; it is not the
point beyond which the resulting bound is better than the trivial one.
That second threshold is computed in A.5.

Nor was \(P_0\) always the threshold of the whole paper. In an earlier
draft Stage 2 of Theorem 5.3 was run at \(R_0=P^{1/4}\), and with that
truncation the depth-five Theorem 6.3 needed \(1.8\cdot10^{24}\), ten
orders above \(P_0\). Section A.6 shows that \(R_0=P^{5/16}\) removes
the gap at no cost that binds, and that is the value carried
throughout. With it, every threshold in the paper is \(P_0\).

### A.5 The two constants that carry the threshold

\(P_0\) is carried entirely by \(W\le c_7S/2\), whose two ingredients
are the curvature constant \(c_7\) and the interpolant error \(E\).
Both were attacked; only one moved.

*\(c_7\): not by changing the exponent triple.*
\(c_7=1/\lVert M^{-1}\rVert_\infty\) depends only on the exponents,
through \(\det M=\prod_{i<j}(x_j-x_i)\), and scales as the square of
their gap: for an equally spaced triple of gap \(\delta\) about
\(x_0\), \(\delta^2/c_7=x_0^2-2x_0+c\) with \(c\in[1.75,2]\) for
\(\delta\in[\tfrac18,\tfrac12]\). Step 5b's triple is
\((\tfrac54,\tfrac{11}8,\tfrac32)\), and each entry is forced:
\(\tfrac32\) is the level-1 wave \(X=\nu^{3/2}\); \(\tfrac{11}8\) is the
frozen-shape global model; \(\tfrac54\) is the differenced-wave
monomial after the frozen gap \(G\sim3h\nu^{1/2}\). In eighths they are
\(10,11,12\) --- adjacent on the lattice \(\tfrac18\mathbb Z\) the whole
paper lives on --- so \(\det M=\tfrac1{256}\) and
\(\lVert M^{-1}\rVert_\infty=232\). Across all \(165\) triples of the
paper's exponent inventory \(c_7\) runs from \(1/259\) to \(144/287\),
the good end being triples of gap \(\tfrac32\); these three lie within
\(\tfrac14\) of each other by construction.

*\(c_7\): by dropping the uniform constant, under a factor ten, and not
for free.* The proof needs only \(\lvert M^{-1}\rvert c\le1\) for a
vector \(c=(c_2,c_3,c_4)\), and only \(c_2\) gates \(W\le c_2S/2\). The
middle row of \(\lvert M^{-1}\rvert\) is \((24,144,64)\), so
\(c_3,c_4\to0\) gives \(c_2\le\tfrac1{24}\) (Lean
`step5b_c2_ceiling`). But the uniform choice **saturates that row
exactly**, \(24+144+64=232\) (Lean `step5b_uniform_saturates`): every
increase in \(c_2\) is paid out of \(c_3,c_4\), and those sit in
\(C\), through the \(r=3\) length \(2PV/(c_3S)\) and the \(r=4\) length
\(P(V/(c_4S))^{1/2}\). Taking
\(c=(\tfrac1{27},\tfrac1{1872},\tfrac1{1872})\) --- again exactly
tight, \(\tfrac89+\tfrac19=1\) (Lean `step5b_c2_optimum_feasible`) ---
moves \(P_0\) to \(2.6\cdot10^{13}\) but \(P_1\) below from
\(5.0\cdot10^{19}\) to \(5.3\cdot10^{23}\). We keep the uniform
constant.

*\(E\): yes, by a factor \(2.07\); and the factor \(10\) beside it, by
removing it.* The earlier \(219=202.5+16\) opened the middle-band cap
\(185.7\) to \(360\) and carried \(8\) where step (ii) gives
\(0.567\). Keeping the shifts visible lets the two error terms combine
into \(52.9\,k(h_1{+}h_2)P^{-9/8}\le106P^{-25/24}\). More consequential
is the comparison beside it: the former
\(V\ge10\lvert f''-\Lambda\rvert\) is not needed at all. Running
Lemma 3.9 at the raised threshold \(W=V+E\) gives
\(\lvert f''\rvert\ge W-E=V\) off \(\Omega_W\) directly, under the
single hypothesis \(W\le c_7S/2\). The factor \(10\) had forced \(V\)
to be large exactly where \(c_7\) wanted it small; with it gone,
\(\kappa\) can fall from \(\tfrac13\) to \(\tfrac1{12}\) and \(P_0\)
with it.

*The second threshold.* A.1 certifies that the printed inequalities are
true beyond \(P_0\); it does not ask when the resulting bound is better
than the trivial one. The middle band costs
\[
\underbrace{4P\,\frac{W}{c_7S}}_{r=3,\ \asymp P^{41/48}}
+\underbrace{P\Bigl(\frac{W}{c_7S}\Bigr)^{1/2}}_{r=4,\ \asymp P^{89/96}}
+\underbrace{3.5\,P^{13/24}V^{-1/2}}_{\asymp P^{89/96}},
\]
and \(P_1\) is the least \(P\) at which that total is \(\le P\). The
three exponents are not equal, so they cannot be collected into a
single coefficient of \(P^{89/96}\); doing so over-counts the \(r=3\)
term by \(P^{7/96}\). Honestly computed,
\(P_1=5.0\cdot10^{19}\) at the operating point, against
\(2.1\cdot10^{21}\) at \(\kappa=\tfrac13\) with the factor \(10\).
Between \(P_0\) and \(P_1\) the middle-band estimate is true but weaker
than the trivial bound; the theorem is asymptotic and its implied
constant absorbs the difference.

*What is left.* At the operating point the binding comparison is still
\(W\le c_7S/2\), now with \(c_7\) shown near its floor and \(E\)
reduced by a factor two. The remaining slack is in \(E\) itself: the
middle-band half-width \(60\), which enters \(106\) linearly through
the cap \(\tfrac{60\cdot2.6}{0.84}\), and the range \([0.35,2.6]\) for
\(\lambda_0\). Narrowing the band would reduce \(E\) but weakens the
margin-\(20\) domination claims in the anchor-dominant and
mode-dominant regimes, which is a trade this draft has not made.

### A.6 Why Stage 2 is truncated at \(P^{5/16}\)

Stage 2 of Theorem 5.3 Vaaler-expands the gap-cell indicator at a
truncation \(R_0=P^{a}\). Four printed inequalities depend on \(a\),
two of them monotone each way, so \(a\) is not free.

*Paid for by raising \(a\).*

- The **collision-band sum** of Stage 5 is
  \(3R_0^{1/2}P^{3/4}\log P=3P^{a/2+3/4}\log P\), which must stay inside
  the theorem's own \(P^{23/24}\); this forces \(a\le5/12\).
- The **\(q''\) curvature** of Step 5b(a) is
  \(\bigl(1.85khP^{1/8}+R_0\bigr)\cdot3|j|P^{-5/4}\), whose ratio to the
  main curvature is \(\asymp P^{a-1/2}\) once \(R_0\) is the larger
  term; it must clear the margin \(\tfrac14\).

*Bought by raising \(a\).* Both come from the fifth-letter Lemma 3.7
window of Theorem 6.3, opened at \(T=R_0\) against
\(\lvert C\rvert\le1.2812\,P^{19/96}\):

- the **window hypothesis** \(T\ge8(1+\lvert C\rvert)\), and
- the **flat cost** \(8(1+\lvert C\rvert)/T\) per point, which over a
  block must stay inside \(P^{1-1/96}\).

Both have margin \(P^{a-19/96}\), so both need \(a>19/96=0.198\), and
they need it with room: the constant is \(8\cdot\tfrac98\cdot2^{3/16}
=10.25\), and the flat cost must beat not \(1\) but \(P^{-1/96}\).

Solving each site for its least admissible \(P\):

| \(a\) | collision | \(q''\) | window | flat cost | worst |
|---|---|---|---|---|---|
| \(1/4\) | \(5.3\cdot10^{5}\) | \(3.0\cdot10^{10}\) | \(2.5\cdot10^{19}\) | \(1.8\cdot10^{24}\) | \(1.8\cdot10^{24}\) |
| \(9/32\) | \(1.1\cdot10^{7}\) | \(6.6\cdot10^{10}\) | \(1.4\cdot10^{12}\) | \(7.4\cdot10^{13}\) | \(7.4\cdot10^{13}\) |
| \(5/16\) | \(1.4\cdot10^{9}\) | \(3.0\cdot10^{11}\) | \(7.4\cdot10^{8}\) | \(5.5\cdot10^{9}\) | \(3.0\cdot10^{11}\) |
| \(1/3\) | \(2.8\cdot10^{11}\) | \(1.6\cdot10^{12}\) | \(3.5\cdot10^{7}\) | \(1.4\cdot10^{8}\) | \(1.6\cdot10^{12}\) |
| \(3/8\) | \(8.0\cdot10^{22}\) | \(1.1\cdot10^{15}\) | \(6.9\cdot10^{5}\) | \(1.5\cdot10^{6}\) | \(8.0\cdot10^{22}\) |

The window is what makes the choice sharp. At \(a=1/4\) the two
fifth-letter requirements are not merely inconvenient, they are the
whole threshold of the depth-five theorem, and the binding one is the
flat cost, which does not clear \(P^{1-1/96}\) until
\(1.8\cdot10^{24}\) --- ten orders above \(P_0\). At \(a=9/32\) the
worst site is \(7.4\cdot10^{13}\), which sneaks under
\(P_0=8.9\cdot10^{13}\) by less than a factor \(1.3\): too close to
print. At \(a=5/16\) the worst site is \(3.0\cdot10^{11}\), a clear
factor \(300\) below \(P_0\), and it is the minimum of the last column
over the admissible range. That is the value carried.

Two things this table settles. First, the choice costs the paper
nothing that binds: the collision-band term moves from
\(3P^{7/8}\log P\) to \(3P^{29/32}\log P\), still inside \(P^{23/24}\)
with \(P^{5/96}\) to spare, and the \(q''\) ratio moves from
\(52P^{-5/24}\) to \(48.9P^{-3/16}\), which at \(P_0\) is \(0.12\)
against a margin of \(\tfrac14\). \(P_0\) itself is unchanged. One
exponent in a statement does move: the collision-band term is the fifth
term of Lemma 5.2(i), which carries \(R_0^{1/2}P^{3/4}\) explicitly for
this reason, and reads \(P^{7/8}\) at \(a=1/4\) and \(P^{29/32}\) at
\(a=5/16\). Second, the window's margin is
genuinely narrow --- \(P^{a-19/96}\) with a constant above \(10\) ---
so this is a place where an asymptotic argument and an effective one
diverge by twenty orders of magnitude, and the paper's claim of
effectivity is what forced the choice.


## Acknowledgments

I used large language models extensively while drafting and revising
the text, organizing companion notes, and as an interactive assistant
for Lean statements, tests, and literature records. The models are
not authors. The theorems of this paper are human proofs from the
cited classical inequalities; the Lean certificates cover only the
exact floor identities and the companion's finite-itinerary theorems. I
take full responsibility for the contents.

## References

1. C. A. Pickover, *Computers and the Imagination: Visual Adventures Beyond
   the Edge*, St. Martin's Press, New York, 1991, ch. 40, p. 232.
2. OEIS Foundation Inc., “Juggler sequence: if \(n\) even then
   \(\lfloor\sqrt n\rfloor\) else \(\lfloor n^{3/2}\rfloor\),”
   Sequence A094683 in *The On-Line Encyclopedia of Integer Sequences*,
   https://oeis.org/A094683 (accessed 28 August 2026).
3. J. C. Lagarias, “The \(3x+1\) problem and its generalizations,”
   *Amer. Math. Monthly* 92 (1985), 3–23.
   [doi:10.1080/00029890.1985.11971528](https://doi.org/10.1080/00029890.1985.11971528).
4. R. Terras, “A stopping time problem on the positive integers,”
   *Acta Arith.* 30 (1976), 241–252.
   [doi:10.4064/aa-30-3-241-252](https://doi.org/10.4064/aa-30-3-241-252).
5. C. J. Everett, “Iteration of the number-theoretic function
   \(f(2n)=n\), \(f(2n+1)=3n+2\),” *Adv. Math.* 25 (1977), 42–45.
   [doi:10.1016/0001-8708(77)90087-1](https://doi.org/10.1016/0001-8708(77)90087-1).
6. T. Tao, “Almost all orbits of the Collatz map attain almost bounded
   values,” *Forum Math. Pi* 10 (2022), e12.
   [doi:10.1017/fmp.2022.8](https://doi.org/10.1017/fmp.2022.8).
7. V. Bergelson and A. Leibman, “Distribution of values of bounded
   generalized polynomials,” *Acta Math.* 198 (2007), 155–230.
   [doi:10.1007/s11511-007-0015-9](https://doi.org/10.1007/s11511-007-0015-9).
8. L. Kuipers and H. Niederreiter, *Uniform Distribution of Sequences*,
   Wiley-Interscience, New York, 1974.
9. H. Iwaniec and E. Kowalski, *Analytic Number Theory*, American
   Mathematical Society Colloquium Publications 53, Providence, RI, 2004.
10. J. D. Vaaler, “Some extremal functions in Fourier analysis,”
    *Bull. Amer. Math. Soc. (N.S.)* 12 (1985), 183–216.
    [doi:10.1090/S0273-0979-1985-15349-2](https://doi.org/10.1090/S0273-0979-1985-15349-2).
11. S. W. Graham and G. Kolesnik, *Van der Corput's Method of
    Exponential Sums*, London Mathematical Society Lecture Note
    Series 126, Cambridge University Press, Cambridge, 1991.
12. I. I. Piatetski-Shapiro, “On the distribution of prime numbers in
    sequences of the form \(\lfloor f(n)\rfloor\),” *Mat. Sb.* 33
    (1953), 559–566.
13. D. Leitmann, “The distribution of prime numbers in sequences of
    the form \(\lfloor f(n)\rfloor\),” *Proc. London Math. Soc. (3)*
    35 (1977), 448–462.
14. J. Rivat and P. Sargos, “Nombres premiers de la forme
    \(\lfloor n^c\rfloor\),” *Canad. J. Math.* 53 (2001), 414–433.
15. J. Rivat and J. Wu, “Prime numbers of the form
    \(\lfloor n^c\rfloor\),” *Glasg. Math. J.* 43 (2001), 237–254.
16. C. Mauduit and J. Rivat, “Propriétés \(q\)-multiplicatives de la
    suite \(\lfloor n^c\rfloor\), \(c>1\),” *Acta Arith.* 118 (2005),
    187–203.
17. J. F. Morgenbesser, “The sum of digits of
    \(\lfloor n^c\rfloor\),” *Acta Arith.* 148 (2011), 367–393.
    [doi:10.4064/aa148-4-4](https://doi.org/10.4064/aa148-4-4).
18. R. C. Baker, W. D. Banks, J. Brüdern, I. E. Shparlinski, and
    A. J. Weingartner, “Piatetski-Shapiro sequences,” *Acta Arith.*
    157 (2013), 37–68.
19. A. G. Abercrombie, “Beatty sequences and multiplicative number
    theory,” *Acta Arith.* 70 (1995), 195–207.
20. W. D. Banks and I. E. Shparlinski, “Short character sums with
    Beatty sequences,” *Math. Res. Lett.* 13 (2006), 539–547.
21. D. Glasscock, “Solutions to certain linear equations in
    Piatetski-Shapiro sequences,” *Acta Arith.* 177 (2017), 39–52.
22. P. Cochin, “Cycle Financing and Near-Convergent Diophantine Obstructions in the Juggler Map,” companion
    manuscript, 2026.
23. C. Müllner and L. Spiegelhofer, “Normality of the Thue–Morse
    sequence along Piatetski-Shapiro sequences, II,” *Israel J. Math.*
    220 (2017), 691–738.
    [doi:10.1007/s11856-017-1535-6](https://doi.org/10.1007/s11856-017-1535-6).
24. P. Cochin, “Fate Contagion in the Juggler Map and the Almost-All
    Reduction of Termination,” companion manuscript (Paper C), 2026;
    `docs/theory/juggler_fate_almost_all_note.md` in the repository
    https://github.com/sneakyweasel/balanced_ternary/.
