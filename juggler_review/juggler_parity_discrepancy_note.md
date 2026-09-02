---
title: Parity equidistribution of nested floor powers, with descent applications to the Juggler map
author: Philippe Cochin
date: 2 September 2026
subtitle: Working draft. Not submitted.
header-includes:
  - \AtBeginDocument{\author{Philippe Cochin \\ \texttt{philippe@cochin.fr}}}
---

## Abstract

For odd \(n\) set \(m=\lfloor n^{3/2}\rfloor\), \(v=\lfloor m^{3/2}\rfloor\),
and so on: the integer chains obtained by iterating \(x\mapsto\lfloor
x^{3/2}\rfloor\) and \(x\mapsto\lfloor\sqrt x\rfloor\) in a prescribed
pattern. We prove parity equidistribution, with power savings, for
every such pattern of depth at most four over odd starts. The obstacle
at depth two and beyond is that the naive expansion of \(m^{3/2}\)
leaves the sawtooth \(\{n^{3/2}\}\) with an amplitude that grows like
\(n^{3/4}\), which defeats the classical van der Corput method. The
proof reorganizes the phase by an exact linearization —
\(m^{3/2}=\tfrac32mn^{3/4}-\tfrac12n^{9/4}+O(n^{-3/4})\) with a
one-signed remainder, a Taylor rewrite that keeps the integer \(m\)
linear with a smooth coefficient — and funnels the deeper patterns
into a single *kernel*: the exponential sum of the level-2 floor
defect \(\{\lfloor n^{3/2}\rfloor^{3/2}\}\) against smooth weights of
scale \(n^{9/8}\). The central result (Theorem 5.3) is a power-saving
bound for that kernel, \(K_c\ll P^{1-1/96+\varepsilon}\), by double
Weyl differencing over an exact carry-branch decomposition and master
identity, with a targeted third differencing for the exact level-2
wave pieces (Lemma 5.2).

The sequences arise as the itineraries of the Juggler map
\(J(n)=\lfloor\sqrt n\rfloor\) (\(n\) even), \(\lfloor n^{3/2}\rfloor\)
(\(n\) odd), whose finite exact theory is developed in a companion
manuscript [22]. As a corollary, the class of starts carrying a
uniform power-envelope descent certificate of length at most five has
natural density \(7/8\); the four-step subclass has density
\(13/16\). An unconditional counting argument shows that parity
equidistribution at *all* depths would give density one to the set of
starts with some finite descent certificate. None of these is a
density of starts that reach \(1\), and no statement about the
Juggler conjecture itself is claimed. The remaining obstacle is the level-3
kernel, where the weight scale \(n^{27/16}\) exceeds \(n\); we state
it as an open problem and record precisely what blocks every method
of this paper.

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
in the single-floor literature stop before this point (Section 2).

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

2. **The kernel theorem** (Theorem 5.3). Every reorganization of the
   depth-4 pattern \(OOO*\) funnels into one object, the exponential
   sum of the level-2 floor defect
   \[
   K_c(P)=\sum_{\substack{n\sim P\\ n\ \mathrm{odd}}}
   e\bigl(c(n)\,\{\lfloor n^{3/2}\rfloor^{3/2}\}\bigr),
   \qquad c\asymp kP^{9/8}.
   \]
   We prove \(K_c(P)\ll P^{1-1/96+\varepsilon}\), uniformly for
   \(k\le P^{1/24}\), by double Weyl differencing over an exact
   carry-branch decomposition and master identity (Lemma 5.1), with a
   targeted third differencing for the level-2 wave pieces
   (Lemma 5.2). This is the hardest result of the paper, and
   Section 5 is written at full length — every estimate displayed
   with its constant — so that it can be checked without reference to
   anything outside this manuscript.

With the kernel theorem, depth-4 parity equidistribution over odd
starts is complete (Theorem 6.1): the eight \(O\)-rooted length-4
words each receive their expected share with a power saving. The same
estimates, applied to one further letter, count the two length-five
contractors \(OOOEE\) and \(OOEOE\) (Theorem 6.3), so the certified
descent class has density \(7/8\) (Corollary 6.4). The leftover
eighth is the expanding length-five tree
\(OOEOO\cup OOOEO\cup OOOO*\): the first two of those words are
counted and do not contract, and \(OOOO*\) is the level-3 kernel.

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
within four steps has natural density \(13/16\) (Corollary 4.9), and
the two length-five contractors raise that class to density \(7/8\)
(Corollary 6.4). Equidistribution at all depths would give the set of
starts with *some* finite descent certificate density one
(Proposition 7.1). We state plainly what these corollaries are not:
they are not densities of starts that reach \(1\), and they do not
touch the Juggler conjecture, whose analogue of Terras's almost-all
theorem for Collatz [4, 5, 6] remains open; see Lagarias [3] for the
Collatz survey.

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

### 1.1 Verification and evidence conventions

Every theorem in this paper is an ordinary human proof from the stated
classical inequalities; none is machine-checked, and no numerical
computation is used as a step in any proof below. Every exact identity
used — the parity bridge \(\lfloor x\rfloor\) odd iff
\(\{x/2\}\ge1/2\), the gap-cell identity, the double-gap identity, the
master identity of Lemma 5.1, and the fifth-letter identities of
Lemma 6.2 — is printed in the text with its proof. A companion
repository (Section 8) contains machine formalizations and numerical
probes of several of these identities;
nothing in this paper depends on it. Densities of certificate classes
are never densities of starts that reach \(1\).

## 2. Related work

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
drives Sections 4–6 has no analogue there. We know of no published
estimate for \(\sum e(\xi\{f(\lfloor g(n)\rfloor)\})\)-type sums, or
for the fractional parts \(\{f(\lfloor g(n)\rfloor)\}\), with \(f,g\)
convex powers and growing \(\xi\).

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

**What is not covered.** We know of no published equidistribution or
parity result for *nested* floor powers
\(\lfloor\lfloor n^{c}\rfloor^{d}\rfloor\) with \(c,d>1\), nor any
treatment of the level-2 defect sums \(K_c(P)\) of Section 5. The
obstruction is structural, not incremental: after one floor the
argument of the second floor is an integer sequence, not a smooth
function, and its fractional defect enters later phases with growing
amplitude. The individual devices of this paper are not new — the
linearization of Lemma 4.3 is a Taylor rewrite, and the carry
bookkeeping of Lemma 5.1 will be recognized by anyone who has
differenced \(\lfloor f(n)\rfloor\); what we believe is new is the
package (one-signed remainders, gap cells, the master identity, and
the kernel bound of Theorem 5.3) and the results it yields. A
literature check was last refreshed in September 2026; we would welcome
pointers to anything missed.

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

## 3. Preliminaries

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
If the word \(w\) is realized at \(n\ge2\) (the orbit's parities are
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

A word \(w\) with \(3^{\#O(w)}<2^{|w|}\) is *contracting*; realizing a
contracting word is a *descent certificate* of length \(|w|\).
Contracting words used below: \(E\), \(OE\), \(OOEE\), and the two
length-five words \(OOOEE\) and \(OOEOE\). Every even start realizes
\(E\), and every odd start with even image realizes \(OE\); those two
certificates cover all starts except the odd-to-odd class, which is
where the counting problem lives. Longer contracting words exist
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
branches are dictated by the target word, not by the orbit. The next
lemma is the exact identity that justifies this; it replaces any
appeal to sampled verification.

**Lemma 3.6 (branch consistency).**
Let \(d\ge1\) and let \(w=w_1\cdots w_d\) be a word with \(w_1=O\).
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
Section 5: a finite Fourier expansion for sawtooth phases whose
coefficient may exceed \(1\); a second-derivative test for two-term
monomial phases in which the curvature transition — the short set
where the two curvatures cancel — receives a trivial bound; and a
sublevel splitting for three-term monomial phases, again with the
transition set destined for a trivial bound. No third- or
fourth-derivative exponential-sum test is used anywhere in this
paper: on the short cells of Section 5 those tests do not sum, and
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
applications in Section 5 use exponent pairs from
\(E=\{\tfrac34,\tfrac54,\tfrac{11}8,\tfrac32,\tfrac{15}8\}\). One
corner of Section 5 (three curvature scales meeting on a zero-offset
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
\(\rho\le\rho_0(E)\). There are constants \(c_7(E)>0\) and \(C(E)\)
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
shorten the argument). The ratios \(A/B\), \(B/C\), \(A/C\) are
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
Step 5b, the \(\ell^\infty\) operator norm of the inverse is
\(288\), and one may take \(c_7=1/288\). \(\square\)

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

Every application of Lemmas 3.3 and 3.7–3.9 in Sections 4–6 is to be
read through this substitution; no displayed constant below needs
adjustment.

## 4. Exact linearization and depths one to four

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
\(f''(t)=\tfrac38(X-t)^{-1/2}\). Taylor with Lagrange remainder at
\(0\) gives
\(f(\theta)=f(0)+f'(0)\theta+\tfrac12 f''(\xi)\theta^2
=X^{3/2}-\tfrac32X^{1/2}\theta
+\tfrac3{16}(X-\xi)^{-1/2}\theta^2\) for some \(\xi\in(0,\theta)\).
Substituting \(\theta=X-m\) in the linear term yields
\(-\tfrac12X^{3/2}+\tfrac32mX^{1/2}=-\tfrac12n^{9/4}+\tfrac32mn^{3/4}\).
Since \(\theta\in[0,1)\) and \(f''>0\), the remainder \(E(n)\) lies
in \(\bigl[0,\tfrac3{16}(X-1)^{-1/2}\bigr]\). The coarser bound
\(\tfrac38(X-1)^{-1/2}\) used in the statement absorbs the missing
factor of \(2\) against \(\theta^2\le1\), and
\((X-1)^{-1/2}\le\tfrac43X^{-1/2}\) already for \(n\ge3\), whence
\(E(n)\le\tfrac12 n^{-3/4}\). (ii)
\(g=\lfloor X+\delta\rfloor-\lfloor X\rfloor
=\lfloor\delta\rfloor+\lfloor\{X\}+\{\delta\}\rfloor\), and the last
floor is \(1\) precisely when \(\{X\}+\{\delta\}\ge1\). \(\square\)

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
Together with Theorem 4.4 this makes depth 3 complete: each of
\(OOO\), \(OOE\), \(OEO\), \(OEE\) has density \(1/8\) with a power
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
not a census of \(E\)-rooted words of length \(\ge2\), and it is
not a census of every \(O\)-rooted word of length four (the
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

The density \(13/16\) is the exact ceiling of this one-growing-layer
machinery: a word contracts iff \(3^{o}<2^{\ell}\), the method so far
proves letters at positions 1–3 of any word plus further letters along
even branches only, and the contracting minimal words with all odd
letters at positions \(\le2\) are exactly \(E\), \(OE\), and \(OOEE\).
Completing depth 4 requires the \(OOO*\) split — a second
growing layer, where the fourth-letter phase coefficient
\(W\asymp kn^{9/8}\) crosses integers within single steps and no
drift-1 interval exists. Sections 5 and 6 close that split. The
\(OOO*\) words are non-contracting at depth 4, so the four-step
certified density remains \(13/16\); the next increment is the two
length-five contractors of Theorem 6.3.

## 5. The kernel theorem

Every reorganization of the \(OOO*\) phase funnels into one object:
for smooth weights \(c\) of scale \(kP^{9/8}\) on \(n\sim P\),
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
\(Y^{3/2}=m^{9/4}\). (ii) The gap identity of Lemma 4.3(ii) applied
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
\(n\), \(n{+}d_1\), \(n{+}d_2\), \(n{+}d_1{+}d_2\). \(\square\)

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
\]
and every displayed constant below is valid for
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
weight \(c=\tfrac{3k}4n^{9/8}\) (the general \(c\) of Theorem 5.3
changes only the absolute constants),
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
+O\bigl(kh_1h_2P^{-5/8}\bigr),
\]
the two shapes being the composite monomials \(kjn^{15/8}\)
(offset branches) and \(kh_1h_2\)-scale \(n^{11/8}\) (zero-offset),
with sign product
\(\alpha(\alpha-1)(\alpha+\beta-2)(\alpha+\beta-3)>0\) at
\(\alpha=\tfrac98\), \(\beta\in\{\tfrac34,\tfrac14\}\). Finally, the
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

Every numerical margin in this section is claimed only for
\(P\ge P_0\), with an absolute but ineffective \(P_0\). The
comparisons stratify. The Lemma 3.7 / Lemma 5.2 window
hypotheses first hold together on the printed majorants at a
moderate threshold (of size \(3\cdot 10^5\)). The interpolant
error of Step 5b is \(O(P^{-5/6})\) with leading coefficient
\(0.11\), and is not absorbed into a smaller constant. The
comparison \(V\le c_7S/2\) at \(c_7=1/288\) for the printed
triple of Step 5b forces \(P_0\) to be large (of size
\(10^{24}\)): until then a three-term zero of \(\Phi''\) can
keep the sublevel \(\Omega_V\) of length \(\Theta(P)\) on a
dyadic block, and the printed length \(P^{89/96}\) is the bound
of Lemma 3.9, not a claim that the sublevel is short at small
\(P\). The constants are not asserted to be sharp.

The proof of the kernel theorem classifies the differenced pieces
into four classes; three are handled by standard tests, and the
fourth — an exact level-2 wave \(e(qY)\), possibly riding a frozen
floor — is the genuinely new difficulty. We isolate it as a
standalone lemma with its own differencing, so that it can be
checked independently.

**Lemma 5.2 (level-2 waves: the mixed-piece bound).**
Assume (C1)–(C3), write \(\mathcal D=\{0,d_1,d_2,d_1{+}d_2\}\), and
call a *decoration* any sum \(\rho\) of at most nine terms of the
classes

- (D1) \(q'\,\Delta_{2h}\Delta_{2h'}Y(n{+}d')\) with
  \(|q'|\le 4P^{1/24}\), \(1\le h'\le2P^{1/24}\),
  \(d'\in\mathcal D\);
- (D2) \(-\Delta_{2h}\bigl(c\,\lfloor
  F_{\boldsymbol\kappa}(X)\rfloor\bigr)(n)\), with
  \(F_{\boldsymbol\kappa}\) a branch function of Lemma 5.1(iii),
  offset \(|j|\le3\);
- (D3) a smooth \(\varphi\) with \(|\varphi''|\le3kh_1h_2P^{-5/8}\)
  and \(|\varphi'''|\le3kh_1h_2P^{-13/8}\);

here \(2h\) is the shift of part (i), and in part (ii) the
decorations are read after the differencing there. Then, for sums
over \(n\in(P,2P]\), \(n\) odd:

(i) *(differenced wave)* for all integers \(u,h\ge1\) with
\(h\le P^{1/8}\), \(uh\le P^{1/2}\), and \(d\in\mathcal D\),
\[
V:=\Bigl|\sum_n
e\bigl(u\,\Delta_{2h}Y(n{+}d)+\rho(n)\bigr)\Bigr|
\;\ll\;
\Bigl((uh)^{1/2}P^{5/8}+(h/u)^{1/2}P^{7/8}+P^{7/8}\Bigr)
P^{\varepsilon};
\]

(ii) *(waves)* for all integer coefficients \((q_d)_{d\in\mathcal D}\)
with \(|q_d|\le 4P^{1/24}\) and
\(t:=\sum_{d\in\mathcal D}q_d\ne0\), all
\(\varepsilon_0\in\{0,1\}\), and \(\varphi\) of class (D3),
\[
U:=\Bigl|\sum_n
e\Bigl(\sum_{d\in\mathcal D}q_d\,Y(n{+}d)
-\varepsilon_0\,c(n)\lfloor F_{\boldsymbol\kappa}(X(n))\rfloor
+\varphi(n)\Bigr)\Bigr|
\;\ll\;|t|^{-1/6}\,P^{23/24+\varepsilon}.
\]

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

*Proof of (ii) from (i).* Replacing the summand by its conjugate we
may take \(t\ge1\). Fix \(e_1\in\mathcal D\) with
\(q_{e_1}\ne0\) and write, exactly (telescoping onto the base
\(e_1\)),
\[
\sum_{d\in\mathcal D}q_d\,Y(n{+}d)
=t\,Y(n{+}e_1)+\sum_{d\ne e_1}q_d\,
\Delta_{|d-e_1|}Y\bigl(n{+}\min(d,e_1)\bigr),
\]
and the second sum is a set of at most three decoration seeds with
shifts \(|d-e_1|/2\le h_1{+}h_2\le2P^{1/24}\). Weyl differencing at
shift \(2h_3\), \(1\le h_3\le H_3:=\lceil t^{1/3}P^{1/12}\rceil\),
by the \(A\)-process recorded after Lemma 3.3:
\[
|U|^2\le\frac{P^2}{H_3}
+\frac{2P}{H_3}\sum_{h_3=1}^{H_3}
\bigl|V_{h_3}\bigr|,
\qquad
V_{h_3}
=\sum_ne\bigl(t\,\Delta_{2h_3}Y(n{+}e_1)+\rho_{h_3}(n)\bigr),
\]
where \(\rho_{h_3}\) collects
\(q_d\Delta_{2h_3}\Delta_{|d-e_1|}Y\) (class (D1) with
\(h'=|d-e_1|/2\le2P^{1/24}\)),
\(-\varepsilon_0\Delta_{2h_3}(c\lfloor F(X)\rfloor)\) (class (D2)),
and \(\Delta_{2h_3}\varphi\) (class (D3):
\(|(\Delta_{2h_3}\varphi)''|\le2h_3\sup|\varphi'''|
\le6kh_1h_2h_3P^{-13/8}\le3kh_1h_2P^{-5/8}\) since
\(h_3\le P^{1/4}\)). The hypothesis of (i) holds:
\(th_3\le t\cdot2t^{1/3}P^{1/12}=2t^{4/3}P^{1/12}\).
With \(|q_d|\le4P^{1/24}\) one has \(t\le16P^{1/24}\), so
\(2t^{4/3}P^{1/12}\le81P^{5/36}\le P^{1/2}\) for
\(P\ge P_0\), and \(H_3\le3P^{7/72}\le P^{1/4}\). Part (i) gives
\[
|U|^2\le\frac{P^2}{H_3}
+\Bigl(4t^{1/2}H_3^{1/2}P^{13/8}
+4t^{-1/2}H_3^{1/2}P^{15/8}
+4P^{15/8}\Bigr)P^{\varepsilon},
\]
and at \(H_3=\lceil t^{1/3}P^{1/12}\rceil\) the four terms are, in
order, \(\le t^{-1/3}P^{23/12}\);
\(\le6t^{2/3}P^{5/3}=6\,(tP^{-1/4})\,t^{-1/3}P^{23/12}
\le96P^{1/24-1/4}\cdot t^{-1/3}P^{23/12}\);
\(\le6t^{-1/3}P^{1/24}P^{15/8}=6t^{-1/3}P^{23/12}\); and
\(\le4\,(t^{1/3}P^{-1/24})\,t^{-1/3}P^{23/12}
\le11P^{1/72-1/24}\,t^{-1/3}P^{23/12}\). Hence
\(|U|^2\ll t^{-1/3}P^{23/12+\varepsilon}\), which is (ii).

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
at truncation \(R_0=P^{1/4}\) (majorant cost \(\le4P/R_0=4P^{3/4}\)).
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
\(\min(2,2\pi|B|)\le14P^{-1/16}\), mass \(O(\log P)\), flat cost
\(\le12P^{1/2}\), majorant \(\le14P^{-1/16}\cdot4P^{3/4}\).
(s2) If \(P^{3/16}<uh\le P^{1/2}\) then \(|B|\le2.25P^{1/4}\) and
\(B\) drifts by at most \(1\) on windows of length
\(\ge P^{5/4}/(0.6uh)\ge1.2P^{3/4}\): at most \(0.6P^{1/4}+1\)
windows. Per window Lemma 3.7 at the centre \(B_0\)
(\(T=P^{1/2}\ge8(1+2.25P^{1/4})\) for \(P\ge P_0\), since
\(P^{1/4}\ge19\); flat cost \(\le8(1{+}2.25P^{1/4})P^{1/2}
\le27P^{3/4}\) in total) produces modes \(e(w\nu^{3/2})\) whose
coefficients decay as
\(\min(2,\tfrac1{\pi|w+B_0|})+\min(2,\tfrac1{\pi|w|})\); the
window-boundary cost is, using \(uh>P^{3/16}\),
\(\le(0.6P^{1/4}{+}1)\cdot1.83\,(0.30\,uh)^{-1/2}P^{3/8}
\le2.1\,P^{1/4-3/32+3/8}=2.1\,P^{17/32}\le P^{5/8}\). Modes with
\(|w|\) in the collision window are treated in Stage 5.

*Stage 4 (the main curvature, \(r=w=0\)).* On a cell the remaining
phase is \(\tfrac{3u}2G(\nu{+}2h)^{3/4}+uA_h+(\text{smooth
decorations})\), with second derivative
\[
-\tfrac9{32}\,uG\,(\nu{+}2h)^{-5/4}
\in-[0.30,\,1.35]\,uh\,P^{-3/4}
\qquad(\text{E2}),
\]
single-signed with in-cell ratio \(\sup/\inf\le4.5\): the second
derivative of \(\tfrac{3u}2G(\nu{+}2h)^{3/4}\) is the single term
\(\tfrac{3u}2G\cdot\tfrac34\cdot(-\tfrac14)(\nu{+}2h)^{-5/4}\), with
\(G\) frozen and bounded by (E2). The competitor
\(uA_h''\) has ratio
\(\le0.64uh^2P^{-7/4}/(0.30uhP^{-3/4})\le2.2hP^{-1}\le2.2P^{-3/4}\);
decoration competitors are bounded in Stage 6. Lemma 3.3 per cell
and summation give
\[
\sum_{\text{cells}}
\Bigl(\ell_i\lambda^{1/2}+\lambda^{-1/2}\Bigr)
\le2.3\,(uh)^{1/2}P^{5/8}
+2.8\,(h/u)^{1/2}P^{7/8}.
\]

*Stage 5 (nonzero modes and collisions).* A mode \(w\ne0\) (or
\(r\ne0\); identical treatment with weight \(1/|r|\)) adds the phase
\(w\nu^{3/2}\) of curvature \(\ge0.53|w|P^{-1/2}\).
If \(0.53|w|P^{-1/2}\ge4\cdot1.35uhP^{-3/4}\), i.e.
\(|w|\ge10.2\,uhP^{-1/4}\), the mode curvature dominates at margin
\(\ge4\): Lemma 3.3 over the full block gives
\(\le1.4|w|^{1/2}P^{3/4}+1.4|w|^{-1/2}P^{1/4}\), and the
coefficient-weighted sums are
\(\le3R_0^{1/2}P^{3/4}\log P=3P^{7/8}\log P\) (families of Stage 2,
regime (s1)) and \(\le CP^{7/8}\log P\) (regime (s2) tails). If
\(|w|\le0.1\,uhP^{-1/4}\) the main curvature dominates at margin
\(\ge4\) and the mode rides along at Stage 4's scale, weight
summable to \(O(\log P)\). In the remaining collision window
\(0.1\,uhP^{-1/4}\le|w|\le10.2\,uhP^{-1/4}\) (nonempty only in
regime (s2)), the two curvatures can cancel: there the phase is the
two-term monomial
\(a\nu^{3/4}+w\nu^{3/2}\) with \(a=\tfrac{3u}2G\asymp uh P^{1/2}\)
plus perturbations already shown \(\rho_0\)-small, and Lemma 3.8
with \((\alpha,\beta)=(\tfrac34,\tfrac32)\) applies per window with
\(M\in[0.03,\,11]\,uhP^{-3/4}\) (both curvature scales lie in this
window on the collision band, and \(M\le11P^{-1/4}\)):
\[
\le C_E\bigl(|I_w|M^{1/2}+M^{-1/2}+(P/M)^{1/3}\bigr)
\quad\text{per window.}
\]
Summing over the at most \(0.6P^{1/4}{+}1\) windows — the transition
cost \((P/M)^{1/3}\) carries no window-length factor, which is why
it sums — with the \(O(\log P)\) collision-band coefficient mass:
\[
\sum_w|I_w|M^{1/2}\le3.4\,(uh)^{1/2}P^{5/8},\qquad
\sum_wM^{-1/2}\le4.5\,(uh)^{-1/2}P^{5/8}\le4.5\,P^{5/8},
\]
\[
\sum_w(P/M)^{1/3}
\le0.77P^{1/4}\cdot3.3\,(uh)^{-1/3}P^{7/12}
=2.5\,(uh)^{-1/3}P^{5/6}\le2.5\,P^{5/6-1/16}=2.5\,P^{37/48},
\]
the last using \(uh>P^{3/16}\) in regime (s2). The collision-band
total is \(\le C\bigl((uh)^{1/2}P^{5/8}+P^{5/6}\bigr)\log P\le
CP^{7/8}\log P\).

*Stage 6 (decorations).* Each class is dominated at a displayed
margin against the Stage-4 curvature
\(\ge0.30uhP^{-3/4}\).

- (D1). On the branch decomposition of Lemma 5.1(iii) at the shift
  pair \((h_3\text{-role }h,\,h')\): the arcs are absorbed by the
  shift device (log mass); the \(b\)-run boundaries add
  \(\le1.5(h{+}2h')P^{1/2}+2\) cells, at boundary cost
  \(\le1.5(h{+}2h')P^{1/2}\cdot1.83(0.30uh)^{-1/2}P^{3/8}
  \le5.1(h/u)^{1/2}P^{7/8}+10.3\,h'(uh)^{-1/2}P^{7/8}\)
  (the second term is what the \(H_3\)-averaging of part (ii)
  absorbs: it contributes
  \(\le2h't^{-2/3}P^{43/24}\le P^{1/24-1/8}\,t^{-1/3}P^{23/12}\)
  there).   The \(\theta\)-coefficient of the decoration is
  \(\le|q'|\bigl(2|j'|P^{-1/4}+20hh'P^{-3/4}\bigr)
  \le24P^{1/24-1/4}+160P^{1/24+1/8+1/24-3/4}
  =24P^{-5/24}+160P^{-13/24}<1\): sub-unit, expanded
  in the Stage-2 families. Its smooth curvature has ratio
  \(\le|q'|\bigl(2|j'|P^{-5/4}+25hh'P^{-7/4}\bigr)
  /(0.30uhP^{-3/4})\le80P^{1/24-1/2}+672P^{1/24+1/24-1}
  \le P^{-1/4}\): dominated.
- (D2). Write
  \(\Delta(c\lfloor F\rfloor)
  =(\Delta c)\lfloor F\rfloor+c_+\Delta\lfloor F\rfloor\)
  with \(c_+=c(\cdot{+}2h)\).
  (a) \((\Delta c)\lfloor F\rfloor=(\Delta c)F-(\Delta c)\{F\}\):
  the smooth part has curvature
  \(\le\bigl((\Delta c)F\bigr)''\le7kh|j|P^{-9/8}
  +28khh_1h_2P^{-13/8}\), ratio to the main curvature
  \(\le24k|j|P^{-3/8}/u\le72P^{1/24-3/8}\): dominated. The sawtooth
  part has coefficient
  \(\Delta c\in(1.68,1.85)\,khP^{1/8}\), handled per windows of
  drift \(\le1\): at most \(2khP^{1/8}{+}1\) windows, at boundary
  cost
  \(\le2khP^{1/8}\cdot1.83\,(0.30\,uh)^{-1/2}P^{3/8}
  \le7k\,(h/u)^{1/2}P^{1/2}\). Per window, Lemma 3.7 at
  \(T=P^{1/2}\) yields modes \(e(q''(F\circ X))\) of curvature
  \(\le(2khP^{1/8}{+}P^{1/2})\cdot3|j|P^{-5/4}\le18P^{-3/4}
  \cdot P^{-1/16}\), ratio to the main curvature
  \(\le60P^{-1/16}\): dominated. The flat cost is, per point,
  \(8(1{+}B_0)/T\), so in total
  \(\le8\bigl(1{+}1.85khP^{1/8}\bigr)P^{1/2}
  \le8P^{1/2}+15\,khP^{5/8}\le23\,P^{1/24+1/8+5/8}
  =23\,P^{19/24}\le P^{7/8}\), using \(h\le P^{1/8}\) and (C3).
  (b) \(c_+\Delta\lfloor F\rfloor\): by the gap identity applied to
  the sequence \(F\circ X\),
  \(\Delta\lfloor F\rfloor=\lfloor\Delta F\rfloor+\kappa_F\).
  \(\Delta F\) has total drift
  \(\le P\cdot2h\sup|(F\circ X)''|\le P\cdot2h(2|j|P^{-5/4}
  +25h_1h_2P^{-7/4})\le13hP^{-1/4}+50h\,h_1h_2P^{-3/4}<1\), so
  \(\lfloor\Delta F\rfloor\) takes at most two values, on at most
  two intervals; per value the phase \(-q_0c_+\) (\(|q_0|\le
  2{+}6hP^{-1/4}\le3\)) has curvature \(\le0.4kP^{-7/8}\), ratio
  \(\le1.4kP^{-1/8}/(uh)\le1.4P^{1/24-1/8}\): dominated. The carry
  \(\kappa_F=\{F\}+\{\Delta F\}-\{F{+}\Delta F\}\) is a sum of unit
  sawtooths in slow variables (all drifts \(<1\) per step): Lemma
  3.5 at truncation \(P^{1/8}\) (majorant \(\le3\cdot4P^{7/8}\))
  gives modes \(e(q''(F\circ X))\)-type of curvature
  \(\le P^{1/8}\cdot3|j|P^{-5/4}\le9P^{-9/8}\), ratio
  \(\le30P^{-3/8}\): dominated.
- (D3). Ratio
  \(\le2h\sup|\varphi'''|/(0.30uhP^{-3/4})
  \le20kh_1h_2P^{-7/8}/u\le20P^{1/8-7/8}\): dominated.

*Totals.* Stages 1–6 bound \(V\) by
\[
C\Bigl((uh)^{1/2}P^{5/8}+(h/u)^{1/2}P^{7/8}+P^{7/8}
+k\,(h/u)^{1/2}P^{1/2}\Bigr)\log^3P,
\]
and the fourth term is \(\le P^{1/24}\cdot(h/u)^{1/2}P^{1/2}\), 
absorbed by the second. This is (i) up to the stated
\(P^{\varepsilon}\).

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
| (D1) run boundaries | \((h/u)^{1/2}P^{7/8}+h'(uh)^{-1/2}P^{7/8}\) | (i); \(H_3\)-average |
| (D2)(a) smooth / sawtooth | dominated; \(P^{7/8}\) flat | Stage 4; (i) |
| (D2)(b) gap / carry | dominated; \(P^{7/8}\) majorant | Stage 4; (i) |
| (D3) | dominated at \(P^{-3/4}\) | Stage 4 |

No decoration class is used later unless it appears in this
table. \(\square\)

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

**Theorem 5.3 (kernel cancellation).**
Let \(c\) be smooth on \((P,2P]\) with \(c^{(r)}\asymp kP^{9/8-r}\)
for \(r=0,\ldots,4\), derivative signs following the monomial pattern
(e.g. \(c=\tfrac{3k}4n^{9/8}\)), and \(1\le k\le P^{1/24}\). Then
\[
K_c(P)\ll P^{1-1/96+\varepsilon},
\]
uniformly in \(k\).

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
(C1)–(C3) hold with room \(P^{-1/48}\). We prove
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

(3c) *\(M_3\).* The mirror of (3a)–(3b) with \(h_1\leftrightarrow
h_2\), producing \(e(qY(n{+}d_2))\), \(e(qW')\)-modes.

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
shift device at \(O(\log P)\) mass and \(4P^{3/4}\) majorant, as in
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
\(|t|\le3J_2\le12P^{1/24}\), inside the coefficient budget of
Lemma 5.2(ii).

If \(t\ne0\): telescoping,
\(\sum_iq_iY(n{+}e_i)=t\,Y(n{+}e_1)+\sum_{i\ge2}q_i\,
\Delta_{e_i-e_1}Y(n{+}\min(e_1,e_i))\), and after the targeted
differencing of Lemma 5.2(ii) the differenced-wave remainders and
the \(u,u'\)-modes become (D1) decorations, the anchor becomes the
(D2) decoration, and the smooth content is (D3): Lemma 5.2(ii)
applies and gives \(\ll|t|^{-1/6}P^{23/24+\varepsilon}\) per piece.
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
Step 4, which by Lemma 5.1(iii) are smooth-per-branch with sub-unit
\(\theta\)-coefficients), slow modes, and (D3)-smooth content.
Split by the anchor branch type.

**(5a) Offset branches (\(j\ne0\)).** The anchor curvature is,
by (E6) and the window-centre composite,
\[
\lambda_a=\tfrac{729}{512}\,k|j|\,n^{-1/8}\,(1+O(P^{-1/8}))
\ \in\ [1.2,\,1.5]\,k|j|P^{-1/8},
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
ratio \(\le0.43P^{-1/8}\) against \(\lambda_a\ge1.2P^{-1/8}\);
resonant (D1) content \(\le6\,|q'|P^{-5/4}\) with
\(|q'|\le4P^{1/24}\), ratio \(\le20P^{1/24-5/4+1/8}=20P^{-13/12}\);
slow modes
\(\le3J_2|j|P^{-5/4}\), ratio \(\le8P^{1/24-9/8}\); (D3) content,
ratio \(\le3h_1h_2P^{-1/2}\le P^{-1/4}\). The \(\theta\)-sawtooth of
the anchor has coefficient \(\tfrac9{16}k|j|P^{3/8}\)-scale with
per-step drift \(\le0.2k|j|P^{-5/8}<1\): at most
\(1.2k|j|P^{3/8}{+}1\) windows of length \(\ge0.8P^{5/8}/(k|j|)\),
window-boundary cost
\(\le1.2k|j|P^{3/8}\cdot0.92(k|j|)^{-1/2}P^{1/16}
\le1.1(k|j|)^{1/2}P^{7/16}\). Off the collision band, window modes
\(w\) are dominated at margin \(\ge4\) either way and ride along or
are estimated by Lemma 3.3 at their own scale with \(1/|w{+}B_0|\)
weights (\(\ll P^{7/8}\log P\) in total); on the collision band
\(|wX''|\in[\tfrac14,4]\lambda_a\), Lemma 3.8 with
\((\alpha,\beta)=(\tfrac{15}8,\tfrac32)\) and
\(M\in[0.3,\,6]\,k|j|P^{-1/8}\) gives
\(\le C_E(|I_w|M^{1/2}+M^{-1/2}+(P/M)^{1/3})\) per window; summed
over the at most \(1.2k|j|P^{3/8}{+}1\) windows with the
\(O(\log P)\) band mass,
\[
\sum_w|I_w|M^{1/2}\le2.5\,(k|j|)^{1/2}P^{15/16},\qquad
\sum_wM^{-1/2}\le2.2\,(k|j|)^{1/2}P^{7/16},
\]
\[
\sum_w(P/M)^{1/3}
\le1.2k|j|P^{3/8}\cdot1.5\,(k|j|)^{-1/3}P^{3/8}
=1.8\,(k|j|)^{2/3}P^{3/4}\le3.8\,P^{1/36+3/4},
\]
so the band total is \(\ll(k|j|)^{1/2}P^{15/16}\log P\).
The main estimate is Lemma 3.3 per frozen run at scale
\(\lambda_a\): run lengths \(\ge\tfrac1{22}P^{1/4}/(|j|{+}1)\)
(Lemma 5.1(iii)), and
\(\lambda_a^{-1/2}\le0.92(k|j|)^{-1/2}P^{1/16}\ll\) run length, so
\[
\sum_{\text{runs}}\bigl(\ell\lambda_a^{1/2}+\lambda_a^{-1/2}\bigr)
\le1.3\,(k|j|)^{1/2}P^{15/16}
+21\,(|j|{+}1)|j|^{-1/2}k^{-1/2}P^{13/16}.
\]
Summed over the eight carry branches and \(|j|\le3\) with the
\(O(\log^3P)\) piece masses:
\(\ll(k)^{1/2}P^{15/16+\varepsilon}
\le1.8\,P^{1/48}P^{15/16+\varepsilon}=1.8\,P^{23/24+\varepsilon}\)
at \(k\le P^{1/24}\) — the absorbed \((k|j|)^{1/2}\) loss, exactly
at the bottleneck.

**(5b) Zero-offset branches (\(j=0\)).** The expanded interpolant
below gives the anchor curvature
\(\lambda_0\in[1.0,5.0]\,kh_1h_2P^{-5/8}\) (leading coefficient
\(\tfrac{243}{128}\), times the \((E2)\) variation of the gaps and
the dyadic range of \(\nu^{-5/8}\)). Runs of length
\(\ge\tfrac1{22}P^{3/4}/(h_1h_2)\). Let
\(\mu=0.84\max(uh_1,u'h_2)P^{-3/4}\) be the strongest
differenced-wave scale present. Three regimes.

- *Anchor-dominant* (\(60\mu\le\lambda_0\)): Lemma 3.3 per run at
  \(\lambda_0\), all else dominated at margin \(\ge20\):
  \(\le3.0(kh_1h_2)^{1/2}P^{11/16}
  +25\,(h_1h_2/k)^{1/2}P^{9/16}\).
- *Mode-dominant* (\(\mu\ge60\lambda_0\), i.e.
  \(uh_1\ge60\,kh_1h_2P^{1/8}\)-form): Lemma 5.2(i) with the
  undifferenced anchor as decoration: its run boundaries number
  \(\le22h_1h_2P^{1/4}\le22P^{5/16}\), cost
  \(\le22P^{5/16}\cdot3.4(uh_1)^{-1/2}P^{3/8}\le75P^{11/16}\); its
  smooth part is dominated at margin \(\ge20\) by hypothesis. On a
  zero-offset branch the anchor's \(\theta\)-coefficient is
  \(c\,\partial_m F=\tfrac34 c\cdot\bigl(-\tfrac12\beta_1\beta_2
  (m+\xi)^{-3/2}\bigr)\), hence
  \(\lvert B\rvert\le1.2\,kh_1h_2P^{-1/8}\le1.2P^{-1/48}<1\) by
  (C1): the sawtooth is sub-unit, Lemma 3.7 applies in a single
  window at \(T=P^{1/2}\) (hypothesis \(T\ge8(1+|B|)\) is
  immediate), and there is no large-\(B\) window inventory. (The
  offset-scale amplitude \(kh_1h_2P^{3/8}\) does not occur at
  \(j=0\).) Centre modes \(w\) are treated as in Lemma 5.2(i),
  Stage 5. Total
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
  \(0.84\,uh_1P^{-3/4}=\mu\le60\lambda_0\le300\,kh_1h_2P^{-5/8}\)
  forces \(u\le360\,kh_2P^{1/8}\le360\,P^{5/24}\), and likewise
  \(u'\le360\,kh_1P^{1/8}\le360\,P^{5/24}\). The phase's second
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
  integers.

  *Interpolant.* Write
  \(\delta_h(\nu)=(\nu{+}2h)^{3/2}-\nu^{3/2}\) and
  \(F_{\mathrm{sm}}(\nu)=\tfrac34\,(\Delta_1X(\nu))(\Delta_2X(\nu))\,
  X(\nu)^{-1/2}\), the \(j=0\) branch function of Lemma 5.1(iii)
  with each frozen \(\beta_i\) replaced by the smooth gap
  \(\Delta_iX\). The second derivative on a cell is
  \[
  f''
  =-\tfrac9{32}\Bigl(uG_1(\nu{+}2h_1)^{-5/4}
  +u'G_2(\nu{+}2h_2)^{-5/4}\Bigr)
  +\bigl(c_{11}(G_F-J_F)\bigr)''
  +wX''+O(\rho_0\text{-small}),
  \]
  with \(G_i,J_F\) frozen. Expand the anchor *before* interpolating:
  since \(J_F\) is constant on the run,
  \[
  \bigl(c_{11}(G_F-J_F)\bigr)''
  =2c'G_F'+c\,G_F''+c''(G_F-J_F).
  \]
  The last summand is \(O(|c''|)\) because \(\lvert G_F-J_F\rvert<1\).
  Define the interpolant by replacing the remaining frozen integers
  in this expanded expression:
  \[
  \begin{aligned}
  \Lambda(\nu)
  &=-\tfrac9{32}u\,\delta_{h_1}(\nu)\,(\nu{+}2h_1)^{-5/4}
  -\tfrac9{32}u'\,\delta_{h_2}(\nu)\,(\nu{+}2h_2)^{-5/4}\\
  &\qquad
  +2c'(\nu)F_{\mathrm{sm}}'(\nu)+c(\nu)F_{\mathrm{sm}}''(\nu)
  +\tfrac12 c''(\nu)
  +wX''(\nu).
  \end{aligned}
  \]
  The replacement \(J_F\mapsto F_{\mathrm{sm}}-\tfrac12\) is made
  only in the already-expanded \(c''\)-term, and produces the
  displayed \(\tfrac12 c''\). It is *not* a replacement in the
  phase \(c(G-J_F)\), which would collapse the anchor to
  \(c/2\) and destroy the curvature.

  Each replacement moves its argument by at most \(1\), so
  \[
  |f''-\Lambda|
  \le\tfrac9{32}(u{+}u')P^{-5/4}
  +\lvert c_{11}''\rvert
  +8k(h_1{+}h_2)P^{-9/8}
  \le219P^{-25/24}+0.11P^{-5/6}.
  \]
  The second term is the leading interpolant error and is not
  absorbed into a smaller multiple of \(P^{-5/6}\). The first
  term dies relative to it. The comparison
  \(V\ge10\lvert f''-\Lambda\rvert\) below is read from this
  two-term majorant, for \(P\ge P_0\).

  *Leading monomials.* Mean-value expansion gives
  \(\delta_h(\nu)=3h\,\xi^{1/2}\) with \(\xi\in(\nu,\nu{+}2h)\),
  hence
  \(\delta_h(\nu)\,(\nu{+}2h)^{-5/4}=3h\,\nu^{-3/4}\bigl(1+O(hP^{-1})\bigr)\),
  and
  \[
  -\tfrac9{32}u\,\delta_{h_1}(\nu)\,(\nu{+}2h_1)^{-5/4}
  =-\tfrac{27}{32}uh_1\,\nu^{-3/4}\bigl(1+O(h_1P^{-1})\bigr),
  \]
  and likewise for \(u'\). For the anchor,
  \(\Delta_iX=3h_i\nu^{1/2}(1+O(h_iP^{-1}))\) and
  \(X^{-1/2}=\nu^{-3/4}\), so
  \(F_{\mathrm{sm}}=\tfrac{27}{4}h_1h_2\nu^{1/4}(1+O(hP^{-1}))\).
  With \(c=\tfrac{3k}4\nu^{9/8}\),
  \[
  2c'F_{\mathrm{sm}}'+c\,F_{\mathrm{sm}}''
  =\tfrac{243}{128}\,kh_1h_2\,\nu^{-5/8}\bigl(1+O(hP^{-1})\bigr):
  \]
  indeed \(cF_{\mathrm{sm}}=\tfrac{81k}{16}h_1h_2\nu^{11/8}
  (1+O(hP^{-1}))\), so
  \((cF_{\mathrm{sm}})''=\tfrac{2673}{1024}kh_1h_2\nu^{-5/8}
  (1+O(hP^{-1}))\) and
  \(c''F_{\mathrm{sm}}=\tfrac{729}{1024}kh_1h_2\nu^{-5/8}
  (1+O(hP^{-1}))\), and the difference is
  \(2c'F'+cF''=(cF)''-c''F\). The term \(\tfrac12 c''\) is
  \(O(kP^{-7/8})\) and is absorbed in the perturbation below.
  The window mode is exactly \(wX''=\tfrac34 w\nu^{-1/2}\).

  Thus \(\Lambda=\Phi''+r\), where
  \[
  \Phi(\nu)
  =a\,\nu^{5/4}+b\,\nu^{11/8}+w\,\nu^{3/2},
  \qquad
  a=-\tfrac{27}{10}(uh_1+u'h_2),\quad
  b=\tfrac{81}{22}\,kh_1h_2,
  \]
  and the remainder \(r\) collects the relative
  \(O(hP^{-1})\) expansions, the \(\tfrac12 c''\) term, and the
  \(O(\rho_0)\) decorations. (Check:
  \(\Phi''\) has leading coefficients
  \(a\cdot\tfrac54\cdot\tfrac14=-\tfrac{27}{32}(uh_1+u'h_2)\) and
  \(b\cdot\tfrac{11}8\cdot\tfrac38=\tfrac{243}{128}kh_1h_2\).)
  The exponents \(\bigl(\tfrac54,\tfrac{11}8,\tfrac32\bigr)\) lie in
  \(E\) and are pairwise distinct. If \(w=0\), drop the third term
  and apply Lemma 3.8 (or Lemma 3.3 if only one of \(a,b\) is
  present). In all cases the perturbation satisfies the
  \(\rho_0(E)\) bounds of Lemma 3.8/3.9 for \(P\ge P_0\): each
  relative error is \(O(P^{-1/4})\), and
  \(\lvert\tfrac12 c''\rvert/B_{\mathrm{lead}}=O(P^{-1/4})\)
  whenever \(kh_1h_2\ge1\). The scale is
  \[
  S
  =\max\bigl(\lvert uh_1+u'h_2\rvert P^{-3/4},\,
  kh_1h_2P^{-5/8},\,\lvert w\rvert P^{-1/2}\bigr),
  \]
  and the middle-band constraints give
  \(1.0P^{-5/8}\le S\le300\,P^{-1/2}\): the lower bound is the
  anchor when \(kh_1h_2\ge1\), and the upper bound uses
  \(kh_1h_2\le P^{1/8}\) from (C1) together with
  \(\mu\le60\lambda_0\le300\,kh_1h_2P^{-5/8}\) and the
  collision-band restriction
  \(\lvert wX''\rvert\ll P^{-1/2}\).

  *Splitting.* Choose \(V:=3S^{1/2}P^{-11/24}\), so that
  \(V/S\le6.7P^{-7/48}\) (hence \(V\le c_7S/2\) at
  \(c_7=1/288\) for \(P\ge P_0\)) and
  \(V\ge1.35P^{-37/48}\ge10\,|f''-\Lambda|\) against the
  two-term interpolant majorant. The comparison
  \(V\le c_7S/2\) is the large ineffective threshold of the
  standing estimates: until it holds, a three-term zero of
  \(\Phi''\) can keep \(\Omega_V\) of length \(\Theta(P)\) on a
  dyadic block. The length bound below is that of Lemma 3.9,
  not a claim that the sublevel is short at small \(P\);
  interval counts remain \(O_E(1)\). By Lemma 3.9 the set
  \(\Omega=\{\nu:|\Lambda(\nu)|\le V\}\) is a union of at most
  \(C(E)\) intervals of total length
  \(\le C(E)\,P(V/S)^{1/2}\le2.6\,C(E)\,P^{89/96}\), and on its
  complement \(f''\) is single-signed per interval with
  \(0.9V\le|f''|\le1.1\,C(E)S\). The three costs:
  \[
  \text{transition (trivial):}\quad\le2.6\,C(E)\,P^{89/96};
  \]
  \[
  \text{piece boundaries:}\quad
  \le(N{+}C(E))\,(0.9V)^{-1/2}
  \le3.5P^{13/24}\cdot0.91P^{37/96}+O_E(P^{37/96})
  \le3.2\,P^{89/96};
  \]
  \[
  \text{good pieces (Lemma 3.3):}\quad
  \sum\ell\,(1.1\,C(E)S)^{1/2}
  \le C'(E)\,P\cdot(300)^{1/2}P^{-1/4}
  \le18\,C'(E)\,P^{3/4}.
  \]
  The middle band therefore totals
  \(\le C(E)\,P^{89/96}\log P\le P^{15/16}\) for \(P\ge P_0\).

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

## 6. Application: depth four complete, and the length-five contractors

**Theorem 6.1 (the OOO\* splits; depth four complete over odd starts).**
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
costs \(\le2\pi kP^{-1/8}\cdot P\le7P^{7/8}\)): the fourth-letter
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
\(kh_1h_2\le2P^{1/96+1/48+1/24}\le P^{1/8}\), so (C1)–(C3) hold) to
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
change the two composites of Step 5 of Theorem 5.3, and both are
recomputed here from the smooth model of the *total* phase — the
model in which every frozen integer is replaced by its interpolant,
as in Step 5b there; each unit deviation of a frozen integer
perturbs the curvatures below by \(\le Ck\nu^{-13/8}\), a relative
\(O(P^{-1})\).

*Offset branches (\(j\ne0\)).* The model offset content is
\(\tfrac k2\,j\,\partial_m\bigl(m^{9/4}\bigr)
=\tfrac{9k}8\,j\,m^{5/4}\), i.e. the smooth phase
\(\tfrac98kj\nu^{15/8}\) with curvature
\(\tfrac{945}{512}kj\nu^{-1/8}\) — the same as in Theorem 5.3 —
*but* the total \(\theta\)-coefficient is now
\(B=\tfrac k2\,j\,\partial_m\partial_\theta\)-content
\(=-\tfrac{9k}8j\cdot\tfrac54m^{1/4}
=-\tfrac{45}{32}\,kj\,\nu^{3/8}\,(1+O(P^{-1/4}))\),
two and a half times the bare-kernel value \(\tfrac9{16}kj\nu^{3/8}\).
The window-centre mode therefore carries
\(u_0X''=-\tfrac{45}{32}\cdot\tfrac34\,kj\,\nu^{-1/8}
=-\tfrac{135}{128}\,kj\,\nu^{-1/8}\), and the composite is
\[
\Bigl(\tfrac{945}{512}-\tfrac{540}{512}\Bigr)kj\,\nu^{-1/8}
=\tfrac{405}{512}\,kj\,\nu^{-1/8},
\qquad\text{ratio }945:540=7:4,
\]
single-signed with
\(\lambda_a'\in[0.72,\,0.80]\,k|j|P^{-1/8}(1+O(P^{-1/8}))\). The
competitors of Step 5a, now read against
\(\lambda_a'\ge0.72\,k|j|P^{-1/8}\ge0.72P^{-1/8}\), remain dominated:
differenced-wave modes
\(\le0.84\,uh_1P^{-3/4}\le0.51P^{-1/4}\), ratio
\(\le0.71P^{-1/8}\); resonant (D1) content, ratio
\(\le7P^{-9/16}\); slow modes
\(\le3J_2|j|P^{-5/4}\), ratio
\(\le5P^{1/24-5/4+1/8}=5P^{-13/12}\); (D3) content, ratio
\(\le4h_1h_2P^{-1/2}\le P^{-1/4}\). The window count grows by
\(\tfrac{45/32}{9/16}=2.5\), so at most
\(3.0\,k|j|P^{3/8}+1\) windows; the collision-band Lemma 3.8 sum
is then \(\le4.0\,(k|j|)^{1/2}P^{15/16}\log P\). Run lengths are
unchanged, and
\[
\sum_{\mathrm{runs}}\bigl(\ell\lambda_a'^{1/2}+\lambda_a'^{-1/2}\bigr)
\le1.7\,(k|j|)^{1/2}P^{15/16}
+26\,(|j|{+}1)|j|^{-1/2}k^{-1/2}P^{13/16}.
\]
Summed over the eight branches and \(\lvert j\rvert\le3\) with the
\(O(\log^3P)\) piece masses:
\(\ll k^{1/2}P^{15/16+\varepsilon}\le P^{1/48}P^{15/16+\varepsilon}
=P^{23/24+\varepsilon}\) already at the kernel's \(k\le P^{1/24}\);
the actual range \(k\le2P^{1/96}\) sits strictly inside.

*Zero-offset branches (\(j=0\)).* The model \(h_1h_2\)-content of
the total differenced phase is
\(4h_1h_2\cdot\tfrac k2\,\partial_\nu^4(\nu^{27/8})(\xi)/4!\)-form;
its curvature is
\[
4h_1h_2\cdot\tfrac k2\cdot
\tfrac{27}8\cdot\tfrac{19}8\cdot\tfrac{11}8\cdot\tfrac38\,
\nu^{-5/8}
=8.27\,kh_1h_2\,\nu^{-5/8}\,(1+O(hP^{-1/2})),
\]
positive and single-signed, so
\(\lambda_0'\in[4.5,\,8.5]\,kh_1h_2P^{-5/8}\) replaces
\(\lambda_0\in[0.2,0.9]kh_1h_2P^{-5/8}\). The three-regime split of
Step 5b is read at this scale. The thresholds (factor \(60\)) are
scale-free. In the anchor-dominant regime, Lemma 3.3 per run gives
\(\le4.0(kh_1h_2)^{1/2}P^{11/16}
+12\,(h_1h_2/k)^{1/2}P^{9/16}\)
(the first term grows like \(\lambda_0'^{1/2}\), the second
shrinks). In the mode-dominant regime the undifferenced-anchor
decoration is the same as in Step 5b, and the \(j=0\)
\(\theta\)-coefficient remains sub-unit. In the middle band the
interpolant of Step 5b is reused with \(B_{\mathrm{lead}}\)
replaced by \(8.27\,kh_1h_2\nu^{-5/8}\): the phase is still
\(\Phi=a\nu^{5/4}+b'\nu^{11/8}+w\nu^{3/2}\) with
\(b'=8.27\cdot\tfrac{64}{33}kh_1h_2\), the \(\rho_0(E)\) bounds
are unchanged, and
\[
S
\le\max\bigl(60\lambda_0',\,\lambda_0',\,\lvert w\rvert P^{-1/2}\bigr)
\le520\,P^{-1/2}
\]
by (C1) and the collision-band restriction. The balanced choice
\(V=3S^{1/2}P^{-11/24}\) still satisfies \(V\le c_7S/2\) at
\(c_7=1/288\) and \(V\ge10\lvert f''-\Lambda\rvert\) against
the two-term interpolant majorant, for \(P\ge P_0\). Transition
length and piece-boundary costs shrink (larger \(S\) shrinks
\(V/S\) and \(V^{-1/2}\)); good pieces cost
\(\le P\cdot(520)^{1/2}P^{-1/4}\le23P^{3/4}\). The middle band
therefore remains \(\ll P^{15/16+\varepsilon}\).

The passengers of Step D are inside these estimates: the
\(\tfrac i2X\)-term is (D3) as listed; the \(\tfrac j2Y\)-term
shifts each \(q_d\) by at most \(P^{1/96}\), keeping
\(\lvert q_d\rvert\le4P^{1/24}\) and \(uh_1\le0.6P^{1/2}\); the
pure-\(m\) smooth pieces add a relative \(O(P^{-1})\) to
\(\lambda_a'\) and \(\lambda_0'\), already present in the
\(O(P^{-1/8})\) and \(O(hP^{-1/2})\) factors; the sub-unit
\(\theta\)-coefficients of those pieces are among the slow modes
already bounded.

*Step F (assembly).* With the inventory of Step D and the
composites of Step E, Steps 2–6 of Theorem 5.3 give
\(|T_2|\ll P^{23/24+\varepsilon}\) uniformly in \((i,j,k)\) on the
stated ranges, hence \(S_{ijk}\ll P^{1-1/96+\varepsilon}\). Summing
the mode weights (\(O(\log^3P)\)), the majorant costs
(\(\le4P^{1-1/96}\) per layer, three layers), and dyadic blocks
gives the theorem. \(\square\)

The four-step certified class remains \(13/16\): \(OOO*\) does not
contract (\(3^3>2^4\)). The next two contracting words are
\(OOOEE\) and \(OOEOE\) (\(3^3<2^5\)). Neither is a third growing
layer. After \(OOOE\) the fifth letter is a decaying nest plus one
slow sawtooth of coefficient \(n^{3/16}<n\); after \(OOEO\) it is
a single growing sawtooth of coefficient \(n^{9/16}<n\), of the
same species as Theorem 4.8. Theorem 6.3 counts both cylinders.

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
\le\tfrac34\,m^{-3/8}+\tfrac12\,v^{-3/4}+\tfrac9{128}\,(X-1)^{-7/8}.
\]
The last term is \(O(n^{-21/16})\); the leading remainder is
\(O(n^{-9/16})\).

(ii) *(\(OOEO*\) linearization.)*
\[
w^{3/2}
=n^{27/16}-\tfrac98 n^{3/16}\,\theta
-\tfrac32\,v^{1/4}\,\theta_w+D_5',
\]
with
\(\lvert D_5'\rvert
\le\tfrac34\,m^{-3/8}+\tfrac38(U-1)^{-1/2}\).

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
for some \(\xi\in(0,\theta)\). The two Lagrange remainders satisfy
\((Y-1)^{-5/4}\ll m^{-3/8}\) and
\((v^{3/2}-1)^{-3/2}\ll v^{-3/4}\) for \(n\ge5\), and
\((X-1)^{-7/8}\asymp n^{-21/16}\), so they are absorbed by the
displayed terms. The leftover sawtooth has coefficient
\(n^{3/16}\).

(ii) Lemma 4.3(i) at base \(U\), using
\(U\,v^{1/4}=v^{3/4}\) exactly:
\(w^{3/2}=v^{3/4}-\tfrac32 v^{1/4}\theta_w+E\) with
\(0\le E\le\tfrac38(U-1)^{-1/2}\). The chain
\(v^{3/4}\to n^{27/16}\) is the second and third steps of (i);
the \(\theta^2\) term of that chain is absorbed by
\(\tfrac34 m^{-3/8}\). Two sawtooths remain, of coefficients
\(n^{3/16}\) on \(\theta\) and \(n^{9/16}\) on \(\theta_w\).
\(\square\)

**Theorem 6.3 (the length-five splits).**
\[
\#\mathrm{OOOEE}(N),\;\#\mathrm{OOOEO}(N)
=\tfrac N{32}+O\bigl(N^{1-1/96+\varepsilon}\bigr),
\qquad
\#\mathrm{OOEOE}(N),\;\#\mathrm{OOEOO}(N)
=\tfrac N{32}+O\bigl(N^{43/48+\varepsilon}\bigr).
\]
Of these four words only \(OOOEE\) and \(OOEOE\) contract. All
estimates below are for \(P\ge P_0\), with the same ineffective
\(P_0\) as in Section 5.

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
Lemma 3.7 with \(T=P^{1/4}\) satisfies
\(T\ge8(1+\lvert C\rvert)\), since
\(8\lvert C\rvert/T\le16P^{-5/96}\to0\). The produced modes are
\(e(uX)\) with \(\lvert u\rvert\le P^{1/4}\). These are
first-letter monomials of the shape already estimated in the
proof of Lemma 5.2(i) — the families \(e(r\nu^{3/2})\) with
truncation \(R_0=P^{1/4}\) — and are not decorations of class
(D1). (The coefficient budget \(\lvert q'\rvert\le4P^{1/24}\) of
Lemma 5.2(ii) is the kernel's own \(Y\)-wave range after
differencing; it is not a slot for \(X\)-modes.)

Write \(I_{\mathrm{tot}}\) for the combined first-letter index:
Theorem 6.1's own \(\lvert i\rvert\le2P^{1/96}\) plus the
fifth-letter \(\lvert u\rvert\le P^{1/4}\). Then
\(\lvert I_{\mathrm{tot}}\rvert\le2P^{1/4}\). Theorem 6.1
Steps D–E apply at this range.

- *The \(\tfrac i2X\)-passenger.*
  \(\Delta\Delta(\tfrac i2 X)\) has second derivative
  \(\le2.3\,\lvert i\rvert h_1h_2P^{-5/2}\). At
  \(\lvert i\rvert\le2P^{1/4}\) and \(h_1h_2\le P^{1/16}\) this is
  \(O(P^{-35/16})\), inside class (D3)
  (\(\lvert\varphi''\rvert\le3kh_1h_2P^{-5/8}\)) by
  \(P^{-35/16}/P^{-9/16}=P^{-13/8}\). The fifth-letter chirp
  \(\tfrac l2 n^{27/16}\), after the same double difference, is
  likewise (D3):
  \(h_1h_2\cdot l\cdot P^{27/16-4}=O(P^{1/16+1/96-37/16})\).
- *The \(\tfrac j2Y\)-passenger.* The fifth letter does not
  enlarge \(j\) or the \(Y\)-wave frequencies. The bound
  \(\lvert q_d\rvert\le3P^{1/24}+P^{1/96}\le4P^{1/24}\) is
  unchanged.
- *The sign-critical composites.* An \(X\)-mode is smooth, so it
  does not enter the kernel \(\theta\)-coefficient \(B\). The
  offset composite \(405/512\) (ratio \(7:4\)) and the
  zero-offset curvature \(8.27\,kh_1h_2\nu^{-5/8}\) are therefore
  the values of Theorem 6.1. The (D3) curvature of the new modes
  is dominated at the ratios already displayed there
  (\(\le P^{-1/4}\) against \(\lambda_a'\ge0.72P^{-1/8}\)).
- *The Lemma 5.2(i) budget.* Modes with \(\lvert u\rvert\le P^{1/4}\)
  are a subset of the family already bounded by
  \(3R_0^{1/2}P^{3/4}\log P=3P^{7/8}\log P\). Collision-band
  mass stays \(O(\log P)\).
- *The flat cost of Lemma 3.7.* Per point
  \(8(1+\lvert C\rvert)/T=O(P^{19/96-1/4})=O(P^{-5/96})\); over
  a block \(O(P^{1-5/96})\), inside Theorem 6.1's
  \(P^{1-1/96}\) budget.

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
\(e(-C_{\mathrm{net}}\theta)\) on the same intervals, again by
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
is not a census of every \(O\)-rooted word of length five: the
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
Then the starts with no contracting prefix of length \(\le d\) number
at most
\[
e^{-cd}\,N+2^dE_d(N),
\qquad
c=2\Bigl(\tfrac{\log2}{\log3}-\tfrac12\Bigr)^2>0.0342 .
\]
Every other start \(n\ge2\) satisfies \(J^t(n)<n\) for some
\(t\le d\) with the uniform power-envelope certificate of
Proposition 3.1. Consequently, if \(E_d(N)=O_d(N^{1-\delta_d})\) with
\(\delta_d>0\) for every \(d\), the set of starts admitting a finite
descent certificate has natural density \(1\).

*Proof.* Every \(E\)-rooted word has a contracting prefix at length
one (\(3^0<2\)), so the starts with no contracting prefix of length
\(\le d\) all realize an \(O\)-rooted word of length \(d\). A word
\(w\) of length \(d\) has a contracting prefix iff
\(3^{o_t}<2^t\) for some \(t\le d\), where \(o_t\) counts odd letters
among the first \(t\). If \(w\) has no contracting prefix then
\(3^{o_d}\ge2^d\), i.e. \(o_d\ge\beta d\) with
\(\beta=\log2/\log3=0.6309\ldots\) The number of such words is at
most \(2^d\Pr[\mathrm{Bin}(d,\tfrac12)\ge\beta d]\le
2^de^{-2(\beta-1/2)^2d}\) by Hoeffding's inequality. Each such class
has at most \(2^{-d}N+E_d(N)\) members by the \(O\)-rooted
hypothesis; summing gives the count. The density-one statement
follows by letting \(d\to\infty\) slowly with \(N\) (any
\(d(N)\to\infty\) with \(2^dE_d(N)/N\to0\)). \(\square\)

Sections 4–6 prove the hypothesis at every depth \(d\le4\), so the
conclusion of Proposition 7.1 is unconditional for those depths.
Corollary 6.4 raises the certified class to density \(7/8\) without
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
coefficient \(c=\tfrac{3k}4z^{1/2}\asymp kn^{27/16}\): Lemma 5.1(i)
with \((m,v)\) replaced by \((v,z)\).

*Proof.* Taylor of \((z+\theta_3)^{3/2}\) at \(z\), with
\(Z^{3/2}=v^{9/4}\). \(\square\)

For smooth \(c\) with \(c\asymp kP^{27/16}\) and
\(c'\asymp kP^{11/16}\) on \(n\sim P\) (the \(z^{1/2}\)-shaped
family), define
\[
K_3(P)=\sum_{\substack{n\sim P\\ n\ \mathrm{odd}}}
e\bigl(c(n)\,\{\lfloor\lfloor
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
floors. The kernel weight now has \(c'\asymp kP^{11/16}\gg1\), so no
drift-1 interval exists for any expansion of the weight itself; the
branch decomposition of Lemma 5.1(iii) has no analogue at the
\(v\)-level, because \(v\) jumps by \(\asymp n^{5/4}\) per step and
the branch set is a *product* of two carry lattices, not a copy of
one; and the forced inner linearization
\(v^{3/2}=m^{9/4}-\tfrac32m^{3/4}\theta_2+E_2\) trades \(\theta_3\)
for a sawtooth family at coefficient scale \(kn^{45/16}\), *above*
the \(9/4\) threshold where every method of this paper stops.

What survives at the frontier is a model problem and one theorem
about it. Stripping every problem-specific structure (carries,
defects, nesting) from \(K_3\) leaves the *amplitude-product* sums
\[
S=\sum_{t\le L}e\bigl(A(t)\,\{B(t)\}\bigr),
\qquad
1\ll A'\ll A,
\]
with smooth monomial-type \(A,B\) (the instance above has
\(A\asymp P^{27/16}\), \(A'\asymp P^{11/16}\)). For \(A'\ll1\)
partial summation makes the amplitude a tame passenger and the
classical single-floor machinery applies; for \(A'\gg1\) we
know of no nontrivial deterministic bound by any method. What can be
proved is an \(L^2\) identity in the shift, a one-page computation
that uses no harmonic analysis:

**Proposition 7.4 (shift-averaged \(L^2\) bound).**
Let \(A_1<\cdots<A_L\) be reals with
\(|A_t-A_{t'}|\ge A'_{\min}|t-t'|\) for some \(A'_{\min}\ge1\), and
let \(x_1,\ldots,x_L\) be arbitrary reals. For
\(S_\lambda=\sum_{t\le L}e\bigl(A_t\{x_t+\lambda\}\bigr)\),
\[
\Bigl|\int_0^1|S_\lambda|^2\,d\lambda-L\Bigr|
\le\frac6\pi\,\frac L{A'_{\min}}\,(\log L+1).
\]
Consequently, for any \(\varepsilon\in(0,1)\), Markov's inequality
gives
\[
|S_\lambda|
\le\sqrt{\frac L\varepsilon
\Bigl(1+\frac6\pi\,\frac{\log L+1}{A'_{\min}}\Bigr)}
\]
outside a shift set of measure at most \(\varepsilon\). This is
square-root cancellation times \(\sqrt{\log L}\) in general, and
genuine square-root cancellation when \(A'_{\min}\gg\log L\) — which
holds in the instance above, where \(A'_{\min}\asymp P^{11/16}\).

*Proof.* Expand the square; the diagonal gives \(L\). For
\(t\ne t'\), the function
\(\varphi(\lambda)=A_t\{x_t+\lambda\}-A_{t'}\{x_{t'}+\lambda\}\) is
piecewise linear on \([0,1)\) with *real* slope \(A_t-A_{t'}\) on at
most three arcs (jumps at \(1-\{x_t\}\) and \(1-\{x_{t'}\}\)); on
each arc \(|\int e(\varphi)\,d\lambda|\le1/(\pi|A_t-A_{t'}|)\).
Summing,
\(\sum_{t\ne t'}3/(\pi A'_{\min}|t-t'|)
\le(6/\pi)(L/A'_{\min})(\log L+1)\). For the second display, the
measure of \(\{|S_\lambda|^2>T\}\) is at most
\(T^{-1}(L+(6/\pi)(L/A'_{\min})(\log L+1))\); take
\(T=(L/\varepsilon)(1+(6/\pi)(\log L+1)/A'_{\min})\). \(\square\)

Two cautions. The amplitude separation \(A'\gg1\) — the very
property that defeats every character expansion, since a Fourier
window centred at the amplitude drifts by \(A'\) harmonics per step
— is what makes the shift *average* trivial; but an average over
shifts says nothing about the single shift \(\lambda=0\), which is
the deterministic sum. Proposition 7.4 does not make the level-3
kernel "generically cancelling" in any sense that bears on
Conjecture 7.3; it only locates the conjecture's difficulty as a
specific-point problem inside a metric statement.

**Conjecture 7.5 (the pure amplitude-product model).**
\(|S|\le L^{1-\delta}\) for some \(\delta>0\), for smooth
monomial-type \(A,B\) with \(1\ll A'\ll A\) as above.

Three structural facts locate the difficulty of the
de-randomization. No second averaging variable exists: amplitude
separation forces any two sample points with \(|A(p)-A(q)|\le1\) to
coincide, and every family average available in the application
re-enters either the differenced-kernel class or the
amplitude-product class itself. The inverse theory is self-similar:
any concentration or discrepancy inverse for \(A\{B\}\bmod1\) is a
statement about \(\sum e(jA\{B\})\) — the same class with amplitude
\(jA\) — so the class is closed under its own inverse theorems and
no bootstrapping is possible. And the metric statement does not
transfer: \(|dS_\lambda/d\lambda|\le2\pi A_{\max}L\) almost
everywhere, so \(S_\lambda\) decorrelates at shift scale
\(1/A_{\max}\), and an almost-all-\(\lambda\) theorem leaves
\(\asymp\varepsilon A_{\max}\) exceptional cells among
\(\asymp A_{\max}\) — no measure argument pins \(\lambda=0\). The
deterministic content of Conjecture 7.5 is a
specific-point-in-metric-theory problem, the same species as the
normality of \(\sqrt2\): a class whose known successes all use
special arithmetic.

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
> depth four. The certified class through length five has density
> \(7/8\). The first open counting case is the \(OOOO*\) kernel of
> Conjecture 7.3, whose deterministic model instance is
> Conjecture 7.5.

![The theorem flow of the paper. The exact finite-itinerary calculus of the companion manuscript feeds the contraction certificates; the discrepancy calculus with the kernel theorem counts every O-rooted itinerary class through depth four and the two length-five contractors (certified-descent density 7/8), leaving the level-3 kernel — and with it almost-all descent — open.](figures/juggler_frontier.png){width=100%}

## 8. Software note

A repository accompanies the paper:
[https://github.com/sneakyweasel/balanced_ternary/](https://github.com/sneakyweasel/balanced_ternary/).
It is not required to read or check any proof above. It contains Lean
formalizations of the exact floor identities cited in Section 1.1 and
of the companion manuscript's finite-itinerary theorems, scaled-integer
validations of the linearization identities of Lemmas 4.3, 4.6, 5.1,
6.2, and 7.2, and exact-phase numerical probes of the sums \(K_c\),
\(K_3\), and the differenced sums of Lemma 5.2 and Theorem 5.3, all
of which exhibit cancellation at square-root scale — stronger than
the theorems claim and stronger than they need. The same companion
records scaled-integer gates for the exact identities of
Section 1.1 and the named numerical margins of Section 5
(Lemma 3.7 / Lemma 5.2 window hypotheses, the Step 5b interpolant
majorant, and the Lemma 5.2 coefficient budget). Probes and
validations are checks, not proofs, and no statement in this paper
depends on them. In particular they are not evidence for
Conjecture 7.3 or Conjecture 7.5.

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
