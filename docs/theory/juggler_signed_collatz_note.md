---
title: "The Juggler Map and the 3n±1 Maps"
subtitle: "Exact Coding and Arithmetic Obstructions"
author: Philippe Cochin
date: "22 September 2026 · Version 0.2.0"
---

## Abstract

The Juggler map and the shortcut \(3n+1\) and \(3n-1\) maps share the
word multiplier \(3^o/2^L\), but realize their words in different arithmetic
and metric spaces. Classical parity coding defines an exact map from every
Juggler orbit into the 2-adic \(3n-1\) system. On actual periodic Juggler
orbits it preserves every return time, and its value is an ordinary integer
exactly when an explicit word divisibility holds. A family of genuine
Juggler prefixes shows that arbitrarily precise modular return does not
force that divisibility. On the positive integers, we prove that every
\(3n-1\) target prime to three has at least \(X^{21/25}\) ancestors below
\(X\), for all sufficiently large \(X\). This signed adaptation uses
height-corrected inverse-tree inequalities, a closed root domain, and an
exact integer certificate with 177147 rows. A mean inequality places every
positive certificate in the fixed \(1/50\) grid, for either sign and at
every finite residue level, strictly below exponent \(0.99\) in the
at-most-linear range. Lean formalizations accompany the orbit, period,
counting, and grid-ceiling results. The modular-return theorem has a
written proof using classical equidistribution. These results separate
symbolic correspondence from integer realization and reciprocal-mass
transport; no universal termination or unrestricted cycle exclusion
theorem is asserted.

**2020 Mathematics Subject Classification:** Primary 11B83; Secondary 11K31, 11Y16, 68V15.

**Keywords:** Juggler map; signed Collatz maps; 2-adic parity coding;
inverse trees; computer-assisted proof; Lean.

## 1. Introduction

We compare the maps
\[
J(n)=
\begin{cases}
\lfloor\sqrt n\rfloor,&n\ \text{even},\\
\lfloor n^{3/2}\rfloor,&n\ \text{odd},
\end{cases}
\qquad
C_\sigma(x)=
\begin{cases}
x/2,&x\ \text{even},\\
(3x+\sigma)/2,&x\ \text{odd},
\end{cases}
\quad \sigma\in\{-1,+1\}.
\]
Unless a larger domain is specified, inputs are positive integers.
Write \(g=C_{-1}\). On ordinary integers \(C_{+1}(-x)=-g(x)\);
positive \(3n-1\) orbits correspond to negative \(3n+1\) orbits,
not to positive \(3n+1\) orbits.

Along a prescribed branch word, the leading Collatz multiplier acts on
\(x\), whereas the leading Juggler multiplier acts on \(\log n\).
The same letters generate the same formal walk one logarithm apart.
Turning this observation into a statement about integer trajectories
requires additional information. This paper asks which information
survives the correspondence.

Sections 2 and 3 construct the exact code and prove period preservation.
Section 4 exhibits actual modular returns whose associated periodic-word
codes are nonintegral. Section 5 proves a signed ancestor-count theorem,
including the height correction that prevents an automatic transfer of
the positive-map proof. Section 6 proves a limitation of the fixed grid
used in that argument. Section 7 distinguishes counting from reciprocal
mass and bounded word identities from unbounded stopping identities.

### 1.1. Contributions and prior work

Terras [T76] supplies the classical parity-vector bijection and
stopping-word combinatorics. Bernstein and Lagarias [BL96] supply the
2-adic inverse parity map, including the signed affine family. We use
that construction, rather than claim a new coding mechanism. Prasad and
Prasad [PP25] discuss the leading-word approximation for Juggler-like
sequences. The shared multiplier and the word counts are background.

The Juggler-specific refinement in Section 3 is preservation of every
return time on an actual periodic orbit. Its proof combines classical
coding with monotonicity within each branch. The integrality criterion
is the classical affine cycle equation stated alongside this refinement.
Section 4 gives a quantified obstruction involving actual floor
iterates, rather than unrestricted symbolic words.

Krasikov and Lagarias [KL03, Theorem 6.1] prove an ancestor exponent
\(0.84\) for every positive target prime to three under \(C_{+1}\).
Their theorem is not a statement about positive \(g\)-targets. Our
Section 5 proves the latter statement by a strict-grid construction.
The \(1/50\) cap table and induction measure follow M. Sharpe's formal
implementation [S26], with attribution and its MIT notice retained in
the source. The signed height estimates, the domain for arbitrary
positive unit targets, and the independently generated certificate are
supplied here. We claim neither priority for the grid method nor a
larger positive-map exponent.

Section 6 isolates a common mean obstruction for this fixed grid at
every finite residue level. This is a limitation of those certificate
inequalities, not a bound on actual ancestor growth.

The companion papers [A], [B], [C], and [D] treat Juggler cycle bounds,
finite-depth descent statistics, fate contagion, and bounded-run
\(3n-1\) cycles. We cite their results without reissuing their proofs.
The present main theorems require neither their large computational
floors nor the analytic estimates in [B].

### 1.2. Proof status

This is the living preprint, version 0.2.0. It has not been
deposited or independently refereed. Mathematical priority for the
signed adaptation and the isolated obstruction results remains subject
to specialist review.

Theorems 2.1, 3.2, 5.1, and 6.1 have corresponding compiled Lean
statements; Appendix B identifies their precise scope. Theorem 4.1
uses a written equidistribution argument and is not covered by that
formalization. The finite certificate is checked with exact integers
both in Lean and by an independent Python verifier. The numerical
search that found its weights is outside the proof. Kernel checking,
agreement between prose and formal statements, and independent
mathematical review are distinct checks.

## 2. Words and the exact orbit code

For \(w=(b_0,\ldots,b_{L-1})\in\{0,1\}^L\), with \(0\) denoting E
and \(1\) denoting O, write \(o(w)=\sum_i b_i\) and
\[
\rho(w)=\frac{3^{o(w)}}{2^L},\qquad
A(w)=\sum_{i=0}^{L-1}b_i2^i3^{\sum_{j>i}b_j}.
\tag{2.1}
\]
Induction on the prescribed affine branches gives
\[
2^L C_{\sigma,w}(x)=3^{o(w)}x+\sigma A(w).
\tag{2.2}
\]
This describes an actual orbit only when all branch guards hold.
For an actual Juggler itinerary \(w\) starting at \(n\), the inequalities
\(J(n)^2\le n\) on E and \(J(n)^2\le n^3\) on O give
\[
\bigl(J^L(n)\bigr)^{2^L}\le n^{3^{o(w)}}.
\tag{2.3}
\]
Thus a contracting prefix forces descent for \(n>1\). For positive
\(3n+1\), the nonnegative correction in (2.2) instead prevents descent
along a prefix with \(\rho\ge1\). Shared combinatorics does not remove
this sign difference.

Let \(d_0<d_1<\cdots\) be the odd times of the Juggler orbit of \(n\),
finite or infinite, and define
\[
H(n)=\sum_j\frac{2^{d_j}}{3^{j+1}}\quad\text{in }\mathbb Z_2.
\tag{2.4}
\]
An empty sum is zero. The summands' valuations tend to infinity, so
the sum converges 2-adically. Both \(C_\sigma\) extend to \(\mathbb Z_2\),
using the residue modulo two to select the branch. Formula (2.4) is
a specialization of the inverse parity map of [BL96].

**Theorem 2.1 (exact signed orbit code).** For every positive integer \(n\),
\[
H(n)\equiv n\pmod2,\qquad
H(J(n))=g(H(n)),\qquad
-H(J(n))=C_{+1}(-H(n)).
\tag{2.5}
\]
Two starts have equal codes if and only if all their finite Juggler
parity itineraries agree. On every finite source set, counting a
prescribed length-\(d\) itinerary is exactly counting its associated
code residue modulo \(2^d\).

*Proof.* Deleting an even first letter gives \(H(n)=2H(J(n))\).
Deleting an odd first letter gives
\(H(n)=1/3+(2/3)H(J(n))\). These identities give parity and the
minus-step identity. Negation gives the plus-step identity. Iterate.
The classical parity bijection identifies length-\(d\) words with
residues modulo \(2^d\). Equality of codes therefore gives equality
of every prefix; conversely, equality of all residues gives equality
in \(\mathbb Z_2\). The finite-set assertion is equality of its
membership conditions. \(\square\)

The formal construction takes compatible finite residues and their
2-adic limit. Its equality with (2.4) is proved by a telescoping sum
whose remainder after time \(k\) has 2-adic norm at most \(2^{-k}\).
The formal odd-time index uses the number of earlier odd times as \(j\);
finite and empty odd-time families are included. This assumes neither
termination nor 2-adic continuity of Juggler on its original integer inputs.

**Example 2.2 (rational values and collisions).** From \(H(1)=1\),
following \(3,5,11,36,6,2,1\) backwards gives
\[
\begin{array}{c|rrrrrrr}
n&3&5&11&36&6&2&1\\ \hline
H(n)&83/27&37/9&17/3&8&4&2&1.
\end{array}
\]
Also \(H(4)=H(6)=4\). Thus the code neither takes every positive
integer to an ordinary integer nor is injective. Every terminating
start has a positive rational code whose reduced denominator divides
a power of three, by backwards application of \(q\mapsto2q\) and
\(q\mapsto(2q+1)/3\) from \(1\).

**Corollary 2.3 (the distribution question is unchanged).** Frequencies
\(2^{-d}\) for all length-\(d\) Juggler words, for every fixed \(d\),
are equivalent to
\[
\lim_{N\to\infty}\frac1N
\#\{1\le n\le N:H(n)\equiv r\pmod{2^d}\}=2^{-d}
\]
for every \(d\) and code residue \(r\). This equivalence proves
neither condition. The formal statement transfers limits using exact
equality of the finite-source counts.

## 3. Actual periods and ordinary integrality

**Lemma 3.1 (order within a code fibre).** If \(H(n)=H(m)\) and
\(n\le m\), then \(J^k(n)\le J^k(m)\) for every \(k\ge0\).

*Proof.* Equal codes imply equal parity at each time. Each branch
function is nondecreasing. Induction applies the same branch to
the two current values. \(\square\)

**Theorem 3.2 (period preservation and integrality).** Suppose
\(J^L(n)=n\) with \(L>0\), and let \(w\) be that actual itinerary.
Put \(D=3^{o(w)}-2^L\). Then \(D\ne0\), and:

1. \(H(n)=A(w)/D\) in the 2-adic field.
2. For every \(d\ge0\), \(g^d(H(n))=H(n)\) if and only if \(J^d(n)=n\).
   The analogous statement holds for \(C_{+1}\) at \(-H(n)\).
3. The least periods of these three points are equal.
4. \(H(n)\) is an embedded ordinary integer exactly when \(D\mid A(w)\).
   In that case its ordinary signed Collatz orbit has the same
   return times as the Juggler orbit.

*Proof.* Iteration of (2.5) gives
\[
3^{o(w)}H(n)=2^LH(J^L(n))+A(w).
\]
The odd integer \(D\) is nonzero and invertible in \(\mathbb Z_2\).
Closing the orbit gives the formula.

One implication about return times is (2.5). Conversely, if the
code returns after \(d\) steps, \(J^d\) preserves its fibre and
is nondecreasing there by Lemma 3.1. If \(J^d(n)>n\), every
subsequent application stays strictly above \(n\); if \(J^d(n)<n\),
every subsequent application stays strictly below \(n\).
Both contradict \((J^d)^L(n)=n\). Hence \(J^d(n)=n\).
Equality of return times gives equality of least periods.

Finally \(A/D\) is an ordinary integer exactly when \(D\mid A\).
Injectivity of the rational embedding into the 2-adic field makes
this necessary as well as sufficient. The integer maps agree with
their 2-adic extensions on embedded integers. \(\square\)

The periodicity assumption on the Juggler start is essential. A
periodic code alone has not been shown to imply a periodic start.
For a nontrivial Juggler cycle, \(D>0\) by strict power-envelope
expansion [A]. Its code is a positive rational \(g\)-periodic point,
and its negative is a negative \(C_{+1}\)-periodic point.
No result here establishes \(D\mid A(w)\) for such a cycle.

## 4. Modular return does not force integrality

**Theorem 4.1 (actual modular returns with large code denominator).**
Fix \(a,b\ge1\) with \(3^a>2^{a+b}\). For every integer \(M\ge1\)
and lower bound \(B\), infinitely many odd \(n>B\) have actual
itinerary \(O^aE^b\), with
\[
J^j(n)\ge n\ (0\le j\le a+b),\qquad J^{a+b}(n)>n,\qquad
J^{a+b}(n)\equiv n\equiv1\pmod{2M}.
\tag{4.1}
\]
The rational periodic code associated with this word has denominator
\[
q_{a,b}=\frac{3^a-2^{a+b}}{\gcd(3^a-2^a,\,2^b-1)}.
\tag{4.2}
\]
These denominators are unbounded at fixed \(b\). In particular \(M\)
may be any fixed power of \(q_{a,b}\).

*Proof.* Put \(s=1+2Mt\), \(n=s^{2^{a-1}}\), and
\(\beta=3^a/2^{b+1}\). The first \(a-1\) odd steps are exact:
\[
J^i(n)=s^{3^i2^{a-1-i}}\quad(0\le i<a).
\]
The next value is \(y_0=\lfloor s^{3^a/2}\rfloor\). Whenever the
subsequent sources are even, their values are
\(y_j=\lfloor s^{2^{b-j}\beta}\rfloor\), \(0\le j\le b\).
Nested square-root floors are exact, since
\(\lfloor\sqrt{\lfloor x\rfloor}\rfloor=\lfloor\sqrt x\rfloor\).

As \(t\) varies, the vector
\[
\left(\frac{s^\beta}{2M},\frac{s^{2\beta}}2,
\frac{s^{4\beta}}2,\ldots,\frac{s^{2^b\beta}}2\right)\pmod1
\tag{4.3}
\]
is uniformly distributed. Every nonzero integer linear combination
has a nonintegral leading exponent: all exponents have odd numerator
and denominator divisible by two. It is a Hardy-field function of
polynomial growth, and its distance from any rational polynomial,
divided by \(\log t\), tends to infinity. Boshernitzan's criterion
[Bo94, Theorem 1.3], also stated in [R26, Theorem 1.1], applies.
Weyl's criterion gives joint distribution.

Place the first coordinate's fractional part in
\([1/(2M),2/(2M))\), and the others in \([0,1/2)\).
The box has volume \(1/(2^{b+1}M)\). It enforces
\(y_b\equiv1\pmod{2M}\) and even \(y_0,\ldots,y_{b-1}\),
so the word is actual. Since \(\beta>2^{a-1}\), its endpoint
exceeds \(n\) for sufficiently large \(s\). The odd portion
increases and the even portion decreases to that endpoint,
proving (4.1).

For \(O^aE^b\), (2.1) gives \(A=3^a-2^a\) and
\(D=3^a-2^{a+b}\). The oddness of \(A\) gives
\(\gcd(A,D)=\gcd(A,2^b-1)\), proving (4.2).
The quotient is at least \((3^a-2^{a+b})/(2^b-1)\), which
tends to infinity with \(a\) at fixed \(b\). \(\square\)

The theorem concerns growing prefixes and their associated
*periodic-word* codes. It does not identify that code with \(H(n)\),
which depends on the entire subsequent itinerary. It gives no
common start at all precisions, no actual nontrivial cycle, and
no denominator bound for true Juggler cycles. Finite modular return
is not exact orbit closure.

## 5. A signed ancestor-count theorem

Define
\[
\pi^-_a(X)=\#\{1\le n\le X:\exists j\ge0,\ g^j(n)=a\}.
\]
Let \(N(a,X)\) additionally require \(g^i(n)\le X\) for every
\(0\le i\le j\). Then \(N(a,X)\le\pi^-_a(X)\); both counts
are nondecreasing in \(X\). They count starts, not paths.

**Theorem 5.1 (positive \(3n-1\) ancestors).** For every positive
integer \(a\) with \(3\nmid a\), there is \(X_0(a)\) such that,
for every integer \(X\ge X_0(a)\),
\[
X^{21}\le N(a,X)^{25}\le\bigl(\pi^-_a(X)\bigr)^{25}.
\tag{5.1}
\]
In particular \(\pi^-_a(X)\ge X^{21/25}\).

### 5.1. Why height changes with the sign

A fertile \(g\)-target has \(a\equiv1\pmod3\) and odd predecessor
\(b=(2a+1)/3>2a/3\). For \(C_{+1}\), the odd predecessor at
\(a\equiv2\pmod3\) is \((2a-1)/3<2a/3\). The homogeneous
child budget \((X/a)(3/2)b\) therefore exceeds \(X\) on the
minus side. For \(a=19\), \(b=13\), \(X=103\), the nominal
budget is \(4017/38>105\), admitting \(104,52,26,13\) even
though its start already exceeds the actual cutoff.

### 5.2. Valid grid recurrences

Let \(r_0,\ldots,r_{49}\) be the integer table in Appendix A and set
\[
C(t)=2^{\lfloor t/50\rfloor}r_{t\bmod50},\qquad
F_a(t)=N(a,C(t)a).
\]
Thus \(C(t+100)=4C(t)\) and \(C(50j)=10000\,2^j\).
Integer checks on the fifty residues of \(t\) give
\[
8193C(t+29)\le12288C(t),\qquad
16386C(t)\le12288C(t+21).
\tag{5.2}
\]
If \(a\ge4096\) and \(3b=2a+1\), then
\(12288b\le8193a\). Combining these inequalities puts every
selected child cutoff below its parent cutoff.

**Lemma 5.2 (actual inverse trees).** If \(a\ge4096\),
\(a\equiv1\pmod3\), and \(a\) is nonperiodic, then
\[
\begin{aligned}
F_a(t+100)&\ge F_{4a}(t),\\
F_a(t+100)&\ge F_{4a}(t)+F_b(t+129),\\
F_a(t+100)&\ge F_{4a}(t)+F_{2b}(t+79).
\end{aligned}
\tag{5.3}
\]
The first inequality needs neither nonperiodicity nor the threshold.

*Proof.* The child paths are \(4a,2a,a\), \(b,a\), and \(2b,b,a\).
The cutoff comparisons permit extension to \(a\).
The \(4a\) subtree is disjoint from each alternative odd subtree.
Otherwise a common start reaches the nonperiodic root at two
different times, or the last steps force odd \(b\) to equal
even \(2a\). A nonperiodic root has a unique hitting time:
two times would give it a positive return. Thus the indicated
cardinalities add. \(\square\)

Use the second recurrence at \(a\equiv1\pmod9\), the third
at \(a\equiv7\pmod9\), and only the first at \(a\equiv4\pmod9\).
These choices keep children in residue \(1\pmod3\).
The two odd alternatives are never added together.

Set \(\mathcal M(t,a)=10t+\lfloor\log_2(a^{498})\rfloor\).
The exact inequality
\[
2^{291}8193^{498}<12288^{498}
\tag{5.4}
\]
forces the odd child's root-size term to fall by at least 291.
Doubling or quadrupling adds exactly 498 or 996. Therefore
\[
\begin{aligned}
\mathcal M(t,4a)+4&\le\mathcal M(t+100,a),\\
\mathcal M(t+79,2b)+3&\le\mathcal M(t+100,a),\\
\mathcal M(t+129,b)+1&\le\mathcal M(t+100,a).
\end{aligned}
\tag{5.5}
\]
Even the advanced-index call decreases this natural-number measure.

### 5.3. A closed domain for arbitrary targets

**Lemma 5.3 (root domain).** Every positive target \(a\) prime to
three has a nonperiodic ancestor \(r>2^{19}\) with \(r\equiv1\pmod3\).
All fertile ancestors of \(r\) are at least 4096 and form a domain
closed under the selected productions in (5.3). For all sufficiently
large \(X\), \(N(r,X)\le N(a,X)\).

*Proof.* At most three doublings reach a value \(z\equiv1\) or
\(7\pmod9\). Its two predecessors \(2z\) and \((2z+1)/3\)
are distinct, positive, and prime to three. They cannot both
be periodic, since a deterministic map is injective on its
periodic points. Select a nonperiodic predecessor, double
once if necessary to reach residue 1 modulo three, then
multiply by \(2^{20}\). This gives \(r\) as required.
Ancestors of nonperiodic points are nonperiodic.

The finite barrier used here is
\[
0\le u<4096\quad\Longrightarrow\quad
g^k(u)<2^{19}\quad(k\ge0),
\tag{5.6}
\]
where \(g(0)=0\). A finite descent certificate and strong induction
prove it: each start reaches a smaller value or the explicit
forward-invariant set of zero and the fifteen members of the
three known positive cycles. Appendix A specifies an independent
finite check. No exhaustiveness of the known cycles is assumed.
An ancestor below 4096 could not reach \(r>2^{19}\), by (5.6).
The residue calculations after (5.3) give closure. Above the
maximum on the fixed path from \(r\) to \(a\), every capped
path to \(r\) extends to a capped path to \(a\). \(\square\)

A threshold alone is insufficient: 4096 has odd predecessor 2731.
Restricting to ancestors of \(r\) repairs that boundary.

### 5.4. Certificate and growth induction

Take \(p=5059\), \(q=5000\), \(C_{\max}=10^{12}\), \(\mu=p/q\).
The certificate has a positive integer weight \(c_m\) for each
of the \(3^{11}=177147\) fertile classes modulo \(3^{12}\).
Its minimum is 7307142888 and its maximum is \(C_{\max}\).
For a child class modulo \(3^{11}\), let \(\bar c\) be the
minimum over its three lifts modulo \(3^{12}\).
Every row satisfies the exact integer inequality
\[
\begin{aligned}
c_m p^{100}&\le c_{4m}q^{100}
&& (m\equiv4\pmod9),\\
c_m p^{100}&\le c_{4m}q^{100}
 +\bar c_{(4m+2)/3}p^{79}q^{21}
&& (m\equiv7\pmod9),\\
c_m p^{100}q^{29}&\le c_{4m}q^{129}
 +\bar c_{(2m+1)/3}p^{129}
&& (m\equiv1\pmod9).
\end{aligned}
\tag{5.7}
\]
Indices are reduced at the indicated moduli. A minimum ensures
validity for the actual child's lift, irrespective of root size.

**Lemma 5.4 (growth).** Throughout the domain of Lemma 5.3,
\[
F_a(t)\ge\frac{c_a}{C_{\max}}\mu^{t-100}\quad(t\ge0).
\tag{5.8}
\]

*Proof.* Induct on \(\mathcal M(t,a)\). For \(t<100\) the root
itself is counted and the right side is at most one. For
\(t=s+100\), use (5.3), the decreases (5.5), and the inductive
bounds. The three cases reduce exactly to (5.7) after division
by the appropriate positive powers of \(p,q\).
The minimum weight does not exceed the actual child's weight.
Equivalently the induction uses only integers:
\(c_ap^tq^{100}\le F_a(t)C_{\max}q^tp^{100}\). \(\square\)

*Proof of Theorem 5.1.* Apply (5.8) at \(r\) and \(t=50j\).
For all sufficiently large \(j\), Lemma 5.3 gives
\[
N(a,10000r\,2^j)\ge K\mu^{50j}
\]
with fixed \(K>0\). Exact integer comparison gives
\[
2^{21}5000^{1250}<5059^{1250},
\tag{5.9}
\]
so \(\mu^{50}>2^{21/25}\). For
\(10000r\,2^j\le X<10000r\,2^{j+1}\), monotonicity gives
the same lower bound at \(X\). The strict exponential advantage
eventually absorbs \(K\) and the fixed interpolation factor.
Raise to the twenty-fifth power to obtain (5.1). \(\square\)

This is a lower bound on ancestors, not positive natural density
or a conclusion about every orbit. No classification of all
positive \(3n-1\) cycles enters its proof.

## 6. A common ceiling for the fixed grid

Keep shifts \(100,79,129\) fixed, but allow any finite residue
level \(\ell\ge2\). Put \(M=3^{\ell-2}\) and take positive
weights \(c_0,\ldots,c_{3M-1}\). For minus use representatives
\(3i+1\); for plus use \(3i+2\).
The normalized minus rows are (5.7) with rate \(\mu>0\);
their coefficients are \(\mu^{-100},\mu^{-21},\mu^{29}\).
For plus the odd children are \((4m-2)/3\) at
\(m\equiv2\pmod9\) and \((2m-1)/3\) at
\(m\equiv8\pmod9\); the sterile parent is \(m\equiv5\pmod9\).
The same coefficients define its rows.

**Theorem 6.1 (fixed-grid ceiling for both signs).** If the rows
hold for either sign at any finite level, and
\(0<\mu\) with \(\mu^{50}\le2\), then
\[
\mu<5069/5000,\qquad \mu^{5000}<2^{99}.
\tag{6.1}
\]
Thus \(\gamma=50\log_2\mu<99/100\). In particular
the harmonic rate \(\mu^{50}=2\) is impossible.

*Proof.* Put
\[
S=\sum_{i=0}^{3M-1}c_i,\qquad
B=\sum_{j=0}^{M-1}\min(c_j,c_{j+M},c_{j+2M}).
\]
Then \(3B\le S\). The fourfold-parent index maps are
\(i\mapsto4i+1\) for minus and \(i\mapsto4i+2\) for plus,
modulo \(3M\). The odd-child maps modulo \(M\) are
\(j\mapsto2j,\ j\mapsto4j+3\) for minus, and
\(j\mapsto2j+1,\ j\mapsto4j\) for plus.
All are permutations. Summing the rows gives
\(S\le\mu^{-100}S+(\mu^{29}+\mu^{-21})B\), hence
\[
1\le F(\mu):=\mu^{-100}+\frac{\mu^{29}+\mu^{-21}}3.
\tag{6.2}
\]
The function \(F\) is convex on the positive reals, as each
power has nonnegative second derivative. Exact arithmetic gives
\[
\begin{gathered}
F(5069/5000)<1,\quad F(507/500)<1,\\
(5069/5000)^{50}<2<(507/500)^{50},\\
(5069/5000)^{5000}<2^{99}.
\end{gathered}
\tag{6.3}
\]
Convexity makes \(F<1\) between the rational endpoints.
Every \(\mu\ge5069/5000\) with \(\mu^{50}\le2\) lies there,
contradicting (6.2). The last comparison proves (6.1).

At the harmonic rate, clearing (6.2) gives
\(3\mu^{100}\le3+\mu^{129}+\mu^{79}\). If
\(\mu^{50}=2\), it forces \(\mu^{79}\ge3\) and then
\(2^{79}\ge3^{50}\), contrary to \(2^{79}<3^{50}\).
\(\square\)

This obstruction reflects the fixed rounding slack
\(79/50<\log_2 3\). It applies at all finite table sizes,
but not to every finer grid, different production system,
or direct reciprocal-mass argument. It is not an upper bound
for actual ancestor counts.

## 7. Two other limits of transfer

### 7.1. Counts and reciprocal mass

**Proposition 7.1 (finite backward mass).** For either shortcut
sign, the set \(\mathcal R=\{3\cdot2^k:k\ge0\}\) is infinite
and backward-closed on the positive integers, with
\(\sum_{n\in\mathcal R}1/n=2/3\).

*Proof.* A multiple of three has no odd predecessor:
\(3u+\sigma=2m\) would imply \(\sigma\equiv0\pmod3\).
Its only predecessor is its double. Sum the geometric series
\(\frac13\sum_{k\ge0}2^{-k}\). \(\square\)

The set is not forward-closed: \(C_{+1}(3)=5\), \(g(3)=4\).
It refutes a statement for all backward-closed sets, not one
restricted to complete fate classes. Juggler's even inverse
block consists of the even integers in \([m^2,(m+1)^2)\).
Its reciprocal mass has the uniform lower bound
\(m/(m+1)^2\) used in [C]. The code preserves neither these
ordinary heights nor their reciprocal weights.

A lower bound \(N(X)\gg X^\kappa\) with \(\kappa<1\) alone
cannot force divergent reciprocal mass. For example the
distinct integers \(\lfloor j^{1/\kappa}\rfloor\) have
count at least \(\lfloor X^\kappa\rfloor\) and convergent
reciprocal sum. Theorem 5.1 therefore supplies no missing
harmonic estimate for a fate-class argument.

### 7.2. Stopping a word family

At fixed depth, fair words satisfy
\[
\sum_{|w|=d}2^{-d}=1,\qquad
\sum_{|w|=d}2^{-d}\rho(w)
=\left(\frac12\frac12+\frac12\frac32\right)^d=1.
\tag{7.1}
\]
Both identities persist for bounded complete prefix trees.
The formal statement represents these as finite binary trees with
both children at every internal node, and sums over their leaf words.
Completeness alone does not suffice at unbounded depth.

**Proposition 7.2 (moment loss at unbounded stopping).** Let
\(\mathcal C\) consist of the minimal words whose multiplier
first becomes less than one. It is prefix-free, and
\[
\sum_{w\in\mathcal C}2^{-|w|}=1,\qquad
\sum_{w\in\mathcal C}2^{-|w|}\rho(w)\le3/4.
\tag{7.2}
\]

*Proof.* The fair log-multiplier walk has mean increment
\(\frac12\log(3/4)<0\). The strong law makes its first
strictly negative time finite almost surely. Its minimal
stopping prefixes partition this probability-one event.
Every stopped multiplier is less than one; E alone has mass
\(1/2\) and multiplier \(1/2\), losing \(1/4\) relative to
fair mass. The other terms cannot restore it. \(\square\)

The Lean proof instead uses the established survivor-count
decay for completeness. It then regroups the nonnegative sums by word
length to prove (7.2) directly on the type of minimal certificate words. The
probabilistic proof explains the missing moment without
invoking an optional-stopping equality.

## 8. What remains open

Integer transport on an actual Juggler cycle requires
\(D\mid A(w)\), or a useful restriction on its reduced
denominator. Distribution of Juggler words requires estimates
of integer-source multiplicities in code cylinders. Transport
of fate contagion requires control of ordinary reciprocal
mass. Existence of the exact code supplies none of these
additional estimates.

The signed ancestor theorem leaves universal termination and
the classification of all cycles open. Its grid ceiling is
a restriction of the stated certificate family. The finite-mass
ray does not settle harmonic divergence for a full fate class.

Future versions may add results with their hypotheses, proof
status, prior-art comparison, and reproducibility record.
The companion papers retain their own claims and histories.

## Acknowledgments and use of AI

The author thanks the authors of the cited work and the Lean
and Mathlib communities for the mathematical and formal
infrastructure. M. Sharpe's grid implementation is specifically
acknowledged in Section 1.1 and the attributed source modules.

AI assistance was used in mathematical exploration, drafting,
programming, and formalization. The author is responsible for
the manuscript and its claims. Kernel-checked results are
identified individually; AI assistance and local checking
do not replace independent mathematical review.

## Availability and versioning

The project is maintained at
[github.com/sneakyweasel/btlab](https://github.com/sneakyweasel/btlab).
The canonical source is `docs/theory/juggler_signed_collatz_note.md`.
Build with the command given in Appendix A; the update and
validation guide is `docs/theory/PAPER_E_BUILD.md`.
The release manifest records SHA-256 hashes of the manuscript,
mathematical dependencies, build tools, and outputs. This
edition makes no claim of an existing external deposit.

The manuscript uses CC BY 4.0. Software retains its repository
license and third-party notices; reused grid material retains
M. Sharpe's MIT notice. The local deposit kit contains the PDF
and a source-and-certificate archive, so finite proof data need
not be recovered from a moving repository branch.

## Appendix A. Finite data and reproduction

The cap table is indexed from zero:

~~~text
10000 10140 10281 10425 10570 10718 10867 11019 11173 11329
11487 11647 11810 11975 12142 12311 12483 12658 12834 13013
13195 13379 13566 13755 13947 14142 14340 14540 14743 14948
15157 15369 15583 15801 16021 16245 16472 16702 16935 17171
17411 17654 17901 18150 18404 18661 18921 19185 19453 19725
~~~

The full table is stored in
`data/research/juggler/negative_preimage_density/grid_k12_certificate.json`.
Its ordering is \(m=3i+1\), \(0\le i<177147\).
For each row compute \(4m\bmod3^{12}\), and, when needed,
the odd child modulo \(3^{11}\). Read the minimum over its
three lifts, then check (5.7) with integers. Recorded
floating-point diagnostics are ignored.

The weights were found by damped iteration of the positive
production operator from all ones, normalizing the maximum
and rounding at scale \(10^{12}\). The first successful
table occurred after 62 iterations. Any table passing the
exact checks would suffice; its discovery is outside the proof.

For an independent check of (5.6), start from all integers
below 4096 and repeatedly add successors until no new state
occurs. The closure of the positive starts has 6417 states
and maximum 417718, below \(2^{19}=524288\); zero is fixed
and can be added separately. The verifier checks closure
and the strict barrier.

~~~text
python tools/check_paper_e.py
python tools/generate_signed_grid_certificate.py --check
python tools/build_paper_e.py
python tools/build_paper_e.py --check
cd formal
lake build Problems.JugglerCollatzPaper
lake env lean AxiomCheckJugglerCollatzPaper.lean
~~~

The first command checks the integer certificate, grid,
barrier, rational examples, modular-return witnesses, and
exact comparisons (5.4), (5.9), and (6.3), together with
the manuscript's numbered references and declaration inventory.
These finite checks do not prove Theorem 4.1's infinite
equidistribution assertion. The second command verifies the
five generated Lean certificate modules against the data.

## Appendix B. Formalization and review boundary

The paper barrel is Problems.JugglerCollatzPaper. It imports
the existing proofs without changing their hypotheses.

| Result | Module and declaration |
| --- | --- |
| Theorem 2.1 | `CollatzPadic.orbit_bridge` |
| Series (2.4) | `PaperECompletion.code_hasSum_odd_times` |
| Codes and cylinders | `CollatzPadic.code_eq_iff`, `code_cylinder_eq` |
| Corollary 2.3 | `PaperECompletion.all_frequency_limits_iff` |
| Example 2.2 | `CollatzPadic.code_three_cleared`, `code_not_injective` |
| Lemma 3.1 | `CollatzPadic.iterate_le_of_code_eq` |
| Theorem 3.2 | `CollatzPadic.periodic_bridge` |
| Theorem 4.1 | Written proof; no Lean coverage claimed |
| Lemma 5.2 | `PreimageGrid.count_odd`, `count_doubled_odd`, `count_four` |
| Lemma 5.3 | `PreimageDomain.closed_domain_for_target` |
| Lemma 5.4 | `PreimageGrowth.growth_root` |
| Theorem 5.1 | `PreimageCertificate12.density_21_25`, `ancestor_density_21_25` |
| Real exponent \(21/25\) | `PaperECompletion.ancestor_density_real` |
| Theorem 6.1 | `PreimageBalance.certificate_power_ceiling`, `rate_lt_of_rows`, `rate_lt_of_plus_rows` |
| Logarithmic ceiling | `PaperECompletion.certificate_log_ceiling` |
| Proposition 7.1 | `BackwardMass.backward_mass_counterexample` |
| Finite complete trees | `PaperECompletion.full_prefix_tree_masses` |
| Proposition 7.2 | `CollatzMoments.complete_family_moment_loss`, `PaperECompletion.stopping_word_masses` |

AxiomCheckJugglerCollatzPaper.lean prints the dependencies
of the 28 selected declarations. The permitted logical
dependencies are propext, Classical.choice, and Quot.sound.
No additional assumption or native-evaluation trust extension
belongs to this paper's selected theorem audit.
Review of the correspondence between those statements and
the prose is a separate responsibility.

Theorem 4.1 imports a fixed-function equidistribution
criterion, not a shrinking-target estimate or a bound
uniform in growing \(a,b,M\). The source archive and release
manifest identify this version's files; they establish
neither novelty nor independent review.

## References

[T76] R. Terras, *A stopping time problem on the positive integers*,
Acta Arithmetica 30 (1976), 241-252.
[doi:10.4064/aa-30-3-241-252](https://doi.org/10.4064/aa-30-3-241-252).

[BL96] D. J. Bernstein and J. C. Lagarias, *The 3x+1 conjugacy map*,
Canadian Journal of Mathematics 48 (1996), 1154-1169.
[doi:10.4153/CJM-1996-060-x](https://doi.org/10.4153/CJM-1996-060-x).

[PP25] V. Prasad and M. A. Prasad, *Estimates of the maximum excursion
constant and stopping constant of juggler-like sequences*, preprint,
January 2025.
[doi:10.13140/RG.2.2.14110.04168](https://doi.org/10.13140/RG.2.2.14110.04168).

[KL03] I. Krasikov and J. C. Lagarias, *Bounds for the 3x+1 problem
using difference inequalities*, Acta Arithmetica 109 (2003), 237-258.
[arXiv:math/0205002](https://arxiv.org/abs/math/0205002).

[S26] M. Sharpe, *Collatz*, Lean source repository, 2026;
Grid50.lean and KLGrid.lean, MIT license; accessed 22 September 2026.
[Source repository](https://github.com/msharpe248/collatz).
The reused material is attributed in the archived local
PreimageGrid.lean and PreimageGrowth.lean.

[Bo94] M. D. Boshernitzan, *Uniform distribution and Hardy fields*,
Journal d'Analyse Mathematique 62 (1994), 225-240.
[doi:10.1007/BF02835955](https://doi.org/10.1007/BF02835955).

[R26] M. Reilly, *A criterion for weighted uniform distribution along
functions from a Hardy field*, preprint, 2026.
[arXiv:2606.08040v1](https://arxiv.org/abs/2606.08040v1).
Theorem 1.1 states the ordinary criterion used in Section 4.

[A] P. Cochin, *Lower Bounds for Cycle Lengths in the Juggler Map*,
preprint, 2026.
[Concept DOI:10.5281/zenodo.22676452](https://doi.org/10.5281/zenodo.22676452).

[B] P. Cochin, *Five-Step Descent Certificates for the Juggler Map:
Parity Statistics of Nested Floor Powers*, preprint, 2026.
[Concept DOI:10.5281/zenodo.22864933](https://doi.org/10.5281/zenodo.22864933).

[C] P. Cochin, *Fate Contagion and Termination Criteria for the Juggler Map*,
preprint, 2026.
[Concept DOI:10.5281/zenodo.22678164](https://doi.org/10.5281/zenodo.22678164).

[D] P. Cochin, *No m-cycles of the 3n-1 map for m at most 61*,
local version 1.1.0, 2026. Deposited version 1.0.0 states 58.
[Concept DOI:10.5281/zenodo.22876189](https://doi.org/10.5281/zenodo.22876189).
