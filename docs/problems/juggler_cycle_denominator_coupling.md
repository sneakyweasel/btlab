# Exact floor closure and the rational cycle denominator

Status: **CLOSE** for automatic denominator cancellation from algebraic
or modular closure. A quantified counterfamily is retained. The question
of a denominator bound for actual integer cycles remains unresolved.

## Problem

Authorized next question, 22 September 2026: can the exact Juggler floor
equations restrict the denominator of the rational 3n-1 periodic point
associated with a returning parity word, beyond restrictions on that
word already supplied by finance?

## Exact statement

For a nonempty word \(w=(b_0,\ldots,b_{K-1})\), with \(b_i=1\) for O and
\(b_i=0\) for E, put \(o=\sum b_i\), \(a_i=1+2b_i\), and
\[
D=3^o-2^K,\qquad
\lambda_i=2^i\prod_{j>i}a_j,\qquad
A=\sum_i\lambda_i b_i,\qquad q=\frac{|D|}{\gcd(|D|,A)}.
\]
The rational 3n-1 periodic point has value \(A/D\) and reduced
denominator \(q\). The target concerns words of genuine integer Juggler
cycles, not arbitrary formal words or congruence returns.

**Retained theorem, EXACT — HUMAN PROOF (AI-assisted written argument).**
Fix integers \(a,b\ge1\) with \(3^a>2^{a+b}\), any integer modulus
\(M\ge1\), and any lower bound \(B\). There are infinitely many odd
integers \(n>B\) whose actual Juggler itinerary is \(O^aE^b\), such that
\[
J^{a+b}(n)>n,\quad
J^j(n)\ge n\ (0\le j\le a+b),\quad
J^{a+b}(n)\equiv n\equiv1\pmod{2M}.
\]
The code denominator of this word is
\[
q_{a,b}=
\frac{3^a-2^{a+b}}{\gcd(3^a-2^a,\ 2^b-1)}
\ \ge\ \frac{3^a-2^{a+b}}{2^b-1}.
\]
For fixed \(b\), these denominators tend to infinity with \(a\).
In particular one may take \(M=q_{a,b}^r\), for any fixed \(r\ge1\).
Whenever \(q_{a,b}>1\), the code remains nonintegral. The starts depend on the word and
the modulus; no uniform bound for their size is asserted.

This is an obstruction to a congruence-only transfer, not a counterexample
to a statement about true cycles. These paths grow, and no claim is made
that they lie inside the finance window for the same word.

## Current literature

- Bernstein--Lagarias 1996, equations (1.5), (1.6), (4.2):
  **known** parity coding and the affine rational-cycle formula;
  bernstein-lagarias-1996-conjugacy-map.
- Cyclic integer linear systems and their cokernels: **known** elementary
  algebra. The quotient interpretation below is a reparameterization.
- Boshernitzan 1994, Theorem 1.3: **known** equidistribution criterion for
  Hardy-field functions of polynomial growth that stay more than
  logarithmically far from every rational polynomial;
  boshernitzan-1994-hardy-fields. The criterion and a new proof were read
  directly in [Reilly, Theorem 1.1 and Theorem A](https://arxiv.org/html/2606.08040v1).
  Only the ordinary unweighted criterion is used.
- [Modular closure](juggler_cycle_mod_closure.md) already closes the
  relaxed fixed-modulus obstruction. The theorem here uses actual
  floor iterates and arbitrary prescribed moduli, including powers of
  their own rational code denominators.
- [p-adic coupling](juggler_cycle_padic_coupling.md) treats primes 2 and 3.
  They do not divide an expanding cycle gap. The present question
  concerns the other primes and is not answered just by that observation.
- [Defect congruence](juggler_cycle_defect_congruence.md) already warns
  that a telescoping remainder identity is not a new restriction.

External novelty of the counterfamily is not claimed. Its role is to
replace a prospective transfer argument with an explicit quantified
obstruction in this laboratory.

## Branch budget

~~~text
Mathematical target     determine whether exact floor closure forces cancellation
                        in the rational Collatz cycle denominator
Novelty hypothesis      the floor remainders impose an additional congruence
                        at primes dividing 3^o - 2^K
Falsifier               the congruence is an identity with nonlinear terms,
                        and does not constrain the parity correction
Already killed by?      the p=2,3 obstruction does not cover these primes;
                        fixed-modulus freeness and defect identities remain hazards
Existing machinery      word-affine formula, exact square/cube remainders,
                        global defect identities
Maximum Phase-0 scope   one algebraic reduction, exact small checks,
                        and a test of the required cancellation
Promotion criterion     a restriction on actual cycle words beyond existing finance
Stop criterion          only a change of variables or a congruence identity survives
~~~

The finite modular-return counterexample justified one theorem phase:
prove an infinite family of actual modular returns. It does not justify
another branch or a larger search.

## Balanced-ternary formulation

None. The relevant modulus is coprime to 6, rather than a fixed power of 3.

## Why BT may be relevant

No representation advantage is used or claimed.

## Candidate operations / invariants

- The order of the parity vector in a cyclic cokernel is \(q\):
  **REPARAMETERIZATION** of the rational-cycle formula.
- Exact floor forcing represents zero in that cokernel on a cycle:
  **EXACT — HUMAN PROOF**, an elementary identity.
- Equating that forcing with the parity vector: unjustified; the
  omitted quadratic and cubic terms are displayed below.
- Modular return, even at arbitrary prescribed denominator precision,
  forces an integer code: **REFUTED** for finite actual trajectories.
- A bound on \(q\) for true Juggler cycles: unresolved.

## Experiments

No production probe or floor campaign. The
[exact regression checks](../../tests/research/juggler_sequence/test_cycle_denominator_coupling.py)
use rational Gaussian elimination, literal integer-square-root iteration,
and the fixed witnesses below.

- All 126 binary words of lengths 1 through 6, each with three forcing
  vectors: 378 independently solved cyclic rational linear systems.
- Starts 1 through 256, eight exact steps each: the floor-forcing identity
  with its nonzero endpoint term.
- Two directly found modular-return witnesses, and five witnesses in
  the perfect-power family.
- The run-word gcd formula for \(1\le b\le9\), \(2\le a\le64\) in the
  expanding cases.

The exploratory searches stopped at the first witness within their caps.
The eleven-step search inspected 2553 starts above 350000000; it checked
only those prefixes, not their eventual fates, and certified no new floor.

## Conjectures

None opened. In particular, no integrality or bounded-denominator
conjecture for true Juggler cycles is adopted.

## Counterexamples

The exact prefix
\[
1065\to34755\to6479267\to16492588200\to128423
\]
has word OOOE, gap \(D=11\), charge \(A=19\), and denominator \(q=11\).
Its endpoint difference is \(127358=22\cdot5789\), so it returns modulo
\(2q\), with every floor and every branch parity genuine, while the
associated rational cycle value \(19/11\) is not integral.

Above the existing floor, the start \(350002553\) has eleven-step word
OOOEOEOOOEE and endpoint \(1330352317\). Here
\[
D=139,\quad A=3187,\quad q=139,\quad
1330352317-350002553=278\cdot3526438.
\]
Every state of that prefix is at least the start. This example has four
even letters, so the obstruction is not confined to the one-even-letter
toy word. It is still not a cycle or a finance-feasible cycle witness.

## Formalization

Written proof with classical equidistribution as a named external input;
no new Lean module. The infinite statement is not inferred from tests.
Independent human review and Lean verification of this application remain
outstanding. Existing exact-root and power-depth results explain the
construction but are not claimed to formalize the theorem below.

## Results

### 1. The denominator is a torsion order

Define the integer matrix \(L\) by
\[
(Lx)_i=a_i x_i-2x_{i+1},
\]
with indices cyclic modulo \(K\); when \(K=1\) the two terms occupy the
same entry. Its determinant is \(D=\prod a_i-2^K\ne0\).
For every integer vector \(x\),
\[
\sum_i\lambda_i(Lx)_i=D x_0. \tag{1}
\]
The intermediate terms cancel because
\(\lambda_i a_i=2\lambda_{i-1}\) for \(1\le i<K\).

The map \(c\mapsto\sum_i\lambda_i c_i\bmod D\) is onto:
\(\lambda_{K-1}=2^{K-1}\) is a unit modulo the odd integer \(D\).
Its kernel contains \(L\mathbb Z^K\). Both have index \(|D|\), the
second by the determinant, hence
\[
\mathbb Z^K/L\mathbb Z^K \simeq \mathbb Z/|D|\mathbb Z.
\]
The parity vector \(b\) maps to \(A\bmod D\), whose order is
\(|D|/\gcd(|D|,A)=q\). Thus the denominator records the failure of
the affine parity correction to be an integer cyclic difference.

For expanding words \(o\ge1\), \(D\) and \(q\) are coprime to 6.
Looking for their cancellation at primes 2 and 3 is therefore empty.

### 2. What the exact floor equations actually put in the quotient

Along a genuine prefix \(n_0,\ldots,n_K\), set \(u_i=n_i-1\) and
\[
r_i=n_i^{a_i}-n_{i+1}^2,\qquad 0\le r_i<2n_{i+1}+1.
\]
Expanding at 1 gives the exact integer equation
\[
a_i u_i-2u_{i+1}
=r_i+u_{i+1}^2-b_i(3u_i^2+u_i^3)=:c_i. \tag{2}
\]
Consequently
\[
\sum_i\lambda_i c_i=3^o u_0-2^K u_K. \tag{3}
\]
On a cycle, the right side is \(D u_0\), so \(c\) has zero
cokernel class. This does not say the parity vector \(b\) has zero
class. Replacing \(c_i\) by \(b_i\) discards the terms in (2).

Likewise, a prefix returning modulo a divisor of \(D\) makes (3)
vanish modulo that divisor, without making \(A\) vanish. The two
explicit witnesses above exhibit exactly this failure.

The useful linearization of Juggler in logarithms has small floor
losses, but no integer lattice to which this cokernel applies.
The integer expansion (2) retains the lattice and retains the nonlinear
terms. No bound removing those terms was obtained.

### 3. Actual modular returns at every prescribed precision

Fix \(a,b,M\) as in the theorem. For \(t\ge1\), write
\[
s=1+2Mt,\qquad n=s^{2^{a-1}},\qquad
\beta=\frac{3^a}{2^{b+1}}.
\]
The first \(a-1\) steps are exact powers:
\[
n_i=s^{3^i2^{a-1-i}}\quad(0\le i<a).
\]
They are odd, and for \(i<a-1\) they are squares. The next odd step is
\(y_0=\lfloor s^{3^a/2}\rfloor\). If it is even, subsequent even
steps have the exact formulas
\[
y_j=\lfloor s^{3^a/2^{j+1}}\rfloor
     =\lfloor s^{2^{b-j}\beta}\rfloor\quad(0\le j\le b).
\]
There is no approximation of a nested floor here:
\(\lfloor\sqrt{\lfloor x\rfloor}\rfloor=\lfloor\sqrt x\rfloor\)
for \(x\ge0\), by comparison with integer squares.

Consider, modulo 1, the \((b+1)\)-tuple
\[
\left(
\frac{s^\beta}{2M},
\frac{s^{2\beta}}2,
\frac{s^{4\beta}}2,\ldots,
\frac{s^{2^b\beta}}2
\right). \tag{4}
\]
It is jointly uniformly distributed as \(t\to\infty\).
To verify this rather than assume independence, take any nonzero
integer linear combination. Its highest nonzero exponent is one
of \(3^a/2^{b+1-j}\), \(0\le j\le b\), hence is nonintegral.
The combination is a Hardy-field function of polynomial growth.
Its distance from any rational polynomial, divided by \(\log t\),
tends to infinity: either the polynomial has higher degree, or the
nonintegral leading power survives. Boshernitzan's criterion gives
uniform distribution of each combination; Weyl's criterion gives (4).

Require the first coordinate's fractional part to lie in
\([1/(2M),2/(2M))\), and all the others in \([0,1/2)\).
These are exactly the conditions
\[
y_b\equiv1\pmod{2M},\qquad y_0,\ldots,y_{b-1}\text{ even}.
\]
The box has volume \(1/(2^{b+1}M)>0\), so the successful parameters
have that asymptotic density among the positive integers \(t\).
For them the entire prescribed word is an actual Juggler itinerary,
and \(n\equiv y_b\equiv1\pmod{2M}\).

Finally \(3^a>2^{a+b}\) means \(\beta>2^{a-1}\), hence \(y_b>n\)
for all sufficiently large \(s\). The odd portion increases and the
even portion decreases to \(y_b\), so all states are at least \(n\).
Taking \(s\) large also gives \(n>B\). This proves the theorem.

For the word \(O^aE^b\), summing its odd corrections gives
\[
A=3^a-2^a,\qquad D=3^a-2^{a+b}.
\]
Since \(A\) is odd,
\[
\gcd(A,D)=\gcd(A,\ 2^a(2^b-1))
         =\gcd(A,\ 2^b-1).
\]
This proves the denominator formula and its divergence for fixed \(b\).
The theorem permits any fixed \(b\), including \(b\ge8\).

This use of classical equidistribution is confined to the explicit
perfect-power family. It proves no all-word FD statement, no
equidistribution along an arbitrary orbit, and no bound uniform in
growing word length or modulus.

### 4. Reproducible perfect-power witnesses

In the construction \(M=q^r\), \(s=1+2Mt\), \(n=s^{2^{a-1}}\),
the following parameters pass literal Juggler iteration:

| \(a\) | \(b\) | \(q\) | \(r\) | \(t\) | \(s\) |
|---:|---:|---:|---:|---:|---:|
| 3 | 1 | 11 | 1 | 9 | 199 |
| 3 | 1 | 11 | 2 | 318 | 76957 |
| 3 | 1 | 11 | 3 | 12589 | 33511919 |
| 4 | 2 | 17 | 1 | 313 | 10643 |
| 6 | 3 | 31 | 1 | 1242 | 77005 |

For the first, \(n=1568239201\) and the endpoint is
\(3290472501622263\), both 1 modulo 22. In the final row \(D=217\)
but \(q=31\), checking nontrivial gcd cancellation as well.

## Open questions

Whether exact equality \(n_K=n_0\), combined with floor inequalities
and the finance size window, constrains \(q\) remains unresolved.
The counterfamily establishes no compatible integer start satisfying
all congruence precisions at once. Its witnesses can grow with the
precision and escape the size window.

## Decision

**CLOSE** the automatic algebraic/modular denominator-cancellation route.
The promotion criterion, a new restriction on actual cycle words, was
not met. Retain the infinite counterfamily as a scoped exact obstruction,
and retain the cokernel calculation as classical algebra explaining it.
This does not close the mathematical question about actual cycles.

Best next question: can actual equality of endpoints yield a denominator
restriction using the finance size window that the modular-return family
necessarily escapes? No bound or executable method is proposed, and no
further branch is opened.

## Publication assessment

The authorized escape-continuation question of 22 September 2026 is
recorded in [power-family re-entry](juggler_power_family_reentry.md).
It establishes density-zero square re-entry and conditional finiteness
under abc for each fixed block type. The finite-prefix theorem above
remains unchanged; no infinite escaping trajectory is constructed.

Status: **STRUCTURAL** as a scoped method obstruction, not a new cycle
bound or a separate paper candidate. The infinitude proof is AI-assisted
and awaits independent human review. Papers A--D, their releases, the
Juggler floor and its period bound are unchanged.
