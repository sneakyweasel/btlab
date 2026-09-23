# Archimedean / 2-adic compatibility of valuation itineraries

Milestone 4. This document records exact affine dynamics of finite
accelerated Collatz valuation words, the minimum-realizer sequence, and
the exceptional-itinerary compatibility problem. It does **not** claim
progress on the Collatz conjecture.

Claim labels: **EXACT — HUMAN PROOF**, **COMPUTATIONALLY VERIFIED**, **CONJECTURE**,
**OBSERVATION**. Finite checks are never proofs. Homogeneous comparison
of \(2^K\) and \(3^m\) is not a Lyapunov function.

Residue convention (unchanged from Milestone 3): leftover \(Q=1\), unique
class modulo \(2^{K+1}\), density \(2^{-K}\) among odd residues. Layer C
`FORBIDDEN` remains relative to an insufficient fixed starting precision.

---

## Exact affine dynamics

Let \(T(n)=(3n+1)/2^{v_2(3n+1)}\) on odd integers. If the first \(m\)
valuations of \(n\) are \(\mathbf{k}=(k_0,\ldots,k_{m-1})\) and
\(K=\sum k_i\), then **EXACT — HUMAN PROOF**

\[
T^m(n)=\frac{3^m n+C(\mathbf{k})}{2^K}.
\]

Write \(n_i=T^i(n)\), \(K_0=0\), \(K_{j+1}=K_j+k_j\), \(C_0=0\). From

\[
n_{i+1}=\frac{3n_i+1}{2^{k_i}}
=\frac{3(3^i n+C_i)+2^{K_i}}{2^{K_i+k_i}}
\]

the recurrence is

\[
C_{\mathrm{empty}}=0,\qquad
C_{\mathrm{append}\,k}=3C+2^{K_{\mathrm{old}}}.
\]

Unrolling (**EXACT — HUMAN PROOF** closed form)

\[
C(\mathbf{k})=\sum_{j=0}^{m-1} 3^{m-1-j}\,2^{K_j}.
\]

Each summand is a positive integer for \(m\ge 1\), so \(C>0\) for nonempty
words. The formula never divides a residue modulo \(2^P\).

Implemented as `ValuationItinerary` in `src/research/collatz/itinerary.py`.
Verified against iterating \(T\) on cylinder realizers
(**COMPUTATIONALLY VERIFIED**, redundant with the proof).

Partial states: \(n_i=(3^i n+C(\mathbf{k}[:i]))/2^{K_i}\).

### Positivity

\(n_i>0\) iff \(3^i n+C_i>0\) (denominator \(2^{K_i}>0\)), iff
\(n>-C_i/3^i\). Since \(C_i\ge 0\), every such bound is \(\le 0\).
Among positive odd integers the threshold is \(1\). Independently, \(T\)
sends positive odds to positive odds. Positivity of a genuine positive
Collatz trajectory is therefore automatic; 2-adic cylinder membership is
the separate constraint.

---

## Valuation cylinders

Unchanged: \(C_{\mathbf{k}}\) is the unique class \(n\equiv r(\mathbf{k})
\pmod{2^{K+1}}\) of odd integers. Every finite word over \(\{1,2,\ldots\}\)
is finitely 2-adically realizable. Density among odd residues is
\(2^{-K}\). **EXACT — HUMAN PROOF** (Milestone 3).

`count_cylinder_up_to(k, X)` is the exact count of positive realizers in
\([1,X]\):

\[
\#\{n:1\le n\le X,\; n\equiv r\pmod{2^{K+1}}\}
=\bigl\lfloor(X-r)/2^{K+1}\bigr\rfloor+1
\]

when \(X\ge r\), else \(0\). This *is* the Haar prediction, not an
approximation.

---

## Minimum realizers

\(R(\mathbf{k})\) is the smallest positive odd integer in the cylinder,
equal to the residue \(r(\mathbf{k})\in(0,2^{K+1})\). Always finite.

**EXACT — HUMAN PROOF lift.** If \(\mathbf{k}'=\mathbf{k}\cdot(j)\), then
\(R(\mathbf{k}')\equiv R(\mathbf{k})\pmod{2^{K+1}}\) and

\[
R(\mathbf{k}')=R(\mathbf{k})+t\cdot 2^{K+1}
\]

for an integer \(t\) with \(0\le t<2^{j}\). Hence \(R\) is nondecreasing
on nested prefixes. A child cannot have smaller \(R\) than its parent.
(**COMPUTATIONALLY VERIFIED** on short words as a regression of the proof.)

**EXACT — HUMAN PROOF bound.** \(1\le R(\mathbf{k})<2^{K+1}\), so \(\log_2 R<K+1\).

At fixed length \(m\), a low-average (expansionary) word has *smaller*
\(K\), hence a *smaller* cap on \(R\). A naive reading of “expansionary
prefixes need especially large realizers at fixed \(m\)” is therefore
false. Along a growing path, \(K_m\to\infty\) still allows \(R_m\to\infty\).

---

## Order dependence

The homogeneous budget depends only on \((m,K)\). \(C\) depends on order.

**EXACT — HUMAN PROOF adjacent swap.** For \(a=k_t\), \(b=k_{t+1}\),

\[
C_{\mathrm{swap}}-C=3^{m-t-2}\,2^{K_t}\,(2^{b}-2^{a}).
\]

Larger valuations earlier strictly increase \(C\). For a fixed multiset,
descending order maximises \(C\) and ascending order minimises \(C\).

The same ordering need not extremize \(R\). Distinct permutations of
\((1,2)\) already have different \(R\) (**COMPUTATIONALLY VERIFIED**), so
\(R\) is order-sensitive at equal \((m,K)\) (hypothesis H3, confirmed on
that pair; not a classification of all extrema).

Normalized exact ratios recorded: \(C/3^m\), \(C/2^K\),
\(C/(2^K-3^m)\) (the last denominator is nonzero for \(m>0\)).

---

## Nested 2-adic cylinders versus integers

Do not conflate:

| Label | Meaning |
| --- | --- |
| FINITELY 2-ADICALLY REALIZABLE | every finite prefix has a nonempty cylinder (**EXACT — HUMAN PROOF** for all finite words) |
| 2-ADICALLY REALIZABLE | nested intersection nonempty in the odd 2-adics (compactness of \(\mathbb{Z}_2\)) |
| REALIZED BY A POSITIVE INTEGER | some positive odd \(n\) lies in every finite cylinder of an *infinite* itinerary |
| REALIZED BY A POSITIVE INFINITE COLLATZ TRAJECTORY | the same \(n\), with the usual forward orbit |

Padded balanced-ternary word counts and canonical words remain separate
languages. Finite-\(L\) entropy is not topological entropy of the
dynamics. Exponentially small cylinder density does not exclude a nested
infinite 2-adic trajectory.

### The \(R_m\to\infty\) proposition

**EXACT — HUMAN PROOF.** Let \(k_0,k_1,\ldots\) be an infinite valuation sequence and
\(R_m=R(k_0,\ldots,k_{m-1})\). If a positive odd integer \(n\) realises
every finite prefix, then \(n\ge R_m\) for all \(m\). Therefore, if
\(R_m\to\infty\), no finite positive integer realises the entire infinite
itinerary.

This is a statement about a *prescribed* itinerary. It says nothing about
whether some other itinerary is realised by a given Collatz orbit, and it
is not a proof of Collatz.

### Full stabilization equivalence

For an infinite itinerary \(\mathbf{k}=(k_0,k_1,\ldots)\), “realized by
one positive integer” means

\[
\exists n\in\mathbb Z_{>0}\text{ odd}\quad
\forall m\ge0,\quad
n\equiv R_m\pmod {2^{K_m+1}}.
\]

**EXACT — HUMAN PROOF.** The following are equivalent:

1. one positive odd integer realizes every prefix;
2. \(R_m\) is bounded;
3. \(R_m\) is eventually constant;
4. the lift digits \(t_m\) are eventually zero.

The sequence \(R_m\) is nondecreasing by the nested lift equation. Every
bounded nondecreasing sequence of natural numbers is eventually constant:
it can make only finitely many strict increases below an integer bound.
Conversely, an eventually constant sequence is bounded.

If \(n\) realizes every prefix, then \(R_m\le n\), so \(R_m\) is bounded.
More precisely, \(K_m\ge m\), hence \(2^{K_m+1}\to\infty\). Once the
modulus exceeds \(n\), the unique representative of \(n\)'s class in
\((0,2^{K_m+1})\) is \(n\), so \(R_m=n\).

If \(R_m=r\) for all \(m\ge N\), then \(r=R_N\) realizes prefix \(N\).
Nesting gives all earlier prefixes, while \(r=R_m\) directly realizes
every later prefix. Thus \(r\) realizes the entire itinerary.

Finally,

\[
R_{m+1}-R_m=t_m2^{K_m+1}
\]

and the power of two is positive, so \(R_{m+1}=R_m\) iff \(t_m=0\).
This proves the full equivalence, not only the one-way unboundedness
criterion. The abstract cylinder/lift theorem is also
**EXACT — LEAN VERIFIED** in `formal/Problems/Collatz/`.

**EXACT — HUMAN PROOF.** For the all-ones word of length \(m\),

\[
R((1)^m)=2^{m+1}-1.
\]

Induction on the inverse step: the unique class for \(m=0\) is \(1=2^1-1\).
If the residue is \(r=2^P-1\) and we prepend valuation \(1\), then

\[
n\equiv(2r-1)3^{-1}\pmod{2^{P+1}}.
\]

Now \(2r-1=2^{P+1}-3\equiv-3\), and \((-3)3^{-1}\equiv-1\pmod{2^{P+1}}\), so
\(n\equiv 2^{P+1}-1\). Thus \(R_m\to\infty\), and by the proposition above
no positive integer realises the entire infinite all-ones itinerary.

This is not a Collatz proof: ordinary orbits are not required to be all ones.

---

## Exceptional itinerary compatibility problem

Let \(\mathbf{k}=(k_0,k_1,\ldots)\) and \(K_m=\sum_{i<m}k_i\). Call the
itinerary *asymptotically non-contracting* if

\[
\liminf_m \frac{K_m}{m}\le\log_2 3,
\]

equivalently \(\liminf(2^{K_m}/3^m)\le 1\) in the exact integer comparison
along a subsequence. Question:

> Can such an itinerary be realised by a positive odd integer under
> accelerated Collatz?

The framework does not answer this. The pipeline records budget, \(R_m\),
order-sensitive \(C_m\), and balanced-ternary features of \(R(\mathbf{k})\).
No Lyapunov function is attached.

---

## Finite certificates

| Attempt | Status |
| --- | --- |
| \(R<2^{K+1}\) | **EXACT — HUMAN PROOF** |
| Nested lift \(R'=R+t 2^{K+1}\); infinitely many \(t\ge 1\) implies \(R_m\to\infty\) | **EXACT — HUMAN PROOF** |
| \(R((1)^m)=2^{m+1}-1\), hence \(R_m\to\infty\) | **EXACT — HUMAN PROOF** |
| Non-contraction implies \(R_m\to\infty\) | **CONJECTURE** (the compatibility problem) |
| Weighted automaton producing a diverging lower bound on \(\log R\) | **OBSERVATION**: not constructed; the residue already uses unbounded precision |

No finite certificate of infinite incompatibility for a class of
non-contracting itineraries was found. Counterexample search for a
*decreasing* child \(R\) found none, as required by the lift theorem.

---

## What this does and does not imply for Collatz

- A proof cannot come from a finite forbidden language of valuation
  words: every finite word is 2-adically realizable.
- Compatibility of an infinite itinerary with a *positive integer* is a
  different question from 2-adic realizability.
- Order of valuations changes \(C\) (exactly) and can change \(R\).
- Nothing here proves or disproves Collatz. Homogeneous contraction of
  \(2^K\) versus \(3^m\) is not a descent function.

CLI: `itinerary`, `realizer`, `enumerate-itineraries`, `fixed-budget`,
`permutations`, `exceptional-search`.

Milestone 5 strengthens the nested-minimum proposition to the exact
three-way zero-lift dichotomy, proves uniqueness of every zero-lift
extension, and treats periodic itineraries. See
[collatz_zero_lift.md](collatz_zero_lift.md).

## Literature-facing coordinate conventions

For this document's affine constant \(C\), Kramer writes \(B=C\). His
coarser start representative is \(r=R\bmod2^K\), while his least-positive
endpoint representative is

\[
M\equiv C\,2^{-K}\pmod {3^m},\qquad1\le M\le3^m.
\]

Thus \(R\), \(r\), \(M\), \(\operatorname{BT}(R)\), and the real drift are
all deterministic functions of the exponent code. Balanced ternary is an
exact representation of \(R\), not an independent information channel;
lossy features may nevertheless remain useful computationally.

See [literature_comparison.md](literature_comparison.md) for the
primary-source formulas and theorem/computation/conjecture boundaries, and
[cerda_comparison.md](https://github.com/sneakyweasel/btlab/blob/f038c8526134cdaabd10857b23a87520c7cebc4f/docs/cerda_comparison.md) for why Cerdá's local affine
branch formulas are comparable but the posted global non-reuse and
convergence reductions are not adopted. The exact statements above remain
on the Milestone 6 verified baseline.
