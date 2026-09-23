# Collatz dual coding

Milestone 6. Every statement is labelled **EXACT — HUMAN PROOF**, **EXACT — LEAN
VERIFIED**, **COMPUTATIONALLY VERIFIED**, **CONJECTURE**, or
**OBSERVATION**. Finite rarity is never treated as impossibility. Nothing
here proves or disproves the Collatz conjecture.

## 1. Motivation

Finite valuation words are never the obstruction: every word over
\(\{1,2,\ldots\}\) defines a nonempty 2-adic cylinder. The exceptional
condition is that one ordinary positive integer belong to every cylinder
of an infinite nested sequence.

The valuation digits \(k_m\) describe consumed powers of two. The lift
digits

\[
t_m=\frac{R_{m+1}-R_m}{2^{K_m+1}}
\]

describe how the canonical positive representative changes when the
cylinder is refined. The pair \((k_m,t_m)\) is the dual code.

## 2. Valuation cylinders

For \(\mathbf{k}=(k_0,\ldots,k_{m-1})\), put
\(K=\sum_i k_i\). At leftover precision \(Q=1\), its cylinder is one odd
residue class modulo \(2^{K+1}\), with density \(2^{-K}\) among odd
residues. Every finite positive word is admissible. **EXACT — HUMAN PROOF**.

Positive-lift children are valid finite extensions. They are never
“forbidden”; that older label applies only when a fixed precision is too
small.

## 3. Canonical realizer \(R\)

Let \(C=C(\mathbf{k})\) use the established recurrence

\[
C_{\varnothing}=0,\qquad C_{u\cdot k}=3C_u+2^{K_u}.
\]

The endpoint must be odd:

\[
3^mR+C\equiv2^K\pmod {2^{K+1}}.
\]

Since \(3^m\) is invertible modulo \(2^{K+1}\),

\[
\boxed{
R\equiv(2^K-C)\,3^{-m}\pmod {2^{K+1}},
\quad 1\le R<2^{K+1}.
}
\]

This direct formula is **EXACT — HUMAN PROOF** and independently
**COMPUTATIONALLY VERIFIED** on 5,461 bounded words during development.

## 4. Lift digits \(t\)

For a parent prefix of length \(m\), let

\[
x=T^m(R)=\frac{3^mR+C}{2^K},\qquad q=\frac{3x+1}{2}.
\]

Changing the initial representative to \(R+t2^{K+1}\) changes the
endpoint before the next Collatz step to \(x+2\cdot3^m t\). Requiring the
next exact valuation to be \(k\) is equivalent to

\[
q+3^{m+1}t\equiv2^{k-1}\pmod {2^k}.
\]

Therefore the unique lift digit is

\[
\boxed{
t(p,k)=
\left(3^{m+1}\right)^{-1}
\left(2^{k-1}-q\right)
\pmod {2^k},
\quad 0\le t<2^k.
}
\]

It was **COMPUTATIONALLY VERIFIED** on 2,046 bounded cases in addition to
the proof.

The child endpoint has the closed recurrence

\[
\boxed{
x'=\frac{q+3^{m+1}t}{2^{k-1}}.
}
\]

Thus the smallest exact unbounded transition state discovered is
\((m,x)\). It computes \(t\) and \(x'\) without replaying the trajectory
or recomputing the child cylinder. This is **EXACT — HUMAN PROOF**.

## 5. Stabilization theorem

For an infinite itinerary, the following are equivalent:

1. one positive odd integer realizes every finite prefix;
2. \(R_m\) is bounded;
3. \(R_m\) is eventually constant;
4. \(t_m=0\) eventually.

This is **EXACT — LEAN VERIFIED**. The detailed
human-readable proof is in
[collatz_itinerary_compatibility.md](collatz_itinerary_compatibility.md).

For every prefix \(p\), define

\[
k_{\rm zero}(p)=v_2(3T^{|p|}(R(p))+1).
\]

Then

\[
R(p\cdot k)=R(p)
\quad\Longleftrightarrow\quad
k=k_{\rm zero}(p).
\]

Hence each node has one zero-lift child and every other child has
positive lift. **EXACT — HUMAN PROOF**. The distinguished path follows the accelerated
Collatz orbit of \(R(p)\), so a complete classification would repackage
the original orbit problem.

## 6. Dual coding

`CollatzDualCode` stores valuations, cumulative \(K\), lift digits,
prefix realizers, canonical endpoints, \(C\), final \(R\), and
\(\operatorname{BT}(R)\).

Starting from \(R_0=1\),

\[
\boxed{
R_m=1+\sum_{j<m}t_j2^{K_j+1}.
}
\]

This reconstruction is **EXACT — LEAN VERIFIED**.
For a fixed valuation word, the lift word is unique.

## 7. Mixed-radix representation

Write \(S=(R_m-1)/2\). Then

\[
S=\sum_{j<m}t_j2^{K_j},\qquad 0\le t_j<2^{k_j}.
\]

This is an ordinary mixed-radix expansion with successive radices
\(2^{k_j}\). For fixed \(\mathbf{k}\),

\[
t_j=\left\lfloor\frac{S}{2^{K_j}}\right\rfloor\bmod2^{k_j},
\]

so the representation is unique. **EXACT — HUMAN PROOF**.

Not every sequence satisfying only the digit bounds is valid. For each
valuation word there is exactly one valid lift word, determined by the
congruence recurrence in Section 4.

At finite precision \(P\), the state
\((x\bmod2^P,m\bmod2^{P-2})\) determines transitions while sufficient
precision remains. A valuation \(k\) consumes \(k\) bits in the
implemented paired precision model. This gives an exact finite,
precision-drop recognizer, not one fixed automaton for unbounded
itineraries. **EXACT — HUMAN PROOF**.

## 8. Balanced ternary representation of \(R\)

All existing balanced-ternary features are recorded exactly. However,
even the complete value \(R\), and hence its entire balanced-ternary
word, does not determine the next zero-lift valuation or a proposed lift
digit without prefix state:

\[
R((1))=R((1,4))=3,\qquad \operatorname{BT}(3)=\texttt{+0},
\]

but their canonical endpoints are \(5\) and \(1\), their zero-lift
successors are \(4\) and \(2\), and for candidate \(k=2\) their lift
digits are \(2\) and \(0\). This is **REFUTED**.

Consequently no bounded suffix of \(\operatorname{BT}(R)\) can determine
these quantities in general. A bounded census of 341 prefixes
(\(m\le4,k\le4\)) found ambiguities for every tested suffix length
\(1\le L\le8\). That supporting result is **COMPUTATIONALLY VERIFIED**.

## 9. Periodic itineraries

For a period \(v\) of length \(p\), a positive realizer must satisfy

\[
n(2^K-3^p)=C(v).
\]

Exact divisibility, positivity, oddness, and cylinder membership classify
the unique candidate. **EXACT — HUMAN PROOF**.

Benchmarks:

- \((1)^\infty\): \(t_m=1\) and \(R_m=2^{m+1}-1\). **EXACT — HUMAN PROOF**.
- \((2)^\infty\): \(t_m=0\), \(R_m=1\), and the realizer is \(1\).
  **EXACT — HUMAN PROOF**.
- A census of 316 primitive words with period at most four,
  \(k_i\le4\), repeated eight times found only period \((2)\) compatible
  with a positive cycle. **COMPUTATIONALLY VERIFIED**; this is not a
  global cycle theorem.

Noncompatible periodic words can have complicated finite lift traces;
finite zero-lift frequency is not an infinite compatibility criterion.

## 10. Non-contracting itineraries

Budget comparisons use exact integers \(2^{K_m}\) and \(3^m\).
The statement

> every asymptotically non-contracting itinerary has infinitely many
> positive lift digits

remains a **CONJECTURE**.

At length ten with \(k_i\le3\), the exact non-contracting census contains
2,343 words, zero-lift counts from 0 through 8, and \(R\) from 27 through
65,531. These are **COMPUTATIONALLY VERIFIED** finite facts only.

The expanding word

\[
(1,2,1,1,1,1,2,2,1,2)
\]

has lift digits

\[
(1,2,1,0,0,0,0,0,0,0)
\]

and \(R=27\) from depth three through ten. This is an **EXACT FINITE
COUNTEREXAMPLE** to the stronger local claim that every expanding
extension must lift. It does not define an infinite counterexample.

## 11. Finite-certificate attempts

The paired precision-drop state certifies exact finite transitions while
precision remains. Coarser `R mod 2^P` states collide: the same residue
can have different canonical endpoints and zero-lift successors.

No finite certificate proving infinitely many positive lifts for a
useful infinite non-contracting class was found. **OBSERVATION**. This
failure does not prove that no richer certificate exists.

## 12. Relation to the 2-adic interpretation

Finite valuation realizability is expected from the 2-adic coding: each
finite word fixes more low-order bits. The mixed-radix lift digits are
exactly the blocks selected when the canonical residue is refined.

An infinite 2-adic intersection exists for every infinite valuation word.
Ordinary positive-integer realizability is exceptional: its canonical
representatives must stop acquiring nonzero mixed-radix blocks.

## 13. Open problems

1. Does asymptotic non-contraction force infinitely many positive lifts?
2. Is there a finite certificate for a nontrivial infinite class?
3. Can the paired precision model be quotiented without losing soundness?
4. Which periodic valuation words have eventually periodic lift words?
5. Can order-sensitive lift extrema be classified without permutation
   enumeration?

The dual code provides useful structural understanding and concrete exact
theorems. It does not currently provide a plausible route to excluding
all exceptional non-contracting integer trajectories.

## 14. Four-coordinate compatibility milestone

The literature-facing state exposes the refined start \(R\), Kramer's
endpoint \(M\), \(\operatorname{BT}(R)\), and exact drift
\((3^m,2^K)\). With this document's affine constant,

\[
B=C,\qquad r=R\bmod2^K,\qquad
M\equiv C\,2^{-K}\pmod {3^m}
\]

where \(r\) is least nonnegative and \(M\) least positive. Kramer's
\(d,\rho_r,\rho_M\) use natural logarithms.

**EXACT — HUMAN PROOF.** Every displayed coordinate and every lift digit is
deterministic from the exponent code. In particular,
\(\operatorname{BT}(R)\) contains no information-theoretically independent
coordinate beyond \(R\). Its lossy suffixes and features can still expose
useful finite partitions; any benefit of that kind is
**COMPUTATIONALLY VERIFIED** or an **OBSERVATION**.

See [literature_comparison.md](literature_comparison.md),
[balanced_ternary_vs_collatz_literature.md](balanced_ternary_vs_collatz_literature.md),
and [cerda_comparison.md](https://github.com/sneakyweasel/btlab/blob/f038c8526134cdaabd10857b23a87520c7cebc4f/docs/cerda_comparison.md). These comparisons use the
Milestone 6 verified baseline and do not adopt unproved global
non-reuse/convergence claims from preprints.
