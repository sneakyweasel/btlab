# Exact even-fibre mass and its signed Collatz transport

Status: **PROMOTE**, 22 September 2026. The results below are
**EXACT — HUMAN PROOF** in the repository's terminology: AI-assisted written
proofs, with independent review and Lean formalization outstanding.

## Problem

Where does Juggler's inverse multiplicity go when the signed Collatz code
identifies different starts? Philippe asked to continue tracing that information,
rather than stop at the failure of ordinary Collatz reciprocal weights.

## Exact statement

Write J for the Juggler map on positive integers and

\[
 E(m)=\{n\ge1:n\text{ even},\ J(n)=m\},\qquad
 e(n)=n+(n\bmod2),\qquad
 w(n)=\log\frac{e(n)+1}{e(n)-1}.
\]

Then, for every m>=1,

\[
 \boxed{\sum_{n\in E(m)}w(n)=w(m).}                 \tag{1}
\]

Moreover w(n)=2/n+O(1/n^2). It is the unique real-valued function with this
asymptotic normalization and exact even-fibre conservation; in fact the
weaker normalization n*w(n)->2 already ensures uniqueness.

Let H be the already constructed minus signed Collatz code into the 2-adic
integers: H preserves parity, H(J(n))=C_-(H(n)), and H(1)=1. Define

\[
 \nu_X(B)=\sum_{1\le n\le X,\ H(n)\in B}w(n),\qquad
 \nu(B)=\sum_{n\ge1,\ H(n)\in B}w(n).
\]

For every set B of codes, allowing infinite values for nu,

\[
 \boxed{\nu(2B)=\nu(B).}                           \tag{2}
\]

For each integer X>=1, put M=floor(sqrt(X)). There is the stronger cutoff law

\[
 \boxed{\nu_X(2B)=\nu_{M-1}(B)
       +\mathbf1_{H(M)\in B}\,b_X(M)},\qquad
 0\le b_X(M)\le w(M),                              \tag{3}
\]

where b_X(M) is the weight of the part of E(M) below X. These are statements
on the coded, source-weighted space. They do not identify nu with the usual
reciprocal measure on positive Collatz integers. The plus code is -H;
negation gives the same even-branch identities on its image.

## Current literature

The signed parity-code construction and its prior art are recorded in
[the bridge dossier](juggler_collatz_bridge.md). Pushforward of a measure is
standard mathematics. The previous even-tree estimates are in
[Paper C](../theory/juggler_fate_almost_all_note.md) and
[FateTaoReduction.lean](../../formal/Problems/Juggler/FateTaoReduction.lean).
They already give bounds on reciprocal mass through many even generations.
The new project-specific refinement here is the explicit parity-paired weight
which conserves mass without an error term, its uniqueness, and its exact
coded cutoff identity. No improvement to Paper C's exponent is asserted.

The [Collatz fibre dossier](collatz_fibre_mass.md), citing
`zarnowski-2008-congruence-structure` and `tao-2019-almost-all-collatz`, treats
ordinary odd-return Collatz fibres and their finite-residue weight obstruction.
Those results do not apply to the source-weighted measure defined here.
A bounded literature search did not identify this explicit Juggler weight;
that is not a priority claim or an exhaustive literature review.

## Branch budget

- **Target:** an explicit mass preserved by every even Juggler fibre and its
  exact transport through H.
- **Novelty hypothesis:** a parity-adjusted logarithmic cell weight removes
  the fibre-mass error exactly.
- **Falsifier:** a parity-boundary counterexample or failure of reciprocal
  comparison.
- **Already killed by?:** the tilted-pushforward mass/energy obstruction
  concerns a pressure bound. No such bound is proposed here. The ordinary
  Collatz finite-residue obstruction concerns a different measure.
- **Existing machinery:** exact even fibres, Paper C mass estimates, and the
  unconditional 2-adic code with parity and semiconjugacy.
- **Maximum Phase-0 scope:** prove the weight law, test rational products and
  finite coded cutoffs, and identify the retained information and limitation.
- **Promotion criterion:** an explicit conservation law and precise transport
  theorem, together with a concrete distinction from ordinary reciprocal mass.
- **Stop criterion:** stop after those results; do not infer a pressure or
  termination estimate, or open an odd-branch estimation campaign.

## Balanced-ternary formulation

None is needed. The fibre endpoints are ordinary integers and the code is
2-adic. Balanced ternary can express the inverse odd-branch denominator 3,
but does not change the mass identity.

## Why BT may be relevant

This is a problem-specific invariant in `research.juggler_sequence`, not a
new BT-core operation. No representation change is used as evidence.

## Candidate operations / invariants

### 1. Exact conservation, including both endpoint parities

Consecutive even integers n have weights log((n+1)/(n-1)). Their sum
telescopes. If m is even, E(m) runs from m^2 to (m+1)^2-1 in steps of two,
so its mass is

\[
 \log\frac{(m+1)^2}{m^2-1}
 =\log\frac{m+1}{m-1}=w(m).
\]

If m is odd, E(m) runs from m^2+1 to (m+1)^2-2, giving

\[
 \log\frac{(m+1)^2-1}{m^2}
 =\log\frac{m+2}{m}=w(m).
\]

This includes m=1: E(1)={2} and w(1)=w(2)=log(3).
All denominators are positive. For disjoint target sets the even fibres
are disjoint, so (1) also gives conservation for arbitrary unions, with
nonnegative sums if the union is infinite.

The example m=5 displays the cancellation directly:

\[
 \frac{27}{25}\frac{29}{27}\frac{31}{29}
 \frac{33}{31}\frac{35}{33}=\frac75.
\]

Thus the five children 26,28,30,32,34 carry exactly w(5)=log(7/5).

### 2. Reciprocal comparison and uniqueness

Since w(n) is the integral of 1/t from e(n)-1 to e(n)+1,

\[
 \frac{2}{e(n)}\le w(n)\le\frac{2}{e(n)-1},\qquad
 \frac1n\le w(n)\le\frac4n.
\]

The lower integral bound follows by pairing t=e-u with t=e+u, or by
convexity of 1/t. For even n>=2, comparing that integral with 2/n gives
absolute error at most 1/(n(n-1))<=2/n^2. For odd n the interval is
from n to n+2, and 0<=2/n-w(n)<=2/n^2. Consequently, for every subset A
and every finite cutoff X,

\[
 \left|\sum_{n\le X,n\in A}w(n)
          -2\sum_{n\le X,n\in A}\frac1n\right|
 \le 2\sum_{n\ge1}\frac1{n^2}\le4.               \tag{4}
\]

This is a uniform bounded additive correction, not just a comparison of
growth orders. Paper C's source reciprocal mass is therefore retained.

For uniqueness, let v be any real-valued function conserving every even
fibre, with n*v(n)->2. Fix m>=2 and let A_d be its d-th complete even
inverse generation. Iterating conservation gives sums of v and w equal to
v(m) and w(m). Every n in A_d satisfies n>=m^(2^d), while v(n)/w(n)->1.
For any epsilon>0 and all sufficiently large d,

\[
 |v(m)-w(m)|\le\sum_{n\in A_d}|v(n)-w(n)|
                  \le\epsilon\sum_{n\in A_d}w(n)=\epsilon w(m).
\]

Hence v(m)=w(m); at m=1 conservation forces v(1)=v(2)=w(1).
This also proves uniqueness with any prescribed finite limit n*v(n)->c,
the solution being (c/2)*w(n).

### 3. Exact transfer and the size variable

Parity and the even code identity H(n)=2H(J(n)) give the set identity

\[
 \{n\ge1:H(n)\in2B\}
     =\coprod_{m\ge1:H(m)\in B} E(m).              \tag{5}
\]

Multiplication by two is injective in the 2-adic integers, so both
directions hold. Applying (1) to (5) proves (2), including infinite masses.
In particular W(q):=nu({q}) satisfies W(2q)=W(q); finiteness of W(q) is
not assumed or proved.

Below X, the fibres for m<M are complete, the fibre for m=M is partial,
and no larger target has an even child below X. This proves (3). Explicitly,
if a=M^2+(M mod 2) and z=2*floor(X/2), then

\[
 b_X(M)=
 \begin{cases}\log((z+1)/(a-1)),&z\ge a,\\0,&z<a.\end{cases}
\]

In particular nu_(M-1)(B)<=nu_X(2B)<=nu_M(B). The source size scale has
not disappeared: it is carried by X, which becomes approximately sqrt(X)
after following one coded even step backwards in this formula.

For each finite precision d, (3) applies exactly to a residue cylinder
B={q:q=a mod 2^d}; its double is the cylinder 2a mod 2^(d+1). This provides
finite, terminating computations without assuming anything about infinite
Juggler trajectories.

The whole family X->nu_X retains the source multiplicities: the increment
nu_X(B)-nu_(X-1)(B) is w(X) if H(X) is in B and zero otherwise. A single
uncut atom weight need not recover its number of sources or their heights.

There is an equally explicit answer for raw multiplicity. Set
N_X(B)=#{1<=n<=X:H(n) in B}. Since E(m) has m+1-(m mod 2) members,

\[
 N_X(2B)=\sum_{m<M,H(m)\in B}\bigl(m+1-(m\bmod2)\bigr)
       +\mathbf1_{H(M)\in B}\,\#\{n\in E(M):n\le X\}. \tag{6}
\]

Thus predecessor multiplicity depends on a first moment of the original
target heights, with the displayed parity correction. Knowing just the
number of targets at code q is insufficient. The count identity is the
ordinary fibre cardinality formula transported through H; it is not
claimed as a separate new theorem. The special weight w is what turns
that height-dependent reproduction into exact conservation.

As a normalization check, paired consecutive odd/even integers give

\[
 \sum_{n\le X}w(n)=
 \begin{cases}2\log(X+1),&X\text{ even},\\
 \log(X(X+2)),&X\text{ odd}.\end{cases}
\]

Thus total mass grows like 2*log(X). Conservation of the unnormalized
measure does not imply conservation of probability after changing cutoffs.
These laws also hold with sources restricted to any full fate class A:
the proof uses n in A iff J(n) in A. Such a restricted measure may need
the fate label in addition to the code; H alone is not assumed to recover it.

### 4. A concrete forest: why ordinary Collatz weights are different

Take A_0={2}, A_(d+1)=the union of E(m) over m in A_d. The generations are
disjoint: a positive even Juggler step strictly decreases its argument,
and after reaching 2 the next value is the odd fixed point 1. Every member
of A_d has H(n)=2^(d+1), and each generation has total weight log(3).

| d | Number of sources | Smallest | Largest | Common code | Total weight |
|---|---:|---:|---:|---:|---|
| 0 | 1 | 2 | 2 | 2 | log(3) |
| 1 | 3 | 4 | 8 | 4 | log(3) |
| 2 | 21 | 16 | 80 | 8 | log(3) |
| 3 | 1063 | 256 | 6560 | 16 | log(3) |

For every d, w(A_d)=log(3), and every source lies between 2^(2^d) and
3^(2^d), with the upper bound strict. The first four counts are finite
computations; the mass, code, disjointness, and size statements hold at
all depths by induction. These are contributions to full code fibres,
not assertions that the table lists all starts with those codes.

It follows that nu({2^(d+1)})>=log(3) for every d. Ordinary reciprocal
mass assigns the integer code 2^(d+1) only 2^(-d-1). There is therefore
no finite constant K with nu({q})<=K/q for every positive integer q.
This is an explicit unbounded distortion, even on integral minus codes;
it does not rely on hypothetical divergent Juggler trajectories.

## Experiments

Runner: `python -m research.juggler_sequence.code_mass_transport`.
All mass equalities are checked as products of exact rational numbers,
without logarithmic floating-point tolerances:

- full fibre products for every target 1..1000;
- 7936 coded-cutoff cylinder identities, X=1..256 and d=0..4;
- the complete first four even generations of 2.

The 21 tests in
[test_code_mass_transport.py](../../tests/research/juggler_sequence/test_code_mass_transport.py)
also obtain fibres independently from the forward Juggler map, check codes
using forward signed Collatz parities, and include empty/partial/full cutoff
boundaries. Finite checks corroborate, but do not replace, the written proofs.

Validation context: the selected mathematical, document-link, dossier, and
ledger checks passed. After refreshing the concurrently changing branch
index, all 17 branch-index/negative-knowledge tests passed. The earlier broad
integration run had 136 passes, 15 skips, and two failures from concurrent
work: the then-unregistered polynomial-dual dossier and Paper E's changing
release-input inventory. The former was subsequently registered by that
work; the Paper E publication gate was not revalidated in this phase.

## Conjectures

None introduced. Neither universal termination nor a pressure bound is a
consequence of this conservation law.

## Counterexamples

The forest above rules out comparison with ordinary reciprocal code weights.
There is also no deterministic odd-predecessor production law for an
individual physical target using its code alone: H(16)=H(18)=8, but 16
has no odd Juggler predecessor whereas 18 has predecessor 7. Odd-source
J is strictly increasing, so this is a complete inverse check. The witness
is retained in the probe tests. It does not exclude an aggregate estimate
over the full coded fibre; it shows what an estimate must average over.

For clarity, if g(q)=(2q+1)/3 is the odd inverse branch of C_-, the full
coded pushforward satisfies

\[
 (C_-)_*\nu(B)=\nu(2B)+\nu(g(B))=\nu(B)+\nu(g(B)).
\]

Only the even contribution is exactly conserved. This is not a finite
invariant probability for the full Collatz map, and it supplies no bound
on the extra odd contribution. The earlier tilted-mass obstruction in
[negative knowledge](../negative_knowledge.md) remains in force.

## Formalization

No new Lean module. The code/parity inputs already compile in
[CollatzPadic.lean](../../formal/Problems/Juggler/CollatzPadic.lean).
The new logarithmic weight, uniqueness, and measure/cutoff conclusions
are written proofs only. A full matching formalization is deferred; the
finite rational checks do not justify a Lean-verified label.

## Results

- `J-even-fibre-exact-log-weight`: (1), reciprocal comparison (4), uniqueness.
- `J-code-weight-cutoff-transport`: (2), (3), the all-depth even forest, and
  failure of a uniform ordinary reciprocal-weight comparison.

## Open questions

Does the distribution of original heights within coded fibres permit a
quantitative odd-predecessor mass estimate that is unavailable from code
values alone? No bound of that kind is supplied here.

## Decision

**PROMOTE** the exact normalized weight and its source-cutoff transport law.
They answer where weighted multiplicity is retained, with a concrete
distinction from ordinary Collatz mass. This closes the bounded phase.
The single best next question is the height-resolved odd-predecessor estimate
stated above; it is not automatically opened.

## Publication assessment

Status: **STRUCTURAL**. An elementary exact refinement suitable for the
research record and possible later review. No manuscript change, priority
claim, termination improvement, or new paper is asserted.
