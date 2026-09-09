# First-image parity: the sharp neighbor-distance exponent

## Problem

Determine how far an odd source must move to find another odd source
whose first Juggler image has the opposite parity. This is a spatial
first-step question, not an orbit-length or conditional-count question.

## Exact statement

Write \(F(x)=\lfloor x^{3/2}\rfloor\), and, for a positive odd integer
\(n\), let
\[
D(n)=\min\{|u-n|:u\ge1\text{ odd},\ F(u)\not\equiv F(n)\pmod2\}.
\]
The upper bound below ensures this minimum exists in its stated range.
On odd sources \(F\) is the actual Juggler map.

**Theorem (`J-parity-neighbor-scale`, EXACT — HUMAN PROOF).**

1. For every odd integer \(n\ge4096\), put
   \(L=\lceil n^{1/4}\rceil\). Both parities occur among
   \[
   F(n),F(n+2),\ldots,F(n+8L).
   \tag{U}
   \]
   These are \(4L+1\) consecutive odd sources. In particular, an odd
   \(u>n\) exists with opposite image parity and \(u-n\le8L\), so
   \(D(n)\le8\lceil n^{1/4}\rceil\).
2. Infinitely many odd nonsquare \(n\), themselves having an odd
   nonsquare image \(F(n)\), satisfy
   \[
   D(n)\ge\tfrac14 n^{1/4}.
   \tag{L}
   \]

Thus \(1/4\) is the optimal exponent for worst-case pointwise
availability. The constants are not claimed optimal. The theorem
does not construct an injective or bounded-multiplicity pairing, nor
does it preserve any preceding orbit prefix.

## Current literature

**Extended within the repository; external priority not claimed.**
[Parity complexity, Results 2](juggler_parity_complexity.md) already
uses Taylor expansion and joint equidistribution to realize every
interior rotation word. In particular, arbitrarily long constant
first-image parity blocks are already a qualitative consequence.
The finite length-52 block in
[parity discrepancy transfer](juggler_parity_discrepancy_transfer.md)
is an illustration, not by itself an asymptotic counterexample for
every unspecified discrepancy constant. The explicit unbounded family
below supplies such a counterexample directly.

The additional result here is the matching quantitative upper and
lower distance scale, with an elementary proof and an explicit
nonsquare family. No external exponential-sum or equidistribution
theorem is imported into this proof. No new literature id is required.

## Branch budget

- **Target:** determine the distance needed to find an odd source
  with opposite first-image parity.
- **Novelty hypothesis:** monotone slopes and the floor-error bound
  give an explicit upper bound matching the near-square clusters.
- **Falsifier:** a gap in the slope argument or a longer monochromatic
  source block than (U) permits.
- **Already killed by?:** qualitative long blocks are already in
  parity complexity; the explicit matching distance scale is the test.
  The closed discrepancy-transfer route is not reopened.
- **Existing machinery:** convexity, exact floors, and cube–square
  identities; the parent pressure dossier's sparse-source bound.
- **Maximum Phase-0 scope:** prove and check the first-step bound;
  no census, new runtime framework, or deep-prefix assertion.
- **Promotion criterion:** matching quantitative bounds with exact scope.
- **Stop criterion:** record the first-step theorem without extrapolating
  to a prefix-preserving pairing or a termination estimate.

**Follow-up budget (9 September 2026).** Test one direct lift of (U)
through an odd image, and price a bounded-multiplicity assignment on
the same finite prefix-selected source set. A source-level construction
with an actual quantitative count is the promotion gate. A missing
odd preimage or only a renamed split inequality closes this shortcut.
No large census, new framework, or independent sparse-image campaign.

## Balanced-ternary formulation

The sources and images are ordinary integers and may be represented
canonically in balanced ternary. The proof does not use their digits.

## Why BT may be relevant

No balanced-ternary advantage is needed for this theorem. Keeping it
in the Juggler application avoids adding problem-specific assumptions
to the representation-independent core.

## Candidate operations / invariants

The useful invariant is the strictly increasing smooth increment of
\((n+2x)^{3/2}\). A monochromatic floor sequence forces its integer
increments into one parity class. When the smooth increments move
by less than two, the integer increments have at most one switch.
Convexity then contradicts a long affine stretch of floors.

## Experiments

No runtime probe or data census was introduced. Exact integer
regressions in
[test_parity_neighbor_scale.py](../../tests/research/juggler_sequence/test_parity_neighbor_scale.py)
check the fourth-root rounding, curvature constants, both parities
on selected upper-bound intervals, and the lower family for
\(c=37,101,1009,10007\). One follow-up regression checks the isolated
target window in Results 4, including the nonsquare OO source
\(n=66053\). Finite tests check formulas and endpoints;
the proofs below establish the quantified statements.

## Conjectures

None added. The growing-depth pressure estimate remains open in
[pressure external average](juggler_pressure_external_average.md).

## Counterexamples

The family in (L) refutes a universal \(o(n^{1/4})\) distance bound,
even if square sources and square first images are excluded. Its
unbounded constant-parity blocks also refute a translation-uniform
discrepancy bound \(C|I|^\alpha\), \(\alpha<1\), on all intervals of
the odd-source index, for every fixed \(C\). It does not refute
estimates on sufficiently long scale-dependent intervals, adaptive
longer-distance assignments, or aggregate pressure estimates.

## Formalization

No Lean module was added. The tag is **EXACT — HUMAN PROOF**, not
Lean verified. The tests use integer square roots only and are not
a substitute for the proof.

## Results

### 1. Uniform upper bound

Fix an odd \(n\ge4096\), set \(L=\lceil n^{1/4}\rceil\) and
\(M=4L\), and suppose that all floors
\(m_j=\lfloor g(j)\rfloor\), \(0\le j\le M\), have the same
parity, where \(g(x)=(n+2x)^{3/2}\).

Writing \(r=n^{1/4}\ge8\), we have \(L\le r+1\),
\(6(r+1)<r^2\), and \(8(r+1)\le r^4\). Consequently
\[
6L<\sqrt n,\qquad 8L\le n.
\tag{1}
\]
Since \(g''(x)=3/\sqrt{n+2x}>0\), the smooth increments
\(s_j=g(j+1)-g(j)\) are strictly increasing. Moreover,
\[
s_{M-1}-s_0\le\frac{3(M-1)}{\sqrt n}
 <\frac{12L}{\sqrt n}<2.
\tag{2}
\]
Put \(e_j=g(j)-m_j\in[0,1)\). The integer increments
\(d_j=m_{j+1}-m_j\) are even and satisfy
\[
|d_j-s_j|=|e_j-e_{j+1}|<1.
\tag{3}
\]
Thus \(d_j\) is the unique even integer within distance less than
one of \(s_j\). If a slope is an odd integer, (3) is already
impossible. Otherwise the disjoint open intervals about the even
integers show that the \(d_j\) are nondecreasing. By (2) they take
at most two adjacent even values: a difference of at least four
would require a slope difference greater than two. They switch at
most once.

Among the \(4L\) increments there is therefore a constant run of
at least \(2L\) increments. Choose exactly \(2L\) of them, starting
at index \(a\). The floors \(m_j\) are affine for
\(a\le j\le a+2L\). Throughout \([0,M]\), (1) gives
\[
g''(x)\ge\frac3{\sqrt{n+8L}}\ge\frac3{\sqrt{2n}}.
\]
Subtracting the quadratic with this constant second derivative
and applying midpoint convexity yields
\[
\frac{g(a)+g(a+2L)}2-g(a+L)
 \ge\frac{3L^2}{2\sqrt{2n}}
 \ge\frac3{2\sqrt2}>1.
\tag{4}
\]
But the affine floors cancel in the same expression, leaving
\((e_a+e_{a+2L})/2-e_{a+L}<1\). This contradiction proves (U).

### 2. Explicit matching lower family

Let \(c\ge1\) and \(t\ge1\) be odd integers with \(t^2\le4c\).
Set \(n=4c^2+t\) and \(m=8c^3+3ct\). Direct expansion gives
\[
n^3-m^2=3c^2t^2+t^3>0,
\]
\[
\begin{aligned}
(m+1)^2-n^3
 &=16c^3+6ct+1-3c^2t^2-t^3\\
 &\ge4c^3+2ct+1>0.
\end{aligned}
\tag{5}
\]
Here \(3c^2t^2\le12c^3\) and \(t^3\le4ct\). Hence
\[
F(4c^2+t)=8c^3+3ct,
\tag{6}
\]
an odd image of an odd source.

Now restrict \(c\) to primes \(c\ge37\). Then
\(3t\le6\sqrt c<c\), so
\(m=c(8c^2+3t)\) is divisible by \(c\) exactly once and is not
a square. Also \(0<t<4c+1\), so \(n\) lies strictly between
\((2c)^2\) and \((2c+1)^2\) and is not a square. No squarefree
claim about \(n\) is made.

There are
\[
M_c=\left\lfloor\sqrt c+\tfrac12\right\rfloor
\]
positive odd offsets satisfying \(t^2\le4c\). They are
\(1,3,\ldots,2M_c-1\). Choose the central source
\[
n_c=4c^2+2\left\lfloor\frac{M_c-1}2\right\rfloor+1.
\]
The nearest odd sources outside this block are at offsets \(-1\)
and \(2M_c+1\). Each is at distance at least \(M_c\) from
\(n_c\). Every odd source within distance less than \(M_c\)
therefore has an odd image, proving \(D(n_c)\ge M_c\).
Finally,
\[
M_c\ge\sqrt c-\tfrac12\ge\tfrac12\sqrt c,
\qquad n_c\le4c^2+2\sqrt c\le9c^2,
\]
so \(M_c\ge n_c^{1/4}/4\). Unboundedness of the primes proves (L).

### 3. The lower family is sparse, not a pressure obstruction

Even without requiring \(c\) prime, let \(W\) be the union of
the positive-offset clusters in (6), with \(c\) odd. If a source
in \(W\) is at most \(2y\), then \(c\le\sqrt{y/2}\).
There are at most \(\sqrt c+1\) offsets for each \(c\), whence,
for \(y\ge1\),
\[
\#(W\cap(y,2y])
 \le\sqrt{y/2}\bigl((y/2)^{1/4}+1\bigr)
 \le2y^{3/4}.
\tag{7}
\]
This is an instance of the existing sparse-source result (B1) in
[pressure external average](juggler_pressure_external_average.md):
the restricted normalized pressure has bounded cumulative mass.
It is not a new obstruction to the aggregate pressure estimate.

### 4. Prefix-pairing follow-up: the direct lift does not iterate

This is a scope check against existing results, not a new counting
theorem or a new named pressure hypothesis.

**The guaranteed target neighbors have no odd pullback.** Let
\(n\ge65536\) be odd, \(m=F(n)\),
\(a=n^{3/8}\ge64\), and \(R=8\lceil m^{1/4}\rceil\le8a+8\).
The existing [image-gap theorem](juggler_hug_flow_depth_two.md),
`J-hug-flow-image-gap`, gives
\[
\min\{F(n)-F(n-2),F(n+2)-F(n)\}
 \ge3\lfloor\sqrt{n-2}\rfloor
 >3\sqrt n-6\ge12a-6>8a+8\ge R.
\tag{8}
\]
Here \(\sqrt{n-2}\ge\sqrt n-1\) and \(n^{1/8}\ge4\).
By monotonicity, the interval \([m-R,m+R]\) contains no other
image of a positive odd source. If \(m\) is odd, every
opposite-image-parity neighbor supplied by (U) at \(m\) is therefore
outside \(F(\{1,3,5,\ldots\})\). It cannot be pulled back even
one odd step. The same obstruction applies at the last inverse edge
of a longer all-odd prefix whose original source is at least 65536.
This is the already-recorded sparse-image transfer obstruction,
now compared with radius \(m^{1/4}\), not a refutation of larger
target windows or direct source-level constructions.

**Multiplicity without a construction is a count in different words.**
Fix the odd sources in \((y,2y]\), \(y>N_0\), of size \(N\), and let \(A_t\) denote
its starts with first \(t\) letters odd. Set
\(C_t=A_{t+1}\), \(E_t=A_t\setminus A_{t+1}\). For an integer
\(K\ge1\), a map \(C_t\to E_t\) with at most \(K\) sources
assigned to each exit exists if and only if
\[
|C_t|\le K|E_t|,
\quad\text{equivalently}\quad
|A_{t+1}|\le\frac K{K+1}|A_t|.
\tag{9}
\]
Necessity is counting; sufficiency assigns the sources to \(K\)
slots per exit. Both sides must remain in the same finite source
window. Allowing arbitrarily remote exits proves no dyadic bound.
With prescribed allowable edges, pointwise neighbor existence is
also insufficient: every subset of continuers needs enough exit
capacity, not just each singleton.

For calibration only, suppose (9) holds at **every** extension level
\(1\le t<d_k\), with \(d_k=19\log_2 k+O(1)\) as in the parent
dossier. Then
\[
|A_{d_k}|/N_k\ll k^{-b_K},\qquad
b_K=19\log_2(1+1/K).
\tag{10}
\]
One controlled level near \(d_k\) gives only one constant factor,
not (10). At the parent's fair optimized tilt, the all-odd
contribution to normalized pressure is at most
\(O(k^{\kappa-b_K})\), \(\kappa=4.89342683035\ldots\).
For \(K=5\), \(b_K=4.99765371084\ldots\), so its cumulative
bound through scale \(H\) is \(O(H^{0.89577311951\ldots})\).
For \(K=6\), the corresponding exponent is
\(1.66797082496\ldots\), above the permitted total-pressure
budget \(1.01952654911\ldots\). Thus five-to-one control at
every depth would suffice for the **all-odd contribution only**.
This is the existing tower-tolerance calculation in
[Tao note §10.4(b)](../theory/juggler_tao_reduction_note.md), not a
new reduction. Other high-odd-count words remain uncontrolled.
No assignment establishing (9) at growing depth was found.

## Open questions

The upper bound only supplies a pointwise choice of a neighbor.
There is no bound on how many starts choose the same neighbor and no
scale-independent positive exit-share estimate. If the original source belongs to
\(O^t\), \(t\ge2\), its first-image-flipping neighbor necessarily
leaves that cylinder: both sources in \(O^t\) would have odd first
images. Here \(O^t\) prescribes oddness of the iterates numbered
\(0,\ldots,t-1\); a prefix-preserving argument would instead have
to flip the next unprescribed image, \(F^t(n)\).
Consequently neither the necessary all-odd count (C3) nor the full
pressure bound (A2) in the parent dossier has been proved.

## Decision

**PROMOTE** the sharp first-step neighbor-distance exponent. The
proof gives a uniform quantitative consequence beyond the already
recorded qualitative long-block result, with matching explicit
lower examples. **PARK** remains the parent arithmetic-pressure
status. No termination estimate, floor increase, paper edit, or
automatic follow-on branch is justified by this lemma.

**Follow-up decision: CLOSE** the direct neighbor-pullback shortcut,
by (8). Unrestricted assignment language in (9) is a reformulation,
not an arithmetic mechanism. Neither a larger-distance matching nor
the actual count is refuted. The promoted first-step theorem and
the parked pressure estimate retain their statuses; no new named
theorem or conjecture is introduced by this follow-up.

**Best next question:** can the existing necessary all-odd count
(C3) be bounded directly on the original source integers, without
replacing their selected images by an interval?

## Publication assessment

Status: `THEOREM`. An elementary standalone local-scale theorem;
external priority is unverified. Not a paper-level termination claim.
