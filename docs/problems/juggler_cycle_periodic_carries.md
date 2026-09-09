# Periodic return carries and a wider excluded cubic-height strip

Status: **PROMOTE** the scoped periodic height restriction.
Authorized continuation, 9 September 2026.

**A Juggler cycle with minimum \(m\ge7\) and maximum \(M<m^3\) must satisfy**
\[
\boxed{M<m^3-m^{15/8}.}
\]
Equivalently, a periodic threshold cycle in the complementary top strip
must have a wrong-parity state. A sharper integer ceiling is proved below.
This does not exclude the remaining cubic-height region or taller cycles,
and global no-cycle remains open.

## Problem

The user authorized the next question after the
[fixed-residue obstruction](juggler_cycle_guard_residues.md):
can exact periodicity force a wrong-parity carry in the joint OE/OOE
first-return partition? The analysis must retain the complete periodic
set, rather than reuse isolated blocks as counterexamples to periodicity.

## Exact statement

For an actual Juggler cycle with minimum \(m\ge5\), maximum \(M<m^3\),
let
\[
q=O(m),\qquad t=E(M),\qquad z=Q(m^{9/8}),
\]
where \(O(x)=\operatorname{isqrt}(x^3)\),
\(E(x)=\operatorname{isqrt}(x)\), and \(Q\) is the largest odd integer
not exceeding its argument. Then
\[
t^3\le[z(z-2)]^2-2,\qquad M\le(t+1)^2-2.
\tag{S}
\]
If \(T\) is the largest positive odd integer satisfying
\(T^3\le[z(z-2)]^2-2\), then \(M\le(T+1)^2-2\).
The smooth consequences are
\[
t<m^{3/2}-\frac43m^{3/8},
\qquad M<m^3-m^{15/8}\quad(m\ge7).
\tag{H}
\]
The second inequality can be checked without fractional powers as
\((m^3-M)^8>m^{15}\), with \(m^3-M>0\).

Every actual cycle with \(M<m^3\) is a cycle of the threshold map
\(S_m\): an even source must be at least \(m^2\), since its image is
at least \(m\); an odd source at least \(m^2\) would map to at least
\(m^3\), contradicting the height hypothesis. Thus the normalized
threshold proof below applies to every cycle in the stated class.

## Current literature

**Internal extension; external priority not claimed.**
[Paper A](../theory/juggler_finite_dynamics_note.md) supplies the
cubic-band order and earlier extrema anchors. The
[Euclidean-induction dossier](juggler_cycle_cubic_induction.md)
supplies the rank return permutation and conditional odd-projected
OOE endpoint identity. The new consequence combines an ordered
return boundary with both exact parity faces of the OE square cells.
It strengthens the earlier minimum-only extrema ceiling; it is not
claimed to dominate every period-dependent grid estimate.
No external theorem or literature novelty claim is used.

## Branch budget

Mathematical target: Does exact periodicity force at least one wrong-parity carry in the OOE/OE first-return partition of every threshold cycle?

Novelty hypothesis: A permutation of the complete retained periodic set imposes joint absolute carry constraints unavailable for isolated return blocks.

Falsifier: The derived sum/product/valuation is an endpoint telescoping identity, the original expanded guard, or known floor finance; open-block residue collisions alone do not answer this periodic question.

Already killed by?: Fixed residue summaries, endpoint-only guards, mismatch energy bookkeeping, bounded additive pure-power substitution, generic local cells and finance reformulations. The present target keeps all exact closed-orbit constraints and tests whether they supply a new global identity or incompatibility.

Existing machinery: Cubic threshold cycles and sorted rank rotation, Euclidean return towers, exact OE/OOE guards, the exact-remainder repair, and seven archived threshold cycles.

Maximum Phase-0 scope: Prove or correct the return partition, derive its exact cyclic carry constraints, and audit whether they imply a parity contradiction. Reuse only the seven literal archived cycles; no cycle/source census, larger trajectory cap or descent floor. Implementation or Lean packaging only after a useful mathematical statement survives.

Promotion criterion: A proved wrong-parity intersection for a new class of exact periodic sets, or another nontrivial cycle-specific restriction beyond the original guard and floor finance.

Stop criterion: Retain any precise reduction or obstruction, state the missing arithmetic implication, and decide PROMOTE/PARK/CLOSE without automatically opening another branch.

Post-proof verification scope, fixed before implementation: the same seven archived cycles, and exact evaluation of the necessary integer ceilings at five previously used starts m=9,6569,390633,214358889,10828567056280809. These five evaluations do not run trajectories or assert periodicity; they compare the old and new symbolic ceilings. No new census.


## Balanced-ternary formulation

The exact cells, carries and ceiling certificates are integer relations.
Their validity is independent of integer representation.

## Why BT may be relevant

No representation advantage is used or claimed.

## Candidate operations / invariants

The successful quantity is the gap between two ordered return images:
the image of the minimum base under OOE and that of the maximum base
under OE. On a compatible cycle these are distinct odd integers,
so their gap is at least two. Propagating this gap through the actual
OE cells bounds the maximum retained base and then the original maximum.

The tested aggregate carry sums and products remain identities; they
do not make the permitted periodic set empty. Their limitation is
recorded after the proof.

## Experiments

The [exact verifier](../../src/research/juggler_sequence/cycle_periodic_carries.py)
replays [summary.json](../../data/research/juggler/cycle_periodic_carries/summary.json):

    python -m research.juggler_sequence.cycle_periodic_carries

The [tests](../../tests/research/juggler_sequence/test_cycle_periodic_carries.py)
check normalized thresholds, the exact retained set, complete disjoint
return towers, rank adjacency, all square cells and hypothesis-sensitive
parity bounds. They reuse only the seven archived threshold cycles.
None is presented as an actual Juggler cycle.

Five additional arithmetic evaluations compare conditional ceilings at
the previously used starts \(9,6569,390633,214358889,10828567056280809\).
They do not run trajectories or assert periodicity. For example, at
hypothetical minimum 9, the previous extrema ceiling is 674 and the
new exact ceiling is 482. At minimum 6569 the ceilings are
283462537742 and 283388004962. The quantified result follows from
the proof, not from these controls.

No cycle/source census, orbit extension, descent-floor campaign or
period-bound computation is performed.

## Conjectures

No new conjecture file is opened. Wrong-parity intersection throughout
the remaining threshold region and global no-cycle are unproved.

## Counterexamples

The old exact \(S_9\) cycle with minimum 9 and maximum 374 passes the
new local seam conditions: \(Y=\{9,11,14,19\}\), \(q=27\),
\(t=19\), \(z=11\), \(w=9\), and
\[
t^3=6859\le[11(11-2)]^2-2=9799.
\]
It still has wrong parities elsewhere, including the even retained base
14. Thus satisfying the new extrema consequences does not establish
all guards or make the exact threshold periodic set empty.

The cycles at minima 3 and 4 each have one OOE return fixing the base.
They are explicitly outside the \(m\ge5\) strict-growth argument.

## Formalization

**J-cycle-periodic-return-height-strip, EXACT — HUMAN PROOF.**
This is an AI-assisted written proof, separately audited for the return
section, endpoint assumptions, exact integer faces and power-bound constants.
The repository tag names its written-proof tier; independent human review
and new Lean verification are not claimed.

## Results

### A periodic return boundary excludes an additional height strip

#### 1. Uniform run bound for the threshold map

Write O(x)=isqrt(x^3), E(x)=isqrt(x). For every integer x>=3,

\[
O^2(x)\ge x^2.
\tag{R1}
\]

For x>=4 put k=isqrt(x)>=2. Then

    x <= k^2+2k <= k^3,

because k^3-k^2-2k=k(k-2)(k+1)>=0. Also O(x)>=kx since
(kx)^2<=x^3. Hence O(x)^3>=k^3x^3>=x^4, proving R1. At x=3,
the exact calculation O^2(3)=11>=9 completes the proof.

For S_b on [b,b^3), b>=3, two consecutive O steps therefore land
at or above b^2, so a third consecutive O label is impossible.
Every E step lands below b^2, because sqrt(b^3)<b^2. Thus there
are no EE blocks either. These are facts about the whole threshold
domain, without assuming actual source parity.

One further elementary estimate is useful:

\[
F_{OOE}(x)\ge x+1\qquad(x\ge5).
\tag{R2}
\]

For x>=9, k=isqrt(x)>=3 gives k^3>=x+12, so
O(x)^3>=(x+12)x^3>(x+1)^4. The last difference is
8x^3-6x^2-4x-1>0. Taking fourth roots proves R2. The remaining
x=5,6,7,8 use O(x)=11,14,18,22 and respectively
11^3>=6^4, 14^3>=7^4, 18^3>=8^4, 22^3>=9^4.
In contrast F_OOE(3)=3 and F_OOE(4)=4; those exceptions must not
be included in R2.

#### 2. Normalize a periodic threshold set by its actual minimum

Let C be a primitive S_b cycle, with minimum m and maximum M.
Its O-sources are below b^2<=m^2. Every E-source x satisfies
E(x)>=m, hence x>=m^2. Thus the same cycle follows S_m, with

\[
M<b^3\le m^3.
\tag{N1}
\]

No source parity has been assumed. The minimum is an O-source,
since an E step would lower it; the maximum is an E-source,
since an O step would raise it. Put

\[
q=O(m),\qquad Y=C\cap[m,q),\qquad t=E(M).
\tag{N2}
\]

All O-images are at least q. All E-images are at most
isqrt(m^3-1)<=q. Equality q is impossible on the cycle: q is
already the image of m under O, and the cycle permutation is
injective, while an E-source differs from m. Consequently the
E-images are exactly Y, and t=max(Y). In particular q is on C
but is excluded from Y.

Every base in Y is below q<=m^(3/2)<m^2, so begins with O.
An O-image cannot return to Y; an E-image always returns to Y.
R1 and the absence of EE therefore show that every first return
to Y is exactly OE or OOE.

This is a statement about cycle-selected points. Replacing Y by a
larger interval without checking the cut can change the return words.
For example [3,ceil(3^(3/2)))=[3,6) contains the step 3->5, giving
an O first return, rather than OOE. The correct cut in N2 is the
exact O(m), and the proof above uses periodic-set injectivity.

#### 3. Proper return partition and its extrema

On Y the exact return word is

\[
OOE\quad\text{if }x^3<m^4,
\qquad OE\quad\text{if }x^3\ge m^4.
\tag{N3}
\]

Indeed this compares O(x) with m^2, using the exact integer root
cell. It gives an absolute numerical cut on the retained finite
set, not merely a formal word partition.

Let o,e be the original lower/upper branch counts. The positive
total exponent implies o>e, while the run bounds give o<=2e.
If m>=5, equality o=2e is impossible: every return would be OOE,
contrary to R2 on the finite invariant Y. Therefore, putting

\[
a=o-e>0,\qquad \beta=2e-o>0,\qquad e=a+\beta,
\]

the return map on the e sorted bases Y_0=m<...<Y_(e-1)=t is

\[
Y_i\longmapsto Y_{(i+\beta)\bmod e},
\]

with OOE on i<a and OE on i>=a. This is the two subtractive
steps of the proved rank induction. In particular

\[
z:=F_{OOE}(m)=Y_\beta,\qquad
w:=F_{OE}(t)=Y_{\beta-1}.
\tag{N4}
\]

The two extremal return images are adjacent in the sorted base.
The maximum base uses OE also follows directly from R2: OOE
would return t to a value greater than the maximum base.

#### 4. Exact carry anchors for a parity-compatible cycle

Now assume C is an actual Juggler cycle with m>=5 and M<m^3.
All points of Y, and q=O(m), are odd. All upper states are even.
Writing p_0=O(q), z=E(p_0), p=O(t), and w=E(p), the minimum
and maximum return blocks have the exact anchor data

\[
m\overset O\longmapsto q\overset O\longmapsto p_0
\overset E\longmapsto z,
\qquad
t\overset O\longmapsto p\overset E\longmapsto w.
\]

Here m,q,t,z,w are odd, and p_0,p,M are even. Consequently

* m^3-q^2 is an even integer in [0,2q];
* q^3-p_0^2 and t^3-p^2 are positive odd square remainders;
* p_0-z^2, p-w^2 and M-t^2 are odd displacements in
  [1,2z-1], [1,2w-1] and [1,2t-1], respectively.

These are actual coupled cells, not independently chosen carry
variables. The short-return endpoint identity gives

\[
z=Q(m^{9/8}),
\tag{A1}
\]

where Q is the largest odd integer at most its argument. Its use
here is justified by the true odd endpoint z; it does not supply
the hidden guards independently.

#### 5. A sharper exact return seam

By N4, w and z are adjacent odd bases. Therefore

\[
w\le z-2.
\tag{A2}
\]

The exact OE cell at the maximum base first gives
t^3<(w+1)^4<=(z-1)^4. Keeping both actual parity faces gives
a stronger bound. Since p is even and w is odd,

\[
p\le(w+1)^2-2\le(z-1)^2-2.
\]

Since t and p+1 are odd, the strict odd-source square cell gives

\[
\boxed{t^3\le(p+1)^2-2
\le[z(z-2)]^2-2.}
\tag{A3}
\]

The maximum M is even with E(M)=t odd, so also

\[
\boxed{M\le(t+1)^2-2.}
\tag{A4}
\]

For an exact integer ceiling, let T be the largest positive odd
integer with T^3<=[z(z-2)]^2-2. A3-A4 imply

\[
M\le(T+1)^2-2,
\qquad z=Q(m^{9/8}).
\tag{A5}
\]

This is determined by the actual minimum. It is a further necessary
extrema restriction, not a proof that the permitted interval is empty.

#### 6. Explicit power exclusion strip

For z>=3 the positive quantity
g(z)=z^(4/3)-(4/3)z^(1/3) satisfies

\[
g(z)^3-[z(z-2)]^2
=\frac4{27}z(9z-16)>0.
\]

Thus A3 gives t<g(z). Since
g'(z)=4(3z-1)/(9z^(2/3))>0 for z>=1, A1 yields

\[
\boxed{t<m^{3/2}-\frac43m^{3/8}.}
\tag{A6}
\]

A particularly simple corollary is

\[
\boxed{M<m^3-m^{15/8}\qquad(m\ge7).}
\tag{A7}
\]

To verify its constants, set r=m^(3/8)>=2 and A=m^(3/2)=r^4.
A6 in particular gives t<A-r. Therefore

    M <= (t+1)^2-2 < (A-r+1)^2-2.

The remaining difference is exactly

\[
[A^2-Ar]-[(A-r+1)^2-2]
=(r-2)(r^4-r)+1\ge1.
\]

This proves A7. Positivity of the quantities being squared follows
from A>=r and t>=m>1. The condition r>=2 follows already from
7^3>2^8.

The exponent 15/8 excludes a wider terminal strip of the cubic
height band than the earlier bound based only on q and t<=q-2.
The comparison is with the earlier minimum-only extrema anchor, not
with every available period-dependent grid estimate. It does not
exclude all maxima below m^3, the tall regime, or any new period.



### Scope audit — carry bookkeeping alone does not force a failure

For a return permutation \(y_i=x_{\sigma(i)}\), with E peaks \(v_i\)
and displacements \(c_i=v_i-y_i^2\), periodicity gives
\[
\sum_i c_i=\sum_i v_i-\sum_i x_i^2.
\]
If all retained bases are odd and all peaks are even, its parity is
exactly the parity of the number of bases, as already required by all
\(c_i\) being odd. The sum is not zero: the peak set does not equal
the squared-base set.

Endpoint permutation and E cells alone admit an explicit partial model:
for any distinct odd bases at least 3 and any permutation, set
\(v_i=x_{\sigma(i)}^2+1\). Every E cell and E-source parity then holds
with \(c_i=1\). The O-prefix equations have been omitted, so this is
not a Juggler cycle or a counterexample to the full periodicity question.
It isolates why the joint source-to-peak constraints are essential.

Multiplying all exact O and E cells gives the existing product-of-defects
identities. Their positive factors are compatible with larger hidden
OOE states. Without a new estimate, these products return to the
already recorded floor-finance relation. No contradiction from those
identities is promoted here.

For odd retained bases the complete guard remains precisely: every
first OOE remainder is even and every final E displacement is odd.
The new theorem forces a failure of at least one of those tests only
when the maximum lies in the excluded strip. The seven controls have
carry sums \(2,6,53,51,649,362,361\); only the first has all retained
bases odd, and its even displacement 2 exposes its wrong E source.

## Open questions

Cycles with \(M<m^3-m^{15/8}\), and cycles with \(M\ge m^3\), are
not excluded by this result. Even in the first region, all the
simultaneous absolute O-prefix and E-suffix cells must still be used
to prove a uniform wrong-parity intersection.

Successive induced return boundaries have further parity gaps, but
their propagation through growing return words is not established by
the short-word argument here. A growing list of such inequalities or
the old period-dependent spacing bound is not automatically a new
uniform obstruction.

## Decision

**PROMOTE** the scoped return-boundary theorem and its exact and smooth
height ceilings. It proves wrong-parity intersection for the specified
top strip of threshold cycles. It does not promote a global no-cycle
claim or a new numerical period bound.

The one best next question is: **can the parity gaps at successive
Euclidean return boundaries be propagated with a bound uniform in
the return-word length, strong enough to contradict the final fixed
return?** This requires a new propagation estimate; repeating the
one-boundary proof or restating the full guard does not supply it.

## Publication assessment

Status: **STRUCTURAL**. This dossier is the canonical written source
for the new result and its controls. Paper A, its compiled Lean claims
and its certified period bound are unchanged by this gate.
