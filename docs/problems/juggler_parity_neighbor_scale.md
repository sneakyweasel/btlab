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
alone does not construct an injective or bounded-multiplicity pairing,
nor does it preserve a preceding orbit prefix. Results 5 adds a separate
block pairing using classical discrepancy estimates and states precisely
its fixed-prefix scope.

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

**Fifth-letter resolution audit (10 September 2026).**

Mathematical target: can the source-block pairing at prefix length four
be justified by resolving its final floor with the mode range of the
existing Paper B theorem?

Novelty hypothesis: a controlled last-floor remainder might allow the
new phase to be treated using the already-controlled coordinates.

Falsifier: uniform resolution of that correction requires frequencies
outside the available range, or a new unestimated outer phase remains.

Already killed by?: direct substitution of the even-root coordinate for
the odd operation is closed. This is a quantitative check of the
last-floor approximation and resolution cost, not a claim to reopen the
closed general composition or completed-sum methods.

Existing machinery: exact odd-branch floors, the elementary one-signed
Taylor remainder, Paper B's fixed-mode cutoff, and the three previously
tested short source blocks.

Maximum Phase-0 scope: one last-floor expansion and frequency-budget
check, plus the first uncovered split on those same three blocks.
No new source windows, deeper scan, formalization, or paper edits.

Promotion criterion: a proved exit-capacity bound on actual sources
with useful depth dependence.

Stop criterion: CLOSE this transfer if it needs unprovided frequencies
or a new nested phase; retain the actual counting problem as PARK.


**Block-pairing follow-up (10 September 2026).**

Mathematical target: construct a source-level pairing with multiplicity
at most two and a proved displacement bound; identify its valid prefix
depth range.

Novelty hypothesis: local parity balance on whole blocks supplies enough
distinct exits to repair the capacity missing from pointwise neighbors.

Falsifier: the arithmetic input supplies no exit-capacity bound, or its
scope ends at fixed depth.

Already killed by?: nearest target pullback and unrestricted matching
language are closed. This test supplies a specific block construction
and proves its first-step capacity using curvature. It does not assume
the count it aims to establish at growing depth.

Existing machinery: exact floors; the classical second-derivative bound
and Erdos--Turan inequality; the explicit sharp neighbor-distance family;
the current Paper B fixed-depth corollaries.

Maximum Phase-0 scope: one block pairing, its first-step local balance
proof, its fixed-prefix extension from available counts, and nine small
literal block controls. No full dyadic census or orbit search.

Promotion criterion: uniform capacity on the actual selected source
sets at growing depth.

Stop criterion: retain scoped fixed-depth corollaries and PARK the
termination attack if the first uncontrolled prefix still needs a new
arithmetic estimate. Do not auto-open another pairing rule.


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


### 5. Block pairings: bounded multiplicity at fixed depth


For sufficiently large \(y\), let \(S_y\) be the odd integers in
\((y,2y]\), and let \(A_t(y)\) consist of starts whose first \(t\)
Juggler states are odd. Define
\[
C_t=A_{t+1},\qquad E_t=A_t\setminus A_{t+1}.
\]
An exit here means an exit from the all-odd prefix, not termination.

Divide the consecutive odd sources in \(S_y\) into blocks of \(B\)
points. Merge a final remainder into the preceding full block.
When \(|S_y|\ge B\), every resulting block has between \(B\) and
\(2B-1\) points.

In a block \(I\), sort its continuers and exits:
\[
c_1<\cdots<c_p,\qquad e_1<\cdots<e_q.
\]
Whenever \(p\le2q\), define
\[
\boxed{\Phi_t(c_i)=e_{\lceil i/2\rceil}.}
\]
Each target has at most two assigned sources, both remain in the
same dyadic source window, and the first \(t\) odd letters are preserved.
The next letter changes from odd to even. Displacement is less
than \(4B\). The arithmetic obligation is to prove \(p\le2q\)
on every block; the assignment alone proves no counting estimate.

**First-step capacity from curvature.**

Take any block of \(M\ge2\) consecutive odd sources
\(a,a+2,\ldots,a+2(M-1)\) inside \((y,2y]\), and let \(E\) count
those with even first image. For a positive integer \(h\), set
\[
f_h(x)=\frac h2(a+2x)^{3/2},\qquad
f_h''(x)=\frac{3h}{2\sqrt{a+2x}}\asymp h y^{-1/2}.
\]
The classical second-derivative estimate gives
\[
\left|\sum_{j=0}^{M-1}e(f_h(j))\right|
\ll M h^{1/2}y^{-1/4}+h^{-1/2}y^{1/4},
\]
with an absolute constant, since the curvature ratio is bounded
by \(\sqrt2\). This is an application of
[Montgomery's Theorem 17.5](https://public.websites.umich.edu/~hlm/math775/ch17.pdf).

The image \(\lfloor n^{3/2}\rfloor\) is even precisely when
\(\{n^{3/2}/2\}\in[0,1/2)\). Applying the one-dimensional
Erdős--Turán inequality at cutoff \(H\) therefore gives
\[
\left|E-\frac M2\right|
\ll \frac M H+M y^{-1/4}H^{1/2}+y^{1/4}.
\]
The two frequency sums use
\(\sum_{h\le H}h^{-1/2}\ll H^{1/2}\) and
\(\sum_{h\le H}h^{-3/2}\ll1\). Half-open endpoints retain
integer and half-integer phases exactly.
The discrepancy inequality is in
[Kuipers–Niederreiter, Chapter 2, Theorem 2.5](https://web.maths.unsw.edu.au/~josefdick/preprints/KuipersNied_book.pdf).

With \(H=\lfloor y^{1/6}\rfloor\), this becomes
\[
\boxed{\left|E-\frac M2\right|
\ll M y^{-1/6}+y^{1/4}.}
\tag{P1}
\]
Consequently there are absolute constants \(A,y_0\) such that
for all \(y\ge y_0\) and every such block with \(M\ge A y^{1/4}\),
\[
\frac{3M}{8}\le E\le\frac{5M}{8}.
\tag{P2}
\]
Indeed, if the implicit constant in (P1) is \(K\), choose
\(A\ge16K\), then \(y_0\) so that \(K y^{-1/6}\le1/16\).
The two errors total at most \(M/8\).

Choose \(B=\lceil A y^{1/4}\rceil\). Equation (P2) bounds the
continuer-to-exit ratio by \(5/3<2\) in every block, including
the merged final block. The displayed pairing therefore exists
on **all** first-step continuers in \(S_y\) and has
\[
\max_e|\Phi_1^{-1}(e)|\le2,\qquad
|\Phi_1(n)-n|<4\lceil A y^{1/4}\rceil.
\]
The absolute constants are not numerically optimized or certified here.
The finite controls below do not establish a universal numerical
value for \(A\).

**Why the displacement exponent is sharp.**

The existing neighbor-scale proof supplies infinitely many odd
nonsquare continuers \(n\), with nonsquare odd image, for which
every odd source having an even image lies at distance at least
\(n^{1/4}/4\).
Any pairing to an exit must satisfy that lower bound at those
sources, regardless of its multiplicity.

Putting each such \(n\) in its dyadic source window proves that
no uniform \(o(y^{1/4})\) maximum-displacement bound can replace
the first-step bound above. This establishes the optimal spatial
exponent, not optimal multiplicity or constants.

**What survives with a prescribed odd prefix.**

The current [Paper B](../theory/juggler_parity_discrepancy_note.md) Theorem 4.11 and Corollary 4.12, by projecting
formal sign classes, give for each fixed \(1\le r\le4\)
\[
\#A_r(0,N]=2^{-r}N+
O_\delta(N^{127/128+\delta}).
\tag{P3}
\]
For \(r=1\) the error is actually \(O(1)\).
This input is an AI-assisted written theorem awaiting independent
review; the extension below inherits that limitation.

Fix \(0<\varepsilon<1/128\), put
\(\beta=127/128+\varepsilon<1\), and take \(B=\lceil y^\beta\rceil\).
Subtracting (P3) at the two endpoints of each block, with
\(\delta=\varepsilon/2\), gives, for \(t=1,2,3\),
\[
|C_t\cap I|=\frac{|I|}{2^{t+1}}+O_\varepsilon(y^{127/128+\varepsilon/2}),
\]
\[
|E_t\cap I|=\frac{|I|}{2^{t+1}}+O_\varepsilon(y^{127/128+\varepsilon/2}).
\]
Here \(|I|\) denotes the length of the ordinary integer interval
containing the block, with endpoint rounding absorbed by \(O(1)\);
it is comparable to \(B\).
The errors are \(o(B)\), uniformly over all the blocks. Hence
\(|C_t\cap I|\le2|E_t\cap I|\) for sufficiently large \(y\).
The same explicit rank assignment now preserves the first \(t\)
odd letters and has displacement
\[
|\Phi_t(n)-n|<4\lceil y^{127/128+\varepsilon}\rceil,
\qquad t=1,2,3.
\]
This is just endpoint subtraction of existing global counts. It
does not assert a new short-interval exponential-sum theorem.
In particular, the \(y^{1/4}\) displacement bound has only been
proved for \(t=1\).

**Where the construction stops.**

At \(t=4\), capacity requires counts of \(OOOOO\) versus \(OOOOE\).
Paper B's formal fourth coordinate is an even-root operation and
does not supply those counts. At growing \(t\), the needed local
capacity estimates are also unknown.

Thus this construction answers the previously missing first-step
multiplicity question and supplies fixed-prefix pairings, but does
not establish the five-to-one control throughout the required
depth range. The target \(y/(\log y)^5\) count and the remaining
high-odd-count words remain open. No further pairing rule is opened
by this bounded test.


### 6. Fifth-letter capacity: the last-floor resolution audit


On a block of original odd sources, let \(C\) count \(OOOOO\) and
\(E\) count \(OOOOE\). Here the letters describe states numbered zero
through four. Both classes preserve the first four odd states; an
exit means an even fifth state, not termination.

Put \(A=C+E\) and \(S=E-C\). The rank assignment from the preceding
follow-up, \(c_i\mapsto e_{\lceil i/2\rceil}\), exists exactly when
\[
C\le2E
\quad\Longleftrightarrow\quad
S\ge-A/3,
\qquad 2E-C=(A+3S)/2.
\]
This elementary identity calibrates the needed exit capacity; it does
not supply an arithmetic estimate for \(S\).

**What the last-floor expansion actually gives.**

Write \(F(x)=\lfloor x^{3/2}\rfloor\) for the formal odd branch and,
on \(P<n\le2P\), define
\[
m=F(n),\quad v=F(m),\quad Z=v^{3/2},\quad
w=\lfloor Z\rfloor,\quad \zeta=\{Z\},\quad W=w^{3/2}.
\]
On the actual \(OOOO\) class these are the successive odd operations.
The new fifth-state parity is that of \(\lfloor W\rfloor\).
Uniformly as \(P\to\infty\),
\[
v\asymp P^{9/4},\qquad Z\asymp P^{27/8}.
\]

Taylor's theorem for \(x^{3/2}\), with \(Z>1\), gives
\[
W=(Z-\zeta)^{3/2}
=v^{9/4}-a(n)\zeta+R,\qquad
a(n)=\tfrac32v^{3/4},
\]
\[
0\le R\le\tfrac38(Z-1)^{-1/2}\zeta^2
\ll P^{-27/16}.
\]
Indeed, the second derivative is \(3/(4\sqrt{x})\), positive and
decreasing on the interval from \(Z-\zeta\) to \(Z\).

With \(e(x)=\exp(2\pi i x)\), replacing \(W\) by the displayed two
main terms in **one exponential mode** \(e(\ell W/2)\) incurs total
error, over any subset of this source block, at most
\[
O\!\left(P|\ell|P^{-27/16}\right)
=O_C(P^{-31/48})
\quad\text{if }|\ell|\le CP^{1/24}.
\]
The same comparison holds in a mixed mode with any additional
unit-modulus factor. It does not by itself justify replacing floor
parities: those are discontinuous at integers.

Thus the Taylor remainder is harmless for the proposed mode transfer.
The main correction is the difficulty:
\[
a(n)\asymp P^{27/16}.
\]

**Why the tested resolution shortcut stops.**

[Paper B](../theory/juggler_parity_discrepancy_note.md) Theorem 4.11 controls integer modes of
\[
(X,Y,Z,U),\qquad X=n^{3/2},\quad Y=m^{3/2},\quad U=\sqrt{w},
\]
up to a fixed multiple of \(P^{1/24}\). It does not control the
new coordinate \(W=w^{3/2}\).

The shortcut tested here freezes \(\zeta\) in cells of width
\(1/H\), using the resolution \(H\asymp P^{1/24}\) associated
with that available mode range. Even for \(|\ell|=1\), the phase
length of the correction across a whole such cell, with \(a(n)\)
held fixed, has order
\[
\frac{a(n)}H\asymp P^{27/16-1/24}=P^{79/48}.
\]
For a uniform small-error replacement by a cell representative, this
scheme instead needs \(|\ell|a(n)/H=o(1)\), hence
\[
\frac{H}{|\ell|P^{27/16}}\longrightarrow\infty.
\]
Across a full cell at the available resolution, the corresponding
exponential traverses many complete turns; it cannot be uniformly
approximated by one value. Actual sampled \(\zeta(n)\) are not free
variables. This observation rules out the stated *uniform cellwise
approximation*, not cancellation on those actual samples.

There is a second scope gap: \(v^{9/4}\asymp P^{81/16}\) remains
as a new nested outer phase. It is not one of Paper B's controlled
coordinates. Merely enlarging a frequency cutoff would not establish
a bound for that phase.

**Decision: CLOSE this transfer.** This is a limitation of a specified
shortcut within an existing theorem, not a counterexample to fifth-state
balance or an impossibility result for other analytic methods. Paper B
itself is an AI-assisted written proof awaiting independent review;
no assumption about its correctness removes these scope gaps.

**Finite verification on the three existing blocks.**

For each previously used \(y\), take the first
\(B=32\lceil y^{1/4}\rceil\) odd sources above \(y\).
All roots and parity decisions use exact integer arithmetic.
Every assignment has multiplicity at most two and displacement
less than \(2B\).

| \(y\) | Odd sources \(B\) | \(OOOOO\) | \(OOOOE\) | Capacity margin \(2E-C\) | Maximum displacement |
|---:|---:|---:|---:|---:|---:|
| 1,048,576 | 1,024 | 59 | 63 | 67 | 1,028 |
| 268,435,456 | 4,096 | 218 | 256 | 294 | 4,104 |
| 68,719,476,736 | 16,384 | 932 | 983 | 1,034 | 16,626 |

All **1,209** assignments pass. These are three finite fixtures,
not full dyadic counts and not evidence sufficient to promote a
uniform \(y^{1/4}\) displacement assertion at this depth.
The existing neighbor-scale regression file records the three exact
count pairs; the workspace audit additionally saves assignment hashes.

**The arithmetic target remains PARK:** obtain an actual source-count
estimate for the fifth split, and ultimately one uniform in growing
prefix length. No new branch, deeper scan, manuscript edit, or
termination claim follows from this bounded test.


## Open questions

The pointwise choice in (U) still has no multiplicity bound. Results 5
constructs a different block pairing with multiplicity at most two:
first-step displacement is O(y^(1/4)); the inherited prefix lengths
two and three use O_epsilon(y^(127/128+epsilon)). No exit-capacity
estimate uniform in growing prefix length is proved. If the original source belongs to
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


**Block-pairing follow-up decision: PARK** the growing-depth target.
Retain the standard local-balance corollary and explicit two-to-one
assignment in Results 5, with optimal first-step displacement exponent.
The prefix-length-two/three extension inherits the current AI-assisted
Paper B proof and its outstanding independent-review limitations. These
are scoped written corollaries, not a new named frontier hypothesis or
a growing-depth arithmetic result. No paper or Lean edit is made.

**Fifth-letter follow-up decision: CLOSE** the uniform cell-freezing
transfer in Results 6. Its Taylor remainder is small, but the main
last-floor correction exceeds the available resolution and an
uncontrolled outer phase remains. The three finite pairings pass;
the actual fifth-split count and growing-depth target remain PARK.
No new named theorem, manuscript edit, or further branch is added.

**Best next question:** can the existing necessary all-odd count
(C3) be bounded directly on the original source integers, without
replacing their selected images by an interval?

## Publication assessment

Status: `THEOREM`. An elementary standalone local-scale theorem;
external priority is unverified. Not a paper-level termination claim.
