# Absolute floor cells in cubic-band Juggler cycles

Status: **PARK**. Authorized continuation dated 9 September 2026.

**The universal wrong-parity statement remains unproved.** Three written
results are retained: an upper-cell refinement of the sorted-grid charge,
smaller permitted extrema ranges for an actual cubic-band cycle, and an
explicit positive phase interval on which each threshold map is unchanged.
None improves the Paper A's numerical period bound or proves no-cycle.

## Problem

Can absolute unit-cell positions exclude a parity-compatible threshold
cycle after its rank order and log-log geometry have been determined?
The six base results, including the distinctions between the exact and
altered maps, are consolidated in [Paper A, Section 3.10](../theory/juggler_finite_dynamics_note.md),
results 3.33–3.38. Their proofs are not duplicated here.

## Exact statement

For an integer \(b\ge3\), let \(I_b=\{b,\ldots,b^3-1\}\) and

\[
S_b(x)=\begin{cases}
\lfloor\sqrt{x^3}\rfloor,&x<b^2,\\
\lfloor\sqrt x\rfloor,&x\ge b^2.
\end{cases}
\]

Its wrong-parity set is

\[
B_b=\{x\in I_b:x<b^2,\ x\text{ even}\}
\cup\{x\in I_b:x\ge b^2,\ x\text{ odd}\}.
\]

The target is: **for every integer \(b\ge3\), every primitive cycle of
\(S_b\) intersects \(B_b\)**. Equivalently, every \(S_b\) orbit eventually
visits \(B_b\), since this is a finite invariant map. Such a theorem would
exclude actual Juggler cycles with minimum \(m>1\) and maximum \(M<m^3\).
Conversely, a threshold cycle avoiding \(B_b\) is an actual Juggler cycle
with \(M<b^3\le m^3\). Cycles with \(M\ge m^3\) remain a separate issue.

The three proved statements below are weaker necessary restrictions or
obstructions to specific comparison arguments. Their tag is
**EXACT — HUMAN PROOF**, indicating written analytic proofs, not new Lean
verification or independent human review.

## Current literature

**Extended within the repository; external priority not claimed.** The
Juggler map is defined in [OEIS A094683](https://oeis.org/A094683)
(accessed 9 September 2026). That reference supplies the map definition,
not the results below. No extensive literature search or external novelty
determination is claimed.

[The cubic-band dossier](juggler_cycle_cubic_band.md) records the preceding
order, grid, projection and branch-offset results. [Method ceilings](juggler_cycle_method_ceilings.md)
and [negative knowledge](../negative_knowledge.md) explain why local cells,
uncalibrated branch differences and previously exhausted finance campaigns
cannot themselves be promoted to a global cycle obstruction. The new
charge inequality uses the complete sorted grid to improve a necessary
bound; it still belongs to the finance method and does not detect parity.

## Branch budget

- **Target:** the quantified wrong-parity intersection above.
- **Novelty hypothesis:** upper unit-cell faces and absolute branch anchors
  may add a restriction lost by difference-only equations.
- **Falsifier:** a proposed contradiction applies to the known altered-map
  controls, assumes strict phase response or parity independence, or merely
  restates a closed local-cell argument.
- **Already killed by?:** the cubic-band one-unit and branch-offset
  controls, and the local-cell/finance clusters in negative knowledge.
  The user expressly authorized examining the remaining exact global
  absolute-cell system; no earlier floor or band scan was reopened.
- **Existing machinery:** Paper A's cubic-band order, common-period and
  grid results; exact integer square cells; the finite projection controls.
- **Maximum Phase-0 scope:** three analytic routes: ranked cell slacks,
  branch-offset/phase anchors, and grid versus absolute unit cells. Only
  seven old cycles at \(b=3,9,29\), whole-map phase controls at \(b=3,9\),
  and two explicit anchor controls were checked.
- **Promotion criterion:** a correct uniform obstruction or a rigorously
  narrower permitted parameter region; structural findings remain scoped.
- **Stop criterion:** record the valid statements and leave the uniform
  intersection open if no parity-specific contradiction is proved.

## Balanced-ternary formulation

The states and square-cell slacks are ordinary integers. Canonical
balanced ternary represents them without changing any constraint.

## Why BT may be relevant

No representation advantage is used or claimed. This work introduces no
dependency in the core `bt` package.

## Candidate operations / invariants

The exact cell is \(y^2\le x^h<(y+1)^2\), with \(h=1\) or \(3\).
The completed grid proof uses its lower face. Its upper face bounds the
logarithmic defect by a function of the absolute successor, which leads
to Result 1. Adjacent odd ranks couple the two absolute extrema cells in
Result 2. Result 3 tests whether positive pre-floor phase changes must
alter the finite dynamics.

## Experiments

Supporting implementation and tests remain with the existing
[cubic-band probe](../../src/research/juggler_sequence/cycle_cubic_band.py)
and [its tests](../../tests/research/juggler_sequence/test_cycle_cubic_band.py).
The continuation data are
[absolute_cells_controls.json](../../data/research/juggler/cycle_cubic_band/absolute_cells_controls.json).

| Control | Scope and outcome |
|---|---|
| Upper-cell/grid charge | Seven previously surveyed cycles at \(b=3,9,29\) satisfy the finite-sum and closed bounds at 80 decimal places |
| Positive phase interval | Every state of \(I_3\) and \(I_9\): 24 and 720 exact integer square comparisons, all strict |
| Anchored altered cycle | \(3\to5\to10\to3\), with the minimum and maximum edges exact and the middle edge altered |
| Extremal two-edge control | \(m=9,q=27,M_0=674\), attaining the maximum ceiling for the two anchored cells |

The decimal calculations are numerical consistency checks, not rigorous
interval certificates. The phase and anchor controls use integers. These
finite checks do not prove the quantified results; their proofs follow.
No old census, descent floor or large-orbit cap was enlarged.
Regenerate only these controls with
`python -m research.juggler_sequence.cycle_cubic_band --absolute-cells`.

## Conjectures

No new conjecture file is opened. The stated uniform wrong-parity question
is the existing missing step within the cubic-band class.

## Counterexamples

The known projected-map cycle \(3\to5\to10\to3\) has exact anchors
\(J(3)=5\) and \(J(10)=3\). It has correct source parity, cubic height,
rank rotation and the full grid bounds, and satisfies Result 2's extrema
inequalities. Nevertheless \(J(5)=11\): its altered edge fails the upper
cell because \(5^3=125\ge(10+1)^2=121\).

This refutes sufficiency of the two anchors plus these necessary bounds.
It does not preserve every exact same-branch image difference and is not
a Juggler cycle. If a candidate preserves all image differences within
each connected comparison component, its difference from \(J\) is constant
on that component. One exact output anchor in each component then recovers
\(J\). This is recovery of the original map, not a contradiction to closure.
Comparing only pairs with both equal source parity and equal successor
parity can leave four components, so two anchors need not suffice.

## Formalization

**No new Lean theorem is claimed for the three results in this dossier.**
They are AI-assisted written proofs. Separate AI agents checked the new
charge inequality and the extrema algebra; this is not independent human
review. The base geometry is now formalized in
[CubicGrid.lean](../../formal/Problems/Juggler/CubicGrid.lean) and
[CubicLogGrid.lean](../../formal/Problems/Juggler/CubicLogGrid.lean), with
the exact cycle-order connection in
[CubicBand.lean](../../formal/Problems/Juggler/CubicBand.lean).
Those earlier verified results do not upgrade the new upper-cell,
extrema-strip or phase-plateau statements to Lean verification.

## Results

### Result 1 — upper unit cells and sorted defect density

**`J-cycle-absolute-cell-grid-charge`, EXACT — HUMAN PROOF.** Let a
primitive exact threshold cycle, or an actual Juggler cycle with \(m>1\)
and \(M<m^3\), have sorted states \(c_0=m<\cdots<c_{L-1}\) and branch
counts \(o,e\). Put

\[
T=\log3,\quad \Lambda=o\log3-L\log2>0,\quad
\kappa=1-1/L,\quad a=\log m,\quad A=a e^{-\kappa\Lambda}.
\]

Then \(A>0\) and

\[
\Lambda<\frac{e^{-A}}A
\sum_{i=0}^{L-1}e^{-iT(A+1)/L}
<\frac{e^{-A}}A\left(1+\frac{L}{T(A+1)}\right),
\tag{1}
\]

so in particular

\[
\boxed{e^A A(A+1)\Lambda<A+1+L/T.}\tag{2}
\]

**Proof.** For successor \(y_i\), real branch exponent \(p_i\in\{1/2,3/2\}\),
and defect \(\delta_i=\log(p_i\log c_i/\log y_i)\), the exact upper
cell gives \(c_i^{p_i}<y_i+1\). Since all states exceed 1,

\[
0\le\delta_i<\log\frac{\log(y_i+1)}{\log y_i}
=\log\left(1+\frac{\log(1+1/y_i)}{\log y_i}\right)
<\frac1{y_i\log y_i}.
\]

Successors permute the states and \(\sum_i\delta_i=\Lambda\), hence
\(\Lambda<\sum_i1/(c_i\log c_i)\). The uniform grid gives
\(\log c_i\ge A e^{iT/L}\). For \(t=iT/L\ge0\), monotonicity of
\(q e^q\) for \(q>0\), followed by \(e^t\ge1+t\), yields

\[
c_i\log c_i\ge A e^{Ae^t+t}\ge A e^A e^{(A+1)t}.
\]

This proves the first bound in (1). For \(z=T(A+1)/L>0\), the finite
geometric sum is smaller than
\(1/(1-e^{-z})=1+1/(e^z-1)<1+1/z\), proving (1)–(2).

**Conditional asymptotic consequence.** Along a sequence with \(L\to\infty\),
\(a=\log m\to\infty\), \(a=o(L)\), and \(\Lambda a\to0\), one has
\(A/a\to1\) and \(e^A/m\to1\). Thus

\[
m(\log m)^2\Lambda\le(1+o(1))L/\log3.\tag{3}
\]

For example, if \(\Lambda\sim c/L\) with fixed \(c>0\) and \(m\) grows
polynomially, then \(m(\log m)^2\le(1+o(1))L^2/(c\log3)\).
For \(m\sim K L^2/(\log L)^2\), this requires
\(K\le1/(4c\log3)\); a positive-constant scale \(m\sim K L^2/\log L\)
is excluded under these hypotheses. This is narrower than the old
statewise charge scale. No uniform lower bound \(\Lambda\gg1/L\), or
actual-cycle scaling law, is asserted. Exact threshold cycles also obey
(2), so this restriction does not itself detect wrong parity.

### Result 2 — absolute extrema strips and neighboring cells

**`J-cycle-absolute-cell-extrema`, EXACT — HUMAN PROOF.** For an actual
primitive Juggler cycle with minimum \(m>1\), maximum \(M<m^3\), and
largest odd state \(u\), set \(q=J(m)=\lfloor\sqrt{m^3}\rfloor\) and
\(r=m^3-q^2\). Then

\[
\boxed{M\le(q-1)^2-2,\qquad m^3-M\ge r+2q+1,}\tag{4}
\]

\[
\boxed{u^3\le[q(q-2)]^2-2,\qquad
u<m^2-\frac43\sqrt m.}\tag{5}
\]

An integer consequence of (5) is
\(u\le m^2-2\lfloor2\sqrt m/3\rfloor-2\).

**Proof.** The minimum is odd with \(m\ge3\), and the maximum is even.
If \(q\) were even, \(q\le m^{3/2}<m^2\) would imply \(J(q)<m\), a
contradiction. Put \(t=J(M)\). Since \(t^2\le M<m^3<m^4\), one has
\(t<m^2\), so the cubic-band parity separation makes \(t\) odd. Weak
monotonicity gives \(t\le q\); injectivity on the cycle excludes equality.
Thus the odd states \(t,q\) satisfy \(t\le q-2\). The even cell is
\(M<(t+1)^2\); both sides are even integers, so
\(M\le(t+1)^2-2\le(q-1)^2-2\). This proves (4).

Rank rotation sends the largest odd state \(u\) to \(M\). Its odd cell
is \(u^3<(M+1)^2\), and both sides are odd; hence
\(u^3\le(M+1)^2-2\le[q(q-2)]^2-2\).
Write \(s=\sqrt m\ge\sqrt3\). Since \(q\le s^3\) and \(q\ge5\),
\([q(q-2)]^2\le(s^6-2s^3)^2\). Furthermore

\[
\left(s^4-\frac43s\right)^3-(s^6-2s^3)^2
=\frac4{27}s^3(9s^3-16)>0.
\]

The cube-root comparison is between positive quantities, proving (5).
Finally \(m^2-u\) is an even integer strictly greater than \(4\sqrt m/3\),
which gives the stated integer form.

**Neighboring-rank consequence.** In sorted ranks, \(t=c_{e-1}\), \(q=c_e\),
and \(e<o\). For \(0\le j<e\), the even state \(c_{o+j}\) maps to the
odd state \(c_j\). Odd spacing and the exact even cell give

\[
(m+2j)^2+1\le c_{o+j}\le[q-2(e-j)+1]^2-2.\tag{6}
\]

With \(d=o-e>0\), its odd predecessor is \(c_{d+j}\), so

\[
[(m+2j)^2+1]^2+1\le c_{d+j}^3
\le\{[q-2(e-j)+1]^2-1\}^2-2.\tag{7}
\]

Indeed \(m+2j\le c_j\le q-2(e-j)\), while
\(c_j^2+1\le c_{o+j}\le(c_j+1)^2-2\); the odd predecessor's cube is
at least one above its even successor's square and at least two below
the next odd square. These observations give (6)–(7).

These are restrictions on a genuine cycle, not claims that the remaining
intervals are empty. The two-edge example \(m=9,q=27,M_0=674\) attains
the first ceiling, since \(J(674)=25=q-2\); it is not a closed cycle.
Sharpness for the two anchored cells does not imply sharpness among
actual cycles.

**Grid comparison.** The lifted seam gap obeys

\[
\log\frac{3\log m}{\log[(q-1)^2-2]}
\le h_{L-1}\le T/L+(1-1/L)\Lambda.
\]

Its lower bound has order \(1/(m^{3/2}\log m)\). Under
\(\Lambda\le C/L\), direct combination yields only
\(L=O(m^{3/2}\log m)\), weaker than the existing
\(L=O(m\log m)\) comparison from the first two odd ranks. Transporting
one gap through the defect equations spends at most the same total
\(\Lambda\); it does not automatically amplify the seam into a contradiction.

### Result 3 — a positive phase plateau for every threshold map

**`J-cycle-threshold-phase-plateau`, EXACT — HUMAN PROOF.** For every
integer \(b\ge3\), independently add phases \(\theta_O,\theta_E\) before
the two floors of \(S_b\). Then

\[
0\le\theta_O,\theta_E\le\frac1{2b^3}
\quad\Longrightarrow\quad
S_{b,\theta_O,\theta_E}(x)=S_b(x)\quad(x\in I_b).\tag{8}
\]

Here \(S_{b,\theta_O,\theta_E}\) uses
\(\lfloor\sqrt{x^3}+\theta_O\rfloor\) below \(b^2\), and
\(\lfloor\sqrt x+\theta_E\rfloor\) at or above it.

**Proof.** Put \(B=b^3\). Every branch radicand \(N\) is an integer
less than \(B^2\). For \(k=\lfloor\sqrt N\rfloor\), one has
\(k+1\le B\) and \((k+1)^2-N\ge1\). Therefore

\[
\begin{split}
[2B(k+1)-1]^2-4B^2N
&=4B^2[(k+1)^2-N]-4B(k+1)+1\\
&\ge1.
\end{split}
\]

Since \(k+1-1/(2B)>0\), this proves
\(\sqrt N<k+1-1/(2B)\). Hence
\(k\le\sqrt N+\theta<k+1\) whenever \(0\le\theta\le1/(2B)\), and
the floor is unchanged. This proves (8) simultaneously on the whole band.

Thus the full finite dynamics and every exact output anchor persist on
a positive phase rectangle. This refutes a comparison argument requiring
every positive phase to change the rotation number or isolate zero phase.
It does not refute a proof using absolute cells. The interval is one-sided
and depends on \(b\); no positive size uniform in \(b\) is asserted.

## Open questions

After imposing (2), (4)–(7), exact integer upper cells and the known rank
rotation, a large permitted parameter region remains. The missing step is
a parity-specific incompatibility of the globally closed unit-cell system.
Phase continuity, recovering branch offsets, or inequalities valid for all
threshold cycles do not provide that incompatibility.

## Decision

**PARK.** Retain the upper-cell charge refinement, the exact extrema strips,
and the positive phase plateau with their stated scopes. No uniform
wrong-parity intersection or numerical period improvement was proved.
The one best next question is: **what parity-specific global unit-cell
obstruction excludes a closed threshold cycle in the surviving grid
region?** This question does not authorize automatically opening another
branch or enlarging a computation.

## Publication assessment

Status: **STRUCTURAL**. This is a canonical research dossier of three
AI-assisted written results and bounded controls, following Paper A's
completed consolidation. It is not a publication-ready no-cycle proof.
The recorded certified floor and period lower bound remain unchanged.
