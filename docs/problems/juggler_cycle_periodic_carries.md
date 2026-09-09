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

Current declaration-level coverage is recorded in Paper A, Appendix A,
and its [formalization map](../theory/juggler_finite_dynamics_formalization.md).
The canonical Lean files are in `formal/Problems/Juggler/` and are imported
by `Problems.JugglerPaper`. The theorem ledger distinguishes the compiled
statements from the additional written consequences. No general no-cycle
or escape-exclusion theorem is claimed.

## Results

The current statements and proofs are consolidated in **Section 3.11 and Appendix E.6** of
[Paper A](../theory/juggler_finite_dynamics_note.md).
That manuscript is the canonical editorial source. This dossier retains
the original branch budget, controls, limitations and decision record;
it is not a second editable copy of the proof.

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

Status: **STRUCTURAL**. The results are now consolidated into Paper A,
Section 3.11 and Appendix E.6, with the formal scope recorded beside the claims.
The certified period floor remains 780239. This consolidation is a local
revision; it does not upload a new Zenodo version.

