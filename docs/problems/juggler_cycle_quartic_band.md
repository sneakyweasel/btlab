# Cycle order below the quartic height

Status: **PROMOTE** the scoped return-order and height/count restrictions.
Completed, strengthened and audited 10 September 2026. The first taller slab is not excluded.
This dossier is the canonical proof owner for the new written results;
Paper A has not yet incorporated them. Six laboratory Lean modules verify
the actual return/cell machinery and finite component-budget kernels;
the complete primitive-cycle-to-component assembly remains unformalized.
The precise boundary is recorded in the Formalization section below.

## Problem

Does an actual primitive Juggler cycle with minimum m and maximum
\(m^3\le M<m^4\) have a useful replacement for cubic rank rotation?
The test must retain absolute floor cells and all parity guards.

## Exact statement

Let an actual primitive nontrivial cycle have minimum \(m\ge16\),
maximum \(M<m^4\), period L, odd count o and even count \(e=L-o\).
Write
\[
k=\lceil m^{4/3}\rceil,\quad
\ell=\lceil k^{4/3}\rceil,\quad q=\lfloor m^{3/2}\rfloor,\quad
D=\lceil\ell^{1/4}\rceil.
\tag{Q1}
\]
Its section \(H=\mathcal C\cap[k,m^2)\) has e odd states.
Its first-return words, read chronologically, are
\[
F=OOE,\qquad G=OEO,\qquad B=OE.
\]
The first \(r=o-e\) sorted sources, those below ell, use F or G;
the last \(s=2e-o\) use B. Both r and s are positive. The B images
are the first s target ranks, those below q.

For a permutation pi of the first r ranks the exact return permutation is
\[
\sigma(i)=
\begin{cases}
s+\pi(i),&i<r,\\
i-r,&i\ge r.
\end{cases}
\qquad |\pi(i)-i|\le D.
\tag{Q2}
\]
An F source only moves up in the ordering of growing images; a G
source only moves down. Let c be the number of F sources, equivalently
the number of odd cycle states at or above \(m^2\), and let I count
inversions of pi. Then
\[
\boxed{
\begin{gathered}
d:=\gcd(L,o),\qquad d-1\le I\le\min(c,r-c)D,\\
I\equiv d-1\pmod2.
\end{gathered}}
\tag{Q3}
\]
Here \(D\le\lceil2m^{4/9}\rceil\); it is independent of period.
In the taller slab c is positive. With
\[
J_*=\max\left(1,\left\lceil\frac{d-1}{D}\right\rceil\right)
\]
there are the additional necessary height inequalities
\[
\boxed{(M+1)^2>(m^2+2J_*)^3,\qquad
M\ge m^3+3mJ_*,\qquad M\ge(q+2J_*)^2+1.}
\tag{Q4}
\]
The last inequality also uses the distinct images of the high odd states.
If c=0, the shuffle disappears and d=1, recovering cubic coprimality.
**Shared-cell refinement (Results 8--11).** An earlier F and later G
invert if and only if their exact auxiliary OE values agree. Each cell
contains at most one G source. Thus pi is a product of disjoint
cell-prefix cycles, every F displacement is zero or one, and
\[
\boxed{d-1\le I\le\min(c,(r-c)D),\qquad d\le c+1.}
\]
The parity condition in (Q3) remains. In (Q4), J_* can consequently
be replaced by the stronger \(J_{\rm cell}=\max(1,d-1)\).
The active F ranks must also connect the d rotation residue classes;
at the boundary I=d-1, this is equivalent to primitive closure of the
abstract permutation, without asserting floor realizability.

**Nonparticipant audit (Results 12--14).** The target of forcing
c_0>=1 is PARK: neither the extremal descent nor closure of the
noninjective auxiliary map supplies such a bound. The prior
shared-cell theorem and its height restrictions remain valid.

**Component comparison (Results 15--18).** The new disjoint actual-block
budget, claim J-cycle-quartic-auxiliary-loss-budget, proves a conditional
nonparticipant theorem. For the taller side, put
\(\Lambda=\log(3^o/2^L)>0\). Then
\[
\boxed{
\gcd(L,o)=1,\quad(e-1)\Lambda\le\log(3/2)
\quad\Longrightarrow\quad c_0\ge1.
}
\]
If c is even, the conclusion strengthens to c_0>=2. This is an
additional small-product hypothesis; no uniform bound on that
product has been proved. At c=d-1 the auxiliary map has one periodic
component lifting to a threshold cycle of length L/d with exactly
one wrong-parity high state, not to a smaller actual Juggler cycle.

**Covered-cell extension (Results 19--22).** Claim
J-cycle-quartic-covered-cell-budget permits a selected G on either
side of an F source. Put eta(m)=log(log(m+1)/log m). Then
\[
\boxed{
\gcd(L,o)=1,\quad(e-1)\Lambda+e\eta(m)\le\log(3/2)
\quad\Longrightarrow\quad
\exists x\text{ an F source with }B(x)\notin Y.
}
\]
Thus the conclusion is an F cell with no selected G, rather than
only a nonparticipant. The hypothesis adds an explicit term
e eta(m)<e/(m log m) to the earlier condition and is not established
uniformly. Negative substitutions are controlled by full-cell rank
displacement, not absorbed by the corresponding F towers.

**Neighboring-cell localization (Results 23--26).** Claim
J-cycle-quartic-component-gap-witness strengthens the same conditional
conclusion. Projecting each missing valley to the preceding selected
G valley closes a monotone rank map T_-. Under the hypotheses of
(Q43), every periodic component of T_- contains an uncovered F,
so there are at least N uncovered sources when there are N components.
Each component has a witness whose partner gap divided by its rank
displacement exceeds tau>=eta(m), as specified in (Q53)--(Q56).
An uncovered source confined to a transient path cannot suffice.
The coarse maximum neighboring-gap inequality is already implied
by counts and span; it gives no additional exclusion.

**Complete selected-cell separation (Results 27--29).** Claim
J-cycle-quartic-separated-cells strengthens the conclusion under exactly
the condition of (Q43): B is injective on the whole selected section H,
every F source is uncovered, and pi is the identity. Sorting the actual
lower power envelopes gives a positive rotation-defect equation; its
coprime gap bound is at least eta(m), while a repeated B cell would
have a strictly smaller gap. Bare transport still does not force an
upper bound below tau, as the nonconstant real-potential control shows.

**Absolute re-entry localization (Results 30--33).** Under the same
condition, a strict missing F valley's O image can re-enter H only at
the preceding target, through two consecutive F valleys whose later
value is at most 2m. Adding all missing valleys closes the enlarged
low set exactly when every F endpoint equals its prescribed G endpoint;
the resulting threshold cycle has the old counts and explicit wrong
guards. Equality at valley v>=8 has just one source candidate,
ceil(v^(4/3)). An unbounded exact open family retains the minimum-G
anchor, separated cells, guards and gap allowance while its missing
F valley and next O image are both unselected. These facts refine
the remaining integer matching problem without excluding a cycle.

**Coupled remainder improvement and endpoint equality (Results 34--36).**
An actual OE pair cannot have both positive odd remainders equal to one.
This modulo-7 incompatibility adds the positive charge D(v) in Q84 and
strictly tightens the independent-charge signed interval for whole
actual H-return blocks. It needs no Q43 separation hypothesis, but
does not supply a global sign. The arithmetic kernel is Lean verified;
the logarithmic and cycle assembly remains a written proof. A second
explicit unbounded guarded F family has F=G at every displayed source,
closing eventual local strictness from the full F guards alone. These
open paths do not supply an actual cycle or the all-equality case of Q74.

**Located loss across cut pairs (Results 37--39).** The incoming O
remainder is at least three by a classical Gaussian factorization
argument, independently of the following E edge. This refines the
interpretation of Q82 and locates a positive charge on the O leg.
Q96 accounts for arbitrary original-edge coefficients without double
counting a split pair. In the actual cubic terminal geometry, P and
mixed split the same m-landing pair and Q splits none; every segment's
separate-charge interval tightens at both ends. Their coefficient
vectors still sum to zero on each edge, so no oriented contraction
follows. The general support inequalities have new scoped Lean proofs;
the Gaussian and actual-cycle arguments remain written proofs.

No uniform no-cycle, termination, or new numerical period bound follows.

## Current literature

**PROJECT-SPECIFIC internal extension; external priority is not claimed.**
The source is [Paper A's cubic order theorem](../theory/juggler_finite_dynamics_note.md),
together with the exact root cells and primitive-cycle injectivity.
The [corrected run-alphabet record](juggler_cycle_run_alphabet.md)
explicitly withdraws a factor-free inference from an upper growth bound.
The proof below instead supplies the lower floor margins it uses.

No external analytic estimate is invoked. The elementary permutation
facts needed for (Q3) are proved below. The earlier
[uniform signed-return audit](juggler_cycle_weighted_remainders.md)
concerns the cubic region; its closure obstruction is not reopened.

## Branch budget

- **Target:** a useful exact order restriction in the first taller slab.
- **Novelty hypothesis:** bounded returns through a low section retain
  order even when original source parities interleave.
- **Falsifier:** the reduction only records arbitrary interleaving or
  applies the invalid factor-free height-to-alphabet inference.
- **Already killed by?:** approximate alphabets, local cell summaries and
  repeated cubic cocycle identities are closed. This tests a different
  height regime using exact returns and integer order.
- **Existing machinery:** branch monotonicity, minimum constraints,
  cycle injectivity, exact floor cells and finite permutations.
- **Maximum Phase-0 scope:** one analytic first-return/order derivation,
  with fixed exact regression controls; no cycle or word census.
- **Promotion criterion:** a new uniform structural restriction on
  actual cycles, beyond merely listing short return words.
- **Stop criterion:** retain the strongest restriction and stop this
  gate; no automatic higher slab, induction campaign or floor increase.

**Authorized shared-cell continuation (10 September 2026).** The next
test asks for an actual-cycle restriction on inversions beyond (Q3).
Its novelty hypothesis is shared integer-cell compatibility. The
falsifier is merely restating parity, intervals or closure. Scope is
one analytic inversion audit with fixed exact controls, no census.
Promote only a stronger restriction; otherwise record the missing
input and stop. Results 8--11 supply that stronger restriction.

**Authorized nonparticipant continuation (10 September 2026).**
Test whether selected minimum/maximum cells force nonparticipating
F states beyond (Q18). The falsifier is an unoccupied local hole,
an unjustified iterated descent, or a closure identity without a
new actual-cycle constraint. Scope is one analytic extremal and
occupancy audit with fixed existing controls; no census, parameter
search or higher return campaign. Promote only a forced count or
exclusion; otherwise preserve the proved restrictions and park the
missing arithmetic step. Results 12--14 record the latter outcome.

**Authorized periodic-component continuation (10 September 2026).**
Test whether exact arithmetic forces an auxiliary component using only
actual edges. Scope is one analytic component audit, with fixed controls
and no census. Finite closure, old threshold finance and the whole-set
balance are falsifiers of novelty. Promote a new obstruction to all
participation; otherwise park the missing arithmetic input. The
disjoint-block comparison in Results 15--18 meets the conditional
promotion criterion, without establishing the uniform target.

**Authorized covered-cell continuation (10 September 2026).**
Test whether the genuine-block budget survives G partners before F,
or forces an F cell with no selected G. Scope is one analytic extension
with the three existing scales and one fixed abstract control, no
census. Mere signed telescoping or local occupancy is the falsifier.
Promote a new actual-cycle restriction; otherwise park the missing
input. Results 19--22 meet the conditional promotion criterion by
combining full-cell displacement with a uniform cell-width bound.

**Authorized neighboring-cell continuation (10 September 2026).**
Test disjoint actual-block substitutions across missing selected
cells. Scope is one analytic predecessor-projection audit and two
fixed abstract controls; no census or floor increase. An uncontrolled
boundary or an automatic count/span bound is the falsifier. Promote
a stronger actual-cycle placement or gap restriction, otherwise park
the missing input. Results 23--26 promote the conditional component
witness and close the coarse maximum-gap shortcut.

**Authorized witness-transport continuation (10 September 2026).**
- Mathematical target: bound the component-selected transported gap below tau.
- Novelty hypothesis: actual return order and exact cells control the endpoints.
- Falsifier: transport only cancels the same omitted losses or admits the old gap.
- Already killed by?: generic signed telescoping and the coarse maximum-gap bound
  are closed; this gate retains the quartic cell-prefix permutation and positive
  sorted power envelopes, absent from the earlier cubic-only transport audit.
- Existing machinery: guarded F/G/B returns, exact OE cells, component budgets,
  and the newly consolidated Lean kernels.
- Maximum Phase-0 scope: one analytic transport/order audit and two fixed
  controls at the existing e=7 and e=12 counts; no scan or floor increase.
- Promotion criterion: a stronger restriction on actual quartic cycles.
- Stop criterion: preserve the strongest restriction and name the missing
  arithmetic input; do not open another gate.
Results 27--29 PROMOTE full selected-cell separation under the existing
condition and CLOSE the bare transport-to-upper-bound shortcut.

**Authorized absolute-cell continuation (10 September 2026).**
- Mathematical target: exclude a separated pure-R_s actual cycle with all F valleys unselected.
- Novelty hypothesis: shared absolute square/cube endpoints constrain re-entry beyond the defect cocycle.
- Falsifier: only local cell membership, a repeated loss budget, or unjustified threshold closure remains.
- Already killed by?: bare cyclic transport, local parity-only arguments, phase isolation, and compulsory-charge-only finance are closed; this gate uses the new quartic cell injectivity and original rank matching.
- Existing machinery: exact F/G/B cells, sorted rotation, minimum anchor, and established gap separation.
- Maximum Phase-0 scope: one analytic audit, a derived open family checked at t=3,65,65537, the fixed small equality path, and one abstract matching control at the existing e=7 counts; no census or floor increase.
- Promotion criterion: a stronger restriction on actual quartic cycles.
- Stop criterion: record the strongest restriction and the exact missing integer input, then stop.
Results 30--33 PROMOTE re-entry localization and the exact augmented
closure criterion. Absolute exclusion stays PARK; local anchoring
alone and repeated parity-charge bookkeeping do not close it.

**Authorized coupled-remainder continuation (10 September 2026).**
- Mathematical target: improve the signed residual budget through shared consecutive integer states, with one bounded endpoint-equality check.
- Novelty hypothesis: the shared cube/square equation forbids remainder configurations allowed by independent boxes.
- Falsifier: only a telescoping/matching identity survives, or no stronger quantitative inequality follows.
- Already killed by?: independent compulsory charges, bare cocycles, aggregate matching counted twice, and local guards used as global closure; the tested pair must add an actual compatibility constraint.
- Existing machinery: exact O/E cells, actual quartic tower partition, the Q77 unique equality candidate, and the old CW44 budget.
- Maximum Phase-0 scope: one two-edge arithmetic/finance audit, exact candidate checks for 8<=v<=1000000, one symbolic equality family with isolated large-scale replays, and verification of the resulting arithmetic kernel; no orbit census or floor increase.
- Promotion criterion: a proved stricter actual residual inequality; retain an exact counterfamily if the equality shortcut fails.
- Stop criterion: record the improved bound and its remaining sign obstruction, then stop this gate.
Results 34--36 PROMOTE the coupled charge and whole-block signed
interval improvement. Eventual local strictness and the tested aggregate
elimination shortcut are CLOSE; actual no-cycle stays PARK.

**Authorized cut-pair continuation (10 September 2026).**
- Mathematical target: retain the shared-remainder charge across actual comparison boundaries and determine whether the terminal geometry forces a contradictory sign.
- Novelty hypothesis: the required charge has an arithmetically forced location on an edge of a split pair.
- Falsifier: arbitrary residual allocation or exact cancellation survives after every boundary is included.
- Already killed by?: independent charge sums, the old raw OE contrast, and terminal telescoping; this gate must localize an additional charge and use actual endpoint placement.
- Existing machinery: Q82--Q88, exact O/E cells, original cubic terminal factorization, and the whole-return loss budget.
- Maximum Phase-0 scope: one pair/support derivation, one actual terminal-order audit, a first-witness Q=1 check stopped after 71 candidates, and the fixed L19/e7 symbolic control; no cycle census or floor increase.
- Promotion criterion: a stronger proved bound valid even for cut pairs, with exact scope of any forced sign.
- Stop criterion: record the located bound and all cancellations; stop if the no-cycle orientation remains unsupported.
Results 37--39 PROMOTE located loss and the cut-pair estimate. Counting
boundary charges as an extra net terminal loss is CLOSE; no-cycle is PARK.

## Balanced-ternary formulation

All states and square remainders are exact integers. No special
balanced-ternary representation is used.

## Why BT may be relevant

No representation advantage is claimed.

## Candidate operations / invariants

The new invariant is the inversion count of a bounded, oriented shuffle
inside an exact return permutation. Its connection to the cycle count
of a rank rotation gives (Q3). The theorem has repository label
**EXACT — HUMAN PROOF**, claims **J-cycle-quartic-return-order** and
**J-cycle-quartic-auxiliary-loss-budget**, and
**J-cycle-quartic-covered-cell-budget**, and
**J-cycle-quartic-component-gap-witness**, and
**J-cycle-quartic-separated-cells**, and
**J-cycle-quartic-absolute-reentry**,
**J-cycle-quartic-coupled-remainder**, and
**J-cycle-quartic-unbounded-equality**, and
**J-cycle-quartic-boundary-loss**.
Here that label means an AI-assisted written proof cross-checked by
other AI agents, not independent human review or Lean verification.

## Experiments

The initial gate used fixed controls only. Later bounded local-cell
checks are identified below; none is a cycle or orbit census.
The [fixed regression controls](../../tests/research/juggler_sequence/test_cycle_quartic_band.py)
check the local inversion at exactly \(t=3,65,65537\), its full
integer cells and guards, and several fixed finite permutations.
The permutations are abstract controls, not Juggler cycles. These
tests catch algebra and convention errors; they do not prove the
universal theorem. Its proof is the argument below.
The continuation additionally checks the shared OE value in the
same fixed local family, one abstract primitive permutation excluded
by I<=c, and fixed cell-prefix permutations separated by residue
connectivity. The proof was independently cross-checked by three AI
agents; these controls do not verify universal claims.
The nonparticipant continuation re-anchors the same three fixed
open controls at their listed minimum and checks only u=3 for an
additional maximum-extension guard. That guard fails and is
retained as a regression against treating a prescribed E step as
actual. No further parameter is tested for that extension.
Four fixed component controls check a sharp missing-residue example,
a coprime count/permutation example excluded by the new defect budget,
the exact surplus comparison and integer small-product condition,
and the archived S_3 single-wrong-state example. These do not assert
any new floor-realized cycle. Three AI agents independently audited
the actual block substitution and its conditional consequence.
Five additional fixed checks verify the earlier-G variant at the
same three scales, a full-cell collapse whose sole periodic F is
late, and an integer sufficient check of the new conditional
inequality at previously used counts. They do not search for cycles
or claim those small counts meet the published period floor.
Three AI agents audited the covered-cell extension and its proof.
Two further fixed abstract controls separate a transient uncovered
source from the required periodic witness, and retain a projected
lower fixed point with n=1,p=0. They reuse the existing L=19,o=12
arithmetic control, without asserting floor realization or a new
numerical bound. Three AI agents audited the neighboring-cell proof.

The transport continuation adds two fixed rational/symbolic controls at
the existing e=12 and e=7 counts: a shuffled envelope with nonnegative
redistributed defects and a nonconstant positive-defect model whose
entire lifted gap circuit remains above tau. Three AI agents audited
the conditional separation proof. These controls do not realize
integer floor cells, parity guards, or actual cycles.

The absolute-cell continuation checks one derived separated G/F family
at the same three scales, all six new G square margins, an exact small
F=G path, and a fixed abstract target-matching control at the existing
seven-rank counts. The infinite family and conditional routing theorem
have written proofs audited by three AI agents. None of these controls
asserts a closed actual return permutation or a new count/surplus bound.

The coupled-remainder continuation additionally checks the uniform
endpoint-equality family at t=2^16+9,2^32+9,2^64+9. Its proof uses
ten polynomial coefficient certificates, independently expanded by
symbolic rational and integer polynomial arithmetic. The preliminary
bounded candidate scan is discovery evidence only, not a cycle census
or the basis of the unbounded theorem.

The cut-pair gate adds one exact Q=1 open path and a fixed symbolic
cubic-rank control at L=19,e=7. It verifies all actual-word pair
boundaries and enumerates endpoint allocations covering every extremum
of the explicitly relaxed finite residual problem. The rank/word control supplies no
integer states or actual cycle, and relaxed sharpness is not floor
attainability. The mathematical bounds have independent written audits.

## Conjectures

No new conjecture file. No cycle in the taller slab is constructed.

## Counterexamples

Result 7 supplies arbitrarily large, fully guarded open return pairs
whose combined expanding map reverses order. This refutes a deduction
of merged monotonicity from those local cells and the height band alone.
It does not supply common cyclic closure or refute (Q2).

## Formalization

### Lean coverage and remaining assembly

The new Lean modules check actual periodic-set arithmetic, exact shared
floor cells, finite projection identities, and the finite disjoint-block
budget leading to a normalized uncovered-cell witness. They do **not**
yet constitute a single theorem deriving every conclusion of Results
1--26 from an arbitrary primitive Juggler cycle. The following map
distinguishes established declarations from the remaining connections.

| Dossier portion | Compiled formal content | Exact scope |
| --- | --- | --- |
| Results 1--2: parity and return recipes | `QuarticBand.low_odd`, `even_image_low`, `high_odd_image_even`, `guarded_return_cases`, `returnMap_closed`, `returnMap_inj`, `exists_F_source`, `sorted_return_model`; `QuarticCells.G_gt` | The hypotheses retain a bounded closed set of actual periodic points, its extrema, and `M < m^4`. The guarded F/G/B recipes, their selected endpoints, injectivity, taller-side F existence, and a full sorted enumeration of the section are proved. The section uses the exact integer predicate `x < m^2 ∧ m^4 ≤ x^3`. The return permutation is not yet asserted to be one primitive cycle. |
| Results 3 and 8--11: cell arithmetic | `QuarticCells.F_cell_envelope`, `F_le_G_of_B_lt`, `periodic_inversion_iff_cell`, `periodic_same_cell_strict`, `periodic_G_cell_unique`, `periodic_F_inverts_at_most_one_G`, `G_guard_square_faces` | These include actual F/G guards and derive distinct endpoints from actual periodicity. The same-cell inversion criterion and the one-G-per-cell conclusion are proved. The complete shuffle construction, inversion-count inequalities, residue graph argument and resulting height bounds are not supplied by these declarations. |
| Results 15, 19 and 23: finite projection arithmetic | `QuarticProjection.predecessor_le`, `predecessor_monotone`, `predecessor_eq_self`, `predecessor_mem`, `predecessor_eq_on_cell`; `RankComponent.ofModular`, `displacement_balance`, `gcd_dvd_totalDisplacement`, `totalDisplacement_pos_of_omitted` | A selected integer anchor set and an embedded periodic permutation with its modular step determine the rank lift and nonnegative displacement. Coprimality plus a nonempty component and an omitted ambient rank proves positive displacement. The module does not itself extract the required anchors, modular step, component family or original-cycle count identifications from the actual section. |
| Results 17, 21 and 24: the loss budget | `QuarticLossBudget.defect_sum_of_permutation`, `two_branch_defect_sum`; `BlockSubstitution.strict_budget`, `reserved_budget`, `component_budget` | The strict inequality is derived from finite injective block selection, nonnegative actual defects and a positive omitted block. Reserved disjoint F losses can be retained explicitly. Potential cancellation and the two-branch component sum are proved. The certificate does not assume the final loss-budget inequality; its actual-block data and the original-cycle count calibration must still be instantiated. |
| Actual inputs to Results 17, 21 and 24 | `QuarticDefect.F_strict_upper_pow`, `blockDefect_nonneg`, `blockDefect_pos_F`, `blockDefect_sum`, `actual_sorted_positive_surplus` | Actual selected returns have nonnegative loglog defects, and every F has positive defect. Finite return-permutation telescoping gives `e log(9/8) - s log(3/2)`. In the taller slab the complete sorted actual section has positive surplus. Here e and s are section and upper-source counts; their identification with the original orbit counts remains outstanding. |
| Results 20--21: the covered-cell cap and conditional algebra | `QuarticCells.logEta_pos`, `logEta_antitone`, `logEta_lt_inv`, `same_cell_loglog_lt_min`; `QuarticLossBudget.covered_budget_contradiction`, `gapThreshold_ge` | The exact integer B cells imply the strict logarithmic cap with the actual minimum. The scalar covered-cell contradiction and threshold comparison are proved. The separate own-F-tower nonabsorption calculation in Result 20 is still a written argument. |
| Results 24--25: normalized uncovered witness | `QuarticLossBudget.weighted_gap_witness`, `weighted_uncovered_witness`, `BlockSubstitution.uncovered_component_witness`, `unequal_cell_witness`, `unselected_valley_witness`; `QuarticProjection.selected_displacement_cast_le`, `partner_interval_sum_le`, `adjacent_gap_of_ratio` | From a finite component certificate the proof produces a strict normalized gap; the concrete wrapper fixes the gap to `log log x − log log y` and invokes the exact B-cell cap. A projection fixed on selected valleys turns unequal cells into an absent selected valley. The adjacent-gap implication is proved by finite telescoping. The fully quantified actual-cycle statement for every projected component, and the resulting count of uncovered sources, still require the component-family assembly. |

The continuation adds `QuarticGapSeparation.adjacent_gap_lower`,
`B_injective_of_adjacent_gaps`, `B_injective_of_cocycle`, and
`B_ge_of_lower_power`. These reuse the existing positive cyclic-cocycle
gap theorem to prove the quantitative lower gap and actual integer
B-cell injectivity. The hypotheses explicitly supply the transitive
commuting permutation, nonnegative cocycle, total and small-product
bound. Constructing that cocycle from the arbitrary primitive quartic
orbit via sorted power envelopes and original counts is still the
written argument in Results 27--28. Thus the full actual-cycle claim
J-cycle-quartic-separated-cells remains at the AI-assisted written tier;
J-cycle-quartic-formal-gap-separation records the compiled kernel.

All declarations above are in the namespaces
`Problems.Juggler.QuarticBand`, `QuarticCells`, `QuarticProjection`, or
`QuarticLossBudget`, `QuarticDefect` or `QuarticGapSeparation`, under `formal/Problems/Juggler/`.
The displacement declarations live in the nested `QuarticProjection.RankComponent`
namespace. These six modules are registered in the laboratory barrel and
layer map, not yet in the Paper A review object. Separate scoped ledger rows
`J-cycle-quartic-formal-return`, `J-cycle-quartic-formal-cells`,
`J-cycle-quartic-formal-projection`, `J-cycle-quartic-formal-budget` and
`J-cycle-quartic-formal-defect` record the machine-checked claims; the complete written claims retain their previous tier.

The existing `FamilyChains.ooeFamily_square_cells`,
`ooeFamily_parities`, and `ooeFamily_juggler_block` already certify the
F half `t^8+8 -> ... -> t^9+9t-1` of the open controls. The accompanying
G families, anchor/order statements, and the fixed abstract permutations
remain written or fixed-test checks unless separately cited. A passing
Python control is not a Lean proof of an infinite family or a cycle.

The following obligations remain before the dossier's complete
actual-cycle conditional theorems can be advertised as closed Lean
theorems:

1. **Original orbit and return partition.** Start with one primitive
   actual orbit, prove the F/G/B paths are its first returns to the
   entire section, and partition its actual edges into those towers.
   `PeriodicExtrema` alone permits a union of periodic orbits. The
   strengthened `sorted_return_model` exposes full section coverage,
   but does not supply transitivity of the returned permutation.

2. **Count and order identification.** Identify the section cardinality
   with the original even count, the lower/upper source and image cuts,
   `r=o-e`, `s=2e-o`, `L=3r+2s`, the F/high-odd count, and
   `gcd(e,s)=gcd(L,o)`. The exact integer section predicate must be
   connected to the dossier's ceiling notation when those formulations
   are used. The bounded inversion window, cell-prefix permutations,
   aggregate inversion/gcd inequalities, residue connectivity, sharp
   component classification, and population/height corollaries also
   require their own finite proofs; they are not merely import wiring.

3. **Actual selected-cell projections.** Prove covered F iff its B value
   lies in the selected low set; construct the unique genuine G partner,
   then the full-cell or preceding-cell projection on the actual sorted
   section. Derive the modular step, omitted F-image rank and partner
   interval facts required by `RankComponent`. Decompose its periodic
   points and, when a common `n,p` is used, prove that common-count
   assertion. A predecessor lemma on arbitrary integer anchors does not
   alone establish these actual-cycle identifications.

4. **Concrete finite budget certificate.** Connect the actual defects,
   their proved nonnegativity and positive F defect to the substitution
   certificate. Identify the original total `Lambda`, component formal sum, signed partner
   substitution equation and disjoint omitted F set. The generic
   injection and transient-partner lemmas in `QuarticProjection` and
   the partition theorems in `QuarticLossBudget` discharge the finite
   logic once those actual objects are supplied. The logarithmic
   count equation `e*lambda = n*Lambda + Delta*A` remains part of that
   count assembly, not an assumed final budget.

5. **Final specialization and multiplicity.** Cast the natural rank
   displacement identities to the real witness interface, specialize
   the minimum and coprimality hypotheses, and prove that each extracted
   source belongs to the intended projected component. Apply this to
   every component and use their disjointness to obtain the uncovered
   count `>=N`. The adjacent-gap theorem must be instantiated with the
   actual sorted H-state potential. These steps yield the actual-cycle
   versions of the already proved certificate conclusions.

The extremal descent/noniteration discussion, single-wrong-state lift
and long-excursion identities, own-tower compensation obstruction, and
maximum-gap reparameterization are not newly formalized by these six
modules. They retain their AI-assisted written-proof status. No module
claims universal no-cycle, termination, or an increased numerical floor.

Results 30--33 are new AI-assisted written results, including absolute
re-entry localization, augmented closure, the thin endpoint-equality
test and the separated open family. They are not newly formalized by
the six existing modules. The compiled `QuarticCells` envelope and
source-cell bounds and `QuarticGapSeparation` gap kernel support them,
but do not constitute a Lean proof of their full actual-cycle assembly.

Results 34--36 add a kernel-checked modulo-7 arithmetic restriction in
the existing `QuarticCells` module: `cube_ne_square_successor_square_successor`,
`guarded_OE_remainder_dichotomy`, `guarded_OE_lower_cube`, and
`actual_OE_lower_cube`. This checks the universal integer face Q82--Q83
and its exact O/B specialization. It does not formalize the new
logarithmic correction, its disjoint cycle-budget assembly, or the
unbounded endpoint-equality family; those retain their audited
AI-assisted written-proof tier.

Results 37--39 add `QuarticLossBudget.located_pair_lower`,
`located_pair_upper`, `located_pairs_lower`, and `located_pairs_upper`.
These kernel-checked real inequalities take supplied coefficient bounds,
located residual lower bounds and pair totals. Their finite sums preserve
the exact unused residual term. The Gaussian exclusion R=1, the
logarithmic specialization, disjoint actual-edge extraction and cubic
terminal coefficient table remain audited written proofs. No complete
actual-cycle theorem is attributed to these small support kernels.

## Results

### 1. Exact low returns and lower floor margins

Write \(O(x)=\lfloor\sqrt{x^3}\rfloor\) and
\(E(x)=\lfloor\sqrt x\rfloor\). The minimum is odd and the maximum even.
Every even cycle state is at least \(m^2+1\), and its image is below
\(m^2\), hence odd. Thus EE is impossible.
For an odd state \(h\ge m^2\), its image is at least \(m^3\).
That image must be even: otherwise the following O image is at least
\(O(m^3)\ge m^4\). These are exact integer comparisons.

The low section \(Y=\mathcal C\cap[m,m^2)\) consists of odd states.
Its first return has word O if \(x^3<m^4\); otherwise it has word
OE if O(x) is even, and OOE if O(x) is odd. In the last case its
two intermediate states are outside Y. The return lengths are 1,2,3.

The following lower estimate supplies the needed growth, without
using a one-sided upper envelope: for every integer \(n\ge9\),
\[
(O(n)-1)^3>(n+1)^4.
\tag{Q5}
\]
Indeed \(O(n)-1>n^{3/2}-2\ge(7/8)n^{3/2}\), since \(n^{3/2}>16\).
Cubing gives a lower bound strictly greater than
\((1029/512)n^4>2n^4>(n+1)^4\).
In particular \(O^2(n)\ge(n+1)^2\). Applying this twice shows
\(O^4(n)>n^4\). Consequently an actual cycle in the present height
range has odd runs of length at most three, and isolated even steps.
Its cyclic word is a concatenation of OE, OOE and OOOE.
This implication uses the stated minimum and quartic bound; it does
not restore the previously withdrawn statement for another height ratio.

### 2. A second section with separated source and image blocks

The cuts (Q1) satisfy
\[
m<k<q<\ell<m^2.
\tag{Q6}
\]
The first inequality is immediate, and (Q5) gives \(k\le q-1\).
Also \(q^3\le m^{9/2}<m^{16/3}\le k^4\), so q<ell.
Finally \(q^2\le m^3\) and \(q^3\ge m^4\) imply
\[
(m^2-1)^3-(q-1)^4
\ge m^4-6m^3+3m^2+4q-2>0.
\]
Thus \(k^4<(m^2-1)^3\), giving ell<=m^2-1.

All O returns to Y land at or above q. All OOE returns also land
at or above q, because their high odd intermediate is at least \(m^2\).
The latter inequality is strict: q already has odd predecessor m,
and cannot also have the even predecessor of an OOE endpoint.
For an OE return its low source is below \(m^2\); hence its image
is at most q, and again injectivity excludes equality. Therefore
OE images are below q, while O and OOE images are at or above q.

Delete the O source domain by passing to \(H=Y\cap[k,m^2)\).
An O return from the deleted domain lands in H. Its first-return
words are therefore exactly among F=OOE, G=OEO and B=OE:
an OE return whose endpoint is below k appends one O step.

The exact root identity \(E(O(x))=\lfloor x^{3/4}\rfloor\) gives
\[
B(x)<k\quad\Longleftrightarrow\quad x^3<k^4
\quad\Longleftrightarrow\quad x<\ell.
\]
An F source cannot have \(x\ge\ell\): then \(O(x)\ge k^2\),
and \(O^2(x)\ge k^3\ge m^4\), outside the cycle. Thus lower sources
use F or G and upper sources use B. The corresponding image blocks
are respectively at/above q and below q.

Both lower recipes have output strictly larger than their source.
For F, (Q5) implies \(F(x)\ge x+1\), using
\(F(x)=\lfloor O(x)^{3/4}\rfloor\).
For G, put \(y=B(x)\ge m\); its exact cell and (Q5) give
\(x^3<(y+1)^4<O(y)^3\), so \(G(x)=O(y)>x\).
B has output strictly smaller than its source. Both source blocks must be nonempty in a
finite return cycle. Every first-return tower has exactly one even
source; lower towers have two odd sources and upper towers one.
They partition the original cycle, proving
\[
|H|=e,\quad r+s=e,\quad o=2r+s,\quad L=3r+2s,
\]
hence r=o-e and s=2e-o. The inequality o<2e is not advertised as
a new numerical bound: existing finance is stronger at large minima.

Each F tower contains exactly one high odd state, and no other tower
does. Thus its count is c. A high odd state exists exactly when
\(M\ge m^3\): the even maximum has an odd predecessor, which is
high if \(M\ge m^3\). At least one G return also exists, namely the
return containing the passage through m and then q.

### 3. Inversions are oriented and localized

Let p=9/8. The two expanding recipes satisfy, for x>=1,
\[
0\le x^p-F(x)<2,\qquad
0\le x^p-G(x)<\frac32x^{3/8}+1.
\tag{Q7}
\]
For F, set u=O(x). The root identity gives \(F(x)=\lfloor u^{3/4}\rfloor\).
The change from \(x^{3/2}\) to u is less than one, and the concave
power \(t^{3/4}\) changes by at most \(3/4\) on this interval for
u>=1; its final floor loses less than one. The case x=1 is exact.
For G, write \(v=x^{3/4}\), \(n=\lfloor v\rfloor\). The mean-value
bound \(v^{3/2}-n^{3/2}\le(3/2)\sqrt v\,(v-n)\), followed by the
last unit floor loss, proves the second inequality.

Moreover F(x)>=G(x) pointwise: for u=O(x),
\[
F(x)=E(O(u))=\lfloor u^{3/4}\rfloor
\ge O(E(u))=G(x).
\]
Both recipes are nondecreasing. Cycle injectivity therefore implies
that the only possible inversion has an earlier F source x and a
later G source y. If their actual images reverse order, (Q7) gives
\[
y^p-x^p<\frac32y^{3/8}+1.
\]
Since \(y^p-x^p\ge y^{p-1}(y-x)\),
\[
y-x<\frac32y^{1/4}+y^{-1/8}
<2y^{1/4}<2\ell^{1/4}.
\tag{Q8}
\]
The middle inequality holds for y>=7, supplied by the present domain.

All H sources are odd and separated by at least two. In source-rank
order an inverted pair at distance j therefore satisfies
\(2j\le y-x<2\ell^{1/4}\). Every F source has at most D partners
to its right, and every G source at most D partners to its left.
F sources only move up in image rank, G sources only down.
This proves \(|\pi(i)-i|\le D\) and \(I\le\min(c,r-c)D\).
Finally \(k\le2m^{4/3}\), \(\ell\le2k^{4/3}\) imply
\(\ell^{1/4}\le2^{7/12}m^{4/9}<2m^{4/9}\), proving the stated scale.

### 4. Primitive closure bounds the gcd by the inversion budget

Sorted B sources map increasingly onto all s ranks below q.
The other r images fill the remaining ranks, proving (Q2).
Let tau extend pi by the identity on the last s source ranks.
Then, with \(R_s(i)=i+s\bmod e\),
\[
\sigma=R_s\circ\tau.
\tag{Q9}
\]
The rotation R_s has \(d=\gcd(e,s)=\gcd(L,o)\) cycles.
The first return to a nonempty section of one primitive cycle is
itself one cycle.

A permutation with I inversions can be sorted by exactly I adjacent
transpositions: if an inversion remains, some adjacent pair is inverted;
swapping it removes exactly one inversion. Reverse this sorting
sequence to express tau as I transpositions. Multiplying a permutation
by a transposition merges two cycles if its two points were in different
cycles, and splits one cycle into two if they were in the same cycle.
Thus every transposition changes the number of cycles by exactly one.
To change d cycles to one requires \(I\ge d-1\), with
\(I\equiv d-1\pmod2\). This proves (Q3).

When c=0, pi has no inversions and is the identity, recovering exact
rotation and coprimality. When d=1, I must be even but need not vanish.
The theorem does not infer exact rotation from a small error allowance.

### 5. Height consequences on the taller side

Assume now \(M\ge m^3\), so c>=1. The odd state \(m^2\) is impossible:
it would give \(m^2\to m^3\to O(m^3)\ge m^4\).
The c high odd states are therefore at least
\(m^2+2,m^2+4,\ldots,m^2+2c\). Their largest h is the largest odd
state, and its image is the even maximum M. From (Q3), c>=J_*;
the strict upper square cell yields
\[
(M+1)^2>h^3\ge(m^2+2J_*)^3.
\]
The integer identity
\[
(m^2+2J_*)^3-(m^3+3mJ_*)^2
=3m^2J_*^2+8J_*^3>0
\]
then gives \(M\ge m^3+3mJ_*\).

There is also the valley-count restriction in (Q4). Each of the c
high odd states has an even O image at least \(m^3\), followed by an
odd E image at least q. Equality with q would give q the distinct
predecessors m and an even state, impossible on a cycle. These c
odd valleys are distinct by cycle injectivity, so their largest is
at least q+2c. Put t=E(M). This is the largest such valley, since M
is the image of the largest odd state. Hence t>=q+2c>=q+2J_*.
Since M is even and t odd, \(M\ge t^2+1\ge(q+2J_*)^2+1\).
For J_*=1 this is a stronger onset strip than \(M\ge m^3+3m\);
the two population-dependent cells are retained without claiming
that either one dominates for all J_*.
These exclude stated thin height ranges; they do not exclude all
taller cycles or improve the certified global period bound.

### 6. Scope of the quantitative order theorem

The result supplies a bounded disturbance of rank rotation, not
a bound on the number of contiguous monotone pieces. The F/G labels
may interleave. The absolute disturbance D grows with m; its relative
size becomes small only under the extra comparison \(m^{4/9}=o(e)\),
which is not established here for all actual cycles. Iterating (Q2)
also does not keep an error D without a separate accumulation argument.

The count/height restrictions use integer spacing, actual return
placement and primitive closure. They are not the earlier logarithmic
closure identity. They leave many possible count configurations,
including d=1, and supply no universal parity contradiction.

### 7. A guarded local inversion persists at arbitrarily large scales

For any odd integer t>=3, choose the free anchor \(m_0=t^5\), and set
\[
x=t^8+8,\quad x'=t^8+10,\quad
u=t^{12}+12t^4,\quad u'=t^{12}+15t^4,
\]
\[
N=t^{18}+18t^{10}+54t^2,\quad V=N-1,\quad z=t^9+9t-1.
\]
There are actual guarded paths
\[
x\xrightarrow O u\xrightarrow O V\xrightarrow E z,
\qquad
x'\xrightarrow O u'\xrightarrow E t^6\xrightarrow O t^9.
\tag{Q10}
\]
Here x,x',u,z,t^6,t^9 are odd, and u',V are even.
For j=4,5 the first O cell, with \(x_j=t^8+2j\) and
\(u_j=t^{12}+3t^4j\), has margins
\[
x_j^3-u_j^2=3t^8j^2+8j^3>0,
\]
\[
(u_j+1)^2-x_j^3
=2t^{12}+6t^4j+1-3t^8j^2-8j^3>0.
\]
For the upper margin use \(j\le(2/3)t^2\): it exceeds
\((2/3)t^{12}-(64/27)t^6>0\).
The E cell at u' has lower margin \(15t^4\) and upper margin
\(t^4(2t^2-15)+1>0\).
For the two remaining cells,
\[
N^2-u^3=216t^{12}+2916t^4>0,
\]
\[
u^3-(N-1)^2=2N-1-216t^{12}-2916t^4>0,
\]
\[
V-z^2=2t^9+18t-27t^2-2>0,\qquad
(z+1)^2-V=27t^2+1>0.
\]
For t>=3, \(t^2>8\), so the middle O lower margin exceeds
\((101/64)t^{18}-(729/1024)t^{12}-1>0\);
the E lower margin exceeds \(2t^9-(27/64)t^6-2>0\).
These verify every exact floor in (Q10).

All states lie in \([m_0,m_0^4)\), with
\[
m_0<t^6<x<x'<m_0^2<u<u'<m_0^3<V<m_0^4,
\quad m_0<t^9<z<m_0^2.
\]
For instance \(N<2t^{18}<t^{20}\), and \(z<t^{10}\).
Relative to \(k_0=\lceil m_0^{4/3}\rceil\), t^6 is below k_0,
while x,x',t^9,z are above it. Thus both paths are first returns
to the same interval \([k_0,m_0^2)\), with all intermediate guards
and placements correct, but
\[
x<x',\qquad F(x)=z>t^9=G(x').
\]
This is an open pair, not a cyclic assignment. The anchor is not
asserted to be its actual minimum. It shows precisely why local
guards do not make the merged branch monotone, while respecting
the localized, oriented inversion allowed by (Q8).

### 8. Shared OE cells determine every inversion

The authorized continuation asks whether the shared square and cube
cells restrict the shuffle beyond (Q3). They do. The hypotheses and
notation of (Q1)--(Q3) remain in force. Define the auxiliary integer
map on every lower source by
\[
b(x)=B(x)=E(O(x))=\lfloor x^{3/4}\rfloor.
\]
For an F source this is an arithmetic coordinate, not a claimed
actual E step from its odd intermediate state. For a G source it
is the actual low odd valley of the return.

**Common-cell criterion.** For selected sources x<y using F and G,
respectively,
\[
\boxed{F(x)>G(y)\quad\Longleftrightarrow\quad b(x)=b(y).}
\tag{Q11}
\]
Put v=b(y) and u=O(x). Monotonicity gives b(x)<=v. If b(x)<v,
then u<v^2 and
\[
F(x)=\lfloor u^{3/4}\rfloor
\le\lfloor v^{3/2}\rfloor=G(y),
\]
excluding an inversion. Conversely, if b(x)=v then u>=v^2,
so F(x)>=O(v)=G(y). Equality would give the first-return map two
distinct sources with the same image, impossible on the actual
cycle. Thus the inequality is strict.

The reverse implication uses common cyclic membership; it is not a
claim about arbitrary open paths. The cell has exact integer domain
\[
\left[
\lceil v^{4/3}\rceil,\,
\lceil(v+1)^{4/3}\rceil-1
\right].
\tag{Q12}
\]
At an actual inverted pair, its first images h=O(x) and t=O(y)
obey
\[
v^2<h<t<(v+1)^2.
\]
Here v,h are odd and t even. These local coordinates alone are not
the new cyclic restriction.

There is at most one G source in each such cell: two would have the
same actual valley v, and also the same return image O(v), contrary
to cycle injectivity. Consequently each F source has at most one
inversion partner. This is where the argument improves the earlier
bound by the size D of a possible neighborhood.

### 9. Exact cell-prefix permutations and the improved population bound

The fibers of b are consecutive blocks in source order. Their image
blocks are also ordered. For b(x)=v, the square cell gives
\[
O(v)\le F(x)\le O(v+1),\qquad G(x)=O(v).
\tag{Q13}
\]
For distinct integer cell values v<w, this places every image of
the first cell at or below every image of the second. Injectivity
makes their selected image order strict.

A cell with only F sources preserves order. In a cell containing
its unique G source, every F image is strictly above that G image,
and the F images preserve their own order. If the cell begins at
source rank a and its G source has rank b, its entire nontrivial
contribution to pi is therefore
\[
\pi(a)=a+1,\ldots,\pi(b-1)=b,\qquad \pi(b)=a,
\tag{Q14}
\]
with all later ranks in the same cell fixed. If a=b the contribution
is the identity. Different cells give disjoint prefix cycles.
In particular every F displacement is either zero or one; the G
displacement is minus the number of preceding F sources in its cell.

Let c_inv count the F sources preceding the G source of their cell.
Then, exactly,
\[
\boxed{
I=c_{\rm inv}\le c,\qquad
d-1\le I\le\min(c,(r-c)D),\qquad
I\equiv d-1\pmod2.
}
\tag{Q15}
\]
The G displacement bound D from Result 3 remains valid. The new
restriction on the cycle counts is
\[
\boxed{\gcd(L,o)\le c+1.}
\tag{Q16}
\]
This removes D from the forced high-odd population. Put
\[
J_{\rm cell}=\max(1,d-1).
\]
On the taller side M>=m^3, Result 5's distinct-state arguments now
give
\[
\boxed{
(M+1)^2>(m^2+2J_{\rm cell})^3,\quad
M\ge m^3+3mJ_{\rm cell},\quad
M\ge(q+2J_{\rm cell})^2+1.
}
\tag{Q17}
\]
These strengthen (Q4); they neither alter its original proof nor
assert a global period improvement. Equivalently, if c_0=c-c_inv
is the number of nonparticipating F sources, the exact count obeys
\[
c-c_0\ge d-1,\qquad c-c_0\equiv d-1\pmod2.
\tag{Q18}
\]
No lower bound on c_0 sufficient for a contradiction is established.

### 10. What is excluded, and what remains compatible

An F source moving forward by two ranks in pi is now impossible,
regardless of how large D is. As a fixed abstract control, take
e=12, r=9, s=3, and
\[
\pi=(2,0,1,3,4,5,6,7,8),
\]
with rank 0 labeled F and all other growing ranks G.
Then I=2, c=1, d=3. The permutation R_s composed with
pi extended by the identity is one 12-cycle, and the old (Q3)
allows it whenever D>=2. It fails (Q15), because the same F
would have to invert with two distinct G sources.
This is an abstract separation of the old and new conditions, not
a floor realization or a claim to meet the existing numerical floors.

Nonzero disorder is not eliminated. The exact open family in
Result 7 has
\[
b(t^8+8)=b(t^8+10)=t^6,
\]
and its selected F/G pair reverses order within that one cell.
Thus the new criterion is compatible with genuine local guards.
For d=1, primitive closure still allows a positive even I.

There is no immediate target-packing contradiction either. In a
cell containing G with odd valley v, all selected F targets are
odd integers in
\[
(O(v),O(v+1)].
\]
None can have an odd O predecessor: odd inputs at most v map at
or below O(v), and odd inputs at least v+2 map above O(v+1).
This agrees with their required even predecessors. It does not
make those targets unavailable to F.

The free odd target slots in that interval number
\[
\left\lfloor\frac{O(v+1)-O(v)}2\right\rfloor.
\]
For v>=64 this exceeds the number of all odd integers in the source
cell (Q12), so this free-slot comparison cannot by itself force a
deficit. Indeed the target count is greater than
\((3/4)\sqrt v-3/2\), whereas the source count is at most
\((2/3)(v+1)^{1/3}+1\le(3/4)v^{1/3}+1\).
Now \(\sqrt v\ge2v^{1/3}\) and \(v^{1/3}\ge4\) make the former
strictly larger. This compares an upper allowance for sources with
available parity slots; it does not assert that every slot has a
guarded F preimage.

The new result uses both exact cell separation and injectivity on
the common cycle. It does not obtain a contradiction merely by
renaming local predecessor intervals. The remaining arithmetic
problem is the occupation of these ordered cells by the same
closed orbit, especially how many F sources fail to participate.

### 11. Active cell prefixes must connect the rotation classes

The prefix description also sharpens the use of primitive closure.
Call i an active cut when pi(i)=i+1. These are precisely the
participating F ranks; there are I of them. On the d residues modulo
d, put an undirected edge between i mod d and (i+1) mod d for every
active cut i. For d=1 use the single-vertex graph.

This graph must be connected. To see this, express each prefix cycle
in (Q14) as its b-a adjacent transpositions on the active cuts
a,...,b-1. A union of connected components of the residue graph is
preserved by every such transposition and by R_s, since d divides s.
If the graph were disconnected, its corresponding proper nonempty
union of rank residue classes would therefore be invariant under
sigma=R_s composed with tau, contrary to a single primitive cycle.

For d>=2 this requires at least d-1 distinct active-cut residues:
for d>=3 the available edges form the cycle graph on the residues,
and a connected subgraph can omit at most one edge; for d=2,
one of the two possible cut residues is enough.
This is stronger than merely I>=d-1, because different active cuts
can represent the same residue edge.

When I=d-1, connectivity is also sufficient for the abstract
permutation to be one cycle. The d-1 transposition edges then form
a spanning tree on the d initial cycles of R_s. In any ordering,
each edge joins different components of the preceding forest, so
the corresponding transposition merges two distinct permutation
cycles. After d-1 merges only one remains. This is a permutation
statement; no floor realization follows from that sufficiency.

For a fixed control take e=12, r=9, s=3, d=3, with two F ranks 0
and 3, and pi swapping 0 with 1 and 3 with 4. These are two
disjoint FG cell-prefix cycles, with I=c=d-1=2. All numerical
conditions in (Q15) hold, but both active cuts are 0 modulo 3.
The residue class 2 is isolated, and sigma has three cycles:
\[
(0,4,6,9),\quad(1,3,7,10),\quad(2,5,8,11).
\]
Moving the second active cut from 3 to 4 instead connects all three
residue classes and gives one cycle, as the minimal-I criterion
predicts. Both are abstract controls, not claimed Juggler cycles.

Thus, at the sharp population boundary c=d-1, every F must precede
the G source of its cell, and those F ranks must occupy d-1 distinct
residues modulo d. No argument here forces that boundary or shows
its required arithmetic occupancy impossible.

### 12. Extremal participation gives a descent, not a smaller F cycle

The next authorized gate asks whether the actual extrema force
\(c_0\ge1\), or a stronger bound conflicting with (Q18).
Assume the taller side \(m^3\le M<m^4\), and let a be the largest
F source. Its tower is
\[
a\xrightarrow O h\xrightarrow O M\xrightarrow E t.
\]
Here h is the largest odd cycle state, and t=E(M)>a belongs to H.
Therefore t is not an F source: its next O image is even. The
following E step is actual, so, with T=B(t),
\[
a\xrightarrow{OOEOE}T,\qquad T\le a^{27/32}<a.
\tag{Q19}
\]
This is the existing power-envelope certificate, applied below an
interior cycle state. It is not a descent below the minimum m.

If a participates, let b>a be its G partner and v=B(a)=B(b).
The actual G tower is
\[
b\xrightarrow O p\xrightarrow E v\xrightarrow O w.
\]
Its growth and the inversion give a<b<w<t, with v<k. Since w also
exceeds the largest F source, its O image is even. Hence
W=B(w) and T=B(t) are actual odd cycle states. Injectivity of the
actual two-step map gives W<T. Also W=F(v)>v by the established
floor-aware OOE growth. Thus
\[
\boxed{v<W<T<a<b<w<t.}
\tag{Q20}
\]
Every displayed step is guarded under the hypotheses. The OOE
path from v to W is not an F tower of the section H, because
v<k and its first entry into H is already w after one step.

There is no established iteration of (Q20) through smaller F
sources. The endpoints W,T have no forced F labels or forced
membership in a smaller invariant cycle. Moreover, the proof that
the next O images of w,t are even used the global maximality of a;
that hypothesis cannot be transferred to an arbitrary smaller F.

The rank description supplies no contradiction either. In a
participating cell prefix with j F sources before G, the G source
has rank a_0+j and image rank s+a_0. Its strict growth forces j<s.
At c=d-1, this is automatic since j<=c=d-1 and s is a positive
multiple of d. The connected two-FG control in Result 11 satisfies
all participation, strict growth of the lower sources, strict
decrease of the upper sources, and primitive closure.

### 13. The minimum cell and the limit of its local control

The compulsory G return through m has a unique source y_m in the
exact cell
\[
[\lceil m^{4/3}\rceil,\lceil(m+1)^{4/3}\rceil-1].
\]
Every selected F in this cell before y_m participates; one after
y_m is a nonparticipant. The minimum alone does not force an F
after y_m, or even force any F into this cell.

The already recorded open family can be read with anchor
\(m=u^6\), for odd u>=3, instead of its original free anchor u^5.
Its two sources u^8+8 and u^8+10 then lie in the minimum cell;
their common valley is m, and the F source precedes the G.
The listed states have minimum m, maximum
\(u^{18}+18u^{10}+54u^2-1\), and lie below m^4.
This is the same two open paths, not a cycle or a new word family.
It shows the minimum-cell inference needs more than those local
guards; it does not refute a cycle-specific bound on c_0.

A single fixed control also prevents an invalid maximum extension.
At u=3, the original exact paths have
\[
\begin{gathered}
m=729,\ k=6561,\ a=6569,\ b=6571,\ h=532413,\ p=532656,\\
w=19683,\ t=19709,\ M=388483856.
\end{gathered}
\]
The next floors are
\[
O(w)=2761448\ \text{even},\qquad
O(t)=2766921\ \text{odd}.
\]
Their prescribed square roots are 1661 and 1663, but the second
square-root step has the wrong guard. This open control therefore
does not realize the maximum-participation diagram (Q20).
It would create a high odd state larger than h, so its listed
maximum cannot be retained in a purported quartic completion.
This is one failed extension, not a uniform exclusion. No further
parameter search is made.

### 14. All participation closes an auxiliary map, with a nonzero boundary term

On the taller side \(M\ge m^3\), assume c_0=0, so c>0.
For every x in H, the auxiliary B(x) is a selected
odd cycle state: this is actual for G and B sources, and the
shared G valley supplies it for a participating F.
Consequently the finite odd set \(Y=\mathcal C\cap[m,m^2)\) is
closed under
\[
U(x)=
\begin{cases}
O(x),&x<k,\\
B(x),&x\ge k.
\end{cases}
\tag{Q21}
\]
Compared with the actual first return to Y, only F edges change:
their old images F(x)>q are replaced by B(x)<k.
Each of the c distinct old F targets loses its only incoming edge.
No unchanged edge can replace it, by actual return injectivity;
changed edges end below k. Thus U is noninjective and has those
specified vertices of indegree zero.

A finite self-map can have transient trees feeding periodic
components, so these missing incoming edges are not a contradiction.
Every U cycle must contain a changed F edge. Otherwise it would
also be a cycle of the actual Y return permutation, hence all of
Y, impossible while avoiding its F sources. An auxiliary periodic
component therefore supplies no smaller actual Juggler cycle.

The failure of full-set exponent telescoping is explicit. Put
\(z(x)=\log\log x\), let \(\alpha_U(x)\) be 3/2 below k and 3/4
above, and define the nonnegative defect
\[
\delta_U(x)=z(x)+\log\alpha_U(x)-z(U(x)).
\]
Summing gives
\[
\sum_{x\in Y}\log\alpha_U(x)
=\sum_{y\in Y}(\operatorname{indeg}_U(y)-1)z(y)
 +\sum_{x\in Y}\delta_U(x).
\tag{Q22}
\]
The indegree term is exactly
\[
\sum_{x\ {\rm an}\ F\ {\rm source}}
\bigl(z(B(x))-z(F(x))\bigr)<0.
\tag{Q23}
\]
Old F targets lose their incoming edges, while the actual low
valleys gain redirected edges, counted with multiplicity.
If \(\Lambda=o\log(3/2)-e\log2\) is the original cycle surplus,
the left side of (Q22) is \(\Lambda-c\log(3/2)\).
Replacing an F exponent 9/8 by the B exponent 3/4 removes precisely
log(3/2) per F source.

Thus even a negative aggregate ideal exponent on Y would be
consistent with (Q22). Summation on a periodic component cancels
the indegree term, but the transient vertices cannot be included
as though U were the actual return permutation. Substitution of
the old and new defects only recovers the changed-edge identity.
This route supplies no lower bound on c_0 and no new count or
height exclusion.

### 15. Auxiliary periodic components and the threshold lift

The authorized component audit retains the taller-side hypotheses
\(m\ge16\), \(m^3\le M<m^4\), and initially assumes c_0=0.
Write
\[
\Lambda=\log(3^o/2^L)>0,\qquad A=\log(3/2).
\]
The auxiliary U in (Q21) is exactly the first return to
\([m,m^2)\) of the previously studied threshold map
\[
S_m(x)=
\begin{cases}
O(x),&m\le x<m^2,\\
E(x),&m^2\le x<m^3.
\end{cases}
\tag{Q24}
\]
If x<k then O(x)<m^2; otherwise O(x) lies in [m^2,m^3)
and its next E image is B(x). Every U periodic component therefore
lifts to an S_m cycle by inserting O(x) at its B edges.
All low states are odd. The wrong-parity high states of the lift
are precisely the periodic F sources' odd O images.
No actual Juggler cycle is obtained by this lifting.

Every U orbit visits H: a point below k maps there after one O.
Its first return T to H is prescribed G=OEO at every lower source,
including the former F sources, and B=OE at every upper source.
On H ranks, it has an exact nondecreasing lift
\[
\widetilde T(i)=f(i)+s,\qquad f(i+e)=f(i)+e.
\tag{Q25}
\]
For each cell prefix [a,b] in (Q14), f is constant a throughout
that prefix; elsewhere f(i)=i. This replaces the prefix rotation
by a collapse. The nonfixed f positions are exactly one rank
after the active cuts. Nondecreasing here concerns the lift to
integer ranks; T itself wraps from the upper to the lower block.

The periodic rank set of T is a union of ordered, separated
two-branch cycles. On each cycle the return is an exact rank
rotation. All components have a common period n and common
upper-source count p. For completeness, two integer lifts started
within e ranks remain within e ranks under every iterate, by
monotonicity and periodicity. Thus their asymptotic winding ratios
are equal. On each periodic cycle that ratio is p/n, with p,n
coprime by the two-block rotation, so equality of ratios gives
the same n,p.

Let N be the number of components and
\[
\Delta=sn-ep,\qquad t_{\rm tr}=e-Nn.
\]
Summing (Q25) along a lifted period gives
\[
\Delta=\sum_{i\ {\rm on\ that\ period}}(i-f(i))\ge0.
\tag{Q26}
\]
The terms are independent of the chosen periodic extension.
In particular d divides Delta. If every residue modulo d occurs
among the active cuts, then Delta>0: equality would make that
period follow an entire R_s residue class without a collapse,
but each class contains a nonfixed f position in this case.
Hence full coverage implies Delta>=d.

Each old F image has indegree zero also under T, since its image
is replaced by an existing G image. Therefore
\[
t_{\rm tr}\ge c>0.
\tag{Q27}
\]

### 16. The sharp boundary has one altered periodic edge

If an active-cut residue alpha is missing, the residue
rho=alpha+1 modulo d is untouched by f. Give residues the heights
0,...,d-1 in order starting at rho. Every nontrivial collapse
strictly decreases this height: its consecutive backward steps
cannot cross the missing cut. R_s preserves height.

Primitive closure requires the active-cut residue graph to be
connected, so at most one cut residue can be missing. Every other
residue class then contains a nonfixed f position. An orbit that
stays in such a class follows R_s until it meets a collapse, and
its height decreases. Thus T has exactly one periodic component:
the complete R_s orbit of rho, of period e/d, with r/d lower and
s/d upper sources.

At the sharp boundary c=d-1, (Q15) forces I=c and c_0=0.
The d-1 active cuts occupy distinct residues, leaving exactly one
missing residue; d>=2 on the taller side. The periodic class rho
contains exactly one F source, because each nonmissing active-cut
residue contains exactly one F. Inserting the deleted low valleys
and then the high threshold states gives
\[
\boxed{
\text{one U cycle of length }o/d,\quad
\text{one }S_m\text{ cycle of length }L/d,
}
\tag{Q28}
\]
with threshold branch counts o/d,e/d and exactly one wrong-parity
high odd state. All of these states belong to the original cycle.
The later G partner of the periodic F is transient: two periodic
points cannot have the same auxiliary successor. Its existence
therefore does not create a second component.

The period L/d is a threshold period, not an actual Juggler
period. The certified actual-cycle period floor cannot be applied
to it. The fixed S_3 cycle 3->5->11->3 shows the logical distinction:
its sole high state 11 is odd, and its actual successor is 36.
This small control is outside the current m>=16 hypotheses and
does not refute an arithmetic exclusion at large minima.

### 17. Comparing auxiliary defects with disjoint actual returns

The component periods have the common logarithmic surplus
\[
\lambda=n\log(9/8)-pA
       ={n\over e}\Lambda+{\Delta\over e}A.
\tag{Q29}
\]
Indeed a T period has n-p lower G returns and p upper B returns;
its U cycle has 2n-p low states and n B edges.
Plain component finance is the old threshold finance. The
additional inequality below uses disjoint selected actual blocks.

For a prescribed return R with ideal exponent alpha_R, put
\[
\delta_R(x)=\log\alpha_R+\log\log x-\log\log R(x).
\]
This is the sum of the step defects and is nonnegative by the
power envelope. Sum these defects over every U periodic component.
Cycle telescoping gives N lambda.

Keep every periodic O block and every genuine periodic B block.
For a periodic F source x, replace its prescribed B edge by the
actual OE block from its unique later G partner y, with
B(y)=B(x). The new block's defect exceeds the old one by exactly
\[
\log{\log y\over\log x}>0.
\]
This does not use the wrong E guard at O(x).

All comparison blocks are disjoint actual first-return blocks on Y.
Distinct periodic B edges have distinct target valleys. Thus the
partners of different periodic F sources are distinct. Each partner
is transient under U, so it is not also an unchanged periodic source.
The actual Y first-return towers partition the original cycle.

Let Gamma sum the displayed positive increments, and let D_F be
the sum of the actual defects over all F towers. These towers
are omitted from the comparison and are disjoint from it.
Every F tower has a high odd-to-even O edge, whose floor cannot be
exact, so D_F>0. The original cycle's total defect is Lambda.
Consequently
\[
\boxed{\Lambda\ge N\lambda+\Gamma+D_F.}
\tag{Q30}
\]
This is a budget on disjoint actual returns, not a sum over the
noninjective auxiliary map's transient states. Combining it with
(Q29) gives
\[
\boxed{
t_{\rm tr}\Lambda
\ge N\Delta A+e(\Gamma+D_F)>N\Delta A.
}
\tag{Q31}
\]
Under full active-cut residue coverage, Delta>=d and
t_tr<=e-1. Therefore
\[
\boxed{(e-1)\Lambda>d\log(3/2).}
\tag{Q32}
\]

**Conditional nonparticipant theorem.** For an actual primitive
taller-slab cycle with d=gcd(L,o)=1,
\[
\boxed{
(e-1)\Lambda\le\log(3/2)
\quad\Longrightarrow\quad c_0\ge1.
}
\tag{Q33}
\]
If c_0=0, the taller side has c>0 active cuts, which automatically
cover the sole residue modulo d=1. Then (Q32) contradicts the
stated hypothesis. Finally (Q18) gives c_0 congruent to c modulo 2
when d=1, so an even c strengthens the conclusion to c_0>=2.

The small-product condition is exact and can equivalently be written
\[
2\,3^{o(e-1)}\le3\,2^{L(e-1)}.
\]
It is an additional hypothesis, not proved for every cycle. For
d>1 the analogous condition (e-1)Lambda<=d log(3/2) only forces a
missing active-cut residue under c_0=0; its unique component may
still contain altered edges.

### 18. Separation controls and the remaining one-edge problem

A fixed abstract example separates the new budget from the previous
order conditions. Set e=7,r=5,s=2,c=2, with F ranks 0,3 and
\[
\pi=(1,0,2,4,3).
\]
The actual-form rank permutation R_s composed with pi extended by
the identity is one 7-cycle, with all lower sources increasing and
all upper sources decreasing. It has d=1, I=c=2 and correct inversion
parity. Its collapsed T has the unique periodic set {0,2,4,5};
hence n=4,p=1,Delta=1.

The corresponding original counts would be o=12,L=19, with
positive surplus. But the auxiliary threshold counts are 7,4
(period 11), whose surplus is larger:
\[
1<{3^{12}\over2^{19}}<{3^7\over2^{11}},
\]
where the second comparison reduces to 3^5<2^8. It cannot meet
(Q30). These are abstract count and permutation controls, not
floor-realized cycles or a claim concerning the numerical floor.

At the sharp boundary in Result 16, the budget instead gives the
necessary inequality
\[
{d-1\over d}\Lambda\ge\Gamma+D_F,
\]
which is not contradicted by the available bounds.
Cut its threshold cycle at the unique wrong edge h->E v.
The remaining path from v to h is actual. Its shared partner cell
gives h=v^2+2j, 1<=j<=v-1. Thus the exceptional E defect
\[
\delta_{\rm bad}=\log{\log h\over2\log v}
\ge\log{\log(v^2+2)\over2\log v}>0.
\]
Writing K=L/d, the genuine v-to-h path has K-1 edges and counts
(o/d,e/d-1). The complementary actual excursion from h to v has
(d-1)K+1 edges and counts ((d-1)o/d,(d-1)e/d+1).
Their exact defects are respectively
\[
\Lambda/d-\delta_{\rm bad},\qquad
(d-1)\Lambda/d+\delta_{\rm bad}.
\]
They sum to Lambda, so this decomposition does not itself exclude
the long excursion. No unconditional no-cycle or new numerical
period bound follows. The proved advance is (Q30)--(Q33), together
with the component classification; the uniform arithmetic gap
remains open.

### 19. Covered cells and the full auxiliary collapse

Retain the actual primitive taller-slab hypotheses
\(m\ge16\), \(m^3\le M<m^4\). Call an F source x **covered** if
its exact B cell contains a selected G source y. Such a partner
is unique, but it can precede or follow x. The distinction from
participation is essential: only x<y contributes an inversion.

For every F source,
\[
\boxed{x\text{ is covered}\quad\Longleftrightarrow\quad B(x)\in Y.}
\tag{Q34}
\]
One implication uses its G partner's actual valley. Conversely,
\(m\le B(x)<k\). Every actual first return to Y ending below k
is OE: the O and OOE returns end at or above q>k. Its unique
source y therefore has B(y)=B(x), and its H return is G.
It cannot be x, whose O image is odd. Thus all F sources are
covered if and only if U in (Q21) is a self-map of Y.
An uncovered B value may be even or an unselected odd integer.

Suppose henceforth that every F is covered. A selected lower
cell consists of F sources, its unique G, and possibly more F
sources. If its source ranks are a,...,b and its G rank is g,
the actual G image has rank s+a by Result 9. The auxiliary
H return therefore has the lift
\[
\widetilde T(i)=f(i)+s,\qquad f(i)=a\quad(a\le i\le b),
\qquad f(i+e)=f(i)+e.
\tag{Q35}
\]
Outside these lower cells, f(i)=i. This collapses the **entire**
cell, including F sources after G. The lift is nondecreasing and
f(i)<=i. The full collapse cuts are a,...,b-1; their number is c.
The inversion cuts a,...,g-1 form a subset, with number I=c-c_0.
Neither the full collapse cuts nor the nonfixed positions should
be identified with the inversion cuts when late F sources exist.

The proof of the common component counts in Result 15 still
applies: T is strictly increasing on each branch of a periodic
set, its lower branch grows and its upper branch decreases, so
each component is an ordered two-block rotation. Its degree-one
nondecreasing lift gives the same winding ratio for all components.
Write n,p for their common H period and upper count, N for the
number of components, and
\[
\Delta=sn-ep,\qquad t_{\rm tr}=e-Nn.
\]
The old F images again lose all incoming edges. Consequently
\[
\Delta=\sum_{i\text{ in one component}}(i-f(i))\ge0,
\qquad d\mid\Delta,\qquad t_{\rm tr}\ge c>0.
\tag{Q36}
\]
If the full collapse cuts cover all residues modulo d, then
Delta>=d, by the same untouched-rotation argument as before.
In particular this holds when d=1: c>0 supplies a nonfixed point,
which the complete coprime rotation orbit cannot avoid.

Let q_- count periodic F sources whose G partner precedes them.
Each has rank i>g>=a=f(i), hence integer displacement at least one.
Distinct periodic F sources have distinct G partners. Therefore
\[
\boxed{q_-\le\min(c_0,r-c,N\Delta).}
\tag{Q37}
\]
The last bound couples the harmful substitutions to the same rank
displacement that contributes to the component surplus.

### 20. A late partner has a small negative replacement shift

Put z(u)=log log u and
\[
\eta(m)=\log{\log(m+1)\over\log m}>0.
\]
If y<x are a covered G/F pair with B(y)=B(x)=v, the exact cell
inequalities give
\[
y\ge v^{4/3},\qquad x<(v+1)^{4/3}.
\]
The function z'(u)=1/(u log u) is decreasing for u>1, so
\[
\boxed{0<z(x)-z(y)<\eta(v)\le\eta(m)<{1\over m\log m}.}
\tag{Q38}
\]
Thus its negative replacement shift is controlled uniformly by
the minimum, without assuming an average distribution of states.

Its own F tower does not absorb this negative shift. To see this
directly, for x>1 the exact composition is
\(F(x)=\lfloor O(x)^{3/4}\rfloor>x^{9/8}-2\): the first floor
removes less than one, the function u^(3/4) has derivative below
one for u>=1, and the last floor removes less than one.
The odd sources satisfy x-y>=2. Convexity then gives
\[
x^{9/8}-y^{9/8}\ge{9\over4}y^{1/8}>2,
\qquad F(x)>y^{9/8}.
\]
For the actual F-tower defect this implies
\[
\boxed{\delta_F(x)+z(y)-z(x)
=\log{(9/8)\log y\over\log F(x)}<0.}
\tag{Q39}
\]
Other omitted towers still contribute positive loss. This rules
out only absorbing each late shift into its own F tower.

Late pairs themselves are compatible with local guards. For
every odd t>=3, the F tower in Result 7 can share its minimum
cell with the following earlier G source:
\[
\begin{aligned}
y=t^8+6&\xrightarrow O t^{12}+9t^4
          \xrightarrow E t^6\xrightarrow O t^9,\\
x=t^8+8&\xrightarrow O t^{12}+12t^4
          \xrightarrow O t^{18}+18t^{10}+54t^2-1
          \xrightarrow E t^9+9t-1.
\end{aligned}
\tag{Q40}
\]
The first path has parities odd, even, odd, odd, while the second
has odd, odd, even, odd. For P=t^12+9t^4, its new square margins are
\[
y^3-P^2=27t^8+216>0,
\quad (P+1)^2-y^3=t^8(2t^4-27)+18t^4-215>0.
\]
Also \((t^6+1)^2-P=t^4(2t^2-9)+1>0\).
The remaining floor margins are already proved in Result 7.
At the anchor m=t^6, k=t^8, both sources are in the minimum B
cell and both paths are first returns to H. Their common listed
minimum is m, their listed maximum is between m^3 and m^4, and
y<x. These are open paths for every such t, not a family of cycles.

### 21. Rank displacement pays for the negative shifts

Assume all F sources are covered. The common component surplus
is still
\[
\lambda={n\over e}\Lambda+{\Delta\over e}A,
\qquad \Lambda=\log(3^o/2^L),\quad A=\log(3/2).
\]
Repeat the disjoint actual-block comparison of Result 17, now
allowing either ordering of a periodic F and its partner. The
chosen genuine OE blocks are still distinct: two periodic sources
cannot have the same auxiliary successor. Their G partners are
transient, so none is also an unchanged periodic source. These
blocks, the unchanged periodic O/OE blocks, and all actual F
towers are edge-disjoint parts of the actual Y return partition.

Let Gamma_+ sum z(y)-z(x) for periodic F sources with x<y, and
Gamma_- sum z(x)-z(y) for those with y<x. Let D_F>0 be the total
actual F-tower defect and D_rem>=0 the defects of all remaining
unused actual blocks. Exact partitioning gives
\[
\Lambda=N\lambda+\Gamma_+-\Gamma_-+D_F+D_{\rm rem}.
\tag{Q41}
\]
This identity alone gives no exclusion. The estimates (Q37)--(Q38)
add the required control. They imply
\[
\begin{aligned}
t_{\rm tr}\Lambda+e\Gamma_-
 &=N\Delta A+e(\Gamma_++D_F+D_{\rm rem})>N\Delta A,\\
t_{\rm tr}\Lambda
 &>N\Delta A-eq_-\eta(m)\\
 &\ge N\Delta\bigl(A-e\eta(m)\bigr).
\end{aligned}
\tag{Q42}
\]
For q_-=0 the same strictness follows from D_F>0. The last line
uses q_-<=N Delta, so no unknown late-F population occurs in it.

**Conditional uncovered-cell theorem.** Under the stated actual
primitive taller-slab hypotheses,
\[
\boxed{
\gcd(L,o)=1,\qquad
(e-1)\Lambda+e\eta(m)\le\log(3/2)
\quad\Longrightarrow\quad
\exists x\text{ an F source with }B(x)\notin Y.
}
\tag{Q43}
\]
Suppose instead that every F is covered. Coprimality gives
Delta>=1, while N>=1 and t_tr<=e-1. Since e>=2 and Lambda>0,
the assumed inequality ensures A-e eta(m)>0. Formula (Q42) then
implies
\[
t_{\rm tr}\Lambda>A-e\eta(m)
\ge(e-1)\Lambda\ge t_{\rm tr}\Lambda,
\]
a contradiction. Equivalently every all-covered coprime cycle
must satisfy (e-1)Lambda+e eta(m)>A. More generally, if all F are
covered and the full collapse cuts cover every residue modulo d,
\[
(e-1)\Lambda+de\eta(m)>dA.
\tag{Q44}
\]
For A-e eta(m)>0 this follows from Delta>=d and (Q42); otherwise
it is immediate from Lambda>0. The full-cut coverage hypothesis
is essential in this more general statement.

Condition (Q43) is additional and has not been proved uniformly.
It strengthens (Q33)'s conclusion at the explicit extra cost
e eta(m)<e/(m log m). It also implies the earlier nonparticipant
conclusion, since an uncovered F necessarily contributes to c_0.
Its absent auxiliary valley need not be a missing actual successor:
the actual F return remains in the cycle.

### 22. A periodic late F is allowed by the abstract order

For a fixed abstract control take e=12, r=9, s=3 and the cells
(0_F,1_G,2_F) and (4_F,5_G,6_F), with the other lower ranks G.
Then c=4, I=2, c_0=2 and
\[
\pi=(1,0,2,3,5,4,6,7,8).
\]
The actual-form permutation is the single cycle
\[
(0,4,8,11,2,5,7,10,1,3,6,9).
\]
The full-cell collapse fixes other ranks and sends 0,1,2 to 0
and 4,5,6 to 4 before applying R_3. Its unique periodic component is
\[
(3,6,7,10,1),\qquad n=5,\quad p=1,\quad\Delta=3.
\]
Every lower image grows and every upper image decreases for both
maps. Its sole periodic F is rank 6, whose G partner 5 precedes it
and is transient. The total periodic displacement is 2+1=3,
so q_-=1<=N Delta is visible exactly in this control.
Thus primitive order alone does not force an early periodic F.
No floor realization is asserted, and this example does not refute
(Q43) or any established numerical floor.

The new restriction uses both full-cell rank displacement and
the integer-cell bound on negative shifts. Neither an absent
auxiliary valley nor the conditional inequality by itself is a
no-cycle theorem. No larger slab or further gate is opened here.

### 23. A preceding selected cell closes a projected return map

Retain the actual primitive taller-slab hypotheses, and write
z(u)=log log u, A=log(3/2), b=log(9/8). We no longer assume that
every F source is covered. List the selected G valleys as
\[
m=w_0<w_1<\cdots<w_{g-1}<k,\qquad g=r-c\ge1,
\]
and set w_g=k as a sentinel. The first valley is m because the
minimum has its compulsory actual G return. For a lower source
x choose j with w_j<=B(x)<w_{j+1}, and let y_j be the unique
selected G source with B(y_j)=w_j. Define on H
\[
T_-(x)=
\begin{cases}
G(y_j),&x<\ell,\\
B(x),&x\ge\ell.
\end{cases}
\tag{Q45}
\]
All targets are actual selected H states. Each actual G or upper
B source keeps its return, while an F source uses a projected
G return. If its cell is covered this agrees with prescribed G(x);
otherwise its valley is moved to a strictly smaller selected one.
The resulting map is not asserted to be a threshold-map return.

Let a_j be the first H source rank in the selected cell w_j,
and let gamma_j be its G-source rank. The cell at m is first,
so a_0=0. With a_g=r, all ranks in a_j,...,a_{j+1}-1 project
to the same G image of rank s+a_j. Consequently
\[
\widetilde T_-(i)=f_-(i)+s,\qquad
f_-(i)=a_j\quad(a_j\le i<a_{j+1}),
\qquad f_-(i+e)=f_-(i)+e.
\tag{Q46}
\]
For upper ranks f_-(i)=i. This is a nondecreasing degree-one
lift, with f_-(i)<=i. Each projection block contains exactly one
G and otherwise F sources, so its total number of collapse cuts
is c. Every actual F image has indegree zero under T_-.

Projected lower returns need not grow. Nevertheless, on each
periodic component the two source blocks have strictly ordered
image blocks, by periodic injectivity. This makes the restricted
permutation a rank rotation. The common winding-ratio argument
then gives common period n and upper-source count p for all
components, including the possibility n=1,p=0. Let N be the
number of components. As before,
\[
\Delta=sn-ep=\sum_{i\text{ on one component}}(i-f_-(i))\ge0,
\quad d\mid\Delta,\quad t_{\rm tr}=e-Nn\ge c>0.
\tag{Q47}
\]
For d=1 one has Delta>=1: a zero-displacement component would
follow the entire coprime R_s orbit and could not avoid the
nonfixed collapse points. No pointwise growth assumption is
needed for this argument.

### 24. The signed neighboring-cell budget retains the missing gap

Assign ideal exponent 9/8 to each lower projected return and 3/4
to each upper return. This defines nonnegative defects even for
the projected F returns: G(y_j)<=G(x)<=x^(9/8), since the chosen
valley does not exceed B(x). A component's total formal defect is
\[
\lambda=nb-pA={n\over e}\Lambda+{\Delta\over e}A.
\tag{Q48}
\]
These are defects of the projected map, not exact floor defects
of an S_m cycle when an uncovered source occurs.

Fix just one periodic component P. Keep its genuine G and upper
B return blocks. For each periodic F source x replace its projected
G return by the actual G block from y_j. The defect changes by
z(y_j)-z(x). Distinct periodic targets give distinct partners;
each partner is transient because it shares x's projected target.
Thus the chosen actual H-return blocks are disjoint. All actual
F towers remain omitted and have total defect D_F>0. If D_rem
denotes the remaining unused actual defects, exact partitioning
gives
\[
\Lambda=\lambda+\Gamma_+-\Gamma_-+D_F+D_{\rm rem},
\]
where Gamma_+ and Gamma_- sum the positive and negative magnitudes
of the partner shifts for this component only. Hence
\[
\boxed{(e-n)\Lambda+e\Gamma_-
=\Delta A+e(\Gamma_++D_F+D_{\rm rem})>\Delta A.}
\tag{Q49}
\]
The comparison uses actual F/G/B return partitions throughout;
the projection does not make a missing same-cell block actual.

For a negative partner shift, write i for the F source rank,
gamma_j for its G-partner rank, and
\(d_i=i-a_j\). Then i>gamma_j>=a_j, so d_i>=1. There is at
most one periodic source per projection block, and therefore
\[
\sum_{i\text{ with negative shift}}d_i\le\Delta.
\tag{Q50}
\]
The source intervals from gamma_j to i are disjoint in rank
order. For an uncovered source their numerical gap is not
confined to one B cell. With v=B(x) and u=B(y_j)<v,
\[
0<z(x)-z(y_j)<\log{\log(v+1)\over\log u}.
\tag{Q51}
\]
Replacing this interval by eta(m) would discard the vacant cells.

There is a second way to see the same boundary. At the OE level,
\[
\delta_B(y_j)-\delta_B(x)
=z(y_j)-z(x)-\bigl(z(u)-z(v)\bigr)>-\eta(m).
\]
The last bound is valid because delta_B(y_j)>=0 and
delta_B(x)<eta(v)<=eta(m). But moving the auxiliary target from
v to u increases its formal defect by z(v)-z(u). This term
occurs also in the projected component surplus and cancels
exactly when the genuine block is substituted. Thus the small
two-endpoint defect difference cannot replace the signed source
shift in (Q49).

### 25. Every projected component needs an uncovered gap witness

The preceding budget supplies a placement restriction under the
same hypotheses as (Q43), rather than requiring a new condition.
Assume
\[
d=1,\qquad(e-1)\Lambda+e\eta(m)\le A.
\tag{Q52}
\]
For each periodic component of T_- define
\[
\tau={A\over e}-{(e-n)\Lambda\over e\Delta}.
\tag{Q53}
\]
Here Delta>=1, and
\[
\tau-\eta(m)
\ge{\bigl((\Delta-1)(e-1)+n-1\bigr)\Lambda\over e\Delta}
\ge0.
\]
In particular tau is positive, also when n=1,p=0.
Formula (Q49) gives Gamma_-/Delta>tau. By (Q50), if every
negative shift were at most d_i tau, their sum could not exceed
Delta tau. Consequently that component contains an F source x
with preceding G partner y_j satisfying
\[
\boxed{
{z(x)-z(y_j)\over i-a_j}>\tau\ge\eta(m).
}
\tag{Q54}
\]
This source must be uncovered: a covered negative pair has
z(x)-z(y_j)<eta(m) by (Q38), and i-a_j>=1. Positive partner
shifts cannot supply this witness.

Thus, under (Q52),
\[
\boxed{\text{every periodic component of }T_-
\text{ contains an uncovered F source};\qquad
\#\{\text{uncovered F sources}\}\ge N.}
\tag{Q55}
\]
Moreover, write H_0<...<H_{e-1} for the actual H states. At least
one adjacent selected gap between the witness partner and source
obeys
\[
z(H_{h+1})-z(H_h)>\tau,
\qquad \gamma_j\le h<i.
\tag{Q56}
\]
Otherwise summing those i-gamma_j gaps, with i-gamma_j<=i-a_j,
would contradict (Q54). Such a gap crosses B cells, since two
sources in a common B cell have z difference below eta(m).

This is stronger than the existence statement (Q43): uncovered
sources confined to transient branches cannot suffice. Neither
N nor the witness gap is bounded in a way that excludes all
actual cycles. The numerical/count hypothesis remains additional.

A fixed abstract separation has e=7,r=5,s=2 and pi the identity.
The actual-form return is the single R_2 cycle
(0,2,4,6,1,3,5). Assign lower labels G,F,G,F,G. Rank 1 shares
the cell of G rank 0, while F rank 3 has an uncovered cell
between the G cells at ranks 2 and 4. Its predecessor collapse is
\[
f_-=(0,0,2,2,4,5,6),
\qquad T_-=(2,2,4,4,6,0,1).
\]
The unique periodic component is (1,2,4,6), with n=4,p=1,
Delta=1. Its only periodic F is covered rank 1; uncovered
rank 3 is transient. Both maps have lower growth and upper
decrease. Its counts L=19,o=12 are the previously used positive
surplus control; at m=729 the exact sufficient check for (Q43)
already appears in the fixed tests. Global uncovered existence
alone permits this assignment, but (Q55) excludes an actual
realization under the stated condition. No floor realization or
compatibility with the published numerical period floor is claimed.

A second assignment at these same counts groups lower ranks
0,1,2 under G rank 0, with rank 1 covered and rank 2 uncovered,
and leaves G ranks 3,4 separate. It has
f_-=(0,0,0,3,4,5,6) and a unique fixed component {2}, with
n=1,p=0,Delta=2. This checks the zero-winding case that must not
be removed by an unjustified growth assumption. It is abstract.

### 26. The maximum neighboring-cell gap gives no new exclusion

One might replace eta(m) in the former proof by
\[
\Omega=\max_{0\le j<g}\bigl(z(w_{j+1})-z(w_j)\bigr).
\]
Each harmful projected shift is below its bucket's gap. Distinct
periodic buckets have disjoint intervals, so their total is also
below z(k)-z(m). Together with the rank displacement this gives,
for d=1, the necessary condition
\[
(e-1)\Lambda+e\Omega>A.
\tag{Q57}
\]
However (Q57) is already forced by the old counts and the span.
Put C=log(4/3)=A-b. Since k>=m^(4/3),
\[
\Omega\ge{z(k)-z(m)\over r-c}\ge{C\over r-c},
\qquad eC=rA-\Lambda.
\]
Hence
\[
e\Omega\ge A+{cA-\Lambda\over r-c}.
\]
If Lambda<=cA, then e Omega>=A, and (Q57) follows from
Lambda>0. If Lambda>cA, then c>=1 implies Lambda>A, so
(e-1)Lambda>A already. Thus (Q57) is a reparameterization,
not an additional arithmetic restriction.

The new placement theorem uses the actual intervals selected by
each periodic component and their individual rank displacement.
A maximum over all neighboring valley gaps loses that information.
No bound currently makes (Q54) or (Q56) impossible in a cycle.
The signed comparison therefore localizes the remaining obstruction
without proving uniform no-cycle or opening a further gate.

### 27. Sorting the power envelope gives a positive rotation defect

Retain the actual primitive quartic hypotheses, and write the sorted
section as H_0<...<H_{e-1}. Put z_i=log log H_i, A=log(3/2),
b=log(9/8), and extend the potential by z_{i+e}=z_i+A. Its cyclic
gaps g_i=z_{i+1}-z_i are positive: the ordinary gaps are positive
by order, and the wrap gap is positive because
H_0>=m^(4/3) and H_{e-1}<m^2. Their sum is A.

The actual lower return images are the permutation
H_{s+pi(i)}, 0<=i<r. Each obeys the power envelope
H_{s+pi(i)}<=H_i^(9/8), with all floor losses retained.
For a fixed i, the first i+1 sources therefore supply i+1 distinct
lower-return images at most H_i^(9/8). Their i-th order statistic
cannot exceed this bound. Hence
\[
H_{s+i}\le H_i^{9/8}\qquad(0\le i<r).
\tag{Q58}
\]
This argument sorts the actual images; it does not replace an F
path by a prescribed G path or assert any new parity guard.

On the upper branch the actual ordered return is H_{i-r}=B(H_i),
so H_{i-r}<=H_i^(3/4). Because log(3/4)+A=b, both branches give
the following nonnegative redistributed defects:
\[
\varepsilon_i=z_i+b-z_{i+s}\ge0,\qquad
\sum_{i=0}^{e-1}\varepsilon_i=eb-sA=\Lambda.
\tag{Q59}
\]
The indices in (Q59) use the lift, including upper-branch wraps.
These are defects of the sorted power envelope. Before pi is
shown to be the identity they need not equal the defect of the
actual return starting at H_i. Their total is nevertheless the
original cycle surplus, by the established count identities.

Subtracting two neighboring equations gives the exact gap transport
\[
g_{i+s}-g_i=\varepsilon_i-\varepsilon_{i+1}.
\tag{Q60}
\]
Assume d=gcd(e,s)=1. Given i,j, choose 0<=k<e with j=i+ks mod e.
Summing (Q60) for k steps writes g_j-g_i as the difference of
two partial sums of epsilon. Each sum uses distinct indices and
lies between zero and Lambda. Consequently
\[
|g_i-g_j|\le\Lambda,\qquad
\boxed{g_i\ge{A-(e-1)\Lambda\over e}\quad\hbox{for every }i.}
\tag{Q61}
\]
For the second assertion, sum g_j<=g_i+Lambda over j!=i and
use sum g_j=A. This is the positive rotation-defect grid estimate,
now available in the quartic slab because of the sorted envelope.

### 28. The existing small-product condition separates every selected cell

Under exactly the additional hypotheses of (Q43), formula (Q61)
gives g_i>=eta(m). Every selected H state has B(H_i)>=m, by the
exact OE cell and H_i^3>=m^4. If i<j and B(H_i)=B(H_j), the
strict same-cell estimate (Q38) gives
\[
z_j-z_i<\eta(B(H_i))\le\eta(m).
\]
But the left side is the sum of j-i ordinary adjacent gaps, and
is at least eta(m), a contradiction. We obtain the stronger
conditional conclusion
\[
\boxed{
\begin{gathered}
d=1,\quad(e-1)\Lambda+e\eta(m)\le A\\
\Longrightarrow\quad B|_H\text{ is injective},\quad
I=0,\quad\pi=\mathrm{id},\quad
\text{every F source is uncovered.}
\end{gathered}}
\tag{Q62}
\]
Indeed a covered F would share its B value with the distinct
selected G source provided by (Q34). The cell inversion criterion
then leaves no inversions and makes the actual return permutation
the pure rank rotation R_s. In particular all c F sources, not
merely one in each projected component, have unselected auxiliary
valleys. The stronger quantitative separation
z_j-z_i >= (j-i)[A-(e-1)Lambda]/e also holds for i<j.

The small-product hypothesis is still not proved uniformly. Nor
does a pure rank rotation identify F with G or force a wrong
parity: the return words remain the actual guarded words. This
is a new conditional order/cell restriction, not a whole-slab
or global no-cycle theorem.

### 29. Transport preserves a witness but does not exclude it

For a negative periodic F substitution, let i be its rank,
gamma<i its selected G partner rank, a<=gamma its predecessor
block start, and d_i=i-a. Then pi(i)=i, pi(gamma)=a. With actual
return defects delta_F(i), delta_G(gamma), the source and target
intervals satisfy
\[
S_i:=z_i-z_\gamma
=T_i+\delta_F(i)-\delta_G(\gamma),\qquad
T_i:=z_{s+i}-z_{s+a}.
\tag{Q63}
\]
The source intervals and the target intervals are each disjoint
over the negative substitutions in one projected component.
The target intervals have total rank length sum d_i<=Delta.

Substitute (Q63) into the component identity behind (Q49). Exactly the
F defects at the negative sources cancel from the reserved F
sum. Their genuine G-partner defects replace them on the positive
side. These G defects are strictly positive because the actual
OE part includes an even-to-odd square-root step, which cannot
be exact. The result is
\[
(e-n)\Lambda+e\sum_i T_i>\Delta A.
\tag{Q64}
\]
Under the small-product hypotheses (Q52), Delta and tau are positive.
Formula (Q64) and sum d_i<=Delta therefore produce a target
interval with T_i/d_i>tau, and
an adjacent target gap greater than tau, just as the source
budget does. This is a transported form of the existing positive
remainder budget. It provides no upper bound contradicting the
witness. A particular source witness need not be the target witness.

For a fixed control, reuse e=7,r=5,s=2, pi=id and
f_-=(0,0,0,3,4,5,6), now labeling both ranks 1 and 2 uncovered F
and ranks 0,3,4 G. The projection has the unique fixed component
{2}, with n=1,p=0,Delta=2. These counts give
Lambda=12 log 3-19 log 2=7b-2A, with 0<Lambda<A, and the prior
exact m=729 check verifies the small-product condition.

Set h_i=(Lambda/100) if i=2 mod7 and zero otherwise, and take
\[
z_i=z_0+{iA\over7}+h_i,\qquad
\delta_i={\Lambda\over7}+h_i-h_{i+2}.
\tag{Q65}
\]
These are strictly ordered real potentials and strictly positive,
nonconstant defects. They satisfy the exact lifted return equation
z_{i+2}=z_i+b-delta_i and sum delta_i=Lambda. The source interval
(0,2) has normalized gap A/7+Lambda/200; its first target (2,4)
has A/7-Lambda/200. Every subsequent cyclic lifted length-two
interval has normalized gap at least
\[
{A\over7}-{\Lambda\over200}
>\tau={A\over7}-{3\Lambda\over7}.
\tag{Q66}
\]
Thus even a full circuit of transport with positive unequal losses
does not force the proposed upper bound. This is a real-potential
control of the transport hypotheses, not an integer floor-cell
realization, parity realization, or actual cycle. It does not meet
or challenge the published period floor. The first unwrapped pair
already makes the relevant separation; later intervals use the
stated cyclic lift rather than raw wrapped endpoint differences.

**Decision for this gate: PROMOTE (Q62)** and its quantified gap
separation. **CLOSE** the bare transport-to-upper-bound shortcut:
(Q63)--(Q66) retain its budget and show its missing arithmetic
input. Exact integer realization of the separated pure-rotation
case and removal of the small-product condition remain **PARK**.

### 30. Absolute cells localize a missing valley's selected image

Assume the actual primitive quartic hypotheses and (Q43). Write the
strictly sorted section as H_0,...,H_{e-1}, with e=r+s. Define
\[
v_i=B(H_i)\quad(0\le i<e),\qquad
w_i=O(v_i),\quad T_i=H_{s+i}\quad(0\le i<r).
\tag{Q67}
\]
The v_i are strictly increasing integers by (Q62). The compulsory
G source through m must be H_0: an earlier source would have the
same minimal B value, violating injectivity. Consequently
\[
v_0=m,\quad H_0\text{ is G},\quad T_0=O(m)=q,
\qquad v_{r+j}=H_j\quad(0\le j<s).
\tag{Q68}
\]
The lower valleys v_i lie in [m,k), while the upper valleys in
(Q68) are actual selected H states. The O images w_i are strictly
increasing and lie numerically in [q,m^2), but need not be selected
or odd. We call w_i a *missing-valley image* at an F source; its
O edge is prescribed, and is actual only if v_i is odd.

The exact envelope from Result 8 gives
\[
w_i\le T_i\le O(v_i+1),
\qquad w_i=T_i\text{ at every G source}.
\tag{Q69}
\]
For i>=1, distinct integer cells give v_{i-1}+1<=v_i. If the
preceding source is G, then T_{i-1}=O(v_{i-1})<O(v_i).
If it is F, then T_{i-1}<=O(v_{i-1}+1)<=O(v_i). Therefore
\[
\boxed{T_{i-1}\le w_i\le T_i\qquad(1\le i<r).}
\tag{Q70}
\]
These are adjacent ranks in H. A strict image w_i<T_i can thus
belong to H only by hitting the preceding target. Equality on
the left is characterized exactly by
\[
\boxed{
w_i=T_{i-1}\iff
\begin{cases}
i-1\text{ is F},\\
v_i=v_{i-1}+1,\\
F(H_{i-1})=O(v_{i-1}+1).
\end{cases}}
\tag{Q71}
\]
Indeed equality sandwiches O(v_i) between T_{i-1} and
O(v_{i-1}+1); strict increase of O forces consecutive valleys.
The converse follows directly. If the current image is strict,
the current source is F as well. No parity of the unselected
valley is silently imposed.

The absolute values of the consecutive valleys now matter. Put
v=v_{i-1}. Their exact source cells imply
\[
z(H_i)-z(H_{i-1})<z(v+2)-z(v).
\]
If v>=2m, decreasing z'(u)=1/(u log u) gives
\[
z(v+2)-z(v)\le z(2m+2)-z(2m)
=\log\left(1+{\log(1+1/m)\over\log(2m)}\right)
<\eta(m).
\tag{Q72}
\]
This contradicts the selected gap lower bound in (Q62). Hence
\[
\boxed{
w_i<T_i,\ w_i\in H\quad\Longrightarrow\quad
w_i=T_{i-1},\ i-1,i\text{ are F},\
v_i=v_{i-1}+1\le2m.
}
\tag{Q73}
\]
In particular, every strict missing-valley image with v_i>2m
lies outside H. More generally, the first index of each run of
strict images has T_{i-1}<w_i<T_i, so there is at least one
unselected image per strict run. This is a new conditional
localization of re-entry. It does not say that these strict
images must exist, or that their absence from H contradicts
the actual F returns.

### 31. Adding the missing valleys has an exact closure criterion

Let Y be the actual low section and insert its missing F valleys:
\[
Y^+=Y\cup\{v_i:i\text{ is F}\}
=H\,\dot\cup\,\{v_i:0\le i<r\}.
\]
Thus |Y^+|=e+r=o; this integer set need not consist only of odd
or actual periodic states. Prescribe U^+=O below k and U^+=B
at or above k. All H images already lie in Y^+. The only closure
question is whether every w_i belongs to H. Since w_i>=q and
the r images are strictly increasing, closure would put r
distinct values into the r-element block H_s,...,H_{e-1}.
Sorted matching therefore gives
\[
\boxed{U^+(Y^+)\subseteq Y^+
\iff F(H_i)=G(H_i)\text{ at every F source}.}
\tag{Q74}
\]
If any F image is strict, merely adding its missing valley does
not close this finite set. If all endpoints agree, the enlarged
set does have an exact threshold interpretation. Put
Z=Y^+ disjoint-union O(H) and use S_m=O below m^2, E above it.
Its lower towers are
\[
H_i\xrightarrow O O(H_i)\xrightarrow E v_i
\xrightarrow O H_{s+i},
\]
and its upper towers are the original OE returns. All towers
are disjoint by the distinct source and valley lists. Their
H return is the primitive R_s, so Z is one threshold cycle
with exactly the original period L and branch counts (o,e).

For an F tower this construction retains the high odd state
h=O(H_i), removes the actual even peak O(h)>=m^3, and inserts
the missing valley v_i. The c retained high odd h states have
wrong threshold E guards. Every even inserted valley contributes
an additional wrong threshold O guard. The endpoint and ideal
exponent of each replaced tower are unchanged, so its total
log-log loss and the cycle surplus Lambda are unchanged.

Thus the equality case supplies a threshold cycle with explicit
wrong parities, not a smaller actual cycle or a loss contradiction.
In the strict case, adjoining further images changes the state
set and its counts without a proved preserved-surplus relation.
Neither automatic completion is a no-cycle argument.

### 32. Endpoint equality is a thin absolute-cell condition

For an actual F source x set h=O(x), v=B(x), and a=O(v).
The guards give x,h odd, O(h) even and F(x) odd. The lower
cell face sharpens to
\[
h\ge v^2+1+\mathbf1_{v\text{ odd}}.
\tag{Q75}
\]
For even v this follows from parity. For odd v, h=v^2 would
give O(h)=v^3 odd, and the next odd spacing is v^2+2.
Nevertheless, the exact equality test remains
\[
\boxed{F(x)=G(x)\iff h^3<(a+1)^4.}
\tag{Q76}
\]
Its other cell face a^4<=h^3 follows from a^2<=v^3 and h>=v^2.
For v>=8, equality forces the unique possible source
\[
\boxed{x=\lceil v^{4/3}\rceil.}
\tag{Q77}
\]
Indeed the cells imply
\[
v^{4/3}\le x<\big((v^{3/2}+1)^{4/3}+1\big)^{2/3}.
\]
Concavity of powers 8/9 and 2/3 bounds this interval's width
strictly by
\[
\frac89v^{-1/6}+\frac23v^{-2/3}<1\qquad(v\ge8).
\]
At v=8 the second term is 1/6 and the first is less than 2/3;
both decrease thereafter. An integer in this interval must
be its least possible integer. This proves uniqueness, not
existence or the required parities of that candidate. In an
actual F equality, v cannot be a perfect cube: (Q77) would
then make h=v^2, contrary to (Q75).

No universal strict F>G assertion follows from the guards alone:
the exact small path 9->27->140->11 has B(9)=5 and O(5)=11.
It does not meet the present large-minimum hypotheses. The
large-valley endpoint-equality question was left open at this gate;
Result 36 now supplies an unbounded fully guarded open family.

The compulsory charge at an actual even-to-odd landing v is
a(v)=log(log(v^2+1)/(2 log v))=eta(v^2). Summing those charges
by F/G/B valley ranges gives valid profile bounds, but this is
the existing parity-switch charge from the earlier period and
weighted-remainder analyses. It supplies no new sign or matched
integer-residual estimate that excludes (Q73) or (Q77). This
rearrangement is not promoted as a new loss mechanism.

### 33. Separated guarded minimum cells coexist at unbounded scales

For every odd t>=3 put
\[
\begin{aligned}
m&=t^6-4,& y&=t^8-4t^2-2,& x&=t^8+8,\\
h_G&=t^{12}-6t^6-3t^4+6,& q&=t^9-6t^3,\\
h_F&=t^{12}+12t^4,&
P&=t^{18}+18t^{10}+54t^2-1,& f&=t^9+9t-1.
\end{aligned}
\]
There are actual guarded open paths
\[
y\xrightarrow O h_G\xrightarrow E m\xrightarrow O q,
\qquad x\xrightarrow O h_F\xrightarrow O P\xrightarrow E f.
\tag{Q78}
\]
The F path is the previously proved family. The new G path has
the following exact positive square margins:
\[
\begin{aligned}
y^3-h_G^2&=12t^{10}+3t^8+8t^6-60t^4-48t^2-44,\\
(h_G+1)^2-y^3&=2t^{12}-12t^{10}-3t^8-20t^6+54t^4+48t^2+57,\\
h_G-m^2&=2t^6-3t^4-10,\qquad
(m+1)^2-h_G=3t^4+3,\\
m^3-q^2&=12t^6-64,\qquad
(q+1)^2-m^3=2t^9-12t^6-12t^3+65.
\end{aligned}
\tag{Q79}
\]
For the first margin, the negative terms total less than 66t^4,
while 12t^10>66t^4. For the second, the bracket
2t^4-12t^2-3 is at least 51, so its first three terms already
dominate 20t^6. The other signs follow from t>=3. The parities
are odd/even/odd/odd and odd/odd/even/odd respectively.

The minimum of these listed paths is m and their maximum P
satisfies m^3<P<m^4. The four states H_*=(y,x,q,f) are strictly
increasing and lie in the selected numerical section; the
intermediate states lie outside it. For the lower face of y,
use y^3>h_G^2>m^4. For the common upper face, use
f<=(4/3)t^9<(4/9)t^12<=m^2. Their exact B values satisfy
\[
B(y)=m<B(x)=t^6<B(q)<B(f).
\tag{Q80}
\]
Here q>2t^8 gives q^3>(t^6+1)^4. Also f<=t^10 and f-q>6t^3
give f^(3/4)-q^(3/4)>(9/2)sqrt(t)>1, so their floors differ.
The F valley t^6 is absent from the paths, and its O image t^9
is absent too, strictly between q and f.

All four circular log-log gaps of H_*, with circumference A,
are strictly greater than eta(m). For ordinary a<b use
\[
z(b)-z(a)>{b-a\over b\log b},\qquad
\eta(m)<{1\over m\log m}.
\]
The bounds m>=(2/3)t^6, log m>=5 log t,
x<=(4/3)t^8, q<=t^9, f<=(4/3)t^9, log x<=9 log t,
log f<=10 log t, and the gaps
x-y>4t^2, q-x>t^8, f-q>6t^3 prove the three comparisons.
For the wrap, y>=t^7 and f<=t^10 give
\[
A+z(y)-z(f)\ge\log(21/20)>1/21>\eta(m),
\tag{Q81}
\]
since m>=725. These are uniform proofs over the stated odd t;
the fixed checks at t=3,65,65537 are regression controls only.

This family retains exact guards, a minimum-G anchor, distinct
cells and the spacing allowance at arbitrarily large scales.
It closes the proposed local shortcut from those properties
alone to a selected missing-valley image or a parity failure.
It supplies no return edges from q or f, no closed rank
permutation, and no original count/surplus identity. It is
neither a family of cycles nor evidence of divergent orbits.

**Decision for this gate: PROMOTE the conditional re-entry
localization (Q70)--(Q73) and the exact closure criterion (Q74).**
The requested absolute no-cycle exclusion remains PARK.
The local anchoring shortcut is CLOSE by (Q78)--(Q81);
the repeated compulsory-charge shortcut adds no new mechanism.

### 34. Shared OE remainders exclude the joint unit corner

Consider an actual pair x -> O -> p -> E -> v, with x and v odd,
p even, and v>1. In this section v=B(x) is an **actual E target**.
For an F tower starting at X, this pair starts at x=O(X) and
has v=F(X), not the auxiliary valley B(X). Put
R=x^3-p^2 and Q=p-v^2. Both are positive odd integers, and the
shared middle state gives
\[
x^3=(v^2+Q)^2+R,\qquad
\boxed{R\ge3\ \text{or}\ Q\ge3.}
\tag{Q82}
\]
Indeed R=Q=1 would give x^3=(v^2+1)^2+1. Modulo 7, the square
classes 0,1,2,4 give right sides 2,5,3,5, disjoint from the
cube classes 0,1,6. This forbids a joint corner that the separate
parity intervals allowed. In particular
\[
\boxed{x^3\ge(v^2+1)^2+3=v^4+2v^2+4.}
\tag{Q83}
\]
If Q=1 this follows from R>=3; if Q>=3, its lower face
(v^2+3)^2+1 is larger. This is not a claim that either new corner
is attainable in actual cells. The arithmetic statements, including
specialization to O(x) and B(x), are kernel checked in
`QuarticCells.guarded_OE_remainder_dichotomy`,
`guarded_OE_lower_cube`, and `actual_OE_lower_cube`.

Write Z(u)=log log u and eta(u)=Z(u+1)-Z(u), for u>1. The two
initialized log-log defects are
delta_O=Z(p^2+R)-Z(p^2) and delta_E=Z(p)-Z(v^2). Define
\[
\mathcal D(v)=Z((v^2+1)^2+3)-Z((v^2+1)^2+1)>0.
\]
The stronger coupled charge is
\[
\boxed{\delta_O+\delta_E\ge
\eta(p^2)+\eta(v^2)+\mathcal D(v).}
\tag{Q84}
\]
For Q=1, p=v^2+1 and R>=3; the E charge is exactly eta(v^2),
and the O excess over eta(p^2) is at least D(v). For Q>=3, the
E excess is at least Z(v^2+3)-Z(v^2+1). This is strictly larger
than D(v): Z'(u)=1/(u log u) is positive and decreasing, and
the two intervals have length two while the latter starts at
(v^2+1)^2+1>v^2+1. The O excess remains nonnegative. The case
split is essential; a direct comparison at arbitrary p would
have the wrong monotonicity.

The endpoint-only version is
delta_O+delta_E>=log(log(v^4+2v^2+4)/(4 log v)). The additional
charge satisfies D(v)~1/(2v^4 log v), whereas the existing E
charge is eta(v^2)~1/(2v^2 log v). Thus this is a strict, small
arithmetic improvement, with no ordering of different towers'
losses implied.

### 35. The signed interval tightens for whole actual return blocks

Every actual quartic H-return has one OE pair: the last two edges
of F, the first two of G, or the entire B tower. These pairs are
edge-disjoint. The additional O edge of F or G has nonnegative
defect. For each tower i, let p_i be its even state, v_i its
actual E target and delta_i its complete defect. Set
\[
b_i=\eta(p_i^2)+\eta(v_i^2),\qquad D_i=\mathcal D(v_i)>0,
\qquad \beta_i=b_i+D_i\le\delta_i.
\tag{Q85}
\]
Since the towers partition the actual cycle, sum delta_i=Lambda.
The old and new residual budgets obey
\[
R_{\rm new}=\Lambda-\sum_i\beta_i
=R_{\rm old}-\sum_i D_i\ge0,
\qquad R_{\rm old}=\Lambda-\sum_i b_i.
\tag{Q86}
\]
This does not require the additional separation condition Q43.

Let S_+,S_- be disjoint sets of whole actual H-return towers,
and let S_0 be their complement. Write B(S)=sum b_i,
D(S)=sum D_i over S and W=sum over S_+ delta_i minus sum over
S_- delta_i. Subtracting beta_i leaves nonnegative residuals
with total R_new, so
\[
\boxed{B(S_+)+D(S_+)-B(S_-)-D(S_-)-R_{\rm new}
\le W\le
B(S_+)+D(S_+)-B(S_-)-D(S_-)+R_{\rm new}.}
\tag{Q87}
\]
Compared with the separate-charge interval of the form CW44,
the exact containment margins are
\[
L_{\rm new}-L_{\rm old}=2D(S_+)+D(S_0),\qquad
U_{\rm old}-U_{\rm new}=2D(S_-)+D(S_0).
\tag{Q88}
\]
Both endpoints improve strictly when both exclusive sets are
nonempty. This improves the old separate parity
lower bounds. The center also moves; no uniform sign
of W, or contradiction with the cycle counts, has been proved.
An original-edge arc cutting an OE pair cannot receive its entire
coupled charge without further boundary accounting. Q87 does
not assert such an improvement for every original-edge CW44 arc.

The same disjoint pairs give a simple integer consequence:
writing R=1+2a and Q=1+2b, each pair has a+b>=1, hence their
total is at least e. For a fixed linear objective ua+wb on a
pair's finite box, the new face a+b>=1 raises its minimum by
min(max(u,0),max(w,0)). This is sharp for that relaxed face,
not asserted sharp for actual cells. A useful global sign still
requires control of the coefficients or the actual residual placement.

The tested alternative of eliminating all internal remainders
and then taking cycle moments adds no independent constraint.
Under Q43, write X_i=H_i and T_i=X_(i+s mod e), and set
K_i=X_i^9-T_i^8 on lower towers and K_i=X_i^6-T_i^8 on upper
towers. The exact cells give K_i>0. Reusing the target multiset
gives exactly
\[
\sum_iK_i=\sum_{i<r}X_i^9+\sum_{i\ge r}X_i^6-\sum_iX_i^8,
\qquad
\frac{\prod_{i<r}X_i}{\prod_{i\ge r}X_i^2}
=\prod_i(1+K_i/T_i^8).
\tag{Q89}
\]
These are moment and logarithmic moment balances, not a new
signed constraint. The modulo-16 check likewise repeats the
same sum, since every odd target has eighth power 1 modulo 16.
This specific elimination shortcut is CLOSE; it does not close
all possible uses of shared integer states.

### 36. Guarded endpoint equality persists at unbounded valleys

The bounded exact check of the Q77 candidate over 8<=v<=1000000
found guarded equalities, beginning with
483 -> 10615 -> 1093654 -> 1045, with B(483)=103 and O(103)=1045.
Such a finite check cannot exclude eventual strictness. The
following uniform family resolves that stronger local question.

For every integer t>=8192 with t=9 modulo 16, define
\[
\begin{aligned}
v&=t^6-3t^2+6,\\
x&=t^8-4t^4+8t^2+2,\\
h&=t^{12}-6t^8+12t^6+9t^4-24t^2+21,\\
p&=t^{18}-9t^{14}+18t^{12}+27t^{10}-90t^8
 +(117t^6-297t^2)/2+108t^4+81,\\
q&=(8t^9-36t^5+72t^3+27t-7)/8.
\end{aligned}
\tag{Q90}
\]
Then
\[
\boxed{x\xrightarrow O h\xrightarrow O p\xrightarrow E q,
\qquad B(x)=v,\quad O(v)=q,\quad F(x)=G(x).}
\tag{Q91}
\]
Here x,h,q are odd and p,v are even. In particular the displayed
F path is actual. The O edge from v is prescribed, since this
auxiliary valley is even; an actual G path is not being claimed.

For a complete uniform cell proof, the following table records
the degree d, leading coefficient C, and sum N of the absolute
values of all negative coefficients for each polynomial margin
obtained by expanding Q90.

| Margin | d | C | N |
|---|---:|---:|---:|
| x^3-h^2 | 12 | 2 | 1075 |
| (h+1)^2-x^3 | 10 | 24 | 1283 |
| h-v^2 | 2 | 12 | 15 |
| (v+1)^2-h | 6 | 2 | 18 |
| h^3-p^2 | 16 | 108 | 57159/4 |
| (p+1)^2-h^3 | 18 | 2 | 55751/4 |
| v^3-q^2 | 9 | 7/4 | 23697/64 |
| (q+1)^2-v^3 | 9 | 1/4 | 22319/64 |
| p-q^2 | 9 | 7/4 | 11313/64 |
| (q+1)^2-p | 9 | 1/4 | 8783/64 |

For t>=1 each margin is at least t^(d-1)(Ct-N). Every row has
N/C<8192, so all ten margins are strictly positive uniformly.
For example
\[
\begin{aligned}
x^3-h^2&=2t^{12}-24t^{10}+87t^8+56t^6-618t^4+1104t^2-433,\\
(h+1)^2-x^3&=24t^{10}-99t^8-32t^6+636t^4-1152t^2+476,\\
h-v^2&=12t^2-15,\qquad (v+1)^2-h=2t^6-18t^2+28.
\end{aligned}
\tag{Q92}
\]
The table's coefficient arithmetic was independently expanded
with symbolic rational arithmetic and a separate integer
polynomial implementation. This is a finite polynomial proof
over all the stated t, not an extrapolation from numerical roots.

The candidates are positive: v>t^6-3t^2>0 and x>t^8-4t^4>0;
8q>8t^9-36t^5>0 for t>=8192. Then the positive margins h-v^2
and p-q^2 give h,p>0. The congruence t=9 modulo 16 gives
2p=0 modulo 4 and 8q=8 modulo 16, proving integrality and the
stated parities. The remaining parities follow directly from
Q90. The ten strict square margins now prove all five exact
floor identities in Q91.

These valleys tend to infinity. Their thin alignment is
h-v^2=12t^2-15=o(sqrt(v)), consistent with Q77. The registered
fixed controls t=2^16+9,2^32+9,2^64+9 verify the five cells with
integer roots; the uniform proof is the polynomial certificate.

Thus eventual local F>G from the full actual F guards and a
large auxiliary valley alone is CLOSE. This family supplies no
selected minimum-G anchor, full H-return partition, cyclic
counts, Q43 condition or periodic membership. It does not
realize the all-equality case of Q74 inside an actual cycle,
refute a theorem using those global hypotheses, or construct
a divergent orbit.

**Decision for this gate: PROMOTE the coupled charge Q84 and
whole-return interval improvement Q87--Q88.** The modulo-7
arithmetic is Lean verified; the logarithmic/cycle assembly and
unbounded equality family are AI-assisted written proofs,
independently audited by three AI agents. Actual no-cycle
remains PARK. Eventual local strictness and the specified
moment-elimination shortcut are CLOSE. No further gate opens here.

### 37. A unit incoming O remainder is impossible by itself

There is a stronger arithmetic interpretation of Q82. In an actual
odd-to-even edge x -> O -> p, with p>0 even, the positive odd
remainder R=x^3-p^2 satisfies
\[
\boxed{R\ge3.}
\tag{Q93}
\]
No following E edge is required. Here is a self-contained classical
factorization proof. The Gaussian integers are Euclidean: rounding
both coordinates of a quotient gives a remainder whose norm is at
most half the divisor's norm. They therefore have unique factorization;
this standard algebraic structure is also documented in
[Mathlib's Gaussian integers](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Zsqrtd/GaussianInt.html#GaussianInt.instEuclideanDomain).

If R=1, factor x^3=(p+i)(p-i). A common Gaussian prime divides
2i, hence is associated to 1+i. But 1+i divides a+bi exactly
when a and b have equal parity, so it does not divide p+i.
The factors are coprime. Unique factorization makes p+i a unit
times a cube. Cubing permutes the four units, so write
p+i=(a+bi)^3 with integer a,b. Its imaginary coordinate is
b(3a^2-b^2)=1. For b=1 this requires 3a^2=2; for b=-1 it
requires a=0, hence p=0. Both are impossible, proving Q93.
This elementary Diophantine observation is not claimed as a new
external theorem.

For an actual OE pair x -> p -> v, use the old charges
b_O=eta(p^2), b_E=eta(v^2), and residuals
u_O=delta_O-b_O, u_E=delta_E-b_E. Define
\[
\kappa(p)=Z(p^2+3)-Z(p^2+1),\qquad
\boxed{u_O\ge\kappa(p)>0,\quad
\kappa(p)\le\mathcal D(v).}
\tag{Q94}
\]
The first inequality follows from Q93. The second uses
p>=v^2+1 and the decreasing function Z(w+2)-Z(w). Equality
in the second holds if Q=p-v^2=1. The actual E upper face also
gives u_O>=kappa((v+1)^2-2)>0, asymptotic to D(v) as v grows.

The previous modulo-7 theorem and Q84 remain valid. Their
description must now be sharpened: the forbidden joint corner
is already excluded by the incoming edge alone. Q84 improves
the old *separate parity* baselines; it is not evidence that
this corner needs an irreducible interaction of two edges.

The two residuals are not interchangeable. The exact path
847 -> 24650 -> 157 has odd/even/odd guards and
\[
847^3-24650^2=22923,\quad24651^2-847^3=26378,\quad
24650-157^2=1,\quad158^2-24650=314.
\]
Thus u_E=0 there, while u_O>0. This fixed open path does not
prove existence at arbitrary larger minima or periodic membership.
The already recorded raw comparison delta_E>delta_O (CW25)
is a different statement: its redundancy within initialized upper
boxes was proved in CW35, and it is not promoted again here.

### 38. Located charges give a bound for arbitrary cut pairs

Index the original actual edges by j. Let delta_j>=b_j>=0,
sum delta_j=Lambda, and let the actual OE pairs be edge-disjoint.
For each pair a write k_a=kappa(p_a) and D_a=D(v_a), so
0<k_a<=D_a. The original residuals obey
u_O>=k_a, u_E>=0, and u_O+u_E>=D_a. Move k_a into the
O-edge baseline and reserve only D_a-k_a on the remaining
two coordinates. The free total is therefore
\[
R_* = \Lambda-\sum_j b_j-\sum_aD_a\ge0.
\tag{Q95}
\]
Reserving k_a and the full D_a separately would double count.
Unpaired edges retain their nonnegative residuals.

For arbitrary fixed coefficients c_j, let alpha=min c_j,
beta=max c_j, W_0=sum c_j b_j and W=sum c_j delta_j. Then
\[
\boxed{\begin{aligned}
L_{\rm loc}&=W_0+\sum_a\{c_Ok_a+
 \min(c_O,c_E)(D_a-k_a)\}+\alpha R_*\ \le W,\\
U_{\rm loc}&=W_0+\sum_a\{c_Ok_a+
 \max(c_O,c_E)(D_a-k_a)\}+\beta R_*\ \ge W.
\end{aligned}}
\tag{Q96}
\]
To prove this, extract nonnegative masses totaling D_a-k_a
from each pair's remaining residuals. Their weighted contribution
lies between that total times its two coefficient extrema.
All mass left over, including unpaired edges, totals R_* and
has coefficients between alpha and beta. Each unit is counted once.

Setting every k_a to zero gives the pair-total version L_pair,
U_pair. Compared with it the exact improvements are
\[
\boxed{\begin{aligned}
L_{\rm loc}-L_{\rm pair}
 &=\sum_a(c_O-\min(c_O,c_E))k_a,\\
U_{\rm pair}-U_{\rm loc}
 &=\sum_a(\max(c_O,c_E)-c_O)k_a.
\end{aligned}}
\tag{Q97}
\]
For coefficients (+1,-1) the lower endpoint rises by 2k_a;
for (-1,+1) the upper endpoint falls by 2k_a. This locates
part of the compulsory loss even when a boundary cuts its pair.

These support bounds are sharp in the relaxation keeping only
the displayed lower demands and total residual: put each pair's
remaining mandatory mass on an extremal leg and all free mass
on a globally extremal edge. That construction omits actual upper
caps, the exact E residual Z(p)-Z(v^2+1), and the shared cube
equations. It is not an arithmetic realization or a cycle.
The kernel-checked `QuarticLossBudget.located_pair_lower/upper`
and their finite-sum counterparts verify the support inequalities
from supplied coefficients and residual constraints. They do not
formalize the Gaussian argument or supply an actual cycle partition.

For signed arc differences with both signs present, alpha=-1 and
beta=1. Relative to the old separate-charge interval W_0+-R_old,
the pair-total gains are sum (1+min(c_O,c_E))D_a at the lower
end and sum (1-max(c_O,c_E))D_a at the upper end. In particular
an overlap pair (0,0) improves both ends by D_a: its compulsory
mass is unavailable for either exclusive arc. A (+1,-1) or
(-1,+1) pair gives zero at both ends in that pair-total comparison,
but Q97 retains the located improvement just described.

For two equal proper chronological arcs, coefficients are
c_j=1_B(j)-1_A(j). An OE pair at consecutive source positions
j,j+1 splits only if j+1 is an endpoint of one of the arcs.
Only endpoints that are even source states count. Consequently
\[
\boxed{\text{at most four actual OE pairs are split.}}
\tag{Q98}
\]
Overlaps and coincident endpoints are included; a coincident
endpoint can cancel a jump or create a jump of size two.
This finite boundary statement does not require rank rotation.

### 39. The actual cubic terminal allocation is exact, but cancels

This specialization assumes the **cubic** primitive-cycle hypotheses
m>=5 and M<m^3 and the established terminal factorization TJ1.
It is not asserted for the sorted original states of a taller
quartic cycle. Write U(m)=c_1, V(c_1)=m, u=|U|, v_len=|V|,
u+v_len=L. The word identities give u>=3, v_len>=2,
|P|=v_len-1, |Q|=u-1; Q begins with OE.

Start chronological coordinates at m. The states m,q,c_1,h,M,t,s
are at positions 0,1,u,v_len-1,v_len,v_len+1,L-1, respectively.
All are odd except M and s. For upper-track minus lower-track
loss, the original-edge coefficients are
\[
c^P=\mathbf1_{[u,L-1)}-\mathbf1_{[0,v_{\rm len}-1)},\qquad
c^Q=\mathbf1_{[1,u)}-\mathbf1_{[v_{\rm len}+1,L)}.
\tag{Q99}
\]
The mixed coefficients are +1 at s,m and -1 at h,M. Intervals
in Q99 are ordinary chronological intervals; their overlaps cancel.

Let C_m be the OE pair ending at m, with even state s and source
positions L-2,L-1. Let C_t be h -> M -> t, and let C_q be the
first OE pair of Q, starting at q, with E target B(q). The exact
boundary facts are:

| Segment | Split OE pairs | Coefficients on C_m |
|---|---|---|
| P | exactly C_m | (+1,0) |
| mixed | exactly C_m | (0,+1) |
| Q | none | (-1,-1) |

For P, its two starts m,c_1 are odd and its endpoints h,s have
only s even. For Q, both starts and both endpoints are odd.
In the mixed passage C_t has coefficients (-1,-1); the remaining
+1 edge at m is odd-to-odd and belongs to no OE pair. This proves
the table and shows that no opposite-sign OE pair occurs here.

The pair-total bound already improves both ends of **each**
terminal interval strictly. Witness lower bounds on its gains are
\[
\begin{array}{c|cc}
 &L_{\rm pair}-L_{\rm old}&U_{\rm old}-U_{\rm pair}\\\hline
P&\mathcal D(m)&\mathcal D(B(q))\\
\mathrm{mixed}&\mathcal D(m)&2\mathcal D(t)\\
Q&2\mathcal D(B(q))&2\mathcal D(m).
\end{array}
\tag{Q100}
\]
Indeed C_q has P coefficients either (0,0) or (-1,-1), and
Q coefficients (+1,+1). C_m and C_t are distinct. The other
pair contributions to each improvement are nonnegative. If
C_q and C_t coincide, the same statements and bounds still hold.

The located O charge further raises the P lower bound by exactly
kappa(s), and lowers the mixed upper bound by exactly kappa(s),
relative to their pair-total bounds. All other endpoints remain
the same in that comparison: every other pair has equal coefficients.

Nevertheless the exact coefficients satisfy
\[
\boxed{c^P+c^{\rm mixed}+c^Q=0\quad\text{on every edge}.}
\tag{Q101}
\]
On C_m this is (+1,0)+(0,+1)+(-1,-1)=(0,0). Its actual
residual contributions are u_O, u_E, and -(u_O+u_E).
Thus the charge is accounted for across both boundaries and the
suffix; none becomes an uncounted net loss. This also follows
from the two full tracks each traversing the cycle once.

Optimizing the three intervals independently can place the same
remaining mass in different coordinates. Those extrema cannot be
combined as three independently realized oriented losses. No
improved lower bound is proved positive, or upper bound negative,
in the direction needed for contraction. The boundary-allocation
omission is resolved; a terminal no-cycle contradiction is not.

For general original chronological quartic arcs, Q96--Q98 apply
to their actual OE pairs. On the separated H section, whole-return
arcs remain the setting of Q87. Their equal return counts need not
give equal original-edge lengths, since towers have length two or
three. No original quartic rank rotation or cubic terminal placement
is being inferred from the H rotation.

**Decision for this gate: PROMOTE the located O charge Q94 and
the bound Q96 for cut pairs, including the explicit cubic terminal
specialization Q99--Q100.** The small support kernels are Lean
verified; the arithmetic and actual-cycle assembly are audited
written proofs. Counting boundary charges as an extra net terminal
loss is CLOSE by Q101. No-cycle remains PARK, with no floor or
paper release change and no further gate launched here.

## Open questions

The small-product condition Q43 remains unproved uniformly. Under it,
all F valleys are unselected and the H return is R_s, but the strict
re-entry restriction does not contradict actual F closure. The unbounded
local equality family leaves global periodic matching unresolved.

The new Q96 estimate accounts for OE pairs cut by original-edge arcs.
The actual cubic P/mixed/Q placement tightens both ends of each signed
interval and locates an extra kappa(s) on specific endpoints. This
resolves the allocation omission raised after Q87. It does not make an
upper bound negative or a lower bound positive in the needed direction.

Further progress needs a quantitative restriction on the actual
remaining losses or their long return weights. Repeating the terminal
charge sum cannot provide it: Q101 cancels every edge coefficient.
Original quartic chronological arcs must also be distinguished from
whole H-return arcs; only the latter have the conditional R_s model.

## Decision

**PROMOTE** the located O-edge loss Q94, the bound Q96 for arbitrary
cut pairs, and its exact cubic terminal specialization Q99--Q100,
claim J-cycle-quartic-boundary-loss. Every genuine positive odd-to-even
edge has remainder at least three. The old modulo-7 theorem remains
valid, but is not an irreducible two-edge obstruction after this stronger
single-edge observation. The new support kernels are Lean verified;
the arithmetic and actual-cycle interpretation remain written proofs.

The boundary-only no-cycle deduction is **CLOSE**: P and mixed split
the same pair, Q contains it whole, and all three coefficient vectors
cancel edge by edge. Their interval extrema cannot be treated as
simultaneously realized independent losses. The old raw OE contrast
is already implied by its initialized upper boxes and is not new input.

Actual no-cycle remains **PARK**. The single-edge and boundary results
are audited by three AI agents; the full new arithmetic/cycle assembly
still awaits Lean formalization and independent human review. The
unbounded F=G family and the prior conditional separation/re-entry
results remain valid. No cycle, divergence, new numerical floor or
paper release is claimed. No additional executable attack is established
by this gate, and no next gate is opened automatically.

## Publication assessment

Status: **THEOREM**, at the AI-assisted written-proof tier.
Independent human review and the complete Lean assembly are outstanding.
The six scoped formal kernels above are now Lean verified.
The canonical proof is this dossier; there is no duplicate manuscript
source. Paper A, its release copies and Zenodo record are unchanged.
The certified descent floor 350000000 and period floor 780239 remain
fixed. No divergent-orbit conclusion is claimed.
