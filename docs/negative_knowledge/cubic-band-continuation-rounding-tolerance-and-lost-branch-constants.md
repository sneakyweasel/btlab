# Cubic-band continuation: rounding tolerance and lost branch constants

**Exact obstructions to weakened tests; no-cycle still PARK (9 September 2026).**
The [same canonical dossier](../problems/juggler_cycle_cubic_band.md) proves
that all cycles at one threshold share a period and interlace, and gives
a uniform log-log grid bound with error at most (1-1/L) times the surplus.
These restrictions do not resolve absolute integer parity.

**Refuted weakened criterion:** correct source parity, cubic-band rank
rotation, coprime counts and one-sided power-rounding error below 2
exclude cycles at all sufficiently large minima. For every odd b>=3,
the finite parity projection R_b on odd [b,b^2] and even [b^2+1,b^3-1]
has a nontrivial cycle with R_b(x) in {J(x),J(x)-1}. The inclusion of
odd b^2 avoids a gap 3 at the seam. Whether every such cycle contains
an altered edge remains unproved, and would itself exclude actual
cubic-band cycles. Equal rotation fractions do not force equality of
maps: S_3 has (3,5,11), while R_3 has (3,5,10), both with counts (2,1).

**Refuted gap-only criterion:** exact same-branch image differences on sources >1,
correct source parity and the global rank rule suffice for no-cycle.
The map G=J-1 on odd x>=3 and G=J on evens has the exact 11-cycle
13,45,300,17,69,572,23,109,1136,33,188,13, wholly below the cube of
its minimum. All same-branch differences on sources >1 agree with those of J;
strict nearest-even smooth-gap tests survive as well. Subtraction erases
an additive constant for each branch. A successful gap argument must
recover absolute floor-cell positions or couple these offsets.

These are different maps, not counterexamples to Juggler no-cycle. The
uniform wrong-parity intersection for the exact S_b remains the question,
and the separate M>=m^3 regime remains open. New controls use only complete
S_3, S_9, S_29 graphs and one R_b orbit at b=3,9,11,29,101; the old
large caps and census were not expanded. Members:
`J-cycle-threshold-common-period`, `J-cycle-cubic-sorted-grid`,
`J-cycle-unit-perturbation`, `J-cycle-branch-offset-obstruction`.


**Consolidation update (9 September 2026).** The six cubic-band structural
results and scoped obstructions now have compiled Lean proofs, with canonical
written proofs in Paper A Section 3.10. Earlier written-only status entries
are historical. Formalization does not settle uniform absolute-cell
wrong-parity intersection; the author authorized that next question.


