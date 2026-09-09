# Exact run inequalities and the floor-free alphabet model

## Problem

Does the height ratio \(R=\log M/\log m\) of a nontrivial Juggler cycle
force a two-block parity alphabet? The September 2026 review found that
the recorded argument confused upper growth bounds with lower bounds and
replaced positive floor drift by exact closure. That implication is withdrawn.

## Exact statement

The following integer statements are **EXACT — LEAN VERIFIED** in
`CycleRunAlphabet.lean`:

1. After \(r\) odd steps from \(v\) to \(y\),
   \(y^{2^r}\le v^{3^r}\). This is an upper growth bound. It does **not**
   imply \((3/2)^r\le R\) or cap odd-run length from cycle height.
2. After \(g\) even steps from \(w\) to \(z\), \(z^{2^g}\le w\).
   Thus an even run inside \([m,M]\), with \(m>1\), gives \(2^g\le R\).
   In particular, an \(EE\) forces \(m^4\le M\).
3. Two odd steps \(x\to y\to z\), with \(y\ge8\), give
   \(x^9<2(z+1)^4\). Inside \([m,M]\), retain the full consequence
   \(m^9<2(M+1)^4\), equivalently \(M+1>m^{9/4}/2^{1/4}\).
4. A linear word without adjacent odd letters satisfies \(2o\le L+1\).
5. With the supplied abstract closure hypothesis \(o\alpha=(L-o)\beta\),
   the formal walk equals \((\alpha+\beta)(o_t-to/L)\).
6. A prefix-noncontracting word beginning \((OOE)^kOE\) has \(k\ge3\).
   Such a word cannot begin \((OOE)^3OE\,OE\). These results assume the
   displayed prefixes; height does not supply that alphabet or fix the
   first fall after exactly three climbs.

The additional cycle interpretation is **EXACT — HUMAN PROOF**, using
Paper A: a nontrivial cycle satisfies
\(o\log(3/2)-e\log2>0\), hence \(o>e\). A cyclic word without an
\(OO\) has \(o\le e\), so an \(OO\) exists. At the certified floor its
intermediate exceeds 8, and item 3 applies. The integer consequence is

\[
M\ge\left\lfloor\left(\frac{m^9}{2}\right)^{1/4}\right\rfloor.
\]

At \(m\ge350000001\) this is approximately \(1.409\cdot10^{19}\),
not the withdrawn factor-free \(1.6\cdot10^{19}\) assertion.

## Current literature

No new external input. Paper A supplies the strict floor-defect inequality;
the abstract block arithmetic is not a new result about realized cycles.

## Branch budget

Repair the existing statements, model labels, and regression checks only.
No floor raise, new census campaign, or attempt to exclude all cycles.

## Balanced-ternary formulation

None. These are integer floor inequalities and formal parity-word sums.

## Why BT may be relevant

It is not used in this branch.

## Candidate operations / invariants

For \(s=o/L\), \(D_t=o_t-ts\), and \(u_t=o_t\alpha-(t-o_t)\beta\),
the unconditional algebraic identity is

\[
u_t=(\alpha+\beta)D_t+
\frac tL\bigl(o\alpha-(L-o)\beta\bigr).
\]

The final term vanishes only under a zero-drift hypothesis. For Juggler's
step sizes it is positive on nontrivial cycles; relating this formal walk
to actual log-log height also requires floor-defect transport.
Neither \(\log R=\log3\,\Delta\) nor the height-to-alphabet claim follows here.

## Experiments

The existing cycle-run probe separately emits exact integer checks and an
`idealized_model` object. The latter holds floor-free run caps,
zero-drift proportions, and prescribed-word necklaces. It is not a census
of realized cycle geometry.

The retained finite necklace counts are total / balanced / sliver / above
the chosen discrepancy cutoff: \((2,5)\): 3 / 1 / 1 / 1;
\((3,7)\): 12 / 1 / 3 / 8; \((4,10)\): 73 / 1 / 10 / 62;
\((5,12)\): 364 / 1 / 15 / 348. These are finite word computations only.

## Conjectures

None opened. No corrected odd-run cap or realized two-block alphabet is
claimed. The existing `J-cyclemin-ooo-inevitable` refutation remains separate.

## Counterexamples

Exact orbit \(9\to27\to140\) has two odd steps, yet \(140^4<9^9\).
Thus two odd steps do not give the factor-free growth inequality used in
the old deduction. The valid inequality is \(9^9<2\cdot141^4\).
This refutes that step inference, not the existence of nontrivial cycles.

Exact logarithmic closure is unavailable: a finite nontrivial cycle has
\(3^o>2^L\), not equality. Recentring an arbitrary word to force zero drift
tests conditional algebra, not a Juggler closure theorem.

## Formalization

`formal/Problems/Juggler/CycleRunAlphabet.lean` proves
`odd_run_upper`, `even_run_contracts`, `oo_step_lower`,
`oddCount_le_of_noAdjOdd`, `walk_eq_discrepancy` with its explicit
closure hypothesis, `ee_forces_fourth_power`, and the displayed-prefix
results `band_min_needs_three_climbs` / `band_min_no_second_fall`.
The corrected comments match their hypotheses; no theorem body is weakened.
There is no Lean theorem deducing the two-block alphabet from \(R<27/8\).

## Results

Retained: exact run inequalities, the factor-and-shift OO consequence,
conditional word algebra, and finite abstract-word computations.
Withdrawn: the odd-run height cap, exact cycle mix, factor-free maximum
bound, realized height/discrepancy identification, and forced fourteen-letter
opening from height alone. Model zero-drift proportions are not cycle proportions.

## Open questions

Can a floor-aware argument establish a useful odd-run upper bound from
cycle height? This repair does not investigate that question.

## Decision

**CLOSE.** The overclaimed implication is withdrawn and the valid integer
core is retained. Model calculations do not establish a cycle exclusion or
termination theorem, and no new research branch is opened.

## Publication assessment

Only the explicitly quantified integer inequalities and conditional word
identities may be cited as proved. The former height-to-alphabet result
must not be used as a theorem about Juggler cycles.
