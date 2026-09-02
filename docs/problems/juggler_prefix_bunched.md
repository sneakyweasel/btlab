# Juggler last three-even bunched leftover after an arbitrary prefix

Status: **STRUCTURAL**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a
bunched-short attack, not a \(Z_5\) family, not a length-11
assembler, and not a claim that every positive integer reaches 1.

## Problem

Once the seven bunched leftovers are excluded as cycle itineraries, do
they remain impossible as a `CycleMin` suffix after an *arbitrary*
prefix \(u\)?

## Exact statement

Let \(n\ge 2\) and let \(u\) be any itinerary. There is no `CycleMin` of
the form

\[
n,\qquad u{+}{+}O^{a}\mathrm{EEE}\ (a\ge 6),\quad
u{+}{+}O^{a}\mathrm{EOEE}\ (a\ge 5),\quad
u{+}{+}O^{a}\mathrm{EOOEE}\ (a\ge 4),
\]
\[
u{+}{+}O^{a}\mathrm{EOOOEE}\ (a\ge 3),\quad
u{+}{+}O^{a}\mathrm{EEOE}\ (a\ge 5),\quad
u{+}{+}O^{a}\mathrm{EOEOE}\ (a\ge 4),\quad
u{+}{+}O^{a}\mathrm{EOOEOE}\ (a\ge 3).
\]

Write \(y=T_u(n)\). `CycleMin` gives \(y\ge n\). The leftover cell
is measured against the cycle start \(n\), so \(y\ge n\) tightens
it against the existing family tail at \(y\).

Large \(y\) is the family cutoff already used for `CycleItinerary`
(\(y\ge 256\), or \(y\ge 314\) for EOEE/EEOE at \(a=5\)). Below
that cutoff, the seal is a path table on \(y\): no start follows
the leftover and lands in \([2,y]\). Longer odd runs are seven
consecutive odds on the remainder.

At \(a=3\) the coarse comparison
\(Y^{27}>2^{38}(Y+1)^{32}\) never fires. Those two families use
the existing tight split, measured at \(y\).

If \(y=n\), the suffix itself is a bunched cycle itinerary, already
excluded.

This is not a `CycleItinerary` theorem at a non-minimum start
(\(y<n\) loosens the cell). It is not a bunched-short exclusion
and not a halt theorem.

## Current literature

- Seven bunched leftovers as cycle itineraries —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_three_even_*`).
- Last two-even leftover after an arbitrary prefix —
  **EXACT — LEAN VERIFIED**
  ([juggler_prefix_two_even.md](juggler_prefix_two_even.md)).
- Last-cluster split —
  **EXACT — HUMAN PROOF** (`J-cyclemin-last-cluster`). Class 3
  of that split is the last three-even bunched suffix after a
  general front; this branch is that class as a `CycleMin`
  theorem.
- First-E at \(e=4\) —
  **REPARAMETERIZATION** / **CLOSE**. Not reopened.
- Necklace slack —
  **REFUTED**. Not pinned here.
- Four-even leftover cells —
  **PARK**. Not reopened as \(Z_5\).

Project relationship: **extended**. The `CycleItinerary` exclusions
are the special case \(u=\varepsilon\).

## Branch budget

```text
Mathematical target     CycleMin n (u ++ threeEvenXXX a) is
                        impossible for every prefix u
Novelty hypothesis      y>=n plus a path table at y replace
                        CycleItinerary tables at the cycle start
Falsifier               a path y -> n in [2,y] below cutoff,
                        or the large-y tail failing when y>=n
Existing machinery      seven bunched CycleItinerary exclusions;
                        CycleMin; family tails; seven-odd
Maximum Phase-0 scope   path census; Lean wrapper;
                        no Z5, no length-11, no bunched-short
Promotion criterion     Lean exclusion for every prefix u
Stop criterion          tables-for-all-u; a leak family that
                        needs a new cell; bunched-short attack
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `CycleMin n (u ++ threeEvenEEE a)` is impossible —
  **EXACT — LEAN VERIFIED**
- `CycleMin n (u ++ threeEvenEOEE a)` is impossible —
  **EXACT — LEAN VERIFIED**
- `CycleMin n (u ++ threeEvenEOOEE a)` is impossible —
  **EXACT — LEAN VERIFIED**
- `CycleMin n (u ++ threeEvenEOOOEE a)` is impossible —
  **EXACT — LEAN VERIFIED**
- `CycleMin n (u ++ threeEvenEEOE a)` is impossible —
  **EXACT — LEAN VERIFIED**
- `CycleMin n (u ++ threeEvenEOEOE a)` is impossible —
  **EXACT — LEAN VERIFIED**
- `CycleMin n (u ++ threeEvenEOOEOE a)` is impossible —
  **EXACT — LEAN VERIFIED**
- large \(y\) is the family tail at \(y\) —
  **EXACT — LEAN VERIFIED**
- no \(y\) below cutoff follows a short leftover into \([2,y]\) —
  **EXACT — LEAN VERIFIED** (`returnsIntoB` tables)
- the coarse \(a=3\) comparison seals EOOOEE/EOOEOE —
  **REFUTED**; the tight split at \(y\) is the seal
- bunched-short last cluster is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.prefix_bunched`
- Records: [juggler_prefix_bunched.md](../research/juggler_prefix_bunched.md),
  [juggler_prefix_bunched.json](../research/juggler_prefix_bunched.json)
- Tests: `tests/research/juggler_sequence/test_prefix_bunched.py`
- Lean: `formal/Problems/Juggler/PrefixBunched.lean` and
  `PrefixBunchedEval.lean`. Not imported by
  `Problems.JugglerPaper`. No `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

None to the `CycleMin` exclusion. The stronger claims that fail
or remain unproved:

- “\(Y^{27}>2^{38}(Y+1)^{32}\) seals \(a=3\)” — false; the
  exponents are 27 versus 32. The tight split at \(y\) is the
  argument.
- “tables-for-all-\(u\) are required for a general prefix” —
  false; the table is on the leftover start \(y\), not on \(u\).
- “every last-cluster class is now Lean-excluded” — false.
  Bunched-short last cluster remains.
- “every cycle itinerary is impossible” — not claimed.

## Formalization

`PrefixBunched.lean` proves `no_cycleMin_prefix_eee`,
`no_cycleMin_prefix_eoee`, `no_cycleMin_prefix_eooee`,
`no_cycleMin_prefix_eoooee`, `no_cycleMin_prefix_eeoe`,
`no_cycleMin_prefix_eoeoe`, and `no_cycleMin_prefix_eooeoe`.
Large \(y\) lifts the existing family cell to \(y\) and compares
it with the family tail at \(y\). At \(a=3\) the tight lemmas
`eoooee_small_y_false` / `eoooee_large_y_false` are applied with
the leftover start \(y\). Below cutoff,
`PrefixBunchedEval.lean` has `returnsIntoB` tables; longer
leftovers are seven-odd on the remainder. \(y=n\) reduces to the
existing cycle-itinerary exclusions. No `sorry`. No `no_juggler_cycle`.
No `no_cycle_itinerary_length_eleven`. Paper A is unchanged.

## Results

Classification **PREFIX_BUNCHED_GREEN**.

Every last three-even bunched leftover is impossible as a
`CycleMin` suffix after an arbitrary prefix. The residual named
by the last-cluster split is unchanged: bunched-short last
cluster. This is not a four-even assembler, not \(Z_5\), not a
length-11 census, and not a halt theorem.

## Open questions

The leftover-suffix attack on bunched-short is now a separate
parked branch
([juggler_bunched_short.md](juggler_bunched_short.md)). Short
leftovers return into \([12,y]\). Do not write \(Z_5\). Do not
assemble `no_cycle_itinerary_length_eleven`.

## Decision

**PROMOTE**. The last three-even bunched leftover is now a
`CycleMin` theorem for every prefix, not only as a cycle itinerary.
The small-\(y\) seal is a path table. The \(a=3\) seal is the
existing tight split at \(y\). Do not claim that every cycle
word is impossible.

Best next question: the leftover-suffix, predecessor-cell,
front-overshoot, and exact-return attacks on bunched-short are
all parked
([juggler_bunched_short.md](juggler_bunched_short.md),
[juggler_bunched_short_front.md](juggler_bunched_short_front.md),
[juggler_front_overshoot.md](juggler_front_overshoot.md),
[juggler_bunched_short_return.md](juggler_bunched_short_return.md)).
The isolated-odd prefix attack is **CLOSE**
([juggler_isolated_odd_return.md](juggler_isolated_odd_return.md)).
The leftover residual is a bunched-short last cluster with no
later \(OO\).

## Publication assessment

Status: `STRUCTURAL`.

A Lean `CycleMin` exclusion for one last-cluster class after an
arbitrary prefix. Not a paper candidate and not a Juggler
totality result.
