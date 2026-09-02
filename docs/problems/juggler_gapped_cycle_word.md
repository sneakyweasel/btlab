# Juggler gapped three-even CycleItinerary leftovers

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It is not a length-8 or length-9
census, not first-E transport at \(e\ge 4\), and not induction on
\(n\) or on the period.

## Problem

First-E transport excludes the gapped leftovers only as `CycleMin`s,
because \(y\ge n\) is required. Are those same words impossible as
`CycleItinerary`s at a non-minimum start?

## Exact statement

The gapped three-even leftovers are

- \(O^aEO^bEE\) with \(a\ge 2\), \(b\ge 4\);
- \(O^aEO^bEOE\) with \(a\ge 2\), \(b\ge 3\).

Theorem 3.13 excludes them as `CycleMin`s. A `CycleItinerary` at a
non-minimum start may have \(y<n\), so first-E transport does not
apply. Every `CycleItinerary` has a `CycleMin` rotation. Phase 0 asks
whether every rotation of either gapped word is an already-excluded
`CycleMin` orientation, so `exists_cycleMin` upgrades both families
to `CycleItinerary`.

This is not a length-8 or length-9 census and not a halt theorem.
There is no `no_cycle_itinerary_length_eight` and no
`no_cycle_itinerary_length_nine`. There is no
`no_cycle_itinerary_bunched`. Theorem 3.13 remains CycleMin-only.

## Current literature

- Uniform two-even leftover families —
  **EXACT — LEAN VERIFIED**.
- Gapped three-even `CycleMin`s —
  **EXACT — LEAN VERIFIED** (`no_cycleMin_gapped_three_even_ee`,
  `no_cycleMin_gapped_three_even_eoe`; Paper A Theorem 3.13).
- Seven bunched last-cluster families —
  **EXACT — LEAN VERIFIED** (Paper A Theorems 3.14--3.20).
- Internal-E bootstrap, end-odd, start-even, and start-`OE` —
  **EXACT — LEAN VERIFIED**.
- Prefix-OOO extra scale from \(n=3\) —
  **REFUTED**. That `CLOSE` is not reopened.

Project relationship: **extended**. This is the CycleItinerary upgrade
of the gapped complement after the bunched Lean exclusions.

## Branch budget

```text
Mathematical target     Are gapped three-even leftovers
                        impossible as CycleItineraries?
Novelty hypothesis      Every CycleMin rotation is already
                        excluded; y<n is irrelevant
Falsifier               A bunched or unclassified rotation
Existing machinery      exists_cycleMin; first-E CycleMin;
                        bootstrap; end-odd / start-even / OE
Maximum Phase-0 scope   Classify rotations; Lean both
                        families; no census
Promotion criterion     Both families are Lean CycleItineraries
Stop criterion          A bunched rotation; a census; e≥4;
                        halt language
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- every rotation of a gapped leftover is `gapped_ee` /
  `gapped_eoe`, bootstrap, ends-odd, starts-even, or starts-`OE` —
  **COMPUTATIONALLY VERIFIED** through \(a,b\le 8\)
- no rotation is a bunched leftover —
  **COMPUTATIONALLY VERIFIED** on that window
- `O^aEO^bEE` is not a `CycleItinerary` for \(a\ge 2\), \(b\ge 4\),
  \(n\ge 2\) —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_gapped_three_even_ee`)
- `O^aEO^bEOE` is not a `CycleItinerary` for \(a\ge 2\), \(b\ge 3\),
  \(n\ge 2\) —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_gapped_three_even_eoe`)
- first-E transport at a non-minimum start —
  not claimed; Theorem 3.13 stays CycleMin-only
- every three-even cycle itinerary is impossible — not claimed
- no cycle of length eight or nine — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.gapped_cycle_itinerary`
- Records: [juggler_gapped_cycle_word.md](../research/juggler_gapped_cycle_itinerary.md),
  [juggler_gapped_cycle_itinerary.json](../research/juggler_gapped_cycle_itinerary.json)
- Tests: `tests/research/juggler_sequence/test_gapped_cycle_itinerary.py`
- The Research Engine control layer is not modified.
- No cycle-state search. No length-8 or length-9 census.
- Lean lives in `GappedCycleItinerary.lean`. Paper A records Theorem 3.21.

## Conjectures

None opened.

## Counterexamples

None to the rotation classification or to the Lean upgrade. The
stronger claims that remain false or unproved:

- “first-E transport excludes the itinerary as `CycleItinerary` at a
  non-minimum start” — still false as a first-E statement.
  The CycleItinerary theorems are a rotation argument, not a
  transport of \(y\ge n\).
- “every three-even leftover is Lean-excluded” — not claimed
  beyond the two gapped families and the seven bunched families.
- “every bunched leftover is one Lean theorem
  `no_cycle_itinerary_bunched`” — not claimed.
- no cycle of length eight or nine — not claimed.

## Formalization

`formal/Problems/Juggler/GappedCycleItinerary.lean` excludes both
gapped families as `CycleItinerary`s:
`no_cycle_itinerary_gapped_three_even_ee` and
`no_cycle_itinerary_gapped_three_even_eoe`. The \(k=0\) rotation is
Theorem 3.13; the bootstrap rotation is last-gap \(\ge 2\); the
last even (resp. the `OE` pair) is start-even (resp. start-`OE`);
every other rotation ends odd. `FirstETransport.lean` is
unchanged and remains CycleMin-only. `SmallCycleCensus.lean`
still assembles only through length seven. No
`no_cycle_itinerary_length_eight`. No `no_cycle_itinerary_length_nine`.
No `no_cycle_itinerary_bunched`. No `sorry`. No halt theorem.
Paper A records Theorem 3.21.

## Results

Classification **GAPPED_CYCLE_WORD_GREEN**.

Every rotation of a gapped three-even leftover is a `CycleMin`
class already excluded. Lean upgrades both families to
`CycleItinerary`. The first-E cell \(y<n\) is irrelevant after
rotation. This is not a length-8 or length-9 census and not a
no-cycles theorem.

## Open questions

First-E at \(e=4\) is `CLOSE` as a reparameterization
([first-E at four evens](juggler_first_e_e4.md)). The
thirty-shape remainder is `PARK`
([four-even short-first-gap](juggler_four_even_short_gap.md)).
Rotation and internal-E next-square are `CLOSE`
([length-11 non-pullback](juggler_length11_nonpullback.md)).
Stop on the thirty length-11 leftovers as a leftover-path
target. Do not assemble `no_cycle_itinerary_length_eight` or
`no_cycle_itinerary_length_nine`. Do not claim halt.

## Decision

**PROMOTE**. Both gapped three-even leftovers are Lean
`CycleItinerary` exclusions by rotation of already-excluded
`CycleMin` orientations. Theorem 3.13 stays CycleMin-only.
Not a length-8/9 census and not a halt theorem.

Best next question: first-E transport at \(e\ge 4\), or stop.

## Publication assessment

Status: `EXPLORATORY`.

A two-family Lean `CycleItinerary` upgrade of the gapped leftovers,
recorded in Paper A as Theorem 3.21, not a length-8/9 census
and not a Juggler totality result.
