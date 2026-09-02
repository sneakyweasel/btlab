# Juggler CycleMin tails

Status: **THEOREM**

Standalone application phase on the four-even short-gap tails
\(a_0>a_0^*\). It is **not** a Research Engine control-layer
experiment, not a length-11 census, not a \(Z_5\) family, not a
four-even assembler, and not a claim that every positive integer
reaches 1.

## Problem

The thirty first-expanding leftovers have seven odds. Leftover
\(Z_4\) misses that layer and fires at \(a_0^*+1\) with
\(N_0\le 180\). Does the CycleMin \((n+1)/n\) exponent machine
kill every tail \(a_0>a_0^*\) at a still smaller cutoff?

## Exact statement

Let \(w=O^{a_0}EO^{a_1}EO^{a_2}EO^{a_3}E\) be a first-expanding
short-gap remainder shape with \(a_0>a_0^*\). Then \(w\) has
\(o=a_0+a_1+a_2+a_3\ge 8\) odds and length \(o+4\). On a
`CycleMin` the exact cells compose to slack
\(3^{o}-2^{o+4}\). For every such word with \(a_0\le 16\)
(367 words) the comparison \(n^{A}>(n+1)^{A-\mathrm{slack}}\)
first holds at some \(N_0\le 7\), and no \(n<8\) follows the
prefix. The first tail layer (\(o=8\), thirty words) has
\(N_0\in\{5,6,7\}\) and first prefix starts \(37\) through
\(4481\). Leftover \(Z_4\) is unused. There is no
`no_cycle_itinerary_four_even`, no `no_cycleMin_four_even`, and no
`no_cycle_itinerary_length_eleven`.

## Current literature

- CycleMin fudge on the thirty first-expanding leftovers —
  **EXACT — LEAN VERIFIED** (`J-cyclemin-fudge`).
- Slack identity \(3^{o}-2^{o+4}\) —
  **EXACT — LEAN VERIFIED** (`J-cyclemin-slack`).
- Four-even short-first-gap \(Z_4\) —
  **PARK**. Fires at \(a_0^*+1\) with \(N_0\le 180\).
- Even-count \(\le 3\) —
  **EXACT — LEAN VERIFIED**. Period \(\ge 11\).

Project relationship: **extended**. Same crossing, infinite
tails through \(a_0=16\). Not \(e=5\).

## Branch budget

```text
Mathematical target     For each of the 30 remainder shapes, does
                        CycleMin (n+1)/n fire for every a0 > a0*
                        through 16, with chain N0 at or below the
                        first prefix start?
Novelty hypothesis      slack 3^o-2^{o+4} grows; CycleMin beats
                        leftover Z4 (N0<=180 at a0*+1)
Falsifier               slack <= 0, chain N0 above the first
                        start, or leftover-scale N0
Existing machinery      cyclemin_fudge exponent machine; 30
                        shapes; four_even_short_gap leftover N0
Maximum Phase-0 scope   Lean slack 3^o-2^{o+4}; no pin, no Z5
Promotion criterion     sorry-free identity covering the English
Stop criterion          identity fails; assembler names; Z5
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- slack on a start-\(O\) four-even word with \(o\) odds is
  \(3^{o}-2^{o+4}\) —
  **EXACT — LEAN VERIFIED** (`slack_of_four_even`,
  `J-cyclemin-slack`)
- 367 tails \(a_0^*+1\le a_0\le 16\) have chain \(N_0\le 7\) —
  **COMPUTATIONALLY VERIFIED**
- no prefix start exists for \(n<8\) —
  **COMPUTATIONALLY VERIFIED**
- the first tail layer fires at the first prefix start —
  **COMPUTATIONALLY VERIFIED**
- leftover \(Z_4\) unused —
  **COMPUTATIONALLY VERIFIED**
- every four-even leftover dies — not claimed
- no cycle of length 11 — not claimed
- \(e=5\) dies — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cyclemin_tails`
- Records: [juggler_cyclemin_tails.md](../research/juggler_cyclemin_tails.md),
  [juggler_cyclemin_tails.json](../research/juggler_cyclemin_tails.json)
- Tests: `tests/research/juggler_sequence/test_cyclemin_tails.py`
- Finite checks: 367 words; slack identity; chain \(N_0\le 7\);
  pin \(n<8\) empty; first tail starts \(37\) through \(4481\).
- Lean: `familySlack`, `two_pow_add_four_le_three_pow`,
  `exponents_slack_add`, `slack_of_four_even`,
  `slack_of_four_even_word` in `CycleMinFudge.lean`. The
  367-word pin and \(N_0\) scan is not Lean. Paper A is
  unchanged.

## Conjectures

None opened.

## Counterexamples

None to the tails. The stronger claims that fail:

- “the tails still need leftover \(N_0\le 180\)” — CycleMin
  fires by \(n=7\).
- “this is a four-even assembler” — thirty remainder shapes,
  \(a_0\le 16\).
- “this is \(Z_5\)” — four evens only.

## Formalization

`Problems/Juggler/CycleMinFudge.lean`, imported by the
laboratory barrel, not by `JugglerPaper`. `familySlack`,
`two_pow_add_four_le_three_pow`, `exponents_slack_add`,
`slack_of_four_even`, `slack_of_four_even_word`. The
length-11 identity `slack139_of_seven_odd_length_eleven` is
now a corollary. There is no `no_cycleMin_four_even` and no
`no_cycle_itinerary_cyclemin_tails`. The 367-word pin and \(N_0\)
scan is not Lean. No `sorry`. No halt theorem. Paper A is
unchanged.

## Results

Classification **CYCLEMIN_TAILS_PROVED**.

The first-expanding layer was the hard case (\(N_0\le 29\)).
On the tails slack grows as \(3^{o}-2^{o+4}\) and chain
\(N_0\) drops to \(3\) through \(7\). The leftover \(2\)-bound
is unused. The slack identity is Lean; the 367-word pin is
not.

## Open questions

Stop. Do not write \(Z_5\). Do not assemble
`no_cycle_itinerary_four_even`. Do not Lean the 367-word pin.

## Decision

**PROMOTE** the slack identity. On every start-\(O\)
four-even word with \(o\ge 7\) odds the leftover is
\(3^{o}-2^{o+4}\). The 367-word pin and \(N_0\) scan stay
computational. This is not a halt result and not a
four-even assembler.

Best next question: stop. Do not open \(e=5\). Do not Lean
the 367-word pin.

## Publication assessment

Status: `THEOREM`. A Lean slack identity plus a computational
exclusion of the scanned tails, not a paper candidate and
not a Juggler totality result.
