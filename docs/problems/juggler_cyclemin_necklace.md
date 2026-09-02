# Juggler CycleMin necklace slack

Status: **ARCHIVED**

Standalone application phase on the 56 CycleMin-shaped length-11
four-even words. It is **not** a Research Engine control-layer
experiment, not a length-11 census, not a \(Z_5\) family, not a
two-word pin rescue, and not a claim that every positive integer
reaches 1.

## Problem

The thirty first-expanding leftovers are 30 of the 56 start-`OO`
four-even itineraries of length 11. Extra CycleMin-shaped rotations of
the other twenty-two leftovers land in the remaining 26, typically
\(a_3\ge 2\). Does slack \(139\) plus a bounded pin exclude the
whole 56?

## Exact statement

Every length-11 four-even word is \(O^{a_0}EO^{a_1}EO^{a_2}EO^{a_3}E\)
with \(a_0+a_1+a_2+a_3=7\). A `CycleMin` starts `OO`, so \(a_0\ge 2\).
There are 56 such words. Slack on every start-`O` four-even word
with seven odds is \(3^{7}-2^{11}=139\). The comparison
\(n^{139}>(1+1/n)^{A-139}\) first holds at some chain \(N_0\). Phase 0
asks whether every one of the 56 has \(N_0\) at or below its first
prefix start, with no prefix follower below \(\max(N_0,30)\).

Five or more evens at length 11 are formally contracting
(\(3^{6}<2^{11}\)). That is not used as a census. There is no
`no_cycle_itinerary_length_eleven`, no `no_cycleMin_necklace`, and no
halt theorem.

## Current literature

- CycleMin fudge on the thirty first-expanding leftovers —
  **EXACT — LEAN VERIFIED** (`J-cyclemin-fudge`).
- Slack identity \(3^{o}-2^{o+4}\) —
  **EXACT — LEAN VERIFIED** (`J-cyclemin-slack`).
- CycleMin tails \(a_0>a_0^*\) —
  **COMPUTATIONALLY VERIFIED**. Different length. Not reopened.
- First-E at \(e=4\) —
  **CLOSE**. Restricted leftovers to \(a_3\in\{0,1\}\).
- Length-11 non-pullback rotation —
  **CLOSE**. Leftover-cell rotation, not the CycleMin crossing.
- Even-count \(\le 3\) —
  **EXACT — LEAN VERIFIED**. Period \(\ge 11\).

Project relationship: **extended**, then **refuted**.

## Branch budget

```text
Mathematical target     Does slack 139 plus a bounded pin exclude
                        every length-11 CycleMin-shaped four-even
                        itinerary (the 56)?
Novelty hypothesis      extra rotations are a3>=2 spellings of the
                        same identity, not a new cell; e>=5 is
                        contracting, so a census is a corollary
Falsifier               some of the 26 have N0 above the first
                        prefix start, or a pin hit below that N0
Existing machinery      no_cycleMin_slack139; slack_of_four_even;
                        prefix_cell_exponents; chain_n0
Maximum Phase-0 scope   one scan of the 56 words; no Lean census,
                        no 26 named theorems, no tails pin, no e=5
Promotion criterion     all 56 have slack 139, chain N0 at or below
                        the first prefix start, pin empty below N0
Stop criterion          any itinerary misses; a 26-word rescue; Z5;
                        assembling the census before the scan
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- slack on every length-11 start-`O` four-even word is \(139\) —
  **COMPUTATIONALLY VERIFIED** (Lean identity already covers it)
- 56 = 30 leftovers + 26 extra orientations —
  **EXACT — HUMAN PROOF**
- \(A\) on the extra 26 reaches \(30705>13905\) —
  **COMPUTATIONALLY VERIFIED**
- `OOEEEOOOOOE` has first prefix start \(5\) and chain \(N_0=55\) —
  **COMPUTATIONALLY VERIFIED**
- `OOOEEEOOOOE` has first prefix start \(3\) and chain \(N_0=42\) —
  **COMPUTATIONALLY VERIFIED**
- the other 24 extra itineraries fire at their first prefix start —
  **COMPUTATIONALLY VERIFIED**
- slack 139 plus a uniform pin excludes the 56 —
  **REFUTED**
- no cycle of length 11 — not claimed
- four-even leftovers die — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cyclemin_necklace`
- Records: [juggler_cyclemin_necklace.md](../research/juggler_cyclemin_necklace.md),
  [juggler_cyclemin_necklace.json](../research/juggler_cyclemin_necklace.json)
- Tests: `tests/research/juggler_sequence/test_cyclemin_necklace.py`
- Finite checks: 56 words; slack 139; two pin misses at \(n=3,5\);
  first starts through \(77625\); \(A\) through \(30705\).
- Lean: none new. `CycleMinFudge.lean` is not rewritten. Paper A
  is unchanged.

## Conjectures

None opened.

## Counterexamples

The uniform-fire claim fails on two extra itineraries:

- `OOEEEOOOOOE` = \((2,0,0,5)\). \(A=30705\), chain \(N_0=55\),
  first prefix start \(5\). The prefix `OOEEEOOOOO` is followed
  at \(n=5\). The last even is not followed at \(5\).
- `OOOEEEOOOOE` = \((3,0,0,4)\). \(A=21633\), chain \(N_0=42\),
  first prefix start \(3\). The prefix `OOOEEEOOOO` is followed
  at \(n=3\). The last even is not followed at \(3\).

Do not pin those two starts. That is the two-word rescue.

## Formalization

None. `Problems/Juggler/CycleMinFudge.lean` is not rewritten.
No `no_cycleMin_necklace`. No `no_cycle_itinerary_length_eleven`.
No `sorry`. No halt theorem. Paper A is unchanged.

## Results

Classification **CYCLEMIN_NECKLACE_REFUTED**.

Slack \(139\) holds on all 56 words. Early evens and late odds
inflate \(A\) past the fudge bound \(13905\). Two extra itineraries
have a prefix start below their chain \(N_0\). The other 24 extra
words fire. This is not a length-11 census and not a halt theorem.

## Open questions

Stop. Do not pin the two misses. Do not write \(Z_5\). Do not
assemble `no_cycle_itinerary_length_eleven`.

## Decision

**CLOSE**. Slack \(139\) is the same identity on every necklace
orientation, but it does not fire at the first prefix start on
`OOEEEOOOOOE` and `OOOEEEOOOOE`. A two-word pin would be the
rescue the stop criterion forbids. This is not a halt result
and not a length-11 census.

Best next question: stop. Do not open \(e=5\). Do not pin the
two misses.

## Publication assessment

Status: `ARCHIVED`. A named refutation of uniform CycleMin-pin
exclusion of the 56 length-11 start-`OO` four-even words, not a
paper candidate and not a Juggler totality result.
