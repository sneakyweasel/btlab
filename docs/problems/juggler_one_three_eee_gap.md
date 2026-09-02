# Juggler `(1,3)` EEE +1-chain gap

Status: **THEOREM**

Standalone application phase on the five first-expanding leftovers
with even-run signature `(1,3)`:

`OOOOOOEOEEE`, `OOOOOEOOEEE`, `OOOOEOOOEEE`, `OOOEOOOOEEE`,
`OOEOOOOOEEE`.

It is **not** a Research Engine control-layer experiment, not a
length-11 census, not a \(Z_5\) family, not the `(2,2)` signature,
and not a claim that every positive integer reaches 1.

## Problem

Does every prefix \(O^{a}EO^{7-a}\) sit at or above the `EEE`
inverse cell \((n+1)^8\), so that the five `(1,3)` words are
excluded by the same exact \(+1\)-chain that killed
\(O^7\mathrm{EEEE}\) and `OOOOOOEEEOE`, rather than by leftover
\(N_0\in[1.57\cdot 10^9, 3.75\cdot 10^{12}]\)?

## Exact statement

If \(n\ge 2\) follows \(O^{a}EO^{7-a}\) with \(a\in\{2,3,4,5,6\}\),
write \(z=T_{O^{a}EO^{7-a}}(n)\). Then \(z\ge(n+1)^8\). In
particular none of the five words is a cycle itinerary. Lean
excludes all five as `CycleMin` words and excludes the
unique-rotation member `OOOOOOEOEEE` as a cycle itinerary. The
other four have extra CycleMin-shaped rotations outside the
thirty first-expanding leftovers. The EEE-cell inequalities
remain human.

## Current literature

- \(O^7\mathrm{EEEE}\) +1-chain —
  **EXACT — LEAN VERIFIED**
  (`o7_image_ge_succ_pow16`, `no_cycle_itinerary_oooooooeeee`).
- \(O^6\mathrm{EEEOE}\) +1-chain —
  **EXACT — HUMAN PROOF** (`J-o6eeeoe-gap`).
- Four-even short-first-gap \(Z_4\) —
  **PARK**. These five shapes first fire between \(1.57\cdot 10^9\)
  and \(3.75\cdot 10^{12}\).
- Amplify versus surplus —
  **REFUTED** / **CLOSE**.
- Length-11 rotation / internal-E —
  **REFUTED** / **CLOSE**.
- Even-count \(\le 3\) —
  **EXACT — LEAN VERIFIED**. Period \(\ge 11\) if a nontrivial
  cycle exists; the four-even leftovers remain.

Project relationship: **extended**. One even-run signature, five
words. Not the remaining twenty-three.

## Branch budget

```text
Mathematical target     Do all five (1,3) leftovers die by
                        prefix image versus (n+1)^8?
Novelty hypothesis      the same exact +1-chain that killed
                        O^7 EEEE / O^6 EEEOE, now mixed
                        through one internal E, fires at the
                        first prefix start, not leftover N0
Falsifier               a prefix image inside the EEE cell,
                        or the chain only at leftover-scale N0
Existing machinery      O^6 / O^7 +1-chain; cycle_trailing_evens
                        r=3; leftover Z4 PARK
Maximum Phase-0 scope   five named (1,3) words; CycleMin
                        Lean; no (2,2) family, no 23-word scan
Promotion criterion     a proof covering every prefix start
Stop criterion          the bound still needs a huge pin;
                        a 23-word scan; Z5; halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- no prefix start below \(37,113,163,173,241\) respectively —
  **COMPUTATIONALLY VERIFIED**
- leading-odd \(+1\)-chain
  \(n^{3^{a+1}-3\cdot 2^{a}}<(n+1)^{2\cdot 3^{a}-3\cdot 2^{a}}(T^{a}+1)^{2^{a}}\) —
  **EXACT — HUMAN PROOF**
- mixed comparison \(n^{2187}<(n+1)^{2048}(1+1/v)^{E}\) on a
  hypothesized cell hit —
  **EXACT — HUMAN PROOF**
- family identity \(3^{7}>2^{11}\) with slack \(139\) —
  **EXACT — HUMAN PROOF**
- leading-chain lower bounds \(v\ge V\) at the first starts,
  with integer certificates
  \(n^{L}>(n+1)^{P}V^{2^{a+1}}\) and
  \(n^{2187}V^{E}>(n+1)^{2048}(V+1)^{E}\) —
  **EXACT — HUMAN PROOF**
- the five words are not `CycleMin` words —
  **EXACT — LEAN VERIFIED** (`no_cycleMin_one_three_eee`)
- `OOOOOOEOEEE` is not a cycle itinerary —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_ooooooeoeee`)
- the other four `(1,3)` words are not cycle itineraries —
  **EXACT — HUMAN PROOF** (extra 4-even CycleMin-shaped
  rotations)
- leftover cells fire at \(1.57\cdot 10^{9}\) through
  \(3.75\cdot 10^{12}\) —
  **COMPUTATIONALLY VERIFIED**
- no cycle of length 11 — not claimed
- the `(2,2)` words die — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.one_three_eee_gap`
- Records: [juggler_one_three_eee_gap.md](../research/juggler_one_three_eee_gap.md),
  [juggler_one_three_eee_gap.json](../research/juggler_one_three_eee_gap.json)
- Tests: `tests/research/juggler_sequence/test_one_three_eee_gap.py`
- Finite checks: first prefix starts \(163,241,37,113,173\);
  pin \(n<10^{4}\) has \(46+48+47+32+36\) starts, all above the
  cell, closest ratio \(5.73\) at \(n=37\) on `OOOOEOOOEEE`.
- Lean: `CycleMin` exclusion of all five and
  `no_cycle_itinerary_ooooooeoeee`. The EEE-cell argument is not
  Lean. Paper A is unchanged.

## Conjectures

None opened.

## Counterexamples

None to the gap. The stronger claims that fail:

- “these shapes need leftover \(N_0\sim 10^{9}\)–\(10^{12}\)” —
  the exact mixed successor cell fires at the first prefix start.
- “this is a length-11 census” — five words, one even-run
  signature.
- “the `(2,2)` words are included” — they are not.

## Formalization

`Problems/Juggler/CycleMinFudge.lean` has `no_cycleMin_*` for
all five `(1,3)` leftovers and `no_cycle_itinerary_ooooooeoeee`.
The mixed EEE-cell inequalities are not Lean. The other four
`(1,3)` words have extra CycleMin-shaped rotations, so there
is no `no_cycle_itinerary_oooooeooeee` (or sibling).
`SmallCycleCensus.lean` still assembles only through length
seven. No `no_cycle_itinerary_length_eleven`. No `sorry`. No halt
theorem. Paper A is unchanged.

## Results

Classification **ONE_THREE_EEE_GAP_PROVED**.

A cycle of \(O^{a}EO^{7-a}\mathrm{EEE}\) is the prefix image in
\([n^{8},(n+1)^{8})\). The leading \(O^{a}\) +1-chain and the
suffix \(O^{7-a}\) +1-chain compose, after the internal even
cell \(u<(v+1)^{2}\), to

\[
n^{2187}<(n+1)^{2048}(1+1/v)^{E},
\]

with \(E=2^{a+1}\cdot 3\cdot(3^{7-a}-2^{7-a})\). This is the
family identity \(3^{7}>2^{11}\). A convenient lower bound \(V\)
on \(v=\lfloor\sqrt{T^{a}(n)}\rfloor\) comes from the leading
chain at the first prefix start and is monotone in \(n\). The
five integer certificates contradict a cell hit. No smaller odd
\(n\) follows the corresponding prefix.

Independently, `OOOOOOEOEEE` is a corollary of
\(T^{6}(n)\ge(n+1)^{11}\): one later odd already overshoots
\((n+1)^{8}\) at the first \(O^{6}\) start \(163\).

The leftover envelopes first fire at \(1.57\cdot 10^{9}\) through
\(3.75\cdot 10^{12}\). They are not used.

## Open questions

The five words are included in the uniform CycleMin crossing
([juggler_cyclemin_fudge](juggler_cyclemin_fudge.md)). The
\(a_0\ge 8\) tails, not a length-11 census. Do not write
\(Z_5\).

## Decision

**PROMOTE** the five-word mixed \(+1\)-chain. The leftover
\(4\)-fudge was again the threshold obstruction. The unifying
arithmetic is \(3^{7}>2^{11}\), the same slack that killed
\(O^{7}\mathrm{EEEE}\). This is not a halt result and not an
exclusion of the other twenty-three words.

Best next question: the \(a_0\ge 8\) tails by the same
CycleMin crossing, not a length-11 census.

## Publication assessment

Status: `THEOREM`. A five-word exact exclusion by an elementary
mixed \(+1\)-chain, not a paper candidate and not a Juggler
totality result.
