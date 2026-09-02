# Juggler length-7 cycle-itinerary inventory

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It does not reopen Paper B densities
and does not start a general no-cycle theorem.

## Problem

Do the Paper A cycle filters, together with the leftover-tail method of
Lemma 3.5, exclude every even-terminating expanding length-7 word as a
`CycleItinerary` for \(n\ge 2\)?

## Exact statement

A length-7 word is formally expanding if and only if it has at least
five odd letters (\(2^7=128<243=3^5\)). Every mixed cycle itinerary rotates
to an even-terminating orientation. The even-terminating expanding
candidates are exactly

\[
OOOOOOE,\ 
EOOOOOE,\ 
OEOOOOE,\ 
OOEOOOE,\ 
OOOEOOE,\ 
OOOOEOE,\ 
OOOOOEE.
\]

Phase 0 asks which of these survive the existing filters, and whether
the two leftover orientations \(OOOOOEE\) and \(OOOOEOE\) satisfy a
Lemma 3.5 tail

\[
n^{243}>2^{422}(n+1)^{128}
\]

for all \(n\ge N_0\), with no `CycleItinerary` realization on
\(2\le n<N_0\).

This is now a Lean census (`no_cycle_itinerary_length_le_seven`) and
not a halt theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Small-cycle census (Paper A Theorems 3.6 and 3.8) —
  **EXACT — LEAN VERIFIED**. No cycle itinerary of length at most seven.
  Length eight is the stated boundary.
- Internal-E bootstrap —
  **EXACT — LEAN VERIFIED**. Length-6 leftovers were `OOOEOE` and
  `OOOOEE`.
- Leftover length-six orientations —
  **EXACT — LEAN VERIFIED**. Finite table below 256 plus
  \(n^{81}>2^{130}(n+1)^{64}\).
- Prefix-OOO extra scale from \(n=3\) —
  **REFUTED**. That `CLOSE` is not reopened.
- Paper B length-7 contracting splits `OOEOOEE` / `OOOEOEE` —
  withdrawn density claims. Not this branch.

Project relationship: **extended**. Length seven is closed; length
eight is the first open even-terminating expanding length.

## Branch budget

```text
Mathematical target     Which even-terminating expanding length-7 words
                        survive the Paper A filters, and do the two
                        leftover tails exclude CycleItinerary for all n≥2?
Novelty hypothesis      Length 7 is the same two-even type as length 6;
                        bootstrap kills the OO/OOO-suffix pair; the
                        leftover-tail method of Lemma 3.5 kills
                        OOOOOEE and OOOOEOE.
Falsifier               A leftover whose tail comparison never fires,
                        or a third leftover shape the filters miss.
Existing machinery      formal expansion; rotation to even-terminating;
                        odd-run; OO/OOO thresholds; CycleMin barriers;
                        no_cycleMin_internal_even_threshold;
                        lowerDenom / last-even cell; leftover finite
                        table + tail (LeftoverCycles.lean).
Maximum Phase-0 scope   One probe: inventory + leftover-tail cutoffs
                        + exact CycleItinerary check on 2≤n<N0 for the two
                        leftovers only. No Lean, no Paper A edit, no
                        length 8/9, no halt, no cycle search, no CLI.
Promotion criterion     Both leftovers excluded by tail+finite check,
                        or a named leftover that is not a rewrite of
                        a closed length-6 identity.
Stop criterion          Inventory is only reparameterization with no
                        exclusion path; tail fails; machinery gravity
                        (census engine, length-9, Paper B).
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- even-terminating expanding length-7 family is the seven words above —
  **COMPUTATIONALLY VERIFIED**
- `OOOOOOE` is the odd-run case of Lemma 3.4(v) —
  **OBSERVATION** (existing Lean theorem applies; not re-proved)
- `OOEOOOE` / `OOOEOOE` are internal-E bootstrap shapes; \(n=3\) fails
  by parity —
  **COMPUTATIONALLY VERIFIED**
- `EOOOOOE` rotates onto `OOOOOEE`; `OEOOOOE` is not a `CycleMin` —
  **OBSERVATION**
- leftovers are exactly `OOOOOEE` and `OOOOEOE` —
  **COMPUTATIONALLY VERIFIED**
- `lowerDenom(OOOOO)=2^{422}` and the tail
  \(n^{243}>2^{422}(n+1)^{128}\) for \(n\ge 14\) —
  **COMPUTATIONALLY VERIFIED**
- neither leftover is a `CycleItinerary` on \(2\le n<14\) (neither is even
  realized) —
  **COMPUTATIONALLY VERIFIED**
- length-8 is the same two-even type; length 9 is the first
  three-even length —
  **OBSERVATION** (not implemented)
- every length-7 cycle itinerary is impossible —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_length_le_seven`)
- leftover orientations `OOOOOEE` and `OOOOEOE` —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_oooooee`,
  `no_cycle_itinerary_ooooeoe`)
- bootstrap pair `OOEOOOE` / `OOOEOOE` —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_ooeoooe`,
  `no_cycle_itinerary_oooeooe`)
- cycles of length eight or more are impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_length_seven`
- Records: [juggler_cycle_length_seven.md](../research/juggler_cycle_length_seven.md),
  [juggler_cycle_length_seven.json](../research/juggler_cycle_length_seven.json)
- Tests: `tests/research/juggler_sequence/test_cycle_length_seven.py`
- The Research Engine control layer is not modified.
- No cycle-state search. No length 8. No O-terminating programme.
- Lean: `LeftoverEval.lean`, `LeftoverCycles.lean`, `Cycles.lean`,
  `SmallCycleCensus.lean`. No `sorry`.

## Conjectures

None opened.

## Counterexamples

None to the inventory or to the two leftover tails. The stronger
claims that remain false or unproved:

- “`LowerPowerBound` extra scale from \(n=3\) excludes the leftovers”
  — still the closed prefix-OOO branch.
- “every length-8 word is Lean-excluded” — not claimed.
- “a uniform defect tax excludes length 7” — still false; slack
  tends to 0.

## Formalization

`formal/Problems/Juggler/LeftoverEval.lean` isolates the `Fin 14`
tables and `2^{422}15^{128}<14^{243}`.
`formal/Problems/Juggler/LeftoverCycles.lean` proves
`no_cycle_itinerary_oooooee` and `no_cycle_itinerary_ooooeoe`.
`formal/Problems/Juggler/Cycles.lean` proves the bootstrap pair
`no_cycle_itinerary_ooeoooe` and `no_cycle_itinerary_oooeooe`.
`formal/Problems/Juggler/SmallCycleCensus.lean` assembles
`no_cycle_itinerary_length_le_seven`. No `sorry`. No halt theorem. No
`CycleSearch`. No `PowerBoundEq` attack. No `PowerHeight`.
FloorPower, Progress, and Minimal are not rewritten. Length eight
is open.

## Results

Classification **LENGTH_SEVEN_LEFTOVER_TAIL_GREEN**, with secondary
**TWO_EVEN_TYPE_THROUGH_EIGHT**.

The seven even-terminating expanding itineraries are exactly the predicted
family. Odd-run and internal-E bootstrap cover five of them, up to
rotation. The two leftovers are the length-7 members of the same
families as `OOOOEE` and `OOOEOE`. Both die by the refined tail at
cutoff \(N_0=14\), and the exact tables on \(2\le n<14\) have zero
realizations and zero returns. The naive `OOOOEOE` comparison
\(n^{243}>2^{550}(n+1)^{128}\) also fires, at \(N_0=29\).

The Lean phase packages both leftovers and the bootstrap pair, then
assembles `no_cycle_itinerary_length_le_seven` (**EXACT — LEAN VERIFIED**,
Paper A Lemma 3.7 and Theorem 3.8; ledger rows
`J-leftover-length-seven-orientations` and
`J-small-cycle-census-seven`).

## Open questions

Length 8 is the same two-even type; length 9 is the first three-even
length. Do not open length 8 automatically. Do not start an
O-terminating `CycleItinerary` programme. Do not claim halt.

## Decision

**PROMOTE**. The inventory is the length-6 geometry with one extra
odd letter. Both leftover tails fire at \(N_0=14\), the finite
tables are empty, and Lean now excludes every length-7 cycle itinerary.
This is not a halt theorem and not a length-8 programme.

Best next question: do the same two leftover families exclude every
even-terminating expanding length-8 itinerary, or does a new leftover
shape appear?

## Publication assessment

Status: `EXPLORATORY`.

The length-7 census is now a theorem of Paper A (Theorem 3.8). It
is not a Juggler totality result.
