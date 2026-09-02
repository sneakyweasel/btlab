# Juggler length-8 cycle-itinerary census

Status: **EXPLORATORY**

Standalone laboratory assembly on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It does not edit Paper A and does
not start a length-9 census.

## Problem

Do the named filters already in Lean exclude every cycle itinerary of
length at most eight?

## Exact statement

A length-8 word is formally expanding if and only if it has at least
six odd letters (\(2^8=256<729=3^6\)). Every mixed cycle itinerary rotates
to an even-terminating orientation. The even-terminating expanding
candidates are exactly

\[
OOOOOOOE,\ 
EOOOOOOE,\ 
OEOOOOOE,\ 
OOEOOOOE,\ 
OOOEOOOE,\ 
OOOOEOOE,\ 
OOOOOEOE,\ 
OOOOOOEE.
\]

These are already named: odd-run \(O^7E\), Theorem 3.12 at \(k=8\)
(and the two rotations onto those leftovers), and the internal-E
bootstrap itineraries \(OOOOEOOE\), \(OOOEOOOE\), \(OOEOOOOE\). The
laboratory theorem `no_cycle_itinerary_length_le_eight` assembles them
together with the length-≤7 census. Paper A Corollary 3.23 implies
the same exclusion (period at least eleven). This is not a halt
theorem.

## Current literature

- Small-cycle census (Paper A Theorems 3.6 and 3.8) —
  **EXACT — LEAN VERIFIED**. No cycle itinerary of length at most seven.
- Two-even leftover families (Paper A Theorem 3.12) —
  **EXACT — LEAN VERIFIED**. Includes \(k=8\).
- Length-8 two-even squares —
  **REPARAMETERIZATION**. The suspected leftovers are OO/OOO
  bootstrap. That `CLOSE` is not reopened as a leftover cell.
- Length 9 and the thirty length-11 leftovers — not this branch.

Project relationship: **extended**. Laboratory census bound moves
from 7 to 8. Paper A is unchanged.

## Branch budget

```text
Mathematical target     Assemble no_cycle_itinerary_length_le_eight from
                        the named filters already in Lean
Novelty hypothesis      packaging: the census bound moves from 7 to 8
Falsifier               a length-8 expanding even-terminating word
                        with no CycleItinerary exclusion
Existing machinery      Theorem 3.12, odd-run, internal-E threshold,
                        exists_cycleMin, length-7 assembler
Maximum Phase-0 scope   CycleItinerary for the three bootstrap itineraries;
                        assembler; ledger; no Paper A
Promotion criterion     Lean no_cycle_itinerary_length_le_eight, sorry-free
Stop criterion          an itinerary that needs a new leftover cell
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- even-terminating expanding length-8 family is the eight words
  above — **COMPUTATIONALLY VERIFIED**
- `OOOOOOOE` is odd-run `no_cycle_odd_run_append_even` at \(a=7\) —
  **EXACT — LEAN VERIFIED**
- `OOOOOOEE` / `OOOOOEOE` are Theorem 3.12 at \(k=8\) —
  **EXACT — LEAN VERIFIED**
- `EOOOOOOE` / `OEOOOOOE` rotate onto those leftovers —
  **EXACT — LEAN VERIFIED**
- `OOOOEOOE` / `OOOEOOOE` / `OOEOOOOE` are internal-E bootstrap —
  **EXACT — LEAN VERIFIED**
- every length-8 cycle itinerary is impossible —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_length_le_eight`)
- cycles of length nine or more are impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_length_eight`
- Records: [juggler_cycle_length_eight.md](../research/juggler_cycle_length_eight.md),
  [juggler_cycle_length_eight.json](../research/juggler_cycle_length_eight.json)
- Tests: `tests/research/juggler_sequence/test_cycle_length_eight.py`
- Lean: `formal/Problems/Juggler/LengthEightCensus.lean`. Not imported
  by `Problems.JugglerPaper`. No `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

None to the inventory or to the assembler. The stronger claims that
remain unproved:

- “every length-9 word is Lean-excluded” — not claimed.
- “there are no Juggler cycles” — not claimed.

## Formalization

`formal/Problems/Juggler/LengthEightCensus.lean` proves
`no_cycle_itinerary_ooooeooe`, `no_cycle_itinerary_oooeoooe`,
`no_cycle_itinerary_ooeooooe`, and assembles
`no_cycle_itinerary_length_le_eight`. `SmallCycleCensus.lean` still
assembles only through length seven and records that length eight is
open in that module. No `no_cycle_itinerary_length_eight`. No
`sorry`. No halt theorem. Paper A Corollary 3.23 implies period
at least eleven.

## Results

Classification **LENGTH_EIGHT_CENSUS_GREEN**.

No `n\ge 2` realizes a cycle itinerary of length at most eight. A
nontrivial cycle, if one exists, has period at least nine. Paper A
Corollary 3.23 is stronger (period at least eleven). This is not a
halt theorem.

## Open questions

Length 9 is the first three-even even-terminating expanding length.
Do not assemble `no_cycle_itinerary_length_le_nine` automatically. Do
not claim halt. Do not reopen the thirty length-11 leftovers.

## Decision

**PROMOTE**. The eight expanding even-terminating length-8 words were
already named. The missing pieces were CycleItinerary theorems for the
three bootstrap spellings and an assembler. Both are now sorry-free
Lean. This is not a halt theorem and not a length-9 programme.

Best next question: assemble `no_cycle_itinerary_length_le_nine` from
named leftover families, or stop.

## Publication assessment

Status: `EXPLORATORY`.

A laboratory census strengthening. Not imported into Paper A. Not a
Juggler totality result.
