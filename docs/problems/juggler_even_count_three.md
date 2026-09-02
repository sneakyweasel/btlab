# Juggler even-count ≤ 3 cycle itineraries

Status: **PROMOTE**. Imported into Paper A as Theorem 3.22.

Standalone laboratory assembly on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It is not a length-9 or length-10
itinerary census, not first-E transport at \(e\ge 4\), and not induction on
\(n\) or on the period.

## Problem

Is every cycle itinerary with at most three even letters already excluded
by the named leftover families, so that a nontrivial cycle — if one
exists — has at least four evens and therefore period at least eleven?

## Exact statement

Every mixed cycle itinerary has a `CycleMin` rotation. A cycle minimum
starts `OO`, ends `E`, and is formally expanding. The even-terminating
expanding itineraries with even-count \(e\le 3\) are exactly the odd-run
family, the two-even leftovers (Theorem 3.12), the internal-E
bootstrap, the seven bunched leftovers (Theorems 3.14--3.20), and the
gapped leftovers (Theorems 3.13 and 3.21), or start-`E`/`OE`
rotations onto those families.

Paper A Theorem 3.22 (`no_cycle_itinerary_even_count_le_three`) excludes
every such `CycleItinerary`. Corollary 3.23 (`cycle_itinerary_length_ge_eleven`)
is the expansion demand after four evens. The laboratory leftover
is the finance residual (`cycle_itinerary_length_nineteen_or_ge_thirty`
in `CycleFinance.lean`); this file does not import finance.

A free leftover corollary: the return-to-\(n\) cell of
`minimal_first_even_dichotomy` is an even-count-1 cycle itinerary, so it
is excluded. On `MinimalNonTerm` or `CycleMin` the first even
residual therefore overshoots
(`minimal_first_even_overshoots`,
`cycleMin_first_even_overshoots`). That sharpens the leftover
start, and the cycle-extrema corollary is \(M\ge(m+1)^2\)
(`cycleMin_max_ge_succ_sq`, `cycleMax_min_succ_sq_le`): first-cell
maxima are impossible and \(T(M)>m\). It does not exclude a
four-even word and is not a halt theorem.

This is not a length-9 or length-10 itinerary census. Paper A states
the even-count assembly as Theorem 3.22. There is no
`no_cycle_itinerary_length_nine` and no halt theorem.

## Current literature

- Small-cycle census (Paper A Theorems 3.6 and 3.8) —
  **EXACT — LEAN VERIFIED**. No cycle itinerary of length at most seven.
- Laboratory length-8 census —
  **EXACT — LEAN VERIFIED**. Implied by Paper A Corollary 3.23
  (period \(\ge 11\)). Not reopened as a length census.
- Uniform two-even leftover families (Paper A Theorem 3.12) —
  **EXACT — LEAN VERIFIED**.
- Gapped three-even leftovers (Theorems 3.13 and 3.21) —
  **EXACT — LEAN VERIFIED**.
- Seven bunched last-cluster families (Theorems 3.14--3.20) —
  **EXACT — LEAN VERIFIED**.
- Internal-E bootstrap —
  **EXACT — LEAN VERIFIED**.
- Four-even short-first-gap —
  **PARK**. The leftover-cell path leaks at the first expanding
  \(a_0\). That `PARK` is not reopened.

Project relationship: **extended**. The leftover families are one
even-count partition, not a new shape at each length.

## Branch budget

```text
Mathematical target     Is every cycle itinerary with at most three
                        even letters already excluded by named
                        filters (so any nontrivial cycle has
                        length at least 11)?
Novelty hypothesis      Theorems 3.12--3.21 plus bootstrap and
                        rotation already partition e≤3; length
                        9 and 10 add no new leftover geometry
Falsifier               An even-terminating expanding itinerary with
                        e≤3 whose necklace misses every named
                        filter (start-E/OE glue fails)
Existing machinery      leftover_prefix_preimage; Thms 3.12--3.21;
                        no_cycleMin_internal_even_threshold;
                        rotation; expansion filter
Maximum Phase-0 scope   Necklace inventory of even-terminating
                        expanding itineraries with e≤3 for lengths
                        9..16; one Lean even-count theorem.
                        No length-9 Lean census, no e=4 cells.
                        Paper A now states Theorem 3.22
Promotion criterion     Every such necklace hits a named filter;
                        then a single Lean theorem
                        no_cycle_itinerary_even_count_le_three
Stop criterion          A missed necklace; or the work becomes
                        per-length assembler files
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- every even-terminating expanding itinerary with \(e\le 3\) at
  lengths 9..16 hits a named filter or start-`E`/`OE` glue —
  **COMPUTATIONALLY VERIFIED**
- `e=0` all-odd and `e=1` odd-run are excluded —
  **EXACT — LEAN VERIFIED**
- `e=2` is Theorem 3.12 or last-gap bootstrap —
  **EXACT — LEAN VERIFIED**
- `e=3` is bootstrap, bunched, or gapped —
  **EXACT — LEAN VERIFIED**
- no cycle itinerary has even-count \(\le 3\) —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_even_count_le_three`)
- a nontrivial cycle itinerary has length at least 11 —
  **EXACT — LEAN VERIFIED** (`cycle_itinerary_length_ge_eleven`);
  the finance leftover (period \(19\) or \(\ge 30\)) is
  independent and lives in `CycleFinance.lean`
- first even residual overshoots on `MinimalNonTerm` /
  `CycleMin` —
  **EXACT — LEAN VERIFIED**
  (`minimal_first_even_overshoots`,
  `cycleMin_first_even_overshoots`)
- cycle maximum sits at or above \((m+1)^2\) —
  **EXACT — LEAN VERIFIED**
  (`cycleMin_max_ge_succ_sq`, `cycleMax_min_succ_sq_le`,
  `cycleMax_landing_gt_min`,
  `cycle_distinguished_order_succ_sq`)
- cycles of length 11 or more are impossible — not claimed
- four-even leftovers die — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.even_count_three`
- Records: [juggler_even_count_three.md](../research/juggler_even_count_three.md),
  [juggler_even_count_three.json](../research/juggler_even_count_three.json)
- Tests: `tests/research/juggler_sequence/test_even_count_three.py`
- Lean: `formal/Problems/Juggler/EvenCountThree.lean`. Imported
  by `Problems.JugglerPaper` as Paper A Theorem 3.22. No `sorry`.
  No halt theorem.

## Conjectures

None opened.

## Counterexamples

None to the necklace inventory or to the even-count assembler. The
stronger claims that remain unproved:

- “every length-9 word is Lean-excluded as a census” — not claimed.
- “there are no Juggler cycles” — not claimed.
- “leftover cells kill \(e=4\)” — **REFUTED** at the first
  expanding layer (four-even short-gap `PARK`).

## Formalization

`formal/Problems/Juggler/EvenCountThree.lean` proves
`no_cycleMin_even_count_le_three`,
`no_cycle_itinerary_even_count_le_three`,
`cycle_itinerary_even_count_ge_four`,
`cycle_itinerary_length_ge_eleven`,
`minimal_first_even_overshoots`,
`cycleMin_first_even_overshoots`,
`cycleMin_max_ge_succ_sq`,
`cycleMax_min_succ_sq_le`,
`cycleMax_landing_gt_min`,
`cycleMax_exists_min_succ_sq`, and
`cycle_distinguished_order_succ_sq`. `SmallCycleCensus.lean` still
assembles only through length seven. `LengthEightCensus.lean` remains
the laboratory length-8 assembler. No `no_cycle_itinerary_length_nine`.
No `no_cycle_itinerary_length_le_nine`. No `sorry`. No halt theorem.
Paper A states Theorem 3.22 / Corollary 3.23.

## Results

Classification **EVEN_COUNT_THREE_GREEN**.

No \(n\ge 2\) realizes a cycle itinerary with at most three even letters.
A nontrivial cycle, if one exists, has period at least eleven by
even-count; the laboratory leftover is the finance residual
(period \(19\) or \(\ge 30\)). On a leftover start the first even
residual overshoots; return-to-\(n\) is dead. The extrema corollary is \(M\ge(m+1)^2\). This is Paper A
Theorem 3.22, not a four-even exclusion, not a length-9
itinerary census, and not a halt theorem.

## Open questions

The leftover-cell path is parked at four evens. Do not assemble
`no_cycle_itinerary_length_le_nine` or `no_cycle_itinerary_length_le_ten`.
Do not open \(e=5\) cells. Do not claim halt.

## Decision

**PROMOTE**. The \(e\le 3\) necklace inventory at lengths 9..16 is
complete, and the Lean assembler excludes every such `CycleItinerary`.
Period \(\ge 11\) is the expansion corollary. This is not a halt
theorem and not a length census.

Best next question: a new method for \(e\ge 4\), not a length-11
census.

## Publication assessment

Status: imported into Paper A as Theorem 3.22 / Corollary 3.23.

An even-count strengthening of the leftover families. Not a
Juggler totality result.
