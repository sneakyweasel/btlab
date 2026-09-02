# Juggler CycleMin fudge versus leftover \(2\)-bound

Status: **THEOREM**

Standalone application phase on the thirty first-expanding
four-even short-gap leftovers. It is **not** a Research Engine
control-layer experiment, not a length-11 census, not a \(Z_5\)
family, not a twenty-three-word hunt, and not a claim that every
positive integer reaches 1.

## Problem

Leftover cells pay \((x+1)/x\le 2\) and leak at length 11. The
exact odd \(+1\)-chain pays CycleMin \(x\ge n\), so
\((x+1)/x\le(n+1)/n\). Does that crossing, with the even sibling,
keep slack \(3^{7}-2^{11}=139\) on every first-expanding leftover
and fire at the first prefix start rather than at leftover
\(N_0\sim 10^{8}\)–\(10^{15}\)?

## Exact statement

Let \(w\) be one of the thirty first-expanding short-gap leftovers
\(O^{a_0}EO^{a_1}EO^{a_2}EO^{a_3}E\). Write \(r\) for the trailing
even-run and \(P\) for the prefix. On a `CycleMin` every later
state is \(\ge n\), so the exact cells compose by
`absorb_odd_step` and the even sibling

\[
n^{A}<(n+1)^{B}(x+1)^{\gamma},\quad n\le x\text{ even}
\implies
n^{A+\gamma}<(n+1)^{B+\gamma}(\lfloor\sqrt{x}\rfloor+1)^{2\gamma}.
\]

After \(P\), `cycle_trailing_evens` puts the image below
\((n+1)^{2^{r}}\). The comparison is \(n^{A}<(n+1)^{A-139}\).
Any seven-odd word that starts \(O\) keeps \(\gamma\) a power of
two and raises on each later odd, so the slack is identically
\(3^{7}-2^{11}=139\), independent of even placement.

For every such \(w\) the integer comparison
\(n^{139}>(1+1/n)^{A-139}\) first holds at some \(N_0\le 29\).
No \(n\) with \(2\le n<30\) follows any of the thirty prefixes.
Hence none of the thirty words is a `CycleMin` word. The eight
leftovers whose only CycleMin-shaped rotation is themselves are
not cycle itineraries. There is no `no_cycle_itinerary_length_eleven` and
no `no_cycle_itinerary_four_even`.

## Current literature

- \(O^{7}\mathrm{EEEE}\) +1-chain —
  **EXACT — LEAN VERIFIED**.
- \(O^{6}\mathrm{EEEOE}\) cell argument —
  **EXACT — HUMAN PROOF**; cycle-itinerary corollary Lean.
- the five `(1,3)` words as `CycleMin` —
  **EXACT — LEAN VERIFIED**; EEE-cell argument human.
- Four-even short-first-gap \(Z_4\) —
  **PARK**. The \(2\)-fudge leaks at length 11 and fires at
  \(a_0+1\) with \(N_0\le 180\).
- Amplify versus surplus; rotation / internal-E; first-E
  transport —
  **REFUTED** / **CLOSE**.
- Even-count \(\le 3\) —
  **EXACT — LEAN VERIFIED**. Period \(\ge 11\).

Project relationship: **extended**. One crossing estimate, thirty
words. Not the \(a_0\ge 8\) tails and not \(e=5\).

## Branch budget

```text
Mathematical target     For the 30 length-11 leftovers, does
                        absorb_odd + absorb_even with x>=n give
                        n^A > (n+1)^{A-139} at the first prefix
                        start?
Novelty hypothesis      leftover N0 is the 2-bound; CycleMin
                        replaces it by (n+1)/n and slack survives
Falsifier               some word has slack <= 0, or chain N0
                        still sits at leftover scale
Existing machinery      absorb_odd_step; trailing-evens cell;
                        30-word list; O^7 / (1,3) chains
Maximum Phase-0 scope   exponent machine on 30 words; Lean
                        CycleMin exclusion; no Z5, no census
Promotion criterion     slack 139 on every itinerary and chain N0
                        at or below the first prefix start
Stop criterion          slack <= 0; leftover-scale N0; a
                        23-word rescue
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- slack on any 7-odd word starting \(O\) is \(3^{7}-2^{11}=139\) —
  **EXACT — LEAN VERIFIED** (`family_slack139`)
- the thirty first-expanding leftovers have chain \(N_0\le 29\) —
  **EXACT — LEAN VERIFIED** (`succ_pow_slack139_of_ge_30`)
- no prefix start exists for \(2\le n<30\) —
  **EXACT — LEAN VERIFIED** (`noFollowsFrom2Below`)
- the thirty words are not `CycleMin` words —
  **EXACT — LEAN VERIFIED** (`no_cycleMin_cyclemin_fudge`)
- the eight unique-rotation leftovers are not cycle itineraries —
  **EXACT — LEAN VERIFIED**
- leftover \(2\)-fudge unused —
  **COMPUTATIONALLY VERIFIED**
- no cycle of length 11 — not claimed
- no four-even cycle — not claimed
- the tails \(a_0>a_0^*\) —
  taken up by [juggler_cyclemin_tails](juggler_cyclemin_tails.md)
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cyclemin_fudge`
- Records: [juggler_cyclemin_fudge.md](../research/juggler_cyclemin_fudge.md),
  [juggler_cyclemin_fudge.json](../research/juggler_cyclemin_fudge.json)
- Tests: `tests/research/juggler_sequence/test_cyclemin_fudge.py`
- Finite checks: chain \(N_0\) between \(16\) and \(29\); first
  prefix starts between \(37\) and \(2935\); pin \(n<30\) empty.
- Lean: `Problems/Juggler/CycleMinFudge.lean`. Paper A is unchanged.

## Conjectures

None opened.

## Counterexamples

None to the fudge. The stronger claims that fail:

- “even placement eats slack \(139\)” — the slack is identically
  \(139\) under CycleMin crossings and the trailing-even cell.
- “the layer needs leftover \(N_0\sim 10^{8}\)” — the exact
  crossing fires by \(n=29\).
- “this is a length-11 census” — thirty named leftovers.
- “four-even leftovers are finished” — the \(a_0\ge 8\) tails
  were not opened.

## Formalization

`Problems/Juggler/CycleMinFudge.lean`, imported by the laboratory
barrel, not by `JugglerPaper`. `absorb_even_step`,
`family_slack139`, `no_cycleMin_cyclemin_fudge`, named
`no_cycleMin_*` for all thirty leftovers, and unique-rotation
`no_cycle_itinerary_*` including `no_cycle_itinerary_ooooooeeeoe` and
`no_cycle_itinerary_ooooooeoeee`. `SmallCycleCensus.lean` still
assembles only through length seven. No
`no_cycle_itinerary_length_eleven`. No `no_cycle_itinerary_four_even`.
No `no_cycle_itinerary_cyclemin_fudge`. No `sorry`. No halt theorem.
Paper A is unchanged.

## Results

Classification **CYCLEMIN_FUDGE_LAYER_PROVED**.

The leftover \(2\)-bound was the threshold obstruction. Replacing
it by CycleMin \((n+1)/n\) keeps slack \(139\) on every
first-expanding leftover, independent of even placement. The
integer comparison fires at \(N_0\le 29\). No prefix start
exists below \(30\). The thirty length-11 short-gap leftovers
are not `CycleMin` words. The eight unique-rotation leftovers
are not cycle itineraries.

This is not a four-even assembler. The tails \(a_0>a_0^*\)
were taken up by [juggler_cyclemin_tails](juggler_cyclemin_tails.md).

## Open questions

The tails \(a_0>a_0^*\) are recorded in
[juggler_cyclemin_tails](juggler_cyclemin_tails.md). Do not
write \(Z_5\). Do not assemble `no_cycle_itinerary_length_eleven`.

## Decision

**PROMOTE** the CycleMin crossing. Even placement does not eat
the first-expanding slack once \((x+1)/x\le 2\) is replaced by
\((x+1)/x\le(n+1)/n\). This is not a halt result and not a
length-11 census.

Best next question: stop. The tail slack identity is Lean
(`J-cyclemin-slack`). Do not open \(e=5\).

## Publication assessment

Status: `THEOREM`. A uniform Lean `CycleMin` exclusion of the
thirty first-expanding short-gap leftovers by one crossing
estimate, not a paper candidate and not a Juggler totality
result.
