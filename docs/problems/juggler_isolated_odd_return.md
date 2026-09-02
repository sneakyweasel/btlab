# Juggler isolated-odd prefixes versus short-tail return fibres

Status: **ARCHIVED**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a leftover-suffix
path table, not a predecessor-cell interval census, not a defect
rewrite, not a \(Z_5\) family, not a length-11 assembler, not a
four-even leftover cell, and not a claim that every positive integer
reaches 1.

## Problem

After exact return sets \(R_{b,c}(n)\) are characterized and
**PARK**, can an isolated-odd `CycleMin` prefix land in one of
those fibres?

## Exact statement

Let
\[
S=\{(0,0),(1,0),(2,0),(3,0),(0,1),(1,1),(2,1)\}
\]
and
\[
R_{b,c}(n)=\{y\ge n:T_{O^bEO^cE}(y)=n\}.
\]
An itinerary \(u\) is **isolated-odd** when every maximal odd run has
length \(1\) (equivalently, \(u\) contains no `OO`). Write
\(P_{\mathrm{iso}}(n)\) for the landings \(T_u(n)\) of isolated-odd
words that remain a `CycleMin` prefix at odd \(n\ge 12\). The
Phase-0 question is
\[
P_{\mathrm{iso}}(n)\cap R_{b,c}(n)=\varnothing
\]
for every \((b,c)\in S\).

This is not the parked interval statement \(S_{b,c}(y)\notin[n,y]\).
It is not a four-even cell and not a halt theorem.

## Current literature

- `OE` contracts: \(T_{OE}(x)<x\) for \(x\ge 2\) —
  **EXACT — LEAN VERIFIED** (`oe_block_contracts`).
- `OE` envelope \(T_{OE}(x)^4\le x^3\) —
  **EXACT — LEAN VERIFIED** (`oe_block_scale`).
- No cycle itinerary of length at most six —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_length_le_six`).
- `CycleMin` is `CycleItinerary` plus a path minimum —
  **EXACT — LEAN VERIFIED**.
- Exact return sets \(R_{b,c}(n)\) —
  **PARK** (`J-cyclemin-short-return-census`). The `EE` fibre
  is abundant. Not reopened as a \(y\)-table.
- Defect closure —
  **PARK** (`J-cyclemin-short-defect-obstruction`).
- Leftover-suffix, predecessor cells, front overshoot —
  **PARK**. Not reopened.
- Isolated-odd middle after \(a_0\ge 2\) —
  **PARK** (`J-cyclemin-iso-odd-fibre`). Not reopened.

Project relationship: **reparameterization**. The designated next
question of the parked return and defect branches.

## Branch budget

```text
Mathematical target     P_iso(n) ∩ R_{b,c}(n) empty?
Novelty hypothesis      isolated-odd landings miss the exact
                        short-tail fibres
Falsifier               a broad isolated-odd hit family; OE
                        has no useful inequality
Existing machinery      oe_block_contracts; length ≤ 6 census
Maximum Phase-0 scope   OE block map; isolated-odd family
                        landings; forward R membership; no Lean
Promotion criterion     a reusable exclusion that is not just
                        the two existing Lean lemmas
Stop criterion          KNOWN / REPARAMETERIZATION only;
                        interval table; all-prefix enumeration;
                        Z5 / length-11 / four-even
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(B(x)=T_{OE}(x)\) expands or fixes some odd \(x\ge 3\) —
  **REFUTED**. `oe_block_contracts`. Through odd \(x\le 200\),
  every realized `OE` contracts (43 follows, 0 expands, 0
  fixed)
- repeated \(B^r(n)\) can stay \(\ge n\) —
  **REFUTED**. The first `OE` already drops below \(n\), so
  \((OE)^r\) is not a `CycleMin` prefix
- isolated-odd words with longer even runs (\(OEE\), \(OEEE\),
  \(OEEOE\), \ldots) stay `CycleMin` —
  **REFUTED**. They contain an initial `OE`
- \(P_{\mathrm{iso}}(n)=\{n,T_O(n)\}\) —
  **EXACT — HUMAN PROOF**. The only isolated-odd `CycleMin`
  prefixes are empty and `O`
- \(n\in R_{0,0}(n)\) —
  **REFUTED**. \(R_{0,0}\) is even; CycleMin \(n\) is odd
- \(P_{\mathrm{iso}}(n)\cap R_{b,c}(n)=\varnothing\) —
  **REPARAMETERIZATION**. Empty or single-`O` plus a short tail
  is a `CycleItinerary` of length at most 6
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.isolated_odd_return`
- Records: [juggler_isolated_odd_return.md](../research/juggler_isolated_odd_return.md),
  [juggler_isolated_odd_return.json](../research/juggler_isolated_odd_return.json)
- Tests: `tests/research/juggler_sequence/test_isolated_odd_return.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The hypothesis that \(B\) can expand or stay is **REFUTED**.
Witnesses: \(B(13)=6\), \(B(27)=11\).

The hypothesis that an isolated-odd prefix longer than `O` can
be `CycleMin` is **REFUTED**. Through odd \(12\le n<64\) the
170-word isolated-odd family has 52 landings, all on empty or
`O`, and 0 fibre hits.

The stronger claims that remain false or unproved:

- “\(R_{0,0}(n)\) is empty” — false; it is not the question.
- “every short-cluster CycleMin is impossible” — not claimed.
- “every cycle itinerary is impossible” — not claimed.

## Formalization

None. Existing `Scale.lean` and `SmallCycleCensus.lean` lemmas
are cited, not rewritten. No `no_cycleMin_prefix_short`. No
`no_cycleMin_four_even`. No `no_cycle_itinerary_length_eleven`. No
`no_juggler_cycle`. Paper A is unchanged.

## Results

Classification **ISO_ODD_RETURN_CLOSE**.

An isolated-odd word that contains `OE` contracts at the first
even step (`oe_block_contracts`). CycleMin therefore forbids
every isolated-odd prefix except empty and `O`. Those two
landings are \(\{n,T_O(n)\}\). Composing either with a short
tail \(O^bEO^cE\) produces a `CycleItinerary` of length at most 6,
already excluded.

The Attack-7 dichotomy therefore collapses on this class:
isolated-odd exact closure is impossible, and any remaining
short-cluster `CycleMin` must contain an earlier `OO`.

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

The leftover residual is a bunched-short last cluster whose
prefix already contains `OO`. The isolated-odd-after-first-E
line with \(a_0\ge 2\) is already parked
([juggler_isolated_odd_fibre.md](juggler_isolated_odd_fibre.md)).
Do not write \(Z_5\). Do not assemble
`no_cycle_itinerary_length_eleven`. Do not reopen four-even cells,
the interval seal, or the defect rewrite.

## Decision

**CLOSE**. The intersection \(P_{\mathrm{iso}}\cap R_{b,c}\) is
empty, but only as a reparameterization of `oe_block_contracts`
and `no_cycle_itinerary_length_le_six`. There is no new obstruction.
Do not claim that every cycle itinerary is impossible.

Best next question: the \(a_0\ge 2\) isolated-odd-after-first-E
line is already **PARK**
([juggler_isolated_odd_fibre.md](juggler_isolated_odd_fibre.md)).
Do not reopen four-even cells.

## Publication assessment

Status: `ARCHIVED`.

A named reduction to two existing Lean lemmas. Not a paper
candidate and not a Juggler totality result.
