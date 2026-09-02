# Juggler EOO square-root cell mechanism

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Why does the formally expanding itinerary `EOO` contract exactly at
\(n\in\{2,12,14\}\)? Can that finite list be replaced by a square-root
cell threshold on the intermediate state \(q=\lfloor\sqrt n\rfloor\)?

## Exact statement

Write

\[
n\overset E\longmapsto q=\lfloor\sqrt n\rfloor
\overset O\longmapsto b=\lfloor q^{3/2}\rfloor
\overset O\longmapsto c=\lfloor b^{3/2}\rfloor.
\]

For fixed \(q\), is \(c\) constant on the cell \([q^2,(q+1)^2)\), and
does a realized `EOO` start contract if and only if \(n>c\)? Which
cells then meet the threshold?

This is a local arithmetic question. It is not a termination theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Phase-17 (`juggler_power_itineraries`): weak envelope
  \(T_w(n)^{2^k}\le n^{3^o}\) **EXACT — LEAN VERIFIED**.
- Previous phase (`juggler_compensated_contraction`):
  \(\Delta>G\Rightarrow T_w(n)<n\) **EXACT — LEAN VERIFIED**;
  `EOO` contracts iff \(n\in\{2,12,14\}\) **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The enumerated `EOO` classification
is explained by cell constancy plus an output threshold.

## Branch budget

```text
Mathematical target     Why does EOO contract exactly at 2, 12, 14?
Novelty hypothesis      Cell constancy plus the threshold n > c(q)
                        replaces the enumerated list
Falsifier               Output varies on a cell, or n>c fails, or
                        another cell contracts
Existing machinery      PowerBound, eoo_contracts_iff, Nat.sqrt cells
Maximum Phase-0 scope   Named cell lemmas; OOE/OEO contrast;
                        length-4 first-even check
Promotion criterion     Lean cell/threshold explanation of the three
                        starts, or a minimized cell counterexample
Stop criterion          Generic cell calculus; PowerHeight; engine
                        edits; termination claim; infinite-family hunt
                        before the EOO mechanism is named
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Square-root cell \(n.\mathrm{sqrt}=q\iff q^2\le n<(q+1)^2\) —
  **EXACT — LEAN VERIFIED**
- `follows(n,EOO)` iff \(n\) even, \(q\) odd, \(\lfloor q^{3/2}\rfloor\)
  odd — **EXACT — LEAN VERIFIED**
- `EOO` output equals `eooCellOutput q` and is constant on the cell —
  **EXACT — LEAN VERIFIED**
- Contraction iff \(n>\mathrm{eooCellOutput}\,q\) —
  **EXACT — LEAN VERIFIED**
- \(q=1\Rightarrow c=1\); \(q=3\Rightarrow c=11\);
  \(q\ge5\Rightarrow c\ge(q+1)^2\) —
  **EXACT — LEAN VERIFIED**
- `OOE`/`OEO` freeze on n-sqrt cells — **REFUTED**
  computationally: those itineraries vary inside the start cell
- Length-4 mixed \(o=3\) infinite contraction family —
  **REFUTED** on the scanned window; `EOOO` contracts only at \(n=2\)
- Generic cell calculus — not added
- `PowerHeight` — not added

## Experiments

- Probe: `research.juggler_sequence.eoo_cell_mechanism`
- Records: [juggler_eoo_cell_mechanism.md](../research/juggler_eoo_cell_mechanism.md),
  [juggler_eoo_cell_mechanism.json](../research/juggler_eoo_cell_mechanism.json)
- Tests: `tests/research/juggler_sequence/test_eoo_cell_mechanism.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

- `n=10` realizes `EOO` in the \(q=3\) cell with output \(c=11\), and
  \(10\not>11\), so it expands. Same cell as \(12\) and \(14\).
- `OOE` and `OEO` are not constant on n-sqrt cells (first letter odd).
- First-defect residues \(r=1,3,5\) at the three contraction starts
  are not a reusable three-point pattern beyond “same cell, \(n>c\)”.

## Formalization

`formal/Problems/Engine/FloorPower.lean`. Added:

- `sqrt_cell_iff`
- `eooCellOutput`
- `follows_eoo_sqrt_iff`
- `eoo_output_eq_cell` / `eoo_output_constant_on_sqrt_cell`
- `eoo_contracts_on_cell`
- `eoo_cell_output_one` / `eoo_cell_output_three` /
  `eoo_cell_output_ge_succ_sq`

Unchanged: `power_bound_compensated_contracts`,
`floorPower_eoo_contracts_iff`. The certificate stays generic. The new
lemmas classify one word.

No `PowerHeight`. No `sorry`. No `mixed_word_power_lt`. No ledger row.

## Results

Classification **EOO_CELL_MECHANISM_GREEN**.

On a realized `EOO` start, \(T^3(n)=\mathrm{eooCellOutput}\,q\) with
\(q=\lfloor\sqrt n\rfloor\), and

\[
T^3(n)<n\iff n>\mathrm{eooCellOutput}\,q.
\]

The only cells with \(c<(q+1)^2\) are \(q=1\) (\(c=1\), start \(2\))
and \(q=3\) (\(c=11\), starts \(12,14\)). For \(q\ge5\),
\(c\ge(q+1)^2>n\), so the threshold interval is empty.

`EOOO` uses the same first-even freeze. The extra odd step sends the
\(q=3\) output from \(11\) to \(36>(4)^2\), so only \(n=2\) contracts.
That is a related first-even observation, not a parametrized family.

`OOE` and `OEO` do not freeze on the start square-root cell.

This is not a termination theorem and not a generic cell calculus.

## Open questions

Do `OOE` and `OEO` never contract? Is there a first-even
positive-drift word whose cell output lies strictly inside
\((q^2,(q+1)^2)\) for infinitely many odd \(q\)?

## Decision

**PROMOTE** the EOO cell/threshold classification
`EOO_CELL_MECHANISM_GREEN`. Record the first-even pattern on `EOOO`
without claiming `POSITIVE_DRIFT_CONTRACTION_FAMILY`. Keep the
generic certificate separate from this itinerary-specific geometry. Do not
register an attack. Do not claim termination. Do not add a generic
cell calculus.

Best next question: prove `OOE`/`OEO` never contract, or find a
first-even positive-drift word whose cell output sits strictly inside
\((q^2,(q+1)^2)\) for infinitely many odd \(q\).

## Publication assessment

Status: `EXPLORATORY`. A local finite-itinerary cell classification, not a
paper candidate and not a Juggler totality result.
